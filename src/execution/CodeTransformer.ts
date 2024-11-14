import * as FileSystem from "fs";
import * as Path from "path";
import * as Ts from "ts-morph";

import {makeResolvedFunctionPathKey, resolveCalledExpression} from "#r/analysis/FunctionResolver";
import type {ResolvedFunctionPath} from "#r/analysis/FunctionResolver";
import CoverageKind from "./CoverageKind.js";

type ExtractionResult = {precedingCode: string, newExpression: string};

let nextGeneratedVariableId = 0;

function generateVariableName() {
	++nextGeneratedVariableId;
	return `__concolic\$${nextGeneratedVariableId}`;
}

function ensureCodeBlock(code: string, isStandalone: boolean): string {
	return isStandalone ? `{\n${code}\n}\n` : code;
}

export default class CodeTransformer {
	#originalPath: string;
	#destinationPath: string;
	#coverageKind: CoverageKind;
	#mockedFunctionKeys: Set<string> = new Set<string>();
	#project!: Ts.Project;
	#currentFileHasMocks: boolean = false;

	constructor(
		originalPath: string, destinationPath: string, coverageKind: CoverageKind,
		mockedFunctions: ResolvedFunctionPath[]
	) {
		this.#originalPath = originalPath;
		this.#destinationPath = destinationPath;
		this.#coverageKind = coverageKind;
		this.#mockedFunctionKeys = new Set<string>(mockedFunctions.map(makeResolvedFunctionPathKey));
	}

	async transform(): Promise<void> {
		const isPredicateCoverage = this.#coverageKind === CoverageKind.PREDICATE;
		const transformationInfoFilePath = Path.join(this.#destinationPath, "__concolic_transformed.json");
		let shouldTransform = false;
		if (FileSystem.existsSync(transformationInfoFilePath)) {
			const transformationInfo = JSON.parse(FileSystem.readFileSync(transformationInfoFilePath, "utf8")) as {
				transformedForPredicateCoverage: boolean, transformedFiles: string[]
			};
			//if (isPredicateCoverage !== transformationInfo.transformedForPredicateCoverage) {
				for (const filePath of transformationInfo.transformedFiles) FileSystem.copyFileSync(
					Path.join(this.#originalPath, filePath), Path.join(this.#destinationPath, filePath)
				);
				shouldTransform = true;
			//}
		} else {
			shouldTransform = true;
		}
		if (shouldTransform) {
			this.#project = new Ts.Project({tsConfigFilePath: Path.join(this.#destinationPath, "tsconfig.json")});
			const transformedFiles: string[] = [];
			for (const sourceFile of this.#project.getSourceFiles()) {
				if (Path.basename(sourceFile.getFilePath()).startsWith("__concolic")) continue;
				for (const functionDeclaration of sourceFile.getFunctions())
					this.#transformStatement(functionDeclaration.getBody()! as Ts.Statement, false);
				if (this.#currentFileHasMocks) {
					sourceFile.addStatements(
						"declare global { var __concolic$mockedValues: any[]; }\n"
						+ "function __concolic$mock<T = any>(key: string): T {\n"
						+ "    return globalThis.__concolic$mockedValues.shift() as T;\n"
						+ "}"
					);
					this.#currentFileHasMocks = false;
				}
				transformedFiles.push(Path.relative(this.#destinationPath, sourceFile.getFilePath()));
			}
			await this.#project.save();
			FileSystem.writeFileSync(
				transformationInfoFilePath,
				JSON.stringify({transformedForPredicateCoverage: isPredicateCoverage, transformedFiles}),
				"utf8"
			);
		}
	}

	#transformStatement(statement: Ts.Statement, isStandalone: boolean): void {
		switch (statement.getKind()) {
			case Ts.SyntaxKind.Block:
				for (const subStatement of (statement as Ts.Block).getStatements())
					this.#transformStatement(subStatement, false);
				break;
			case Ts.SyntaxKind.VariableStatement: {
				const newCode = this.#transformVariableDeclarationList(statement as Ts.VariableStatement);
				if (newCode !== null) statement.replaceWithText(ensureCodeBlock(newCode, isStandalone));
				break;
			}
			case Ts.SyntaxKind.ExpressionStatement: {
				const assignmentExpression = (statement as Ts.ExpressionStatement).getExpression();
				if (
					!Ts.Node.isBinaryExpression(assignmentExpression)
					|| assignmentExpression.getOperatorToken().getText() !== "="
				) break;
				const extractedCode = this.#extractConditionalExpression(assignmentExpression.getRight());
				if (extractedCode === null) break;
				statement.replaceWithText(ensureCodeBlock(
					extractedCode.precedingCode
					+ `${assignmentExpression.getLeft().getText()} = ${extractedCode.newExpression};`,
					isStandalone
				));
				break;
			}
			case Ts.SyntaxKind.ReturnStatement: {
				const returnExpression = (statement as Ts.ReturnStatement).getExpression();
				if (returnExpression === undefined) break;
				const extractedCode = this.#extractConditionalExpression(returnExpression);
				if (extractedCode === null) break;
				statement.replaceWithText(ensureCodeBlock(
					extractedCode.precedingCode + `return ${extractedCode.newExpression};`, isStandalone
				));
				break;
			}
			case Ts.SyntaxKind.IfStatement: {
				const ifStatement = statement as Ts.IfStatement;
				const thenStatement = ifStatement.getThenStatement();
				this.#transformStatement(thenStatement, true);
				const elseStatement = ifStatement.getElseStatement();
				if (elseStatement !== undefined) this.#transformStatement(elseStatement, true);
				const extractedCondition = this.#extractConditionalExpression(ifStatement.getExpression());
				if (extractedCondition === null) break;
				ifStatement.replaceWithText(ensureCodeBlock(
					extractedCondition.precedingCode
					+ `if (${extractedCondition.newExpression}) ${thenStatement.getText()}`
					+ (elseStatement === undefined ? "\n" : ` else ${elseStatement.getText()}\n`),
					isStandalone
				));
				break;
			}
			case Ts.SyntaxKind.WhileStatement: {
				const whileStatement = statement as Ts.WhileStatement;
				const bodyStatement = whileStatement.getStatement();
				this.#transformStatement(bodyStatement, true);
				const extractedCondition = this.#extractConditionalExpression(whileStatement.getExpression());
				if (extractedCondition === null) break;
				whileStatement.replaceWithText(
					"while (true) {\n"
					+ extractedCondition.precedingCode
					+ `if (!${extractedCondition.newExpression}) break;\n`
					+ `${bodyStatement.getText()}\n`
					+ "}\n"
				);
				break;
			}
			case Ts.SyntaxKind.ForStatement: {
				const forStatement = statement as Ts.ForStatement;
				const bodyStatement = forStatement.getStatement();
				this.#transformStatement(bodyStatement, true);
				const initializer = forStatement.getInitializer();
				let extractedInitializer: string | null = null;
				if (initializer !== undefined) {
					if (Ts.Node.isExpression(initializer)) {
						const extractionResult = this.#extractConditionalExpression(initializer);
						if (extractionResult !== null) extractedInitializer = (
							extractionResult.precedingCode + extractionResult.newExpression + ";"
						);
					} else {
						extractedInitializer = this.#transformVariableDeclarationList(initializer);
					}
				}
				const condition = forStatement.getCondition();
				const extractedCondition
					= condition === undefined ? null : this.#extractConditionalExpression(condition);
				const incrementor = forStatement.getIncrementor();
				const extractedIncrementor
					= incrementor === undefined ? null : this.#extractConditionalExpression(incrementor);
				if (extractedInitializer === null && extractedCondition === null && extractedIncrementor === null)
					break;
				let newCode = "";
				const shouldMakeOuterBlock = extractedInitializer !== null || extractedCondition !== null;
				if (shouldMakeOuterBlock) newCode += "{\n";
				if (extractedInitializer !== null) {
					newCode += extractedInitializer;
					newCode += "\n";
				}
				if (extractedCondition !== null) {
					newCode += extractedCondition.precedingCode;
					newCode += `while (${extractedCondition.newExpression}) `;
				} else {
					newCode += `while (${condition === undefined ? "true" : condition.getText()}) `;
				}
				if (extractedIncrementor !== null) newCode += "{\n";
				newCode += bodyStatement.getText();
				newCode += "\n";
				if (extractedIncrementor !== null) {
					newCode += extractedIncrementor.precedingCode;
					newCode += extractedIncrementor.newExpression;
					newCode += ";\n}\n";
				}
				if (shouldMakeOuterBlock) newCode += "}\n";
				forStatement.replaceWithText(newCode);
				break;
			}
		}
	}

	#transformVariableDeclarationList(
		variableDeclarationList: Ts.VariableDeclarationList | Ts.VariableStatement
	): string | null {
		const declarations = variableDeclarationList.getDeclarations();
		const extractedCodes = declarations.map(declaration => {
			const initializer = declaration.getInitializer();
			return initializer === undefined ? null : this.#extractConditionalExpression(initializer);
		});
		if (extractedCodes.every(code => code === null)) return null;
		let declarationKeywords
			= variableDeclarationList.getDeclarationKindKeywords().map(keyword => keyword.getText()).join(' ');
		let newCode = "";
		for (let i = 0; i !== declarations.length; ++i) {
			const declaration = declarations[i];
			const type = declaration.getTypeNode();
			const extractedCode = extractedCodes[i];
			if (i !== 0) newCode += '\n';
			if (extractedCode === null) {
				const initializer = declaration.getInitializer();
				newCode += (
					declarationKeywords + ' ' + declaration.getName()
					+ (type === undefined ? "" : ": " + type.getText())
					+ (initializer === undefined ? "" : " = " + initializer.getText())
					+ ';'
				);
			} else {
				newCode += (
					extractedCode.precedingCode
					+ declarationKeywords + ' ' + declaration.getName()
					+ (type === undefined ? "" : ": " + type.getText())
					+ " = " + extractedCode.newExpression
					+ ';'
				);
			}
		}
		return newCode;
	}

	#extractConditionalExpression(expression: Ts.Expression): ExtractionResult | null {
		switch (expression.getKind()) {
			case Ts.SyntaxKind.ParenthesizedExpression: {
				const parenthesizedExpression = expression as Ts.ParenthesizedExpression;
				const extracted = this.#extractConditionalExpression(parenthesizedExpression.getExpression());
				return extracted === null ? null : {
					precedingCode: extracted === null ? "" : extracted.precedingCode,
					newExpression: "(" + (
						extracted === null ? parenthesizedExpression.getExpression().getText() : extracted.newExpression
					) + ")"
				};
			}
			case Ts.SyntaxKind.PrefixUnaryExpression: {
				const unaryExpression = expression as Ts.PrefixUnaryExpression;
				const extracted = this.#extractConditionalExpression(unaryExpression.getOperand());
				return extracted === null ? null : {
					precedingCode: extracted === null ? "" : extracted.precedingCode,
					newExpression: (
						Ts.ts.tokenToString(unaryExpression.getOperatorToken())
						+ (extracted === null ? unaryExpression.getOperand().getText() : extracted.newExpression)
					)
				};
			}
			case Ts.SyntaxKind.PostfixUnaryExpression: {
				const unaryExpression = expression as Ts.PostfixUnaryExpression;
				const extracted = this.#extractConditionalExpression(unaryExpression.getOperand());
				return extracted === null ? null : {
					precedingCode: extracted === null ? "" : extracted.precedingCode,
					newExpression: (
						(extracted === null ? unaryExpression.getOperand().getText() : extracted.newExpression)
						+ Ts.ts.tokenToString(unaryExpression.getOperatorToken())
					)
				};
			}
			case Ts.SyntaxKind.BinaryExpression: {
				const binaryExpression = expression as Ts.BinaryExpression;
				const extractedLeft = this.#extractConditionalExpression(binaryExpression.getLeft());
				const extractedRight = this.#extractConditionalExpression(binaryExpression.getRight());
				if (this.#coverageKind === CoverageKind.PREDICATE) {
					const operator = binaryExpression.getOperatorToken().getText();
					if (operator === "&&") {
						const generatedVariableName = generateVariableName();
						return {
							precedingCode: (
								(extractedLeft === null ? "" : extractedLeft.precedingCode)
								+ `let ${generatedVariableName}: ${binaryExpression.getType().getText()} = ${
									extractedLeft === null
									? binaryExpression.getLeft().getText() : extractedLeft.newExpression
								};\n`
								+ `if (${generatedVariableName}) {\n`
								+ (extractedRight === null ? "" : extractedRight.precedingCode)
								+ `${generatedVariableName} = ${
									extractedRight === null
									? binaryExpression.getRight().getText() : extractedRight.newExpression
								};\n`
								+ "} else {\n"
								+ `${generatedVariableName} = ${generatedVariableName};\n`
								+ "}\n"
							),
							newExpression: generatedVariableName
						};
					}
					if (operator === "||") {
						const generatedVariableName = generateVariableName();
						return {
							precedingCode: (
								(extractedLeft === null ? "" : extractedLeft.precedingCode)
								+ `let ${generatedVariableName}: ${binaryExpression.getType().getText()} = ${
									extractedLeft === null
									? binaryExpression.getLeft().getText() : extractedLeft.newExpression
								};\n`
								+ `if (${generatedVariableName}) {\n`
								+ `${generatedVariableName} = ${generatedVariableName};\n`
								+ "} else {\n"
								+ (extractedRight === null ? "" : extractedRight.precedingCode)
								+ `${generatedVariableName} = ${
									extractedRight === null
									? binaryExpression.getRight().getText() : extractedRight.newExpression
								};\n`
								+ "}\n"
							),
							newExpression: generatedVariableName
						};
					}
				}
				return extractedLeft === null && extractedRight === null ? null : {
					precedingCode: (
						(extractedLeft === null ? "" : extractedLeft.precedingCode)
						+ (extractedRight === null ? "" : extractedRight.precedingCode)
					),
					newExpression: (
						(
							extractedLeft === null
							? binaryExpression.getLeft().getText()
							: extractedLeft.newExpression
						)
						+ binaryExpression.getOperatorToken().getText()
						+ (
							extractedRight === null
							? binaryExpression.getRight().getText()
							: extractedRight.newExpression
						)
					)
				};
			}
			case Ts.SyntaxKind.ConditionalExpression: {
				const conditionalExpression = expression as Ts.ConditionalExpression;
				const extractedCondition
					= this.#extractConditionalExpression(conditionalExpression.getCondition());
				const extractedTrueExpression
					= this.#extractConditionalExpression(conditionalExpression.getWhenTrue());
				const extractedFalseExpression
					= this.#extractConditionalExpression(conditionalExpression.getWhenFalse());
				const generatedVariableName = generateVariableName();
				return {
					precedingCode: (
						(extractedCondition === null ? "" : extractedCondition.precedingCode)
						+ `let ${generatedVariableName}: ${conditionalExpression.getType().getText()};\n`
						+ `if (${
							extractedCondition === null
							? conditionalExpression.getCondition().getText() : extractedCondition.newExpression
						}) {\n`
						+ (
							extractedTrueExpression === null
							? `${generatedVariableName} = ${conditionalExpression.getWhenTrue().getText()};\n`
							: extractedTrueExpression.precedingCode
								+ `${generatedVariableName} = ${extractedTrueExpression.newExpression};\n`
						)
						+ "} else {\n"
						+ (
							extractedFalseExpression === null
							? `${generatedVariableName} = ${conditionalExpression.getWhenFalse().getText()};\n`
							: extractedFalseExpression.precedingCode
								+ `${generatedVariableName} = ${extractedFalseExpression.newExpression};\n`
						)
						+ "}\n"
					),
					newExpression: generatedVariableName
				};
			}
			case Ts.SyntaxKind.CallExpression: {
				const callExpression = expression as Ts.CallExpression;
				const calledExpression = callExpression.getExpression();
				const extractedFunctionExpression = this.#extractConditionalExpression(calledExpression);
				let precedingCode = extractedFunctionExpression === null
					? ""
					: extractedFunctionExpression.precedingCode;
				let newExpression = (extractedFunctionExpression === null
					? callExpression.getExpression().getText()
					: extractedFunctionExpression.newExpression
				) + '(';
				let isFirstArgument = true;
				let hasTransformations = extractedFunctionExpression !== null;
				for (const argument of callExpression.getArguments()) {
					if (isFirstArgument) isFirstArgument = false;
					else newExpression += ", ";
					const extractedArgument = this.#extractConditionalExpression(argument as Ts.Expression);
					if (extractedArgument === null) {
						newExpression += argument.getText();
					} else {
						precedingCode += extractedArgument.precedingCode;
						newExpression += extractedArgument.newExpression;
						hasTransformations = true;
					}
				}
				newExpression += ')';
				const resolvedFunctionInfo = resolveCalledExpression(this.#destinationPath, calledExpression);
				if (
					resolvedFunctionInfo !== null
					&& this.#mockedFunctionKeys.has(makeResolvedFunctionPathKey(resolvedFunctionInfo.path))
				) {
					newExpression = (
						"__concolic$mock<"
						+ calledExpression.getType().getCallSignatures()[0].getReturnType().getText()
						+ ">(" + JSON.stringify(makeResolvedFunctionPathKey(resolvedFunctionInfo.path)) + ")"
					);
					hasTransformations = true;
					this.#currentFileHasMocks = true;
				}
				return hasTransformations ? {precedingCode, newExpression} : null;
			}
			case Ts.SyntaxKind.ObjectLiteralExpression: {
				let precedingCode = "";
				let newExpression = "{";
				let isFirstElement = true;
				let hasTransformations = false;
				for (const element of (expression as Ts.ObjectLiteralExpression).getProperties()) {
					if (isFirstElement) isFirstElement = false;
					else newExpression += ", ";
					let transformableExpression: Ts.Expression | null = null;
					switch (element.getKind()) {
						case Ts.SyntaxKind.PropertyAssignment: {
							const propertyAssignment = element as Ts.PropertyAssignment;
							newExpression += propertyAssignment.getName() + ": ";
							transformableExpression = propertyAssignment.getInitializer()!;
							break;
						}
						case Ts.SyntaxKind.SpreadAssignment: {
							newExpression += "...";
							transformableExpression = (element as Ts.SpreadAssignment).getExpression();
							break;
						}
					}
					if (transformableExpression === null) {
						newExpression += element.getText();
						continue;
					}
					const transformedExpression = this.#extractConditionalExpression(transformableExpression);
					if (transformedExpression === null) {
						newExpression += transformableExpression.getText();
					} else {
						precedingCode += transformedExpression.precedingCode;
						newExpression += transformedExpression.newExpression;
						hasTransformations = true;
					}
				}
				newExpression += '}';
				return hasTransformations ? {precedingCode, newExpression} : null;
			}
		}
		return null;
	}
}