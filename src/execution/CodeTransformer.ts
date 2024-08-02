import * as Ts from "ts-morph";

let nextGeneratedVariableId = 0;

function generateVariableName() {
	++nextGeneratedVariableId;
	return `__concolic\$${nextGeneratedVariableId}`;
}

function ensureCodeBlock(code: string, isStandalone: boolean): string {
	return isStandalone ? `{\n${code}\n}\n` : code;
}

export function transformStatement(statement: Ts.Statement, isStandalone: boolean): void {
	switch (statement.getKind()) {
		case Ts.SyntaxKind.Block:
			for (const subStatement of (statement as Ts.Block).getStatements()) transformStatement(subStatement, false);
			break;
		case Ts.SyntaxKind.VariableStatement: {
			const variableStatement = statement as Ts.VariableStatement;
			const declarations = variableStatement.getDeclarations();
			const extractedCodes = declarations.map(declaration => {
				const initializer = declaration.getInitializer();
				return initializer === undefined ? null : extractConditionalExpression(initializer);
			});
			if (extractedCodes.every(code => code === null)) break;
			let declarationKeywords
				= variableStatement.getDeclarationKindKeywords().map(keyword => keyword.getText()).join(' ');
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
			statement.replaceWithText(ensureCodeBlock(newCode, isStandalone));
			break;
		}
		case Ts.SyntaxKind.ExpressionStatement: {
			const assignmentExpression = (statement as Ts.ExpressionStatement).getExpression();
			if (
				!Ts.Node.isBinaryExpression(assignmentExpression)
				|| assignmentExpression.getOperatorToken().getText() !== "="
			) break;
			const extractedCode = extractConditionalExpression(assignmentExpression.getRight());
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
			const extractedCode = extractConditionalExpression(returnExpression);
			if (extractedCode === null) break;
			statement.replaceWithText(ensureCodeBlock(
				extractedCode.precedingCode + `return ${extractedCode.newExpression};`, isStandalone
			));
			break;
		}
		case Ts.SyntaxKind.IfStatement: {
			const ifStatement = statement as Ts.IfStatement;
			const thenStatement = ifStatement.getThenStatement();
			transformStatement(thenStatement, true);
			const elseStatement = ifStatement.getElseStatement();
			if (elseStatement !== undefined) transformStatement(elseStatement, true);
			const extractedCondition = extractConditionalExpression(ifStatement.getExpression());
			if (extractedCondition === null) break;
			ifStatement.replaceWithText(ensureCodeBlock(
				extractedCondition.precedingCode
				+ `if (${extractedCondition.newExpression}) ${thenStatement.getText()}`
				+ (elseStatement === undefined ? "\n" : ` else ${elseStatement.getText()}\n`),
				isStandalone
			));
			break;
		}
	}
}

function extractConditionalExpression(
	expression: Ts.Expression
): {precedingCode: string, newExpression: string} | null {
	switch (expression.getKind()) {
		case Ts.SyntaxKind.ParenthesizedExpression: {
			const parenthesizedExpression = expression as Ts.ParenthesizedExpression;
			const extracted = extractConditionalExpression(parenthesizedExpression.getExpression());
			return extracted === null ? null : {
				precedingCode: extracted === null ? "" : extracted.precedingCode,
				newExpression: (
					"("
					+ (extracted === null ? parenthesizedExpression.getExpression().getText() : extracted.newExpression)
					+ ")"
				)
			};
		}
		case Ts.SyntaxKind.PrefixUnaryExpression: {
			const unaryExpression = expression as Ts.PrefixUnaryExpression;
			const extracted = extractConditionalExpression(unaryExpression.getOperand());
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
			const extracted = extractConditionalExpression(unaryExpression.getOperand());
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
			const extractedLeft = extractConditionalExpression(binaryExpression.getLeft());
			const extractedRight = extractConditionalExpression(binaryExpression.getRight());
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
			return extractedLeft === null && extractedRight === null ? null : {
				precedingCode: (
					(extractedLeft === null ? "" : extractedLeft.precedingCode)
					+ (extractedRight === null ? "" : extractedRight.precedingCode)
				),
				newExpression: (
					(extractedLeft === null ? binaryExpression.getLeft().getText() : extractedLeft.newExpression)
					+ binaryExpression.getOperatorToken().getText()
					+ (extractedRight === null ? binaryExpression.getRight().getText() : extractedRight.newExpression)
				)
			};
		}
		case Ts.SyntaxKind.ConditionalExpression: {
			const conditionalExpression = expression as Ts.ConditionalExpression;
			const extractedCondition = extractConditionalExpression(conditionalExpression.getCondition());
			const extractedTrueExpression = extractConditionalExpression(conditionalExpression.getWhenTrue());
			const extractedFalseExpression = extractConditionalExpression(conditionalExpression.getWhenFalse());
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
		};
	}
	return null;
}