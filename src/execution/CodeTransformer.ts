import * as Ts from "ts-morph";

const GENERATED_VARIABLE_PREFIX = "__concolic$";

type BooleanExpression = {
	isBinary: boolean,
	expression: BinaryBooleanExpression | Ts.Expression
};
type BinaryBooleanExpression = {
	operator: string,
	leftOperand: BooleanExpression,
	rightOperand: BooleanExpression
};

function decomposeBooleanExpression(expression: Ts.Expression): BooleanExpression {
	if (Ts.Node.isParenthesizedExpression(expression)) return decomposeBooleanExpression(expression.getExpression());
	if (!Ts.Node.isBinaryExpression(expression)) return {isBinary: false, expression};
	const operator = expression.getOperatorToken().getText();
	if (operator === "&&" || operator === "||") return {isBinary: true, expression: {
		operator,
		leftOperand: decomposeBooleanExpression(expression.getLeft()),
		rightOperand: decomposeBooleanExpression(expression.getRight())
	}};
	else return {isBinary: false, expression};
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
			transformStatement(ifStatement.getThenStatement(), true);
			const elseStatement = ifStatement.getElseStatement();
			if (elseStatement !== undefined) transformStatement(elseStatement, true);
			break;
		}
	}
}

function extractConditionalExpression(
	expression: Ts.Expression
): {precedingCode: string, newExpression: string} | null {
	if (
		!Ts.Node.isConditionalExpression(expression)
		|| expression.getCondition().getText().startsWith(GENERATED_VARIABLE_PREFIX)
	) return null;
	const generatedVariableName = GENERATED_VARIABLE_PREFIX + expression.getStart();
	return {
		precedingCode:
			`let ${generatedVariableName} = false;\n`
			+ emitCondition(
				decomposeBooleanExpression(expression.getCondition()),
				`${generatedVariableName} = true;`, `${generatedVariableName} = false;`
			) + '\n',
		newExpression:
			`${generatedVariableName} `
			+ `? ${expression.getWhenTrue().getText()} `
			+ `: ${expression.getWhenFalse().getText()}`
	};
}

function emitCondition(booleanExpression: BooleanExpression, passingCode: string, failingCode: string): string {
	if (!booleanExpression.isBinary) return (
		`if (${(booleanExpression.expression as Ts.Expression).getText()}) {\n${passingCode}\n`
		+ `} else {\n${failingCode}\n}`
	);
	const binaryExpression = booleanExpression.expression as BinaryBooleanExpression;
	if (binaryExpression.operator === "||") return emitCondition(
		binaryExpression.leftOperand,
		passingCode,
		emitCondition(binaryExpression.rightOperand, passingCode, failingCode)
	);
	if (binaryExpression.operator === "&&") return emitCondition(
		binaryExpression.leftOperand,
		emitCondition(binaryExpression.rightOperand, passingCode, failingCode),
		failingCode
	);
	throw new Error(`Unexpected binary boolean expression operator \`${binaryExpression.operator}\`.`);
}