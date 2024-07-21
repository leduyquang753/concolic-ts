import * as Ts from "ts-morph";

import symbolicBuiltinClasses from "./builtins/SymbolicBuiltins";
import BinarySymbolicExpression from "./expressions/BinarySymbolicExpression";
import ConstantSymbolicExpression from "./expressions/ConstantSymbolicExpression";
import SymbolicExpression from "./expressions/SymbolicExpression";
import SymbolicExpressionKind from "./expressions/SymbolicExpressionKind";
import UnarySymbolicExpression from "./expressions/UnarySymbolicExpression";
import VariableSymbolicExpression from "./expressions/VariableSymbolicExpression";

const assignmentOperatorMap: {[assignmentOperator: string]: string | undefined} = {
	"=": "=",
	"+=": "+",
	"-=": "-",
	"*=": "*",
	"/=": "/",
	"%=": "%",
	"**=": "**",
	"<<=": "<<",
	">>=": ">>",
	">>>=": ">>>",
	"&=": "&",
	"^=": "^",
	"|=": "|",
	"&&=": "&&",
	"||=": "||",
	"??=": "??"
};

export default class SymbolicExecutor {
	variableTable: Map<string, SymbolicExpression> = new Map<string, SymbolicExpression>();
	scopeStack: string[][] = [];

	addParametersFromFunctionDeclaration(functionDeclaration: Ts.FunctionDeclaration): void {
		for (const parameterDeclaration of functionDeclaration.getParameters()) this.variableTable.set(
			makeVariableKey(parameterDeclaration.getName(), parameterDeclaration),
			new VariableSymbolicExpression(parameterDeclaration.getName(), true)
		);
	}

	startScope(): void {
		this.scopeStack.push([]);
	}

	endScope(): void {
		for (const key of this.scopeStack.pop()!) this.variableTable.delete(key);
	}

	addVariable(key: string, value: SymbolicExpression) {
		this.variableTable.set(key, value);
		this.scopeStack[this.scopeStack.length - 1].push(key);
	}

	executeStatement(statement: Ts.Statement): void {
		switch (statement.getKind()) {
			case Ts.SyntaxKind.VariableStatement: {
				for (const variableDeclaration of (statement as Ts.VariableStatement).getDeclarations()) {
					const initializer = variableDeclaration.getInitializer();
					this.addVariable(
						makeVariableKey(variableDeclaration.getName(), variableDeclaration),
						initializer === undefined
							? new ConstantSymbolicExpression(undefined)
							: this.evaluateExpression(initializer)
					);
				}
				break;
			}
			case Ts.SyntaxKind.ExpressionStatement:
				this.evaluateExpression((statement as Ts.ExpressionStatement).getExpression(), true);
				break;
		}
	}

	evaluateExpression(expression: Ts.Expression, executeAssignments: boolean = false): SymbolicExpression {
		switch (expression.getKind()) {
			case Ts.SyntaxKind.NumericLiteral:
				return new ConstantSymbolicExpression((expression as Ts.NumericLiteral).getLiteralValue());
			case Ts.SyntaxKind.TrueKeyword:
				return new ConstantSymbolicExpression(true);
			case Ts.SyntaxKind.FalseKeyword:
				return new ConstantSymbolicExpression(false);
			case Ts.SyntaxKind.Identifier: {
				const variable = (
					(expression as Ts.Identifier).getDefinitionNodes()[0]
				) as Ts.ParameterDeclaration | Ts.VariableDeclaration;
				return this.variableTable.get(makeVariableKey(variable.getName(), variable))!.clone();
			}
			case Ts.SyntaxKind.ParenthesizedExpression:
				return this.evaluateExpression((expression as Ts.ParenthesizedExpression).getExpression());
			case Ts.SyntaxKind.PrefixUnaryExpression: {
				const unaryExpression = expression as Ts.PrefixUnaryExpression;
				return new UnarySymbolicExpression(
					Ts.ts.tokenToString(unaryExpression.getOperatorToken())!,
					this.evaluateExpression(unaryExpression.getOperand())
				);
			}
			case Ts.SyntaxKind.BinaryExpression: {
				const binaryExpression = expression as Ts.BinaryExpression;
				const assignmentOperator = assignmentOperatorMap[binaryExpression.getOperatorToken().getText()];
				if (assignmentOperator === undefined) return new BinarySymbolicExpression(
					binaryExpression.getOperatorToken().getText(),
					this.evaluateExpression(binaryExpression.getLeft()),
					this.evaluateExpression(binaryExpression.getRight())
				);
				let newValueExpression = this.evaluateExpression(binaryExpression.getRight());
				const leftOperand = binaryExpression.getLeft();
				if (!Ts.Node.isIdentifier(leftOperand))
					throw new Error("Only simple assignment expressions are supported at the moment.");
				const variable
					= leftOperand.getDefinitionNodes()[0] as Ts.ParameterDeclaration | Ts.VariableDeclaration;
				const variableKey = makeVariableKey(variable.getName(), variable);
				if (assignmentOperator !== "=") newValueExpression = new BinarySymbolicExpression(
					assignmentOperator, this.variableTable.get(variableKey)!.clone(), newValueExpression
				);
				if (executeAssignments) this.variableTable.set(variableKey, newValueExpression);
				return newValueExpression;
			}
			case Ts.SyntaxKind.CallExpression: {
				const callExpression = expression as Ts.CallExpression;
				const functionExpression = callExpression.getExpression();
				if (!Ts.Node.isPropertyAccessExpression(functionExpression))
					throw new Error("Call expression's function expression is too complex.");
				const functionContainerExpression = functionExpression.getExpression();
				if (!Ts.Node.isIdentifier(functionContainerExpression))
					throw new Error("Call expression's function expression is too complex.");
				const className = functionContainerExpression.getSymbol()!.getFullyQualifiedName();
				const builtinClass = symbolicBuiltinClasses[className];
				if (builtinClass === undefined)
					throw new Error(`Call expression's function source ${className} is not supported yet.`);
				const builtinFunction = builtinClass[functionExpression.getName()];
				if (builtinFunction === undefined) throw new Error(
					`Built-in class ${className} does not have function ${functionExpression.getName()}.`
				);
				return builtinFunction(
					callExpression.getArguments().map(argument => this.evaluateExpression(argument as Ts.Expression))
				);
			}
			default:
				throw new Error(`Expression kind ${expression.getKindName()} is not yet supported.`);
		}
	}
}

function makeVariableKey(name: string, tsNode: Ts.Node): string {
	return `${tsNode.getStart()} ${name}`;
}