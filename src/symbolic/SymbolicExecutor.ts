import * as Ts from "ts-morph";

import symbolicBuiltinClasses from "./builtins/SymbolicBuiltins";
import BinarySymbolicExpression from "./expressions/BinarySymbolicExpression";
import ConstantSymbolicExpression from "./expressions/ConstantSymbolicExpression";
import SymbolicExpression from "./expressions/SymbolicExpression";
import SymbolicExpressionKind from "./expressions/SymbolicExpressionKind";
import TernarySymbolicExpression from "./expressions/TernarySymbolicExpression";
import UnarySymbolicExpression from "./expressions/UnarySymbolicExpression";
import VariableSymbolicExpression from "./expressions/VariableSymbolicExpression";

type FunctionCall = {
	scopeLevel: number,
	returnValueKey: string
};

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
	functionCalls: FunctionCall[] = [];

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

	addVariable(key: string, value: SymbolicExpression): void {
		this.variableTable.set(key, value);
		this.scopeStack[this.scopeStack.length - 1].push(key);
	}

	prepareFunctionCall(calledFunction: Ts.FunctionDeclaration, callExpression: Ts.CallExpression): void {
		this.functionCalls.push({
			scopeLevel: this.scopeStack.length, returnValueKey: makeVariableKey("[call]", callExpression)
		});
		this.startScope();
		const parameters = calledFunction.getParameters();
		const callArguments = callExpression.getArguments();
		const argumentCount = callArguments.length;
		if (argumentCount !== parameters.length)
			throw new Error("Parameter and argument list not matching in length are not supported yet.");
		for (let i = 0; i !== argumentCount; ++i) this.addVariable(
			makeVariableKey(parameters[i].getName(), parameters[i]),
			this.evaluateExpression(callArguments[i] as Ts.Expression, true)
		);
	}

	executeNode(tsNode: Ts.Node): void {
		switch (tsNode.getKind()) {
			case Ts.SyntaxKind.Block:
				this.startScope();
				break;
			case Ts.SyntaxKind.CloseBraceToken:
				this.endScope();
				break;
			case Ts.SyntaxKind.VariableDeclaration: {
				const variableDeclaration = tsNode as Ts.VariableDeclaration;
				const initializer = variableDeclaration.getInitializer();
				this.addVariable(
					makeVariableKey(variableDeclaration.getName(), variableDeclaration),
					initializer === undefined
						? new ConstantSymbolicExpression(undefined)
						: this.evaluateExpression(initializer)
				);
				break;
			}
			case Ts.SyntaxKind.ExpressionStatement:
				this.evaluateExpression((tsNode as Ts.ExpressionStatement).getExpression(), true);
				break;
			case Ts.SyntaxKind.ReturnStatement: {
				const returnExpression = (tsNode as Ts.ReturnStatement).getExpression();
				let returnSymbolicExpression: SymbolicExpression | null
					= returnExpression === undefined ? null : this.evaluateExpression(returnExpression, true);
				const functionCall = this.functionCalls.pop()!;
				while (this.scopeStack.length !== functionCall.scopeLevel) this.endScope();
				if (returnSymbolicExpression !== null)
					this.addVariable(functionCall.returnValueKey, returnSymbolicExpression);
				break;
			}
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
			case Ts.SyntaxKind.ConditionalExpression: {
				const conditionalExpression = expression as Ts.ConditionalExpression;
				return new TernarySymbolicExpression(
					this.evaluateExpression(conditionalExpression.getCondition()),
					this.evaluateExpression(conditionalExpression.getWhenTrue()),
					this.evaluateExpression(conditionalExpression.getWhenFalse())
				);
			}
			case Ts.SyntaxKind.CallExpression: {
				const callExpression = expression as Ts.CallExpression;
				const returnValueKey = makeVariableKey("[call]", callExpression);
				if (this.variableTable.has(returnValueKey)) {
					const value = this.variableTable.get(returnValueKey)!;
					this.variableTable.delete(returnValueKey);
					return value;
				}
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