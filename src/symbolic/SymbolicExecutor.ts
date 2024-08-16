import * as Ts from "ts-morph";

import symbolicBuiltinClasses from "./builtins/SymbolicBuiltins";
import BinarySymbolicExpression from "./expressions/BinarySymbolicExpression";
import ConstantSymbolicExpression from "./expressions/ConstantSymbolicExpression";
import SymbolicExpression from "./expressions/SymbolicExpression";
import SymbolicExpressionKind from "./expressions/SymbolicExpressionKind";
import TernarySymbolicExpression from "./expressions/TernarySymbolicExpression";
import UnarySymbolicExpression from "./expressions/UnarySymbolicExpression";
import VariableSymbolicExpression from "./expressions/VariableSymbolicExpression";

type SymbolicVariable = {
	scopeLevel: number,
	previousScopeLevel: number | null,
	value: SymbolicExpression
};
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
	variableTable: Map<string, SymbolicVariable> = new Map<string, SymbolicVariable>();
	scopeStack: string[][] = [];
	shadowedVariableStack: Map<string, SymbolicVariable>[] = [];
	functionCalls: FunctionCall[] = [];

	constructor() {
		this.startScope();
	}

	addParametersFromFunctionDeclaration(functionDeclaration: Ts.FunctionDeclaration): void {
		for (const parameterDeclaration of functionDeclaration.getParameters()) this.addVariable(
			makeVariableKey(parameterDeclaration.getName(), parameterDeclaration),
			new VariableSymbolicExpression(parameterDeclaration.getName(), true)
		);
	}

	startScope(): void {
		this.scopeStack.push([]);
		this.shadowedVariableStack.push(new Map<string, SymbolicVariable>());
	}

	endScope(): void {
		for (const key of this.scopeStack.pop()!) {
			const previousScopeLevel = this.variableTable.get(key)!.previousScopeLevel;
			if (previousScopeLevel === null) {
				this.variableTable.delete(key);
			} else {
				const shadowedFrame = this.shadowedVariableStack[previousScopeLevel];
				this.variableTable.set(key, shadowedFrame.get(key)!);
				shadowedFrame.delete(key);
			}
		}
		this.shadowedVariableStack.pop();
	}

	addVariable(key: string, value: SymbolicExpression): void {
		const scopeLevel = this.scopeStack.length - 1;
		const shadowedVariable = this.variableTable.get(key);
		if (shadowedVariable !== undefined)
			this.shadowedVariableStack[shadowedVariable.scopeLevel].set(key, shadowedVariable);
		this.variableTable.set(key, {
			scopeLevel,
			previousScopeLevel: shadowedVariable === undefined ? null : shadowedVariable.scopeLevel,
			value
		});
		this.scopeStack[scopeLevel].push(key);
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
						: this.evaluateExpression(initializer, true)
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
				return this.variableTable.get(makeVariableKey(variable.getName(), variable))!.value.clone();
			}
			case Ts.SyntaxKind.ParenthesizedExpression:
				return this.evaluateExpression(
					(expression as Ts.ParenthesizedExpression).getExpression(), executeAssignments
				);
			case Ts.SyntaxKind.PrefixUnaryExpression: {
				const unaryExpression = expression as Ts.PrefixUnaryExpression;
				return new UnarySymbolicExpression(
					Ts.ts.tokenToString(unaryExpression.getOperatorToken())!,
					this.evaluateExpression(unaryExpression.getOperand(), executeAssignments)
				);
			}
			case Ts.SyntaxKind.BinaryExpression: {
				const binaryExpression = expression as Ts.BinaryExpression;
				const assignmentOperator = assignmentOperatorMap[binaryExpression.getOperatorToken().getText()];
				if (assignmentOperator === undefined) return new BinarySymbolicExpression(
					binaryExpression.getOperatorToken().getText(),
					this.evaluateExpression(binaryExpression.getLeft(), executeAssignments),
					this.evaluateExpression(binaryExpression.getRight(), executeAssignments)
				);
				let newValueExpression = this.evaluateExpression(binaryExpression.getRight(), executeAssignments);
				const leftOperand = binaryExpression.getLeft();
				if (!Ts.Node.isIdentifier(leftOperand))
					throw new Error("Only simple assignment expressions are supported at the moment.");
				const variable
					= leftOperand.getDefinitionNodes()[0] as Ts.ParameterDeclaration | Ts.VariableDeclaration;
				const variableKey = makeVariableKey(variable.getName(), variable);
				if (assignmentOperator !== "=") newValueExpression = new BinarySymbolicExpression(
					assignmentOperator, this.variableTable.get(variableKey)!.value.clone(), newValueExpression
				);
				if (executeAssignments) this.variableTable.get(variableKey)!.value = newValueExpression;
				return newValueExpression;
			}
			case Ts.SyntaxKind.ConditionalExpression: {
				const conditionalExpression = expression as Ts.ConditionalExpression;
				return new TernarySymbolicExpression(
					this.evaluateExpression(conditionalExpression.getCondition(), executeAssignments),
					this.evaluateExpression(conditionalExpression.getWhenTrue(), executeAssignments),
					this.evaluateExpression(conditionalExpression.getWhenFalse(), executeAssignments)
				);
			}
			case Ts.SyntaxKind.CallExpression: {
				const callExpression = expression as Ts.CallExpression;
				const returnVariable = this.variableTable.get(makeVariableKey("[call]", callExpression));
				if (returnVariable !== undefined) return returnVariable.value;
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
				return builtinFunction(callExpression.getArguments().map(
					argument => this.evaluateExpression(argument as Ts.Expression, executeAssignments)
				));
			}
			default:
				throw new Error(`Expression kind ${expression.getKindName()} is not yet supported.`);
		}
	}
}

function makeVariableKey(name: string, tsNode: Ts.Node): string {
	return `${tsNode.getStart()} ${name}`;
}