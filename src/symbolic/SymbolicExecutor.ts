import * as Ts from "ts-morph";

import type {ParameterType} from "#r/execution/Executor";

import symbolicBuiltinClasses from "./builtins/SymbolicBuiltins.js";
import BinarySymbolicExpression from "./expressions/BinarySymbolicExpression.js";
import ConstantSymbolicExpression from "./expressions/ConstantSymbolicExpression.js";
import ObjectSymbolicExpression from "./expressions/ObjectSymbolicExpression.js";
import SymbolicExpression from "./expressions/SymbolicExpression.js";
import SymbolicExpressionKind from "./expressions/SymbolicExpressionKind.js";
import UnarySymbolicExpression from "./expressions/UnarySymbolicExpression.js";
import VariableSymbolicExpression from "./expressions/VariableSymbolicExpression.js";

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
	shadowedVariableStacks: Map<string, SymbolicExpression[]> = new Map<string, SymbolicExpression[]>();
	functionCalls: FunctionCall[] = [];

	#parameterInfo: Map<string, ParameterType>;
	#nextMockedCallNumber: number = 0;

	constructor(parameterInfo: Map<string, ParameterType>) {
		this.startScope();
		this.#parameterInfo = parameterInfo;
	}

	addParametersFromFunctionDeclaration(functionDeclaration: Ts.FunctionDeclaration): void {
		let parameterIndex = 0;
		for (const parameterDeclaration of functionDeclaration.getParameters()) {
			const nameNode = parameterDeclaration.getNameNode();
			const type = parameterDeclaration.getType();
			const value = type.isObject() || type.isInterface()
				? this.#generateObjectForParameter(
					(Ts.Node.isIdentifier(nameNode) ? nameNode.getText() : `@${parameterIndex}`) + '.',
					parameterDeclaration.getType()
				)
				: new VariableSymbolicExpression(
					parameterDeclaration.getName(), true,
					this.#parameterInfo.get(parameterDeclaration.getName())!.baseType
				);
			switch (nameNode.getKind()) {
				case Ts.SyntaxKind.Identifier:
					this.addVariable(nameNode.getText(), value);
					break;
				case Ts.SyntaxKind.ObjectBindingPattern:
					if (value.kind !== SymbolicExpressionKind.OBJECT)
						throw new Error("Trying to destructure non-object symbolic expression.");
					this.#executeDeclarationObjectBindingPattern(
						nameNode as Ts.ObjectBindingPattern, value as ObjectSymbolicExpression
					);
					break;
				default:
					throw new Error(`Unsupported parameter declaration kind \`${nameNode.getKindName()}\`.`);
			}
			++parameterIndex;
		}
	}

	startScope(): void {
		this.scopeStack.push([]);
	}

	endScope(): void {
		for (const key of this.scopeStack.pop()!) {
			const shadowedStack = this.shadowedVariableStacks.get(key);
			if (shadowedStack === undefined) {
				this.variableTable.delete(key);
			} else {
				this.variableTable.set(key, shadowedStack.pop()!);
				if (shadowedStack.length === 0) this.shadowedVariableStacks.delete(key);
			}
		}
	}

	addVariable(key: string, value: SymbolicExpression): void {
		const scopeLevel = this.scopeStack.length - 1;
		const shadowedVariable = this.variableTable.get(key);
		if (shadowedVariable !== undefined) {
			let shadowedStack = this.shadowedVariableStacks.get(key);
			if (shadowedStack === undefined) {
				shadowedStack = [];
				this.shadowedVariableStacks.set(key, shadowedStack);
			}
			shadowedStack.push(shadowedVariable);
		}
		this.variableTable.set(key, value);
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
		for (let i = 0; i !== argumentCount; ++i) {
			const nameNode = parameters[i].getNameNode();
			const value = this.evaluateExpression(callArguments[i] as Ts.Expression, true, false);
			switch (nameNode.getKind()) {
				case Ts.SyntaxKind.Identifier:
					this.addVariable(nameNode.getText(), value);
					break;
				case Ts.SyntaxKind.ObjectBindingPattern: {
					if (value.kind !== SymbolicExpressionKind.OBJECT)
						throw new Error("Trying to destructure non-object symbolic expression.");
					this.#executeDeclarationObjectBindingPattern(
						nameNode as Ts.ObjectBindingPattern, value as ObjectSymbolicExpression
					);
					break;
				}
				default:
					throw new Error(`Unsupported parameter declaration kind \`${nameNode.getKindName()}\`.`);
			}
		}
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
				const nameNode = variableDeclaration.getNameNode();
				const initializer = variableDeclaration.getInitializer();
				switch (nameNode.getKind()) {
					case Ts.SyntaxKind.Identifier:
						this.addVariable(nameNode.getText(), initializer === undefined
							? new ConstantSymbolicExpression(undefined)
							: this.evaluateExpression(initializer, true, false)
						);
						break;
					case Ts.SyntaxKind.ObjectBindingPattern: {
						if (initializer === undefined)
							throw new Error("No initializer for object destructuring declaration.");
						const source = this.evaluateExpression(initializer, true, false);
						if (source.kind !== SymbolicExpressionKind.OBJECT)
							throw new Error("Trying to destructure non-object symbolic expression.");
						this.#executeDeclarationObjectBindingPattern(
							nameNode as Ts.ObjectBindingPattern, source as ObjectSymbolicExpression
						);
						break;
					}
					default:
						throw new Error(`Unsupported variable declaration kind \`${nameNode.getKindName()}\`.`);
				}
				break;
			}
			case Ts.SyntaxKind.ExpressionStatement:
				this.evaluateExpression((tsNode as Ts.ExpressionStatement).getExpression(), true, false);
				break;
			case Ts.SyntaxKind.ReturnStatement: {
				const returnExpression = (tsNode as Ts.ReturnStatement).getExpression();
				let returnSymbolicExpression: SymbolicExpression | null
					= returnExpression === undefined ? null : this.evaluateExpression(returnExpression, true, false);
				const functionCall = this.functionCalls.pop()!;
				while (this.scopeStack.length !== functionCall.scopeLevel) this.endScope();
				if (returnSymbolicExpression !== null)
					this.addVariable(functionCall.returnValueKey, returnSymbolicExpression);
				break;
			}
		}
	}

	evaluateExpression(expression: Ts.Expression, executeAssignments: boolean, external: boolean): SymbolicExpression {
		switch (expression.getKind()) {
			case Ts.SyntaxKind.NumericLiteral:
				return new ConstantSymbolicExpression((expression as Ts.NumericLiteral).getLiteralValue());
			case Ts.SyntaxKind.StringLiteral:
				return new ConstantSymbolicExpression((expression as Ts.StringLiteral).getLiteralValue());
			case Ts.SyntaxKind.TrueKeyword:
				return new ConstantSymbolicExpression(true);
			case Ts.SyntaxKind.FalseKeyword:
				return new ConstantSymbolicExpression(false);
			case Ts.SyntaxKind.Identifier:
				if (!external) {
					const value = this.variableTable.get(expression.getText());
					if (value !== undefined) return value.clone();
				}
				const declaration = (expression as Ts.Identifier).getSymbolOrThrow().getDeclarations().find(
					Ts.Node.isVariableDeclaration
				);
				if (declaration === undefined) throw new Error("External variable declaration not found.");
				if (
					(declaration.getParentOrThrow().getParentOrThrow() as Ts.VariableStatement).getDeclarationKind()
					!== Ts.VariableDeclarationKind.Const
				) throw new Error("Non-`const` external variables are not yet supported.");
				return this.evaluateExpression(declaration.getInitializerOrThrow(), false, true);
			case Ts.SyntaxKind.PropertyAccessExpression: {
				const propertyAccessExpression = (expression as Ts.PropertyAccessExpression);
				const objectSymbolicExpression
					= this.evaluateExpression(propertyAccessExpression.getExpression(), false, external);
				if (objectSymbolicExpression.kind !== SymbolicExpressionKind.OBJECT)
					throw new Error("Trying to access property from non-object.");
				const result = (objectSymbolicExpression as ObjectSymbolicExpression)
					.value[propertyAccessExpression.getName()];
				if (result === undefined) throw new Error("Trying to access nonexistent property from object.");
				return result;
			}
			case Ts.SyntaxKind.ParenthesizedExpression:
				return this.evaluateExpression(
					(expression as Ts.ParenthesizedExpression).getExpression(), executeAssignments, external
				);
			case Ts.SyntaxKind.PrefixUnaryExpression: {
				const unaryExpression = expression as Ts.PrefixUnaryExpression;
				return new UnarySymbolicExpression(
					Ts.ts.tokenToString(unaryExpression.getOperatorToken())!,
					this.evaluateExpression(unaryExpression.getOperand(), executeAssignments, external)
				);
			}
			case Ts.SyntaxKind.BinaryExpression: {
				// TODO: Handle side effects properly and in order.
				const binaryExpression = expression as Ts.BinaryExpression;
				const assignmentOperator = assignmentOperatorMap[binaryExpression.getOperatorToken().getText()];
				if (assignmentOperator === undefined) return new BinarySymbolicExpression(
					binaryExpression.getOperatorToken().getText(),
					this.evaluateExpression(binaryExpression.getLeft(), executeAssignments, external),
					this.evaluateExpression(binaryExpression.getRight(), executeAssignments, external)
				);
				let newValueExpression
					= this.evaluateExpression(binaryExpression.getRight(), executeAssignments, external);
				if (assignmentOperator !== "=") newValueExpression = new BinarySymbolicExpression(
					assignmentOperator,
					this.evaluateExpression(binaryExpression.getLeft(), executeAssignments, external),
					newValueExpression
				);
				if (!executeAssignments) return newValueExpression;
				this.#executeAssignment(binaryExpression.getLeft(), newValueExpression);
				return newValueExpression;
			}
			case Ts.SyntaxKind.CallExpression: {
				const callExpression = expression as Ts.CallExpression;
				if (callExpression.getType().isVoid()) return new ConstantSymbolicExpression(undefined);
				const returnVariable = this.variableTable.get(makeVariableKey("[call]", callExpression));
				if (returnVariable !== undefined) return returnVariable;
				const functionExpression = callExpression.getExpression();
				if (functionExpression.getText() === "__concolic$mock") {
					const valueName = `__concolic$mock${this.#nextMockedCallNumber}`;
					const valueType = callExpression.getTypeArguments()[0].getType();
					const mockedValue = valueType.isObject() || valueType.isInterface()
						? this.#generateObjectForParameter(valueName + '.', valueType)
						: new VariableSymbolicExpression(valueName, true, this.#parameterInfo.get(valueName)!.baseType);
					++this.#nextMockedCallNumber;
					return mockedValue;
				}
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
					argument => this.evaluateExpression(argument as Ts.Expression, executeAssignments, external)
				));
			}
			case Ts.SyntaxKind.ObjectLiteralExpression: {
				const objectSymbolicExpression = new ObjectSymbolicExpression({});
				const objectValue = objectSymbolicExpression.value;
				for (
					const property of (expression as Ts.ObjectLiteralExpression).getProperties()
				) switch (property.getKind()) {
					case Ts.SyntaxKind.PropertyAssignment: {
						const propertyAssignment = property as Ts.PropertyAssignment;
						objectValue[propertyAssignment.getName()] = this.evaluateExpression(
							propertyAssignment.getInitializer()!, executeAssignments, external
						);
						break;
					}
					case Ts.SyntaxKind.ShorthandPropertyAssignment: {
						const shorthandPropertyAssignment = property as Ts.ShorthandPropertyAssignment;
						objectValue[shorthandPropertyAssignment.getName()] = this.evaluateExpression(
							shorthandPropertyAssignment.getNameNode(), executeAssignments, external
						);
						break;
					}
					case Ts.SyntaxKind.SpreadAssignment: {
						const sourceSymbolicExpression = this.evaluateExpression(
							(property as Ts.SpreadAssignment).getExpression(), false, external
						);
						if (sourceSymbolicExpression.kind !== SymbolicExpressionKind.OBJECT)
							throw new Error("Spread operator is using a non-object value.");
						for (
							const [key, value]
							of Object.entries((sourceSymbolicExpression as ObjectSymbolicExpression).value)
						) objectValue[key] = value!.clone();
						break;
					}
					default:
						throw new Error(`Unsupported object literal property kind \`${property.getKindName()}\`.`);
				}
				return objectSymbolicExpression;
			}
			default:
				throw new Error(`Expression kind ${expression.getKindName()} is not yet supported.`);
		}
	}

	#generateObjectForParameter(prefix: string, tsType: Ts.Type): ObjectSymbolicExpression {
		const object = new ObjectSymbolicExpression({});
		for (const property of tsType.getProperties()) {
			const subType = property.getDeclarations()[0].getType();
			if (subType.isObject()) {
				object.value[property.getName()]
					= this.#generateObjectForParameter(prefix + property.getName() + '.', subType);
			} else {
				const fullName = prefix + property.getName();
				object.value[property.getName()]
					= new VariableSymbolicExpression(fullName, true, this.#parameterInfo.get(fullName)!.baseType);
			}
		}
		return object;
	}

	#executeDeclarationObjectBindingPattern(pattern: Ts.ObjectBindingPattern, source: ObjectSymbolicExpression): void {
		const extractedNames = new Set<string>();
		for (const element of pattern.getElements()) {
			const propertyNameNode = element.getPropertyNameNode();
			if (propertyNameNode !== undefined && propertyNameNode.getKind() !== Ts.SyntaxKind.Identifier)
				throw new Error(`Unsupported destructuring key kind \`${propertyNameNode.getKindName()}\`.`);
			let propertyName = propertyNameNode === undefined ? null : propertyNameNode.getText();
			const nameNode = element.getNameNode();
			const defaultExpression = element.getInitializer();
			switch (element.getNameNode().getKind()) {
				case Ts.SyntaxKind.Identifier:
					const name = element.getName();
					if (element.getDotDotDotToken() !== undefined) {
						const restObject = new ObjectSymbolicExpression({});
						const restValue = restObject.value;
						for (const [key, value] of Object.entries(source.value))
							if (!extractedNames.has(key)) restValue[key] = value!.clone();
						this.addVariable(name, restObject);
					} else {
						if (propertyName === null) propertyName = name;
						this.addVariable(name, source.value[propertyName] ?? (defaultExpression === undefined
							? new ConstantSymbolicExpression(undefined)
							: this.evaluateExpression(defaultExpression, true, false)
						));
						extractedNames.add(propertyName);
					}
					break;
				case Ts.SyntaxKind.ObjectBindingPattern: {
					const value = source.value[propertyName!] ?? (
						defaultExpression === undefined ? null : this.evaluateExpression(defaultExpression, true, false)
					);
					if (value === null) throw new Error("Trying to get non-existent property from object.");
					if (value.kind !== SymbolicExpressionKind.OBJECT)
						throw new Error("Trying to destructure non-object symbolic expression.");
					this.#executeDeclarationObjectBindingPattern(
						nameNode as Ts.ObjectBindingPattern, value as ObjectSymbolicExpression
					);
					break;
				}
				default:
					throw new Error(`Unexpected binding element kind \`${nameNode.getKindName()}\`.`);
			}
		}
	}

	#executeAssignmentObjectBindingPattern(pattern: Ts.ObjectLiteralExpression, value: SymbolicExpression): void {
		if (value.kind !== SymbolicExpressionKind.OBJECT)
			throw new Error("Trying to destructure non-object symbolic expression.");
		const source = value as ObjectSymbolicExpression;
		const extractedNames = new Set<string>();
		for (const element of pattern.getProperties()) switch (element.getKind()) {
			case Ts.SyntaxKind.ShorthandPropertyAssignment: {
				const shorthandPropertyAssignment = element as Ts.ShorthandPropertyAssignment;
				const name = shorthandPropertyAssignment.getName();
				const defaultExpression = shorthandPropertyAssignment.getObjectAssignmentInitializer();
				this.variableTable.set(name, source.value[name] ?? (defaultExpression === undefined
					? new ConstantSymbolicExpression(undefined)
					: this.evaluateExpression(defaultExpression, true, false)
				));
				extractedNames.add(name);
				break;
			}
			case Ts.SyntaxKind.PropertyAssignment: {
				const propertyAssignment = element as Ts.PropertyAssignment;
				const propertyName = propertyAssignment.getName();
				let target = propertyAssignment.getInitializer()!;
				let defaultExpression: Ts.Expression | null = null;
				if (Ts.Node.isBinaryExpression(target) && target.getOperatorToken().getText() === "=") {
					defaultExpression = target.getRight();
					target = target.getLeft();
				}
				this.#executeAssignment(target, source.value[propertyName] ?? (defaultExpression === null
					? new ConstantSymbolicExpression(undefined)
					: this.evaluateExpression(defaultExpression, true, false)
				));
				extractedNames.add(propertyName);
				break;
			}
			case Ts.SyntaxKind.SpreadAssignment: {
				const restObject = new ObjectSymbolicExpression({});
				const restValue = restObject.value;
				for (const [key, value] of Object.entries(source.value))
					if (!extractedNames.has(key)) restValue[key] = value!.clone();
				this.#executeAssignment((element as Ts.SpreadAssignment).getExpression(), restObject);
				break;
			}
		}
	}

	#executeAssignment(target: Ts.Expression, value: SymbolicExpression): void {
		switch (target.getKind()) {
			case Ts.SyntaxKind.Identifier:
				this.variableTable.set(target.getText(), value);
				break;
			case Ts.SyntaxKind.PropertyAccessExpression: {
				const propertyAccessExpression = target as Ts.PropertyAccessExpression;
				const objectSymbolicExpression
					= this.evaluateExpression(propertyAccessExpression.getExpression(), false, false);
				if (objectSymbolicExpression.kind !== SymbolicExpressionKind.OBJECT)
					throw new Error("Trying to access property from non-object.");
				const object = (objectSymbolicExpression as ObjectSymbolicExpression).value;
				const propertyName = propertyAccessExpression.getName();
				if (!(propertyName in object)) throw new Error("Trying to access nonexistent property from object.");
				object[propertyName] = value;
				break;
			}
			case Ts.SyntaxKind.ObjectLiteralExpression:
				this.#executeAssignmentObjectBindingPattern(target as Ts.ObjectLiteralExpression, value);
				break;
			default:
				throw new Error("Unsupported target of assignment operation.");
		}
	}
}

function makeVariableKey(name: string, tsNode: Ts.Node): string {
	return `${tsNode.getSourceFile().getFilePath()}@${tsNode.getStart()} ${name}`;
}