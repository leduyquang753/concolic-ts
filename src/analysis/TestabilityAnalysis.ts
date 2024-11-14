import * as Path from "path";
import * as Ts from "ts-morph";

import {makeResolvedFunctionPathKey, resolveCalledExpression} from "#r/analysis/FunctionResolver";
import type {ResolvedFunctionPath} from "./FunctionResolver.js";

export type ExecutableFunction = {
	calledFunctions: ResolvedFunctionPath[]
};

export default class TestabilityAnalysis {
	#projectPath: string;
	#analysisCache: Map<string, ExecutableFunction | null> = new Map<string, ExecutableFunction | null>();

	constructor(projectPath: string) {
		this.#projectPath = projectPath;
	}

	analyzeFunction(functionDeclaration: Ts.FunctionDeclaration): ExecutableFunction | null {
		const cacheKey
			= Path.relative(this.#projectPath, functionDeclaration.getSourceFile().getFilePath())
			+ '|' + functionDeclaration.getName();
		let result = this.#analysisCache.get(cacheKey);
		if (result !== undefined) return result;
		result = this.#analyzeFunctionInternal(functionDeclaration);
		this.#analysisCache.set(cacheKey, result);
		return result;
	}

	#analyzeFunctionInternal(functionDeclaration: Ts.FunctionDeclaration): ExecutableFunction | null {
		if (!functionHasSupportedSignature(functionDeclaration)) return null;
		const calledExpressions: Ts.Expression[] = [];
		functionDeclaration.getBody()!.forEachDescendant(node => {
			if (Ts.Node.isCallExpression(node)) calledExpressions.push(node.getExpression());
		});
		const calledFunctions: ResolvedFunctionPath[] = [];
		const calledKeys = new Set<string>();
		for (const calledExpression of calledExpressions) {
			const resolvedFunction = resolveCalledExpression(this.#projectPath, calledExpression);
			if (resolvedFunction === null) return null;
			const {path, functionInProject} = resolvedFunction;
			if (functionInProject === null) {
				if (!typeIsSupportedFunction(calledExpression.getType())) return null;
			} else {
				if (this.analyzeFunction(functionInProject) === null) return null;
			}
			const calledKey = makeResolvedFunctionPathKey(path);
			if (!calledKeys.has(calledKey)) {
				calledFunctions.push(path);
				calledKeys.add(calledKey);
			}
		}
		return {calledFunctions};
	}
}

function isPrimitiveType(type: Ts.Type): boolean {
	return type.isString()
		|| type.isNumber()
		|| type.isBoolean()
		|| type.isNull()
		|| type.isUndefined()
		|| type.isEnum()
		|| type.isBigInt();
}

function isValidType(type: Ts.Type): boolean {
	if (isPrimitiveType(type)) return true;
	//if (type.isArray()) return isValidType(type.getArrayElementType() as Ts.Type);
	if (type.isObject() || type.isInterface()) return type.getProperties().every(
		property => isValidType(property.getTypeAtLocation(property.getDeclarations()[0]))
	);
	return false;
}

function functionHasSupportedSignature(functionDeclaration: Ts.FunctionDeclaration): boolean {
	return (
		functionDeclaration.getParameters().every(parameter => isValidType(parameter.getType()))
		&& isValidType(functionDeclaration.getReturnType())
	);
}

function typeIsSupportedFunction(type: Ts.Type): boolean {
	const callSignature = type.getCallSignatures()[0];
	return callSignature.getParameters().every(symbol => {
		const parameterDeclaration = symbol.getDeclarations()[0];
		return Ts.Node.isParameterDeclaration(parameterDeclaration) && isValidType(parameterDeclaration.getType());
	}) && isValidType(callSignature.getReturnType());
}