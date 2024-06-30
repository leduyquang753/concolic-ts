import { Project, FunctionDeclaration, Type } from "ts-morph";

export function getAllFunctions(project: Project) {
	let allFunctions: FunctionDeclaration[] = [];
	for (const sourceFile of project.getSourceFiles()) {
		allFunctions = allFunctions.concat(sourceFile.getFunctions());
	}
	return allFunctions;
}

export function getTestableFunctions(project: Project) {
	let testableFunctions: FunctionDeclaration[] = [];
	for (const sourceFile of project.getSourceFiles()) {
		for (const functionDeclaration of sourceFile.getFunctions()) {
			if (isValidFunction(functionDeclaration)) {
				testableFunctions.push(functionDeclaration);
			}
		}
	}
	return testableFunctions;
}

function isPrimitiveType(type: Type): boolean {
	return (
		type.isString() ||
		type.isNumber() ||
		type.isBoolean() ||
		type.isNull() ||
		type.isUndefined() ||
		type.isEnum() ||
		type.isBigInt()
	);
}

function isValidType(type: Type): boolean {
	if (isPrimitiveType(type)) {
		return true;
	}
	if (type.isArray()) {
		if (!isValidType(type.getArrayElementType() as Type)) {
			return false;
		} else {
			return true;
		}
	}
	if (!type.isObject()) return false;
	for (const prop of type.getProperties()) {
		const propType = prop.getTypeAtLocation(
			prop.getDeclarations()[0]
		);
		if (!isValidType(propType)) {
			return false;
		}
	}
	return true;
}

function isValidFunction(functionDeclaration: FunctionDeclaration): boolean {
	if (functionDeclaration.getParameters().length > 0) {
		for (const parameter of functionDeclaration.getParameters()) {
			if (!isValidType(parameter.getType())) {
				return false;
			}
		}
	}
	const returnValue = functionDeclaration.getReturnType();
	if (!isValidType(returnValue)) {
		return false;
	}
	return true;
}