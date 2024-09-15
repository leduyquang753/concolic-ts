import * as Ts from "ts-morph";

export function getTestableFunctions(sourceFile: Ts.SourceFile): Ts.FunctionDeclaration[] {
	return sourceFile.getFunctions().filter(isValidFunction);
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
	if (type.isArray()) return isValidType(type.getArrayElementType() as Ts.Type);
	if (!type.isObject()) return false;
	for (const prop of type.getProperties())
		if (!isValidType(prop.getTypeAtLocation(prop.getDeclarations()[0]))) return false;
	return true;
}

function isValidFunction(functionDeclaration: Ts.FunctionDeclaration): boolean {
	if (functionDeclaration.getParameters().length > 0) {
		for (const parameter of functionDeclaration.getParameters())
			if (!isValidType(parameter.getType())) return false;
	}
	return isValidType(functionDeclaration.getReturnType());
}