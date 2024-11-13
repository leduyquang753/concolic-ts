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
	//if (type.isArray()) return isValidType(type.getArrayElementType() as Ts.Type);
	if (type.isObject() || type.isInterface()) return type.getProperties().every(
		property => {
			console.log(property.getName());
			return isValidType(property.getTypeAtLocation(property.getDeclarations()[0]));
		}
	);
	return false;
}

function isValidFunction(functionDeclaration: Ts.FunctionDeclaration): boolean {
	if (
		functionDeclaration.getParameters().length !== 0
		&& !functionDeclaration.getParameters().every(parameter => isValidType(parameter.getType()))
	) return false;
	return isValidType(functionDeclaration.getReturnType());
}