import * as Path from "path";
import * as Ts from "ts-morph";

export type ResolvedFunctionPath = {
	source: string,
	container: string | null,
	name: string
};
export type ResolvedFunctionInfo = {
	path: ResolvedFunctionPath,
	functionInProject: Ts.FunctionDeclaration | null;
};

export function resolveCalledExpression(
	projectPath: string, calledExpression: Ts.Expression
): ResolvedFunctionInfo | null {
	let functionPath: ResolvedFunctionPath = null!;
	let functionInProject: Ts.FunctionDeclaration | null = null;
	if (Ts.Node.isIdentifier(calledExpression)) {
		const declaration = calledExpression.getSymbolOrThrow().getDeclarations()[0];
		if (Ts.Node.isFunctionDeclaration(declaration)) {
			const parent = declaration.getParentOrThrow();
			if (!Ts.Node.isSourceFile(parent)) return null;
			functionPath = {
				source: getSourceFilePath(projectPath, parent),
				container: null,
				name: declaration.getNameOrThrow()
			};
			if (!parent.isInNodeModules()) functionInProject = declaration;
		} else if (Ts.Node.isImportSpecifier(declaration)) {
			const importDeclaration = declaration.getParentOrThrow().getParentOrThrow().getParentOrThrow();
			if (!Ts.Node.isImportDeclaration(importDeclaration)) return null;
			const sourceFile = importDeclaration.getModuleSpecifierSourceFile();
			if (sourceFile === undefined) return null;
			const trueDeclaration = sourceFile.getFunction(declaration.getName());
			if (trueDeclaration === undefined) return null;
			functionPath = {
				source: getSourceFilePath(projectPath, sourceFile),
				container: null,
				name: trueDeclaration.getNameOrThrow()
			};
			if (!sourceFile.isInNodeModules()) functionInProject = trueDeclaration;
		} else if (Ts.Node.isImportClause(declaration)) {
			const importDeclaration = declaration.getParentOrThrow();
			if (!Ts.Node.isImportDeclaration(importDeclaration)) return null;
			const sourceFile = importDeclaration.getModuleSpecifierSourceFile();
			if (sourceFile === undefined) return null;
			const defaultExport = sourceFile.getDefaultExportSymbol();
			if (defaultExport === undefined) return null;
			const trueDeclaration = defaultExport.getDeclarations()[0];
			if (!Ts.Node.isFunctionDeclaration(trueDeclaration)) return null;
			functionPath = {
				source: getSourceFilePath(projectPath, sourceFile),
				container: null,
				name: trueDeclaration.getNameOrThrow()
			};
			if (!sourceFile.isInNodeModules()) functionInProject = trueDeclaration;
		} else {
			return null;
		}
	} else if (Ts.Node.isPropertyAccessExpression(calledExpression)) {
		const containerDeclaration = calledExpression.getExpression().getSymbolOrThrow().getDeclarations().find(
			declaration => Ts.Node.isVariableDeclaration(declaration) || Ts.Node.isNamespaceImport(declaration)
		);
		if (containerDeclaration === undefined) return null;
		if (Ts.Node.isVariableDeclaration(containerDeclaration)) {
			const parent = containerDeclaration.getParentOrThrow().getParentOrThrow().getParentOrThrow();
			if (!Ts.Node.isSourceFile(parent)) return null;
			functionPath = {
				source: getSourceFilePath(projectPath, parent),
				container: containerDeclaration.getName(),
				name: calledExpression.getName()
			};
		} else if (Ts.Node.isNamespaceImport(containerDeclaration)) {
			const importDeclaration = containerDeclaration.getParentOrThrow().getParentOrThrow();
			if (!Ts.Node.isImportDeclaration(importDeclaration)) return null;
			const sourceFile = importDeclaration.getModuleSpecifierSourceFile();
			if (sourceFile === undefined) return null;
			const trueDeclaration = sourceFile.getFunction(calledExpression.getName());
			if (trueDeclaration === undefined) return null;
			functionPath = {
				source: getSourceFilePath(projectPath, sourceFile),
				container: null,
				name: trueDeclaration.getNameOrThrow()
			};
			if (!sourceFile.isInNodeModules()) functionInProject = trueDeclaration;
		} else {
			return null;
		}
	}
	return {path: functionPath, functionInProject};
}

function getSourceFilePath(projectPath: string, sourceFile: Ts.SourceFile): string {
	return sourceFile.isInNodeModules()
		? sourceFile.getFilePath()
		: Path.relative(projectPath, sourceFile.getFilePath()).replaceAll('\\', '/');
}

export function makeResolvedFunctionPathKey(path: ResolvedFunctionPath): string {
	return path.source + '|' + (path.container ?? "") + '|' + path.name;
}