import * as Ts from "ts-morph";

import {iterateCfg} from "#r/cfg/Cfg";
import {generateCfgFromFunction} from "#r/cfg/CfgGenerator";
import CfgNode from "#r/cfg/CfgNode";
import CfgNodeKind from "#r/cfg/CfgNodeKind";

type Location = {
	sourceFile: Ts.SourceFile,
	line: number,
	column: number
};

export type Breakpoint = {
	cfgNode: CfgNode,
	isSecondaryBranch: boolean,
	sourceFile: Ts.SourceFile,
	line: number,
	column: number
};

export function getBreakpointsFromFunction(functionDeclaration: Ts.FunctionDeclaration): Breakpoint[] {
	const breakpoints: Breakpoint[] = [];
	for (const cfgNode of iterateCfg(generateCfgFromFunction(functionDeclaration)))
		breakpoints.push(...getBreakpointsFromCfgNode(cfgNode));
	return breakpoints;
}

export function getBreakpointsFromCfgNode(cfgNode: CfgNode): Breakpoint[] {
	const tsNode = cfgNode.tsNode;
	if (tsNode === null) return [];
	switch (cfgNode.kind) {
		case CfgNodeKind.CONDITION: switch (tsNode.getKind()) {
			case Ts.SyntaxKind.IfStatement: {
				const ifNode = tsNode as Ts.IfStatement;
				const elseNode = ifNode.getElseStatement();
				return [
					{cfgNode, isSecondaryBranch: false, ...getLocationOfNode(ifNode.getThenStatement())},
					{cfgNode, isSecondaryBranch: true, ...(
						elseNode === undefined
						? getNearestBreakableLocation(ifNode)
						: getLocationOfNode(elseNode)
					)}
				];
			}
			case Ts.SyntaxKind.ForStatement:
			case Ts.SyntaxKind.WhileStatement: {
				const forNode = tsNode as Ts.ForStatement | Ts.WhileStatement;
				return [
					{cfgNode, isSecondaryBranch: false, ...getLocationOfNode(forNode.getStatement())},
					{cfgNode, isSecondaryBranch: true, ...getNearestBreakableLocation(forNode)}
				];
			}
			default: throw new Error("Unhandled condition node kind.");
		}
		case CfgNodeKind.FOR_EACH: {
			const forNode = tsNode as Ts.ForOfStatement | Ts.ForInStatement;
			return [
				{cfgNode, isSecondaryBranch: false, ...getLocationOfNode(forNode.getStatement())},
				{cfgNode, isSecondaryBranch: true, ...getNearestBreakableLocation(forNode)}
			];
		}
	}
	return [];
}

function getNearestBreakableLocation(tsNode: Ts.Node): Location {
	let currentNode = tsNode;
	let candidate = tsNode.getNextSibling();
	while (candidate === undefined) {
		const parent = currentNode.getParent();
		if (parent === undefined || parent.getKind() === Ts.SyntaxKind.FunctionDeclaration)
			throw new Error("Failed to find breakable location of node.");
		switch (parent.getKind()) {
			case Ts.SyntaxKind.Block:
				candidate = parent.getChildren()[2];
				break;
			case Ts.SyntaxKind.ForStatement:
			case Ts.SyntaxKind.ForInStatement:
			case Ts.SyntaxKind.ForOfStatement:
			case Ts.SyntaxKind.WhileStatement:
				candidate = parent;
				break;
			default:
				currentNode = parent;
				if (currentNode.getKind() !== Ts.SyntaxKind.SyntaxList) candidate = currentNode.getNextSibling();
				break;
		}
	}
	return getLocationOfNode(candidate);
}

function getLocationOfNode(tsNode: Ts.Node): Location {
	const sourceFile = tsNode.getSourceFile();
	const lineAndColumn = sourceFile.getLineAndColumnAtPos(tsNode.getStart());
	return {
		sourceFile,
		line: lineAndColumn.line,
		column: lineAndColumn.column
	};
}