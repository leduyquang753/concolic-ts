import CfgNode from "./CfgNode.js";
import {isEphemeralCfgNodeKind} from "./CfgNodeKind.js";

export type Cfg = {
	beginNode: CfgNode,
	endNode: CfgNode,
	escapeNode: CfgNode,
	continueNode: CfgNode,
	breakNode: CfgNode
};

export function isEmptyCfg(cfg: Cfg): boolean {
	return cfg.beginNode.primaryNext === cfg.endNode;
}

export function* iterateCfg(cfg: Cfg): Generator<CfgNode, undefined, undefined> {
	const visitedNodeIds = new Set<number>();
	const nodeStack: CfgNode[] = [cfg.beginNode];
	while (nodeStack.length !== 0) {
		const node = nodeStack.pop()!;
		if (visitedNodeIds.has(node.id)) continue;
		visitedNodeIds.add(node.id);
		if (node.secondaryNext !== null) nodeStack.push(node.secondaryNext);
		if (node.primaryNext !== null) nodeStack.push(node.primaryNext);
		yield node;
	}
}

export function compactCfg(cfg: Cfg): void {
	const visitedNodeIds = new Set<number>();
	const nodeStack: CfgNode[] = [cfg.beginNode];
	while (nodeStack.length !== 0) {
		const node = nodeStack.pop()!;
		if (visitedNodeIds.has(node.id)) continue;
		visitedNodeIds.add(node.id);
		if (node.primaryNext !== null) {
			const nearestInfo = getNearestNonEphemeralNode(node.primaryNext);
			node.primaryNext = nearestInfo.node;
			node.primaryStatementCount = nearestInfo.statementCount;
			nodeStack.push(node.primaryNext);
		}
		if (node.secondaryNext !== null) {
			const nearestInfo = getNearestNonEphemeralNode(node.secondaryNext);
			node.secondaryNext = nearestInfo.node;
			node.secondaryStatementCount = nearestInfo.statementCount;
			nodeStack.push(node.secondaryNext);
		}
	}
}

function getNearestNonEphemeralNode(node: CfgNode): {node: CfgNode, statementCount: number} {
	let statementCount = node.primaryStatementCount;
	let currentNode = node;
	while (isEphemeralCfgNodeKind(currentNode.kind) && currentNode.primaryNext !== null) {
		currentNode = currentNode.primaryNext;
		statementCount += currentNode.primaryStatementCount;
	}
	currentNode.primaryStatementCount = 0;
	return {node: currentNode, statementCount};
}