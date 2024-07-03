import CfgNode from "./CfgNode";
import {isEphemeralCfgNodeKind} from "./CfgNodeKind";

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
		if (node.primaryNext !== null) nodeStack.push(node.primaryNext);
		if (node.secondaryNext !== null) nodeStack.push(node.secondaryNext);
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
			node.primaryNext = getNearestNonEphemeralNode(node.primaryNext);
			nodeStack.push(node.primaryNext);
		}
		if (node.secondaryNext !== null) {
			node.secondaryNext = getNearestNonEphemeralNode(node.secondaryNext);
			nodeStack.push(node.secondaryNext);
		}
	}
}

function getNearestNonEphemeralNode(node: CfgNode): CfgNode {
	let currentNode = node;
	while (isEphemeralCfgNodeKind(currentNode.kind) && currentNode.primaryNext !== null)
		currentNode = currentNode.primaryNext;
	return currentNode;
}