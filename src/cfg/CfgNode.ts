import {Node} from "ts-morph";

import CfgNodeKind, {isBranchingCfgNodeKind} from "./CfgNodeKind.js";

export default class CfgNode {
	static #nextId: number = 0;

	readonly id: number;
	readonly kind: CfgNodeKind;
	tsNode: Node | null;

	primaryNext: CfgNode | null = null;
	secondaryNext: CfgNode | null = null;
	primaryStatementCount: number = 0;
	secondaryStatementCount: number = 0;

	constructor(kind: CfgNodeKind, tsNode: Node | null = null) {
		this.id = CfgNode.#nextId;
		++CfgNode.#nextId;
		this.kind = kind;
		this.tsNode = tsNode;
	}

	get isBranching(): boolean {
		return isBranchingCfgNodeKind(this.kind);
	}
}