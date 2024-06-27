enum CfgNodeKind {
	START,
	END,
	STRAIGHT,
	CONDITION,
	FOR_IN,
	FOR_OF
}

export default CfgNodeKind;

const branchingNodeKinds = new Set([
	CfgNodeKind.CONDITION,
	CfgNodeKind.FOR_IN,
	CfgNodeKind.FOR_OF
]);

export function isBranchingCfgNodeKind(kind: CfgNodeKind) {
	return branchingNodeKinds.has(kind);
}