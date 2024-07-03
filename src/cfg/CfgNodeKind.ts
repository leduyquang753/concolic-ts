enum CfgNodeKind {
	BEGIN,
	END,
	ESCAPE, // Node reached when `return`ing and `throw`ing.
	CONTINUE,
	BREAK,
	STRAIGHT,
	CONDITION,
	FOR_EACH,
}

export default CfgNodeKind;

const branchingNodeKinds = new Set([
	CfgNodeKind.CONDITION,
	CfgNodeKind.FOR_EACH,
]);

export function isBranchingCfgNodeKind(kind: CfgNodeKind) {
	return branchingNodeKinds.has(kind);
}

const ephemeralNodeKinds = new Set([
	CfgNodeKind.BEGIN,
	CfgNodeKind.END,
	CfgNodeKind.ESCAPE,
	CfgNodeKind.CONTINUE,
	CfgNodeKind.BREAK
]);

export function isEphemeralCfgNodeKind(kind: CfgNodeKind) {
	return ephemeralNodeKinds.has(kind);
}