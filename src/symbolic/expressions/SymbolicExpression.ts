import BaseSymbolicType from "#r/symbolic/BaseSymbolicType";

import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

abstract class SymbolicExpression {
	readonly kind: SymbolicExpressionKind;

	constructor(kind: SymbolicExpressionKind) {
		this.kind = kind;
	}

	abstract generateSmt(): {expression: string, type: BaseSymbolicType};
	abstract getChildExpressions(): SymbolicExpression[];
	abstract clone(): SymbolicExpression;
}

export default SymbolicExpression;