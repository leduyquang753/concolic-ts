import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

abstract class SymbolicExpression {
	readonly kind: SymbolicExpressionKind;

	constructor(kind: SymbolicExpressionKind) {
		this.kind = kind;
	}

	trySimplify(recurse: boolean): SymbolicExpression {
		return this;
	}

	abstract get smtString(): string;
	abstract getChildExpressions(): SymbolicExpression[];
	abstract clone(): SymbolicExpression;
}

export default SymbolicExpression;