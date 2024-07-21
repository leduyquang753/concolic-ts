import SymbolicExpressionKind from "./SymbolicExpressionKind";

abstract class SymbolicExpression {
	readonly kind: SymbolicExpressionKind;

	constructor(kind: SymbolicExpressionKind) {
		this.kind = kind;
	}

	trySimplify(recurse: boolean): SymbolicExpression {
		return this;
	}

	abstract get smtString(): string;
	abstract clone(): SymbolicExpression;
}

export default SymbolicExpression;