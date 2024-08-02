import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";

export default class TernarySymbolicExpression extends SymbolicExpression {
	condition: SymbolicExpression
	trueValue: SymbolicExpression;
	falseValue: SymbolicExpression;

	constructor(condition: SymbolicExpression, trueValue: SymbolicExpression, falseValue: SymbolicExpression) {
		super(SymbolicExpressionKind.TERNARY);
		this.condition = condition;
		this.trueValue = trueValue;
		this.falseValue = falseValue;
	}

	override get smtString(): string {
		return `(if ${this.condition.smtString} ${this.trueValue.smtString} ${this.falseValue.smtString})`;
	}

	override clone(): SymbolicExpression {
		return new TernarySymbolicExpression(this.condition, this.trueValue, this.falseValue);
	}
}