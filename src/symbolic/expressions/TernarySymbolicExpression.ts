import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

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

	override getChildExpressions(): SymbolicExpression[] {
		return [this.condition, this.trueValue, this.falseValue];
	}

	override clone(): SymbolicExpression {
		return new TernarySymbolicExpression(this.condition, this.trueValue, this.falseValue);
	}
}