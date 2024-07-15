import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";

export default class ConstantSymbolicExpression extends SymbolicExpression {
	value: any;

	constructor(value: any) {
		super(SymbolicExpressionKind.CONSTANT);
		this.value = value;
	}

	override get smtString(): string {
		if (typeof this.value === "number" && this.value < 0) return `(- ${-this.value})`;
		return this.value.toString();
	}

	override clone(): SymbolicExpression {
		return new ConstantSymbolicExpression(structuredClone(this.value));
	}
}