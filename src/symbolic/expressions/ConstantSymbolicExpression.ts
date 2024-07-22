import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";

export default class ConstantSymbolicExpression extends SymbolicExpression {
	value: any;

	constructor(value: any) {
		super(SymbolicExpressionKind.CONSTANT);
		this.value = value;
	}

	override get smtString(): string {
		if (typeof this.value === "number") {
			if (this.value < 0) return `(- ${formatNumber(-this.value)})`;
			return formatNumber(this.value);
		}
		return this.value.toString();
	}

	override clone(): SymbolicExpression {
		return new ConstantSymbolicExpression(structuredClone(this.value));
	}
}

function formatNumber(n: number): string {
	const s = n.toString();
	return s.indexOf('.') === -1 ? s + ".0" : s;
}