import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";

export type ObjectSymbolicValue = {[key: string]: SymbolicExpression | undefined};

export default class ObjectSymbolicExpression extends SymbolicExpression {
	value: ObjectSymbolicValue;

	constructor(value: ObjectSymbolicValue) {
		super(SymbolicExpressionKind.OBJECT);
		this.value = value;
	}

	override get smtString(): string {
		throw new TypeError("Object symbolic expression used in SMT expression.");
	}

	override getChildExpressions(): SymbolicExpression[] {
		return Object.values(this.value) as SymbolicExpression[];
	}

	override clone(): SymbolicExpression {
		// Intentional: `value` is not cloned because it's still the same object.
		return new ObjectSymbolicExpression(this.value);
	}
}