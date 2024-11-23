import BaseSymbolicType from "#r/symbolic/BaseSymbolicType";

import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

export type ObjectSymbolicValue = {[key: string]: SymbolicExpression | undefined};

export default class ObjectSymbolicExpression extends SymbolicExpression {
	value: ObjectSymbolicValue;

	constructor(value: ObjectSymbolicValue) {
		super(SymbolicExpressionKind.OBJECT);
		this.value = value;
	}

	override generateSmt(): {expression: string, type: BaseSymbolicType, additionalConstraints: SymbolicExpression[]} {
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