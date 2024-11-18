import BaseSymbolicType from "#r/symbolic/BaseSymbolicType";
import {formatSmtNumber, formatSmtString} from "#r/utilities/SmtUtils";

import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

export default class ConstantSymbolicExpression extends SymbolicExpression {
	value: any;

	constructor(value: any) {
		super(SymbolicExpressionKind.CONSTANT);
		this.value = value;
	}

	override generateSmt(): {expression: string, type: BaseSymbolicType} {
		let expression: string;
		switch (typeof this.value) {
			case "number":
				expression = formatSmtNumber(this.value);
				break;
			case "string":
				expression = formatSmtString(this.value);
				break;
			case "boolean":
				expression = this.value.toString();
				break;
			default:
				throw new Error(`Unhandled constant value type ${typeof this.value}.`);
		}
		return {expression, type: this.#getBaseType()};
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [];
	}

	override clone(): SymbolicExpression {
		return new ConstantSymbolicExpression(structuredClone(this.value));
	}

	#getBaseType(): BaseSymbolicType {
		switch (typeof this.value) {
			case "number": return BaseSymbolicType.NUMBER;
			case "string": return BaseSymbolicType.STRING;
			case "boolean": return BaseSymbolicType.BOOLEAN;
			default: throw new Error("Constant value is not of a supported type.");
		}
	}
}