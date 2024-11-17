import BaseSymbolicType from "#r/symbolic/BaseSymbolicType";

import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

export default class VariableSymbolicExpression extends SymbolicExpression {
	symbolicName: string;
	isParameter: boolean;
	type: BaseSymbolicType;

	constructor(symbolicName: string, isParameter: boolean, type: BaseSymbolicType) {
		super(SymbolicExpressionKind.VARIABLE);
		this.symbolicName = symbolicName;
		this.isParameter = isParameter;
		this.type = type;
	}

	override generateSmt(): {expression: string, type: BaseSymbolicType} {
		if (!this.isParameter) throw new TypeError("Symbolic variable is unresolved.");
		return {expression: this.symbolicName, type: this.type};
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [];
	}

	override clone(): SymbolicExpression {
		return new VariableSymbolicExpression(this.symbolicName, this.isParameter, this.type);
	}
}