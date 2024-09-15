import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

export default class VariableSymbolicExpression extends SymbolicExpression {
	symbolicName: string;
	isParameter: boolean;

	constructor(symbolicName: string, isParameter: boolean) {
		super(SymbolicExpressionKind.VARIABLE);
		this.symbolicName = symbolicName;
		this.isParameter = isParameter;
	}

	override get smtString(): string {
		if (!this.isParameter) throw new TypeError("Symbolic variable is unresolved.");
		return this.symbolicName;
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [];
	}

	override clone(): SymbolicExpression {
		return new VariableSymbolicExpression(this.symbolicName, this.isParameter);
	}
}