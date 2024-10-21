import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";
import VariableType from "./VariableType";

export default class VariableSymbolicExpression extends SymbolicExpression {
	symbolicName: string;
	isParameter: boolean;
	type: VariableType;

	constructor(symbolicName: string, isParameter: boolean, type: VariableType) {
		super(SymbolicExpressionKind.VARIABLE);
		this.symbolicName = symbolicName;
		this.isParameter = isParameter;
		this.type = type
	}

	override get smtString(): string {
		if (!this.isParameter) throw new TypeError("Symbolic variable is unresolved.");
		return this.symbolicName;
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [];
	}

	override clone(): SymbolicExpression {
		return new VariableSymbolicExpression(this.symbolicName, this.isParameter, this.type);
	}

	getType(): string {
		switch (this.type) {
			case VariableType.NUMBER:
				return 'number';
			case VariableType.BOOLEAN:
				return 'boolean';
			case VariableType.STRING:
				return 'string';
			case VariableType.OBJECT:
				return 'object';
		}
	}
}