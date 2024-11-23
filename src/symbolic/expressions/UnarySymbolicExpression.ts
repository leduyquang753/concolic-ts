import BaseSymbolicType from "#r/symbolic/BaseSymbolicType";

import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

const smtOperatorMap: {[jsOperator: string]: string | undefined} = {
	"!": "not"
};

export default class UnarySymbolicExpression extends SymbolicExpression {
	operator: string;
	operand: SymbolicExpression;

	constructor(operator: string, operand: SymbolicExpression) {
		super(SymbolicExpressionKind.UNARY);
		this.operator = operator;
		this.operand = operand;
	}

	override generateSmt(): {expression: string, type: BaseSymbolicType, additionalConstraints: SymbolicExpression[]} {
		const operandSmt = this.operand.generateSmt();
		if (operandSmt.type === BaseSymbolicType.STRING)
			throw new Error("Unary string operations are not yet supported.");
		return {
			expression: `(${smtOperatorMap[this.operator] ?? this.operator} ${operandSmt.expression})`,
			type: this.operator === "!" ? BaseSymbolicType.BOOLEAN : operandSmt.type,
			additionalConstraints: [...operandSmt.additionalConstraints]
		};
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [this.operand];
	}

	override clone(): SymbolicExpression {
		return new UnarySymbolicExpression(this.operator, this.operand);
	}
}