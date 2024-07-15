import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";

const smtOperatorMapping: {[jsOperator: string]: string | undefined} = {
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

	override trySimplify(): SymbolicExpression {
		if (this.operator === "+") return this.operand;
		return this;
	}

	override get smtString(): string {
		return `(${smtOperatorMapping[this.operator] ?? this.operator} ${this.operand.smtString})`;
	}

	override clone(): SymbolicExpression {
		return new UnarySymbolicExpression(this.operator, this.operand);
	}
}