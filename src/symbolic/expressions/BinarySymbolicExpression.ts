import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";

const smtOperatorMapping: {[jsOperator: string]: string | undefined} = {
	"**": "^",
	"==": "=",
	"===": "=",
	"!=": "distinct",
	"!==": "distinct",
	"&&": "and",
	"||": "or",
	"^": "xor"
};

export default class BinarySymbolicExpression extends SymbolicExpression {
	operator: string;
	leftOperand: SymbolicExpression;
	rightOperand: SymbolicExpression;

	constructor(operator: string, leftOperand: SymbolicExpression, rightOperand: SymbolicExpression) {
		super(SymbolicExpressionKind.UNARY);
		this.operator = operator;
		this.leftOperand = leftOperand;
		this.rightOperand = rightOperand;
	}

	override get smtString(): string {
		return (
			`(${smtOperatorMapping[this.operator] ?? this.operator} `
			+ `${this.leftOperand.smtString} ${this.rightOperand.smtString})`
		);
	}

	override clone(): SymbolicExpression {
		return new BinarySymbolicExpression(this.operator, this.leftOperand, this.rightOperand);
	}
}