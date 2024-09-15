import BinarySymbolicExpression from "./BinarySymbolicExpression.js";
import ConstantSymbolicExpression from "./ConstantSymbolicExpression.js";
import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

const inverseOperatorMap: {[operator: string]: string} = {
	"<": ">=",
	">": "<=",
	"<=": ">",
	">=": "<",
	"==": "!==",
	"===": "!==",
	"!=": "===",
	"!==": "==="
};
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

	override trySimplify(recurse: boolean): SymbolicExpression {
		let simplifiedOperand = recurse ? this.operand.trySimplify(recurse) : this.operand;
		if (this.operator === "+") return simplifiedOperand;
		if (simplifiedOperand.kind === SymbolicExpressionKind.CONSTANT) {
			let constantOperand = simplifiedOperand as ConstantSymbolicExpression;
			if (this.operator === "-") return new ConstantSymbolicExpression(-constantOperand.value);
			if (this.operator === "!") return new ConstantSymbolicExpression(!constantOperand.value);
		}
		if (this.operator === "!") {
			if (simplifiedOperand.kind === SymbolicExpressionKind.BINARY) {
				const binaryExpression = simplifiedOperand as BinarySymbolicExpression;
				const invertedOperator = inverseOperatorMap[binaryExpression.operator];
				if (invertedOperator !== undefined) return new BinarySymbolicExpression(
					invertedOperator, binaryExpression.leftOperand, binaryExpression.rightOperand
				);
            }
        }
        this.operand = simplifiedOperand;
		return this;
	}

	override get smtString(): string {
		return `(${smtOperatorMap[this.operator] ?? this.operator} ${this.operand.smtString})`;
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [this.operand];
	}

	override clone(): SymbolicExpression {
		return new UnarySymbolicExpression(this.operator, this.operand);
	}
}