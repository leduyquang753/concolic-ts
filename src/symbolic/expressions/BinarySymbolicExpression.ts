import ConstantSymbolicExpression from "./ConstantSymbolicExpression";
import SymbolicExpression from "./SymbolicExpression";
import SymbolicExpressionKind from "./SymbolicExpressionKind";

const smtOperatorMap: {[jsOperator: string]: string | undefined} = {
	"%": "mod",
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
		super(SymbolicExpressionKind.BINARY);
		this.operator = operator;
		this.leftOperand = leftOperand;
		this.rightOperand = rightOperand;
	}

	override trySimplify(recurse: boolean): SymbolicExpression {
		const simplifiedLeft = recurse ? this.leftOperand.trySimplify(recurse) : this.leftOperand;
		const simplifiedRight = recurse ? this.rightOperand.trySimplify(recurse) : this.rightOperand;
		if (simplifiedLeft.kind === SymbolicExpressionKind.CONSTANT) {
			const constantLeft = simplifiedLeft as ConstantSymbolicExpression;
			const simplifiedWithConstant = this.simplifyExpressionWithConstant(constantLeft, simplifiedRight);
			if (simplifiedWithConstant !== null) return simplifiedWithConstant;
			if (simplifiedRight.kind === SymbolicExpressionKind.CONSTANT) {
				const constantRight = simplifiedRight as ConstantSymbolicExpression;
				switch (this.operator) {
					case '+':
						return new ConstantSymbolicExpression(constantLeft.value + constantRight.value);
					case '-':
						return new ConstantSymbolicExpression(constantLeft.value - constantRight.value);
					case '*':
						return new ConstantSymbolicExpression(constantLeft.value * constantRight.value);
					case '/':
						if (constantRight.value !== 0) {
							return new ConstantSymbolicExpression(constantLeft.value / constantRight.value);
						} else {
							throw new Error("Division by zero");
						}
					case '%':
						return new ConstantSymbolicExpression(constantLeft.value % constantRight.value);
					case '>':
						return new ConstantSymbolicExpression(constantLeft.value > constantRight.value);
					case '>=':
						return new ConstantSymbolicExpression(constantLeft.value >= constantRight.value);
					case '<':
						return new ConstantSymbolicExpression(constantLeft.value < constantRight.value);
					case '<=':
						return new ConstantSymbolicExpression(constantLeft.value <= constantRight.value);
					case '===':
					case '==':
						return new ConstantSymbolicExpression(constantLeft.value === constantRight.value);
					case '!==':
					case '!=':
						return new ConstantSymbolicExpression(constantLeft.value !== constantRight.value);
				}
			}
		}
		if (simplifiedRight.kind === SymbolicExpressionKind.CONSTANT) {
			const simplifiedWithConstant = this.simplifyExpressionWithConstant(
				simplifiedRight as ConstantSymbolicExpression, simplifiedLeft
			);
			if (simplifiedWithConstant !== null) return simplifiedWithConstant;
		}
		if (simplifiedLeft.kind === SymbolicExpressionKind.BINARY) {
			const simplifiedWithConstant = this.simplifyDistributedMultiplication(
				simplifiedRight, simplifiedLeft as BinarySymbolicExpression
			);
			if (simplifiedWithConstant !== null) return simplifiedWithConstant;
		}
		if (simplifiedRight.kind === SymbolicExpressionKind.BINARY) {
			const simplifiedWithConstant = this.simplifyDistributedMultiplication(
				simplifiedLeft, simplifiedRight as BinarySymbolicExpression
			);
			if (simplifiedWithConstant !== null) return simplifiedWithConstant;
		}
		this.leftOperand = simplifiedLeft;
		this.rightOperand = simplifiedRight;
		return this;
	}

	simplifyExpressionWithConstant(
		constant: ConstantSymbolicExpression, other: SymbolicExpression
	): SymbolicExpression | null {
		if (this.operator === "+" && constant.value === 0) return other;
		if (this.operator === "*") {
			if (constant.value === 0) return new ConstantSymbolicExpression(0);
			if (constant.value === 1) return other;
		}
		return null;
	}

	simplifyDistributedMultiplication(
		leftExpression: SymbolicExpression, rightExpression: BinarySymbolicExpression
	): SymbolicExpression | null {
		if (this.operator === '*') {
			if (rightExpression.operator === '+' || rightExpression.operator === '-') {
				return new BinarySymbolicExpression(
					rightExpression.operator,
					new BinarySymbolicExpression('*', leftExpression, rightExpression.leftOperand),
					new BinarySymbolicExpression('*', leftExpression, rightExpression.rightOperand)
				).trySimplify(true);
			}
		}
		return null;
	}

	override get smtString(): string {
		return (
			`(${smtOperatorMap[this.operator] ?? this.operator} `
			+ `${this.leftOperand.smtString} ${this.rightOperand.smtString})`
		);
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [this.leftOperand, this.rightOperand];
	}

	override clone(): SymbolicExpression {
		return new BinarySymbolicExpression(this.operator, this.leftOperand, this.rightOperand);
	}
}