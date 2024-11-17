import BaseSymbolicType from "#r/symbolic/BaseSymbolicType";

import ConstantSymbolicExpression from "./ConstantSymbolicExpression.js";
import SymbolicExpression from "./SymbolicExpression.js";
import SymbolicExpressionKind from "./SymbolicExpressionKind.js";

const numberSmtOperatorMap: {[jsOperator: string]: string | undefined} = {
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
const stringSmtOperatorMap: {[jsOperator: string]: [string, boolean] | undefined} = {
	"+": ["str.++", false],
	"==": ["=", false],
	"===": ["=", false],
	"!=": ["distinct", false],
	"!==": ["distinct", false],
	"<": ["str.<", false],
	"<=": ["str.<=", false],
	">": ["str.<", true],
	">=": ["str.<=", true]
};

const comparisonOperators = new Set<string>([
	"==", "===", "!=", "!==", "<", "<=", ">", ">="
]);

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

	override generateSmt(): {expression: string, type: BaseSymbolicType} {
		const leftSmt = this.leftOperand.generateSmt();
		const rightSmt = this.rightOperand.generateSmt();
		if (leftSmt.type !== rightSmt.type)
			throw new Error("Binary operations with different types are not yet supported.");
		let smtOperator = "";
		let shouldReverse = false;
		switch (leftSmt.type) {
			case BaseSymbolicType.NUMBER:
			case BaseSymbolicType.BOOLEAN:
				smtOperator = numberSmtOperatorMap[this.operator] ?? this.operator;
				break;
			case BaseSymbolicType.STRING:
				[smtOperator, shouldReverse] = stringSmtOperatorMap[this.operator] ?? [this.operator, false];
				break;
			default:
				throw new Error("Unhandled base symbolic type.");
		}
		return {
			expression: `(${smtOperator} `
				+ `${shouldReverse ? rightSmt.expression : leftSmt.expression} `
				+ `${shouldReverse ? leftSmt.expression : rightSmt.expression})`,
			type: comparisonOperators.has(this.operator) ? BaseSymbolicType.BOOLEAN : leftSmt.type
		};
	}

	override getChildExpressions(): SymbolicExpression[] {
		return [this.leftOperand, this.rightOperand];
	}

	override clone(): SymbolicExpression {
		return new BinarySymbolicExpression(this.operator, this.leftOperand, this.rightOperand);
	}
}