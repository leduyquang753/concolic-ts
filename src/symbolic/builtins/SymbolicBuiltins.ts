import BinarySymbolicExpression from "#r/symbolic/expressions/BinarySymbolicExpression";
import SymbolicExpression from "#r/symbolic/expressions/SymbolicExpression";
import UnarySymbolicExpression from "#r/symbolic/expressions/UnarySymbolicExpression";

export type SymbolicBuiltinClassFunction = (args: SymbolicExpression[]) => SymbolicExpression;
export type SymbolicBuiltinClass = {
	[functionName: string]: SymbolicBuiltinClassFunction | undefined
};

function singleArgumentBuiltinImpl(name: string, operator: string, args: SymbolicExpression[]): SymbolicExpression {
	if (args.length !== 1) throw new Error(`${name} expects exactly one argument.`);
	return new UnarySymbolicExpression(operator, args[0]);
}

export function singleArgumentBuiltin(name: string, operator: string): SymbolicBuiltinClassFunction {
	return singleArgumentBuiltinImpl.bind(null, name, operator);
}

function doubleArgumentBuiltinImpl(name: string, operator: string, args: SymbolicExpression[]): SymbolicExpression {
	if (args.length !== 2) throw new Error(`${name} expects exactly two arguments.`);
	return new BinarySymbolicExpression(operator, args[0], args[1]);
}

export function doubleArgumentBuiltin(name: string, operator: string): SymbolicBuiltinClassFunction {
	return doubleArgumentBuiltinImpl.bind(null, name, operator);
}

import mathBuiltins from "./MathBuiltins";

const symbolicBuiltinClasses: {[className: string]: SymbolicBuiltinClass | undefined} = {
	"Math": mathBuiltins
};

export default symbolicBuiltinClasses;