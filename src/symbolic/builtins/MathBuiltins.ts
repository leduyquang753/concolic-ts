import SymbolicExpression from "#r/symbolic/expressions/SymbolicExpression";

import type {SymbolicBuiltinClass} from "./SymbolicBuiltins";
import {singleArgumentBuiltin} from "./SymbolicBuiltins";

const mathBuiltins: SymbolicBuiltinClass = {
	"abs": singleArgumentBuiltin("Math.abs", "abs"),
	"acos": singleArgumentBuiltin("Math.acos", "acos"),
	"asin": singleArgumentBuiltin("Math.asin", "asin"),
	"atan": singleArgumentBuiltin("Math.atan", "atan"),
	"cos": singleArgumentBuiltin("Math.cos", "cos"),
	"sin": singleArgumentBuiltin("Math.sin", "sin"),
	"sqrt": singleArgumentBuiltin("Math.sqrt", "sqrt"),
	"tan": singleArgumentBuiltin("Math.tan", "tan")
};

export default mathBuiltins;