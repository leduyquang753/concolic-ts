import SymbolicExpression from "#r/symbolic/expressions/SymbolicExpression";

import type {SymbolicBuiltinClass} from "./SymbolicBuiltins";
import {singleArgumentBuiltin} from "./SymbolicBuiltins";

const mathBuiltins: SymbolicBuiltinClass = {
	"abs": singleArgumentBuiltin("Math.abs", "abs"),
	"cos": singleArgumentBuiltin("Math.cos", "cos"),
	"sin": singleArgumentBuiltin("Math.sin", "sin"),
	"tan": singleArgumentBuiltin("Math.tan", "tan")
};

export default mathBuiltins;