import * as Ts from "ts-morph";

import symbolicBuiltinClasses from "#r/symbolic/builtins/SymbolicBuiltins";
import type {Cfg} from "./Cfg";
import {isEmptyCfg} from "./Cfg";
import CfgNode from "./CfgNode";
import CfgNodeKind from "./CfgNodeKind";

export function generateCfgFromFunction(functionDeclaration: Ts.FunctionDeclaration) {
	const cfg = generateCfgFromNode(functionDeclaration.getBody()!);
	cfg.escapeNode.primaryNext = cfg.endNode;
	return cfg;
}

function generateCfgFromNode(tsNode: Ts.Node): Cfg {
	const cfg: Cfg = {
		beginNode: new CfgNode(CfgNodeKind.BEGIN, null),
		endNode: new CfgNode(CfgNodeKind.END, null),
		escapeNode: new CfgNode(CfgNodeKind.ESCAPE, null),
		continueNode: new CfgNode(CfgNodeKind.CONTINUE, null),
		breakNode: new CfgNode(CfgNodeKind.BREAK, null)
	};
	cfg.beginNode.primaryNext = cfg.endNode;
	switch (tsNode.getKind()) {
		// Statements.
		case Ts.SyntaxKind.Block: {
			let blockTsNode = tsNode as Ts.Block;
			cfg.beginNode.tsNode = blockTsNode.getChildren()[0];
			cfg.endNode.tsNode = blockTsNode.getChildren()[2];
			let lastCfgNode = cfg.beginNode;
			for (const statement of (tsNode as Ts.Block).getStatements()) {
				const subCfg = generateCfgFromNode(statement);
				if (isEmptyCfg(subCfg)) continue;
				lastCfgNode.primaryNext = subCfg.beginNode;
				subCfg.escapeNode.primaryNext = cfg.escapeNode;
				lastCfgNode = subCfg.endNode;
			}
			lastCfgNode.primaryNext = cfg.endNode;
			break;
		}
		case Ts.SyntaxKind.IfStatement: {
			const ifTsNode = tsNode as Ts.IfStatement;
			const conditionSubCfg = generateCfgFromNode(ifTsNode.getExpression());
			cfg.beginNode.primaryNext = conditionSubCfg.beginNode;
			const ifCfgNode = new CfgNode(CfgNodeKind.CONDITION, ifTsNode);
			conditionSubCfg.endNode.primaryNext = ifCfgNode;
			const thenSubCfg = generateCfgFromNode(ifTsNode.getThenStatement());
			if (isEmptyCfg(thenSubCfg)) {
				ifCfgNode.primaryNext = cfg.endNode;
			} else {
				ifCfgNode.primaryNext = thenSubCfg.beginNode;
				thenSubCfg.escapeNode.primaryNext = cfg.escapeNode;
				thenSubCfg.endNode.primaryNext = cfg.endNode;
			}
			const elseTsNode = ifTsNode.getElseStatement();
			if (elseTsNode === undefined) {
				ifCfgNode.secondaryNext = cfg.endNode;
			} else {
				const elseSubCfg = generateCfgFromNode(elseTsNode);
				if (isEmptyCfg(elseSubCfg)) {
					ifCfgNode.secondaryNext = cfg.endNode;
				} else {
					ifCfgNode.secondaryNext = elseSubCfg.beginNode;
					elseSubCfg.escapeNode.primaryNext = cfg.escapeNode;
					elseSubCfg.endNode.primaryNext = cfg.endNode;
				}
			}
			break;
		}
		case Ts.SyntaxKind.ForStatement:
		case Ts.SyntaxKind.WhileStatement: {
			const loopTsNode = tsNode as Ts.ForStatement | Ts.WhileStatement;
			const loopCfgNode = new CfgNode(CfgNodeKind.CONDITION, loopTsNode);
			cfg.beginNode.primaryNext = loopCfgNode;
			loopCfgNode.secondaryNext = cfg.endNode;
			const subCfg = generateCfgFromNode(loopTsNode.getStatement());
			if (isEmptyCfg(subCfg)) {
				loopCfgNode.primaryNext = loopCfgNode;
			} else {
				loopCfgNode.primaryNext = subCfg.beginNode;
				subCfg.escapeNode.primaryNext = cfg.escapeNode;
				subCfg.continueNode.primaryNext = loopCfgNode;
				subCfg.breakNode.primaryNext = cfg.endNode;
				subCfg.endNode.primaryNext = loopCfgNode;
			}
			break;
		}
		case Ts.SyntaxKind.DoStatement: {
			const doWhileTsNode = tsNode as Ts.DoStatement;
			const doWhileConditionNode = new CfgNode(CfgNodeKind.CONDITION, doWhileTsNode);
			const subCfg = generateCfgFromNode(doWhileTsNode.getStatement());
			if (isEmptyCfg(subCfg)) {
				cfg.beginNode.primaryNext = doWhileConditionNode;
			} else {
				cfg.beginNode.primaryNext = subCfg.beginNode;
				subCfg.escapeNode.primaryNext = cfg.escapeNode;
				subCfg.continueNode.primaryNext = doWhileConditionNode;
				subCfg.breakNode.primaryNext = cfg.endNode;
				subCfg.endNode.primaryNext = doWhileConditionNode;
			}
			doWhileConditionNode.primaryNext = cfg.beginNode.primaryNext;
			doWhileConditionNode.secondaryNext = cfg.endNode;
			break;
		}
		case Ts.SyntaxKind.ForInStatement:
		case Ts.SyntaxKind.ForOfStatement: {
			const forTsNode = tsNode as Ts.ForInStatement | Ts.ForOfStatement;
			const forCfgNode = new CfgNode(CfgNodeKind.FOR_EACH, forTsNode);
			cfg.beginNode.primaryNext = forCfgNode;
			forCfgNode.secondaryNext = cfg.endNode;
			const subCfg = generateCfgFromNode(forTsNode.getStatement());
			if (isEmptyCfg(subCfg)) {
				forCfgNode.primaryNext = cfg.endNode;
			} else {
				forCfgNode.primaryNext = subCfg.beginNode;
				subCfg.escapeNode.primaryNext = cfg.escapeNode;
				subCfg.continueNode.primaryNext = forCfgNode;
				subCfg.breakNode.primaryNext = cfg.endNode;
				subCfg.endNode.primaryNext = cfg.endNode;
			}
			break;
		}
		case Ts.SyntaxKind.SwitchStatement: {
			const switchTsNode = tsNode as Ts.SwitchStatement;
			let previousCaseNode: CfgNode | null = null;
			let previousEndCaseNode: CfgNode | null = null;
			for (const caseClause of switchTsNode.getCaseBlock().getClauses()) {
				const caseCfgNode = new CfgNode(CfgNodeKind.CONDITION, caseClause);
				if (previousCaseNode !== null) {
					previousCaseNode.secondaryNext = caseCfgNode;
				} else {
					cfg.beginNode.primaryNext = caseCfgNode;
				}
				previousCaseNode = caseCfgNode;
				const subCfg = generateCfgFromNode(caseClause);
				if (previousEndCaseNode !== null) {
					previousEndCaseNode.primaryNext = subCfg.beginNode;
				}
				caseCfgNode.primaryNext = subCfg.beginNode;
				subCfg.escapeNode.primaryNext = cfg.escapeNode;
				subCfg.breakNode.primaryNext = cfg.endNode;
				previousEndCaseNode = subCfg.endNode;
			}
			if (previousEndCaseNode !== null)
				previousEndCaseNode.primaryNext = cfg.endNode;
			break;
		}
		case Ts.SyntaxKind.CaseClause:
		case Ts.SyntaxKind.DefaultClause:
			const caseTsNode = tsNode as Ts.CaseOrDefaultClause;
			let lastCfgNode = cfg.beginNode;
			for (const statement of caseTsNode.getStatements()) {
				const subCfg = generateCfgFromNode(statement);
				if (isEmptyCfg(subCfg)) continue;
				lastCfgNode.primaryNext = subCfg.beginNode;
				subCfg.escapeNode.primaryNext = cfg.escapeNode;
				lastCfgNode = subCfg.endNode;
			}
			lastCfgNode.primaryNext = cfg.endNode;
			break;
		case Ts.SyntaxKind.BreakStatement: {
			cfg.beginNode.primaryNext = cfg.breakNode;
			break;
		}
		case Ts.SyntaxKind.ReturnStatement: {
			const expression = (tsNode as Ts.ReturnStatement).getExpression();
			if (expression === undefined) {
				cfg.beginNode.primaryNext = cfg.escapeNode;
				break;
			}
			const expressionSubCfg = generateCfgFromNode(expression);
			if (isEmptyCfg(expressionSubCfg)) {
				cfg.beginNode.primaryNext = cfg.escapeNode;
			} else {
				cfg.beginNode.primaryNext = expressionSubCfg.beginNode;
				expressionSubCfg.endNode.primaryNext = cfg.escapeNode;
			}
			break;
		}
		case Ts.SyntaxKind.VariableStatement: {
			let lastCfgNode = cfg.beginNode;
			for (const variableDeclaration of (tsNode as Ts.VariableStatement).getDeclarations()) {
				const initializer = variableDeclaration.getInitializer();
				if (initializer === undefined) continue;
				const initializerSubCfg = generateCfgFromNode(initializer);
				if (isEmptyCfg(initializerSubCfg)) continue;
				lastCfgNode.primaryNext = initializerSubCfg.beginNode;
				lastCfgNode = initializerSubCfg.endNode;
			}
			lastCfgNode.primaryNext = cfg.endNode;
			break;
		}
		case Ts.SyntaxKind.ExpressionStatement:
			return generateCfgFromNode((tsNode as Ts.ExpressionStatement).getExpression());

		// Expressions.
		case Ts.SyntaxKind.PrefixUnaryExpression:
		case Ts.SyntaxKind.PostfixUnaryExpression:
			return generateCfgFromNode((tsNode as Ts.PrefixUnaryExpression | Ts.PostfixUnaryExpression).getOperand());
		case Ts.SyntaxKind.BinaryExpression: {
			const binaryExpression = tsNode as Ts.BinaryExpression;
			const leftSubCfg = generateCfgFromNode(binaryExpression.getLeft());
			const rightSubCfg = generateCfgFromNode(binaryExpression.getLeft());
			cfg.beginNode.primaryNext = leftSubCfg.beginNode;
			leftSubCfg.endNode.primaryNext = rightSubCfg.beginNode;
			rightSubCfg.endNode.primaryNext = cfg.endNode;
			break;
		}
		case Ts.SyntaxKind.CallExpression: {
			const callExpression = tsNode as Ts.CallExpression;
			const functionExpression = callExpression.getExpression();
			if (Ts.Node.isPropertyAccessExpression(functionExpression)) {
				const functionContainerExpression = functionExpression.getExpression();
				if (Ts.Node.isIdentifier(functionContainerExpression)) {
					const className = functionContainerExpression.getSymbol()!.getFullyQualifiedName();
					const builtinClass = symbolicBuiltinClasses[className];
					if (builtinClass !== undefined && builtinClass[functionExpression.getName()] !== undefined) break;
				}
			}
			const functionSubCfg = generateCfgFromNode(functionExpression);
			cfg.beginNode.primaryNext = functionSubCfg.beginNode;
			let lastCfgNode = functionSubCfg.endNode;
			for (const argument of callExpression.getArguments()) {
				const argumentSubCfg = generateCfgFromNode(argument);
				if (isEmptyCfg(argumentSubCfg)) continue;
				lastCfgNode.primaryNext = argumentSubCfg.beginNode;
				lastCfgNode = argumentSubCfg.endNode;
			}
			const callCfgNode = new CfgNode(CfgNodeKind.CALL, tsNode);
			lastCfgNode.primaryNext = callCfgNode;
			callCfgNode.primaryNext = cfg.endNode;
			break;
		}
	}
	return cfg;
}