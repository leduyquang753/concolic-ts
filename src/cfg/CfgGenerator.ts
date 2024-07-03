import * as Ts from "ts-morph";

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
			const ifCfgNode = new CfgNode(CfgNodeKind.CONDITION, ifTsNode);
			cfg.beginNode.primaryNext = ifCfgNode;
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
		case Ts.SyntaxKind.ReturnStatement: {
			cfg.beginNode.primaryNext = cfg.escapeNode;
			break;
		}
	}
	return cfg;
}