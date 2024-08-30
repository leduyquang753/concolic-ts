import * as ChildProcess from "child_process";
import * as FileSystem from "fs";
import * as Http from "http";
import * as Path from "path";
import {Shescape} from "shescape";
import {SourceMapConsumer} from "source-map";
import * as TemplateFile from "template-file";
import * as Ts from "ts-morph";
import * as Url from "url";

import config from "#r/config";
import type {Cfg} from "#r/cfg/Cfg";
import {compactCfg} from "#r/cfg/Cfg";
import type CfgNode from "#r/cfg/CfgNode";
import CfgNodeKind from "#r/cfg/CfgNodeKind";
import {generateCfgFromFunction} from "#r/cfg/CfgGenerator";
import SymbolicExecutor from "#r/symbolic/SymbolicExecutor";
import SymbolicExpression from "#r/symbolic/expressions/SymbolicExpression";
import SymbolicExpressionKind from "#r/symbolic/expressions/SymbolicExpressionKind";
import UnarySymbolicExpression from "#r/symbolic/expressions/UnarySymbolicExpression";
import VariableSymbolicExpression from "#r/symbolic/expressions/VariableSymbolicExpression";

import type {Breakpoint} from "./Breakpoints";
import {getBreakpointsFromCfg} from "./Breakpoints";
import {transformStatement} from "./CodeTransformer";
import DebuggerWebsocket from "./DebuggerWebsocket";

type FunctionData = {cfg: Cfg, breakpoints: Breakpoint[]};
type BranchingRecord = {parentCalls: string, cfgNode: CfgNode, isSecondary: boolean};

const shescape = new Shescape({shell: true});

export default class Executor {
	#projectPath: string;
	#projectConfiguration: Ts.ts.ParsedCommandLine;
	#sourceFile: Ts.SourceFile;
	#functionDataMap: {[name: string]: FunctionData | undefined} = {};
	#functionNameToTest: string;
	#topLevelParameterNames: string[] = [];
	#parameterNames: Set<string> = new Set<string>();
	#coveredCfgNodes: Set<string> = new Set<string>();
	#currentBranchingSeries: BranchingRecord[] = [];

	constructor(projectPath: string, sourceFile: Ts.SourceFile, functionNameToTest: string) {
		this.#projectPath = projectPath;
		this.#projectConfiguration = Ts.ts.getParsedCommandLineOfConfigFile(
			this.#projectPath + "\\tsconfig.json", undefined, Ts.ts.sys as any
		)!;
		this.#sourceFile = sourceFile;
		this.#functionNameToTest = functionNameToTest;
	}

	// Current limitation: must only be invoked once per instance.
	async execute(): Promise<void> {
		for (const functionDeclaration of this.#sourceFile.getFunctions())
			transformStatement(functionDeclaration.getBody()! as Ts.Statement, false);
		await this.#sourceFile.getProject().save();
		{
			let parameterIndex = 0;
			for (
				const parameterDeclaration
				of this.#sourceFile.getFunctionOrThrow(this.#functionNameToTest).getParameters()
			) {
				const nameNode = parameterDeclaration.getNameNode();
				const topLevelParameterName
					= Ts.Node.isIdentifier(nameNode) ? nameNode.getText() : `@${parameterIndex}`;
				this.#topLevelParameterNames.push(topLevelParameterName);
				collectParametersFromType(
					"", topLevelParameterName, parameterDeclaration.getType(), this.#parameterNames
				);
				++parameterIndex;
			}
		}
		let input: any | null = this.#generateInitialInput();
		while (input !== null) {
			console.log("Inputs: " + Object.entries(input).map(entry => `${entry[0]} = ${entry[1]}`).join("; "));
			this.#generateDriverScript(input);
			input = await this.#executeFunctionAndGetNextInput();
		}
		console.log("Done.");
	}

	async #executeFunctionAndGetNextInput(): Promise<any | null> {
		const sourceFilePath = this.#sourceFile.getFilePath();
		const compiledFilePath = this.#getCompiledFilePath(sourceFilePath);

		console.log("Starting debugger...");
		const process = ChildProcess.spawn("npx", [
			"vitest", "run", "test", "--dir", shescape.quote(this.#projectPath),
			"--inspect-brk=127.0.0.1:9339", "--no-file-parallelism"
		], {cwd: this.#projectPath, stdio: "pipe", shell: true});
		process.stdout!.on("data", data => {});
		process.stderr!.on("data", data => {console.log(data.toString());});
		const debuggerUrl = await new Promise<string>((resolve, reject) => {
			let failureCount = 0;
			const routine = () => {
				const request = Http.get("http://127.0.0.1:9339/json");
				request.on("error", () => {
					++failureCount;
					if (failureCount === 100) reject(new Error("Failed to contact the debugger after 100 tries."));
					setTimeout(routine, 100);
				});
				request.on("response", response => {
					if (response.statusCode !== 200) {
						reject(new Error(`Debugger query failed with status code ${response.statusCode}.`));
						response.resume();
						return;
					}
					response.setEncoding("utf8");
					let data = "";
					response.on("data", chunk => { data += chunk; });
					response.on("end", () => { resolve(JSON.parse(data)[0].webSocketDebuggerUrl); });
				});
			};
			setTimeout(routine, 100);
		});
		console.log(`Debugger started at URL: ${debuggerUrl}`);

		const websocket = new DebuggerWebsocket(debuggerUrl);
		await websocket.waitForConnection();
		console.log("Connected to the debugger.");
		let scriptId = "";
		let sourceMapPath = "";
		let scriptParsed = false;
		{
			const scriptUrl = Url.pathToFileURL(sourceFilePath).toString();
			const eventListener = (rawData: any): void => {
				const data = rawData as {scriptId: string, url: string, sourceMapURL: string};
				if (data.url === scriptUrl) {
					scriptId = data.scriptId;
					sourceMapPath = data.sourceMapURL;
					scriptParsed = true;
					websocket.removeListener("Debugger.scriptParsed", eventListener);
				}
			};
			websocket.on("Debugger.scriptParsed", eventListener);
		}
		websocket.sendCommand("Runtime.enable");
		await websocket.getCommandResponse();
		websocket.sendCommand("Debugger.enable");
		await websocket.getCommandResponse();
		websocket.sendCommand("Runtime.runIfWaitingForDebugger");
		await websocket.waitForEvent("Debugger.paused");
		while (!scriptParsed) {
			websocket.sendCommand("Debugger.stepOver");
			await websocket.waitForEvent("Debugger.paused");
		}
		const breakpointMap: {[id: string]: Breakpoint} = {};
		const functionsWithSetBreakpoints = new Set<string>();
		for (const functionDeclaration of this.#sourceFile.getFunctions()) await this.#setBreakpoints(
			functionDeclaration.getName()!, functionsWithSetBreakpoints,
			scriptId, websocket, breakpointMap
		);
		console.log("Set initial breakpoints, now running.");

		const functionToTest = this.#sourceFile.getFunctionOrThrow(this.#functionNameToTest);
		const symbolicExecutor = new SymbolicExecutor();
		symbolicExecutor.addParametersFromFunctionDeclaration(functionToTest);
		let cfg = this.#getFunctionData(this.#functionNameToTest).cfg;
		let currentCfgNode: CfgNode = cfg.beginNode.primaryNext!;
		let currentCodeNode = functionToTest.getBody()!;
		let pendingCallCfgNodes: CfgNode[] = [];
		const parentCalls: {
			cfg: Cfg, currentCfgNode: CfgNode, currentCodeNode: Ts.Node, pendingCallCfgNodes: CfgNode[]
		}[] = [];
		const parentCallPathStack: string[] = [];
		let parentCallPathString: string = "";
		const newBranchingSeries: BranchingRecord[] = [];
		const branchingConditions: SymbolicExpression[] = [];

		mainExecutionLoop: while (true) {
			if (currentCfgNode === cfg.endNode && parentCalls.length === 0) break;
			while (currentCfgNode !== cfg.endNode && !currentCfgNode.isBranching) {
				if (currentCfgNode.kind === CfgNodeKind.CALL) pendingCallCfgNodes.push(currentCfgNode);
				const next = currentCfgNode.primaryNext;
				if (next === null) throw new Error("Malformed CFG: a non-ending node connects to nowhere.");
				currentCfgNode = next;
			}
			while (true) {
				if (pendingCallCfgNodes.length !== 0) {
					const callCfgNode = pendingCallCfgNodes[0];
					const callPosition = callCfgNode.tsNode!.getStart();
					const expressionNode = getExpressionNode(currentCodeNode);
					if (
						expressionNode !== null
						&& callPosition >= expressionNode.getStart() && callPosition < expressionNode.getEnd()
					) {
						const callExpression = callCfgNode.tsNode! as Ts.CallExpression;
						const functionName = callExpression.getExpression().getText();
						const calledFunction = this.#sourceFile.getFunctionOrThrow(functionName);
						symbolicExecutor.prepareFunctionCall(
							calledFunction, callCfgNode.tsNode! as Ts.CallExpression
						);
						pendingCallCfgNodes.shift();
						parentCalls.push({cfg, currentCfgNode, currentCodeNode, pendingCallCfgNodes});
						parentCallPathStack.push(callExpression.getStart().toString());
						parentCallPathString
							= parentCallPathStack.join(' ') + (parentCallPathStack.length === 0 ? "" : " ");
						await this.#setBreakpoints(
							functionName, functionsWithSetBreakpoints,
							scriptId, websocket, breakpointMap
						);
						cfg = this.#getFunctionData(functionName).cfg;
						currentCfgNode = cfg.beginNode.primaryNext!;
						currentCodeNode = calledFunction.getBody()!;
						pendingCallCfgNodes = [];
						continue mainExecutionLoop;
					}
				}
				symbolicExecutor.executeNode(currentCodeNode);
				if (currentCodeNode === currentCfgNode.tsNode!) break;
				const next = getNextNodeToExecute(currentCodeNode);
				if (next === null) {
					if (parentCalls.length === 0) throw new Error("Code ended prematurely.");
					if (currentCfgNode !== cfg.endNode) throw new Error("Actual function call ended while CFG hasn't.");
					({cfg, currentCfgNode, currentCodeNode, pendingCallCfgNodes} = parentCalls.pop()!);
					parentCallPathStack.pop();
					parentCallPathString
						= parentCallPathStack.join(' ') + (parentCallPathStack.length === 0 ? "" : " ");
					continue mainExecutionLoop;
				}
				currentCodeNode = next;
			}
			while (true) {
				websocket.sendCommand("Debugger.resume");
				const event = await websocket.waitForAnyEvent();
				if (event.method === "Debugger.paused") {
					const hitBreakpoint = breakpointMap[event.params.hitBreakpoints[0]];
					if (hitBreakpoint.cfgNode === currentCfgNode) {
						if (newBranchingSeries.length < this.#currentBranchingSeries.length) {
							const currentRecord = this.#currentBranchingSeries[newBranchingSeries.length];
							if (
								currentRecord.parentCalls !== parentCallPathString
								|| currentRecord.cfgNode !== currentCfgNode
								|| currentRecord.isSecondary !== hitBreakpoint.isSecondaryBranch
							) throw new Error("Actual code execution doesn't match what's predicted.");
						}
						newBranchingSeries.push({
							parentCalls: parentCallPathString,
							cfgNode: currentCfgNode, isSecondary: hitBreakpoint.isSecondaryBranch
						});
						branchingConditions.push(getBranchingCondition(currentCfgNode, symbolicExecutor));
						currentCfgNode = hitBreakpoint.isSecondaryBranch
							? currentCfgNode.secondaryNext! : currentCfgNode.primaryNext!;
						currentCodeNode = getCodeNodeFromBranch(currentCodeNode, hitBreakpoint.isSecondaryBranch);
						break;
					}
				} else if (event.method === "Runtime.executionContextDestroyed") {
					throw new Error("Execution ended prematurely.");
				}
			}
		}
		websocket.close();
		console.log("Finished execution.");
		console.log("Branching series: " + newBranchingSeries.map(e => e.isSecondary ? '0' : '1').join(" "));
		if (this.#currentBranchingSeries.length !== 0) {
			const lastRecord = this.#currentBranchingSeries[this.#currentBranchingSeries.length - 1];
			this.#coveredCfgNodes.add(lastRecord.parentCalls + lastRecord.cfgNode.id);
		}
		while (true) {
			while (newBranchingSeries.length !== 0) {
				const lastRecord = newBranchingSeries[newBranchingSeries.length - 1];
				if (!this.#coveredCfgNodes.has(lastRecord.parentCalls + lastRecord.cfgNode.id)) break;
				newBranchingSeries.pop();
				branchingConditions.pop();
			}
			if (newBranchingSeries.length === 0) return null;
			console.log("Generating constraints...");
			const lastBranchIndex = newBranchingSeries.length - 1;
			newBranchingSeries[lastBranchIndex].isSecondary = !newBranchingSeries[lastBranchIndex].isSecondary;
			const conditions = [];
			for (let i = 0; i !== newBranchingSeries.length; ++i) conditions.push(
				newBranchingSeries[i].isSecondary
				? new UnarySymbolicExpression("!", branchingConditions[i])
				: branchingConditions[i]
			);
			const usedParameters = new Set<string>();
			for (const condition of conditions) collectUsedParametersFromCondition(condition, usedParameters);
			let smtString = "(set-option :pp.decimal true)\n";
			for (const parameter of usedParameters) smtString += `(declare-const ${parameter} Real)\n`;
			for (const condition of conditions) smtString += `(assert ${condition.smtString})\n`;
			smtString += "(check-sat-using qfnra-nlsat)\n(get-model)\n";
			const smtFilePath = Path.join(this.#projectPath, "smt.txt");
			FileSystem.writeFileSync(smtFilePath, smtString, "utf8");
			console.log("Solving constraints...");
			smtString = await new Promise(resolve => { ChildProcess.exec(
				`"${config.pathToZ3}" "${smtFilePath}"`, {cwd: this.#projectPath},
				(error: Error | null, stdout: string | Buffer, stderr: string | Buffer) => {
					resolve(stdout.toString());
				}
			); });
			if (smtString.substring(0, 5) === "unsat") {
				console.log("No input satisfies the constraints for the new path. Generating a new one.");
				newBranchingSeries.pop();
				branchingConditions.pop();
				continue;
			} else if (smtString.substring(0, 3) !== "sat") {
				throw new Error("Failed to solve constraints.");
			}
			this.#currentBranchingSeries = newBranchingSeries;
			const flatInputObject = Object.fromEntries([...smtString.matchAll(
				/\(define-fun ([\w.@]+) \(\) Real[^\d\(]+\(?((?:- )?[\d\.]+)\??\)/g
			)].map(entry => [entry[1], Number(entry[2].replaceAll(" ", ""))]));
			for (const parameterName of this.#parameterNames) if (!usedParameters.has(parameterName))
				flatInputObject[parameterName] = Math.floor(Math.random() * 201) - 100;
			return buildInputObject(flatInputObject);
		}
	}

	#generateDriverScript(input: any): void {
		FileSystem.writeFileSync(Path.join(this.#projectPath, "test.spec.ts"), TemplateFile.render(
			FileSystem.readFileSync(Path.join(this.#projectPath, "test.spec.ts.template"), "utf8"),
			{params: this.#topLevelParameterNames.map(name => input[name]).join(", ")}
		), "utf8");
		//ChildProcess.execSync("tsc", {cwd: this.#projectPath, stdio: "ignore"});
	}

	#generateInitialInput(): any {
		return buildInputObject(Object.fromEntries([...this.#parameterNames].map(
			parameterName => [parameterName, Math.floor(Math.random() * 201) - 100]
		)));
	}

	#getCompiledFilePath(sourceFilePath: string): string {
		return Ts.ts.getOutputFileNames(
			this.#projectConfiguration, sourceFilePath.replaceAll('\\', '/'), false
		)[0];
	}

	#getFunctionData(functionName: string): FunctionData {
		let functionData = this.#functionDataMap[functionName];
		if (functionData === undefined) {
			const cfg = generateCfgFromFunction(this.#sourceFile.getFunctionOrThrow(functionName));
			compactCfg(cfg);
			functionData = {cfg, breakpoints: getBreakpointsFromCfg(cfg)};
			this.#functionDataMap[functionName] = functionData;
		}
		return functionData;
	}

	async #setBreakpoints(
		functionName: string, setFunctions: Set<string>,
		scriptId: string,
		websocket: DebuggerWebsocket, breakpointMap: {[id: string]: Breakpoint}
	): Promise<void> {
		if (setFunctions.has(functionName)) return;
		setFunctions.add(functionName);
		for (const breakpoint of this.#getFunctionData(functionName).breakpoints) {
			websocket.sendCommand("Debugger.setBreakpoint", {
				location: {scriptId, lineNumber: breakpoint.line - 1, columnNumber: breakpoint.column - 1}
			});
			breakpointMap[(await websocket.getCommandResponse()).breakpointId as string] = breakpoint;
		}
	}
}

const breakableSyntaxKinds = new Set<Ts.SyntaxKind>([
	Ts.SyntaxKind.DoStatement,
	Ts.SyntaxKind.ForStatement,
	Ts.SyntaxKind.ForInStatement,
	Ts.SyntaxKind.ForOfStatement,
	Ts.SyntaxKind.SwitchStatement,
	Ts.SyntaxKind.WhileStatement
]);
const loopSyntaxKinds = new Set<Ts.SyntaxKind>([
	Ts.SyntaxKind.DoStatement,
	Ts.SyntaxKind.ForStatement,
	Ts.SyntaxKind.ForInStatement,
	Ts.SyntaxKind.ForOfStatement,
	Ts.SyntaxKind.WhileStatement
]);

function getCodeNodeFromBranch(tsNode: Ts.Node, isSecondary: boolean): Ts.Node {
	switch (tsNode.getKind()) {
		case Ts.SyntaxKind.IfStatement: {
			const ifStatement = tsNode as Ts.IfStatement;
			return isSecondary
				? ifStatement.getElseStatement() ?? getNextNodeToExecute(ifStatement)!
				: ifStatement.getThenStatement();
		}
		default:
			throw new Error(`Node kind ${tsNode.getKindName()} not supported yet.`);
	}
}

function getNextNodeToExecute(tsNode: Ts.Node): Ts.Node | null {
	let nodeToStep = tsNode;
	switch (tsNode.getKind()) {
		case Ts.SyntaxKind.Block:
			return (tsNode as Ts.Block).getStatements()[0];
		case Ts.SyntaxKind.CloseBraceToken:
			nodeToStep = tsNode.getParent()!;
			break;
		case Ts.SyntaxKind.ReturnStatement:
			return null;
		case Ts.SyntaxKind.BreakStatement:
			nodeToStep = tsNode.getParent()!;
			while (!breakableSyntaxKinds.has(nodeToStep.getKind())) nodeToStep = nodeToStep.getParent()!;
			break;
		case Ts.SyntaxKind.ContinueStatement:
			throw new Error("`continue` statement not supported yet.");
		case Ts.SyntaxKind.VariableStatement:
			return (tsNode as Ts.VariableStatement).getDeclarations()[0];
	}
	let candidate = nodeToStep.getNextSibling();
	if (candidate !== undefined && candidate.getKind() === Ts.SyntaxKind.ElseKeyword) {
		nodeToStep = candidate.getParent()!;
		candidate = nodeToStep.getNextSibling();
	}
	while (candidate === undefined) {
		const parent = nodeToStep.getParent();
		if (parent === undefined) throw new Error("Failed to find next node to execute.");
		switch (parent.getKind()) {
			case Ts.SyntaxKind.Block:
				return parent.getChildren()[2];
			case Ts.SyntaxKind.ForStatement:
			case Ts.SyntaxKind.ForInStatement:
			case Ts.SyntaxKind.ForOfStatement:
			case Ts.SyntaxKind.WhileStatement:
				return parent;
			case Ts.SyntaxKind.FunctionDeclaration:
				return null;
			default:
				nodeToStep = parent;
				if (nodeToStep.getKind() !== Ts.SyntaxKind.SyntaxList) candidate = nodeToStep.getNextSibling();
				break;
		}
	}
	return candidate;
}

function getBranchingCondition(cfgNode: CfgNode, symbolicExecutor: SymbolicExecutor): SymbolicExpression {
	const tsNode = cfgNode.tsNode!;
	switch (tsNode.getKind()) {
		case Ts.SyntaxKind.IfStatement:
			return symbolicExecutor.evaluateExpression((tsNode as Ts.IfStatement).getExpression());
		default:
			throw new Error(`Syntax kind ${tsNode.getKindName()} not supported yet.`);
	}
}

function getExpressionNode(tsNode: Ts.Node): Ts.Expression | null {
	switch (tsNode.getKind()) {
		case Ts.SyntaxKind.VariableDeclaration:
			return (tsNode as Ts.VariableDeclaration).getInitializer() ?? null;
		case Ts.SyntaxKind.ExpressionStatement:
			return (tsNode as Ts.ExpressionStatement).getExpression();
		case Ts.SyntaxKind.ReturnStatement:
			return (tsNode as Ts.ReturnStatement).getExpression() ?? null;
		default:
			return null;
	}
}

function collectParametersFromType(prefix: string, name: string, tsType: Ts.Type, parameterNames: Set<string>): void {
	if (tsType.isNumber()) {
		parameterNames.add(prefix + name);
	} else if (tsType.isObject()) {
		for (const property of tsType.getProperties()) collectParametersFromType(
			prefix + name + '.', property.getName(), property.getDeclarations()[0].getType(), parameterNames
		);
	} else {
		throw new Error("Non-number types are not yet supported.");
	}
}

function collectUsedParametersFromCondition(condition: SymbolicExpression, usedParameters: Set<string>): void {
	if (condition.kind === SymbolicExpressionKind.VARIABLE)
		usedParameters.add((condition as VariableSymbolicExpression).symbolicName);
	else
		for (const child of condition.getChildExpressions()) collectUsedParametersFromCondition(child, usedParameters);
}

function buildInputObject(flatObject: any): any {
	const inputObject: any = {};
	for (const [key, value] of Object.entries(flatObject)) {
		const nameChain = key.split('.');
		const terminalName = nameChain.pop()!;
		let containerObject = inputObject;
		for (const name of nameChain) {
			if (!(name in containerObject)) containerObject[name] = {};
			containerObject = containerObject[name];
		}
		containerObject[terminalName] = value;
	}
	return Object.fromEntries(Object.entries(inputObject).map(([key, value]) => [key, JSON.stringify(value)]));
}