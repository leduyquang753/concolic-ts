import * as ChildProcess from "child_process";
import * as FileSystem from "fs";
import * as Http from "http";
import * as Path from "path";
import {SourceMapConsumer} from "source-map";
import * as TemplateFile from "template-file";
import * as Ts from "ts-morph";
import * as Url from "url";

import config from "#r/config";
import type {Cfg} from "#r/cfg/Cfg";
import {compactCfg} from "#r/cfg/Cfg";
import type CfgNode from "#r/cfg/CfgNode";
import {generateCfgFromFunction} from "#r/cfg/CfgGenerator";
import SymbolicExecutor from "#r/symbolic/SymbolicExecutor";
import SymbolicExpression from "#r/symbolic/expressions/SymbolicExpression";
import UnarySymbolicExpression from "#r/symbolic/expressions/UnarySymbolicExpression";

import type {Breakpoint} from "./Breakpoints";
import {getBreakpointsFromCfg} from "./Breakpoints";
import DebuggerWebsocket from "./DebuggerWebsocket";

type BranchingRecord = {cfgNode: CfgNode, isSecondary: boolean};

export default class Executor {
	#projectPath: string;
	#functionDeclaration: Ts.FunctionDeclaration;
	#projectConfiguration: Ts.ts.ParsedCommandLine;
	#cfg: Cfg;
	#breakpoints: Breakpoint[];
	#coveredCfgNodeIds: Set<number> = new Set<number>();
	#currentBranchingSeries: BranchingRecord[] = [];

	constructor(projectPath: string, functionDeclaration: Ts.FunctionDeclaration) {
		this.#projectPath = projectPath;
		this.#functionDeclaration = functionDeclaration;
		this.#projectConfiguration = Ts.ts.getParsedCommandLineOfConfigFile(
			this.#projectPath + "\\tsconfig.json", undefined, Ts.ts.sys as any
		)!;
		this.#cfg = generateCfgFromFunction(this.#functionDeclaration);
		compactCfg(this.#cfg);
		this.#breakpoints = getBreakpointsFromCfg(this.#cfg);
	}

	async execute(): Promise<void> {
		let input: any | null = this.#generateInitialInput();
		while (input !== null) {
			console.log("Inputs: " + Object.entries(input).map(entry => `${entry[0]} = ${entry[1]}`).join("; "));
			this.#generateDriverScript(input);
			input = await this.#executeFunctionAndGetNextInput();
		}
		console.log("Done.");
	}

	async #executeFunctionAndGetNextInput(): Promise<any | null> {
		const sourceFilePath = this.#functionDeclaration.getSourceFile().getFilePath();
		const compiledFilePath = this.#getCompiledFilePath(sourceFilePath);

		console.log("Starting debugger...");
		const process = ChildProcess.spawn("node", [
			"--inspect-brk=9339", "--enable-source-maps",
			this.#getCompiledFilePath(
				this.#functionDeclaration.getProject().getSourceFileOrThrow("driver.ts").getFilePath()
			)
		], {cwd: this.#projectPath, stdio: "pipe"});
		process.stdout!.on("data", data => {});
		process.stderr!.on("data", data => {});
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
			const scriptUrl = Url.pathToFileURL(compiledFilePath).toString();
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
		const sourceMapConsumer = await new SourceMapConsumer(
			FileSystem.readFileSync(Path.join(Path.dirname(compiledFilePath), sourceMapPath), "utf8")
		);
		const breakpointMap: {[id: string]: Breakpoint} = {};
		for (const breakpoint of this.#breakpoints) {
			const compiledLocation = sourceMapConsumer.generatedPositionFor({
				source: Path.basename(sourceFilePath), line: breakpoint.line, column: breakpoint.column - 1
			});
			websocket.sendCommand("Debugger.setBreakpoint", {
				location: {scriptId, lineNumber: compiledLocation.line! - 1, columnNumber: compiledLocation.column}
			});
			breakpointMap[(await websocket.getCommandResponse()).breakpointId as string] = breakpoint;
		}
		console.log("Set breakpoints, now running.");

		const symbolicExecutor = new SymbolicExecutor();
		symbolicExecutor.addParametersFromFunctionDeclaration(this.#functionDeclaration);
		let currentCfgNode = this.#cfg.beginNode.primaryNext!;
		let currentCodeNode = this.#functionDeclaration.getBody()!;
		const newBranchingSeries: BranchingRecord[] = [];
		const branchingConditions: SymbolicExpression[] = [];
		while (true) {
			while (currentCfgNode !== this.#cfg.endNode && !currentCfgNode.isBranching) {
				const next = currentCfgNode.primaryNext;
				if (next === null) throw new Error("CFG ended prematurely.");
				currentCfgNode = next;
			}
			if (currentCfgNode === this.#cfg.endNode) break;
			executeCodeNode(currentCodeNode, symbolicExecutor);
			while (currentCodeNode !== currentCfgNode.tsNode!) {
				const next = getNextNodeToExecute(currentCodeNode);
				if (next === null) throw new Error("Code ended prematurely.");
				currentCodeNode = next;
				executeCodeNode(currentCodeNode, symbolicExecutor);
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
								currentRecord.cfgNode !== currentCfgNode
								|| currentRecord.isSecondary !== hitBreakpoint.isSecondaryBranch
							) throw new Error("Actual code execution doesn't match what's predicted.");
						}
						newBranchingSeries.push({
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
		if (this.#currentBranchingSeries.length !== 0) this.#coveredCfgNodeIds.add(
			this.#currentBranchingSeries[this.#currentBranchingSeries.length - 1].cfgNode.id
		);
		while (true) {
			while (
				newBranchingSeries.length !== 0
				&& this.#coveredCfgNodeIds.has(newBranchingSeries[newBranchingSeries.length - 1].cfgNode.id)
			) {
				newBranchingSeries.pop();
				branchingConditions.pop();
			}
			if (newBranchingSeries.length === 0) return null;
			console.log("Generating constraints...");
			const lastBranchIndex = newBranchingSeries.length - 1;
			newBranchingSeries[lastBranchIndex].isSecondary = !newBranchingSeries[lastBranchIndex].isSecondary;
			let smtString = "(set-option :pp.decimal true)\n";
			for (const parameter of this.#functionDeclaration.getParameters())
				smtString += `(declare-const ${parameter.getName()} Real)\n`;
			for (let i = 0; i !== newBranchingSeries.length; ++i) {
				const condition = newBranchingSeries[i].isSecondary
					? new UnarySymbolicExpression("!", branchingConditions[i])
					: branchingConditions[i];
				smtString += `(assert ${condition.smtString})\n`;
			}
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
			return Object.fromEntries([...smtString.matchAll(
				/\(define-fun (\w+) \(\) Real[^\d\(]+\(?((?:- )?[\d\.]+)\??\)/g
			)].map(
				entry => [entry[1], Number(entry[2].replaceAll(" ", ""))]
			));
		}
	}

	#generateDriverScript(input: any): void {
		FileSystem.writeFileSync(Path.join(this.#projectPath, "driver.ts"), TemplateFile.render(
			FileSystem.readFileSync(Path.join(this.#projectPath, "driver.ts.template"), "utf8"), input
		), "utf8");
		ChildProcess.execSync("tsc", {cwd: this.#projectPath, stdio: "ignore"});
	}

	#generateInitialInput(): any {
		return Object.fromEntries(this.#functionDeclaration.getParameters().map(
			parameter => [parameter.getName(), Math.floor(Math.random() * 201) - 100]
		));
	}

	#getCompiledFilePath(sourceFilePath: string): string {
		return Ts.ts.getOutputFileNames(
			this.#projectConfiguration, sourceFilePath.replaceAll('\\', '/'), false
		)[0];
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

function executeCodeNode(tsNode: Ts.Node, symbolicExecutor: SymbolicExecutor): void {
	if (Ts.Node.isBlock(tsNode)) symbolicExecutor.startScope();
	else if (tsNode.getKind() === Ts.SyntaxKind.CloseBraceToken) symbolicExecutor.endScope();
	else if (Ts.Node.isStatement(tsNode)) symbolicExecutor.executeStatement(tsNode);
}

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
	}
	let candidate = nodeToStep.getNextSibling();
	while (candidate === undefined) {
		const parent = nodeToStep.getParent();
		if (parent === undefined || parent.getKind() === Ts.SyntaxKind.FunctionDeclaration)
			throw new Error("Failed to find next node to execute.");
		switch (parent.getKind()) {
			case Ts.SyntaxKind.Block:
				return parent.getChildren()[2];
			case Ts.SyntaxKind.ForStatement:
			case Ts.SyntaxKind.ForInStatement:
			case Ts.SyntaxKind.ForOfStatement:
			case Ts.SyntaxKind.WhileStatement:
				return parent;
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