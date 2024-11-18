import * as ChildProcess from "child_process";
import * as FileSystem from "fs";
import * as Http from "http";
import * as Path from "path";
import {SourceMapConsumer} from "source-map";
import TemplateFile from "template-file";
import * as Ts from "ts-morph";
import * as Url from "url";

import config from "#r/config";
import type {ResolvedFunctionPath} from "#r/analysis/FunctionResolver";
import {makeResolvedFunctionPathKey, resolveCalledExpression} from "#r/analysis/FunctionResolver";
import type {Cfg} from "#r/cfg/Cfg";
import {compactCfg, iterateCfg} from "#r/cfg/Cfg";
import type CfgNode from "#r/cfg/CfgNode";
import CfgNodeKind from "#r/cfg/CfgNodeKind";
import {generateCfgFromFunction} from "#r/cfg/CfgGenerator";
import BaseSymbolicType from "#r/symbolic/BaseSymbolicType";
import SymbolicExecutor from "#r/symbolic/SymbolicExecutor";
import SymbolicExpression from "#r/symbolic/expressions/SymbolicExpression";
import SymbolicExpressionKind from "#r/symbolic/expressions/SymbolicExpressionKind";
import UnarySymbolicExpression from "#r/symbolic/expressions/UnarySymbolicExpression";
import VariableSymbolicExpression from "#r/symbolic/expressions/VariableSymbolicExpression";
import {formatSmtNumber, formatSmtString, parseSmtString} from "#r/utilities/SmtUtils";

import type {ExecutionEntry} from "./BranchSelector.js";
import BranchSelector from "./BranchSelector.js";
import type {Breakpoint} from "./Breakpoints.js";
import {getBreakpointsFromCfg} from "./Breakpoints.js";
import CoverageKind from "./CoverageKind.js";
import DebuggerWebsocket from "./DebuggerWebsocket.js";

type SourceFileData = {compiledPath: string, sourceMap: SourceMapConsumer};
type FunctionData = {declaration: Ts.FunctionDeclaration, cfg: Cfg, breakpoints: Breakpoint[]};
export type ParameterType = {baseType: BaseSymbolicType, literalValues: any[], literalOnly: boolean};
export type MockedCall = {key: string, value: string};
type InternalMockedCall = MockedCall & {parameterNames: Set<string>};
export type TestCase = {parameters: {name: string, value: string}[], mockedValues: MockedCall[]};

export default class Executor {
	#projectPath: string;
	#project: Ts.Project;
	#projectConfiguration: Ts.ts.ParsedCommandLine;
	#functionToTest: ResolvedFunctionPath;
	#concolicDriverTemplate: string;
	#testDriverTemplate: string;
	#coverageKind: CoverageKind;
	#coverageTarget: number;
	#timeLimit: number;

	#sourceFileDataMap: Map<string, SourceFileData> = new Map<string, SourceFileData>();
	#functionDataMap: Map<string, FunctionData> = new Map<string, FunctionData>();
	#topLevelParameterNames: string[] = [];
	#parameterNames: Set<string> = new Set<string>();
	#parameterInfo: Map<string, ParameterType> = new Map<string, ParameterType>();
	#coveredCfgNodes: Set<CfgNode> = new Set<CfgNode>();
	#halfCoveredCfgNodes: Map<CfgNode, boolean> = new Map<CfgNode, boolean>();
	#currentExecutionPath: ExecutionEntry[] = [];
	#branchSelector: BranchSelector;
	#startTime: number = 0;
	#coveredAmount: number = 0;
	#totalCoverageAmount: number = 0;

	constructor(
		projectPath: string, project: Ts.Project, functionToTest: ResolvedFunctionPath,
		concolicDriverTemplate: string, testDriverTemplate: string,
		coverageKind: CoverageKind, coverageTarget: number, maxSearchDepth: number, maxContextLength: number,
		timeLimit: number
	) {
		this.#projectPath = projectPath;
		this.#project = project;
		this.#projectConfiguration = Ts.ts.getParsedCommandLineOfConfigFile(
			Path.join(this.#projectPath, "tsconfig.json"), undefined, Ts.ts.sys as any
		)!;
		this.#functionToTest = functionToTest;
		this.#concolicDriverTemplate = concolicDriverTemplate;
		this.#testDriverTemplate = testDriverTemplate;
		this.#coverageKind = coverageKind;
		this.#coverageTarget = coverageTarget / 100;
		this.#timeLimit = timeLimit * 1000;
		this.#branchSelector = new BranchSelector(maxSearchDepth, maxContextLength);
	}

	// Current limitation: must only be invoked once per instance.
	async execute(progressCallback: (testCount: number, coverage: number) => void): Promise<{
		testCases: TestCase[], testDriver: string, coverage: number, time: number
	}> {
		const cfg = this.#getFunctionData(this.#functionToTest).cfg;
		if (this.#coverageKind === CoverageKind.STATEMENT) {
			for (const node of iterateCfg(cfg)) this.#totalCoverageAmount
				+= node.primaryStatementCount
				+ (isCfgNodeBranchable(node) ? node.secondaryStatementCount : 0);
			this.#increaseCoveredAmount(cfg.beginNode, false);
		} else {
			for (const node of iterateCfg(cfg)) if (isCfgNodeBranchable(node)) this.#totalCoverageAmount += 2;
		}
		if (this.#totalCoverageAmount === 0) {
			this.#coveredAmount = 1;
			this.#totalCoverageAmount = 1;
		}
		{
			let parameterIndex = 0;
			for (
				const parameterDeclaration
				of this.#project.getSourceFileOrThrow(this.#functionToTest.source)
				.getFunctionOrThrow(this.#functionToTest.name).getParameters()
			) {
				const nameNode = parameterDeclaration.getNameNode();
				const topLevelParameterName
					= Ts.Node.isIdentifier(nameNode) ? nameNode.getText() : `@${parameterIndex}`;
				this.#topLevelParameterNames.push(topLevelParameterName);
				collectParametersFromType(
					topLevelParameterName, parameterDeclaration.getType(), this.#parameterNames, this.#parameterInfo
				);
				++parameterIndex;
			}
		}
		this.#startTime = new Date().getTime();
		const testCases: TestCase[] = [];
		let input: any | null = generateRandomInput(this.#parameterNames, this.#parameterInfo);
		let newMockedCalls: InternalMockedCall[] = [];
		while (input !== null) {
			progressCallback(testCases.length, this.#coveredAmount / this.#totalCoverageAmount);
			console.log("Inputs: " + Object.entries(input).map(entry => `${entry[0]} = ${entry[1]}`).join("; "));
			this.#generateDriverScript(input);
			const oldCoveredAmount = this.#coveredAmount;
			const {mockedCalls, newValues} = await this.#executeFunctionAndGetNextInput(newMockedCalls);
			if (this.#coveredAmount !== oldCoveredAmount) testCases.push({
				parameters: this.#topLevelParameterNames.map(name => ({name, value: input[name]})),
				mockedValues: mockedCalls.map(call => ({key: call.key, value: call.value}))
			});
			if (newValues === null) input = null;
			else ({input, mockedCalls: newMockedCalls} = newValues);
		}
		console.log("Done.");
		const globalDriverVariables = {
			sourceFilePath: this.#functionToTest.source.replace(/\.ts$/, ""),
			functionName: this.#functionToTest.name
		};
		return {
			testCases,
			testDriver: TemplateFile.render(this.#testDriverTemplate, {
				...globalDriverVariables,
				testCases: testCases.map((testCase, index) => {
					const mockedValues: any = {};
					for (const call of testCase.mockedValues) {
						if (!(call.key in mockedValues)) mockedValues[call.key] = [];
						mockedValues[call.key].push(JSON.parse(call.value));
					}
					return {
						...globalDriverVariables,
						index: index + 1,
						params: testCase.parameters.map(arg => arg.value).join(", "),
						mockedValues: JSON.stringify(mockedValues)
					};
				})
			}),
			coverage: this.#coveredAmount / this.#totalCoverageAmount * 100,
			time: (new Date().getTime() - this.#startTime) / 1000
		};
	}

	async #executeFunctionAndGetNextInput(mockedCallsIn: InternalMockedCall[]): Promise<{
		mockedCalls: InternalMockedCall[],
		newValues: {input: any, mockedCalls: InternalMockedCall[]} | null
	}> {
		console.log("Starting debugger...");
		const process = ChildProcess.spawn("node", [
			`--inspect-brk=${config.debuggerPort}`, "--enable-source-maps",
			this.#getCompiledFilePath(this.#project.getSourceFileOrThrow("__concolic.ts").getFilePath())
		], {cwd: this.#projectPath, stdio: "pipe"});
		process.stdout!.on("data", data => {});
		process.stderr!.on("data", data => {});
		const debuggerUrl = await new Promise<string>((resolve, reject) => {
			let failureCount = 0;
			const routine = () => {
				const request = Http.get(`http://127.0.0.1:${config.debuggerPort}/json`);
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
		websocket.sendCommand("Runtime.enable");
		await websocket.getCommandResponse();
		websocket.sendCommand("Debugger.enable");
		await websocket.getCommandResponse();
		websocket.sendCommand("Runtime.runIfWaitingForDebugger");
		await websocket.waitForEvent("Debugger.paused");
		websocket.sendCommand("Runtime.evaluate", {expression: "globalThis.__concolic$mockedValues = []"});
		await websocket.getCommandResponse();
		const breakpointMap: {[id: string]: Breakpoint} = {};
		const functionsWithSetBreakpoints = new Set<string>();
		await this.#setBreakpoints(this.#functionToTest, functionsWithSetBreakpoints, websocket, breakpointMap);
		console.log("Set initial breakpoints, now running.");

		const functionToTest = this.#project.getSourceFileOrThrow(this.#functionToTest.source)
			.getFunctionOrThrow(this.#functionToTest.name);
		const symbolicExecutor = new SymbolicExecutor(this.#parameterInfo);
		symbolicExecutor.addParametersFromFunctionDeclaration(functionToTest);
		let cfg = this.#getFunctionData(this.#functionToTest).cfg;
		let currentCfgNode: CfgNode = cfg.beginNode.primaryNext!;
		let currentCodeNode = functionToTest.getBody()!;
		let pendingCallCfgNodes: CfgNode[] = [];
		const parentCalls: {
			cfg: Cfg, currentCfgNode: CfgNode, currentCodeNode: Ts.Node, pendingCallCfgNodes: CfgNode[]
		}[] = [];
		const parentCallPathStack: string[] = [];
		let parentCallPathString = "";
		const newExecutionPath: ExecutionEntry[] = [];
		const mockedCalls = [...mockedCallsIn];
		let currentMockedCallIndex = 0;

		mainExecutionLoop: while (true) {
			if (currentCfgNode === cfg.endNode && parentCalls.length === 0) break;
			while (currentCfgNode !== cfg.endNode && !currentCfgNode.isBranching) {
				if (parentCalls.length === 0 && !this.#coveredCfgNodes.has(currentCfgNode)) {
					this.#increaseCoveredAmount(currentCfgNode, false);
					this.#coveredCfgNodes.add(currentCfgNode);
				}
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
						const calledExpression = callExpression.getExpression();
						if (calledExpression.getText() === "__concolic$mock") {
							const key = (callExpression.getArguments()[0] as Ts.StringLiteral).getLiteralValue();
							if (currentMockedCallIndex === mockedCalls.length) {
								const mockParameters = new Set<string>();
								const primaryName = `__concolic$mock${currentMockedCallIndex}`;
								collectParametersFromType(
									primaryName, callExpression.getTypeArguments()[0].getType(),
									mockParameters, this.#parameterInfo
								);
								mockedCalls.push({
									key,
									parameterNames: mockParameters,
									value: generateRandomInput(mockParameters, this.#parameterInfo)[primaryName]
								});
							} else if (mockedCalls[currentMockedCallIndex].key !== key) {
								throw new Error("Mocked call has unmatching key.");
							}
							websocket.sendCommand("Runtime.evaluate", {
								expression: `globalThis.__concolic$mockedValues.push(${
									mockedCalls[currentMockedCallIndex].value
								})`
							});
							await websocket.getCommandResponse();
							++currentMockedCallIndex;
						} else {
							const calledFunctionInfo = resolveCalledExpression(this.#projectPath, calledExpression);
							if (calledFunctionInfo === null) throw new Error("Failed to resolve function call.");
							const calledFunction = calledFunctionInfo.functionInProject;
							if (calledFunction === null) throw new Error("Called function doesn't belong to project.");
							symbolicExecutor.prepareFunctionCall(
								calledFunction, callCfgNode.tsNode! as Ts.CallExpression
							);
							pendingCallCfgNodes.shift();
							parentCalls.push({cfg, currentCfgNode, currentCodeNode, pendingCallCfgNodes});
							parentCallPathStack.push(
								callExpression.getSourceFile().getFilePath() + '@' + callExpression.getStart()
							);
							parentCallPathString = JSON.stringify(parentCallPathStack);
							await this.#setBreakpoints(
								calledFunctionInfo.path, functionsWithSetBreakpoints, websocket, breakpointMap
							);
							cfg = this.#getFunctionData(calledFunctionInfo.path).cfg;
							currentCfgNode = cfg.beginNode.primaryNext!;
							currentCodeNode = calledFunction.getBody()!;
							pendingCallCfgNodes = [];
							continue mainExecutionLoop;
						}
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
					parentCallPathString = JSON.stringify(parentCallPathStack);
					continue mainExecutionLoop;
				}
				currentCodeNode = next;
			}
			let shouldResume = true;
			while (true) {
				if (shouldResume) {
					websocket.sendCommand("Debugger.resume");
					shouldResume = false;
				}
				const event = await websocket.waitForAnyEvent();
				if (event.method === "Debugger.paused") {
					shouldResume = true;
					const hitBreakpoint = breakpointMap[event.params.hitBreakpoints[0]];
					if (hitBreakpoint.cfgNode === currentCfgNode) {
						if (newExecutionPath.length < this.#currentExecutionPath.length) {
							const currentEntry = this.#currentExecutionPath[newExecutionPath.length];
							if (
								currentEntry.parentCalls !== parentCallPathString
								|| currentEntry.cfgNode !== currentCfgNode
								|| currentEntry.isSecondaryBranch !== hitBreakpoint.isSecondaryBranch
							) throw new Error("Actual code execution doesn't match what's predicted.");
						}
						newExecutionPath.push({
							parentCalls: parentCallPathString,
							cfgNode: currentCfgNode,
							isSecondaryBranch: hitBreakpoint.isSecondaryBranch,
							branchingCondition: getBranchingCondition(currentCfgNode, symbolicExecutor)
						});
						if (parentCalls.length === 0 && !this.#coveredCfgNodes.has(currentCfgNode)) {
							if (isCfgNodeBranchable(currentCfgNode)) {
								const coveredBranch = this.#halfCoveredCfgNodes.get(currentCfgNode);
								if (coveredBranch === undefined) {
									this.#halfCoveredCfgNodes.set(currentCfgNode, hitBreakpoint.isSecondaryBranch);
									this.#increaseCoveredAmount(currentCfgNode, hitBreakpoint.isSecondaryBranch);
								} else if (coveredBranch !== hitBreakpoint.isSecondaryBranch) {
									this.#coveredCfgNodes.add(currentCfgNode);
									this.#halfCoveredCfgNodes.delete(currentCfgNode);
									this.#increaseCoveredAmount(currentCfgNode, hitBreakpoint.isSecondaryBranch);
								}
							}
						}
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
		console.log("Branching series: " + newExecutionPath.map(e => e.isSecondaryBranch ? '0' : '1').join(" "));
		if (
			this.#coveredAmount / this.#totalCoverageAmount >= this.#coverageTarget
			|| new Date().getTime() - this.#startTime > this.#timeLimit
		) return {mockedCalls, newValues: null};
		this.#branchSelector.addExecutionPath(newExecutionPath);
		while (true) {
			const suggestedExecutionPath = this.#branchSelector.getNextExecutionPath();
			if (suggestedExecutionPath === null) return {mockedCalls, newValues: null};
			console.log("Generating constraints...");
			const conditions = [];
			for (const entry of suggestedExecutionPath) conditions.push(
				entry.isSecondaryBranch
				? new UnarySymbolicExpression("!", entry.branchingCondition)
				: entry.branchingCondition
			);
			const usedParameters = new Set<string>();
			for (const condition of conditions) collectUsedParametersFromCondition(condition, usedParameters);
			let smtString = "(set-option :pp.decimal true)\n";
			let constraintsHaveStrings = false;
			for (const parameter of usedParameters) {
				smtString += generateSmtForParameter(parameter, this.#parameterInfo);
				constraintsHaveStrings ||= this.#parameterInfo.get(parameter)!.baseType === BaseSymbolicType.STRING;
			}
			for (const condition of conditions) smtString += `(assert ${condition.generateSmt().expression})\n`;
			smtString += (
				(constraintsHaveStrings ? "(check-sat)" : "(check-sat-using qfnra-nlsat)")
				+ "\n(get-model)\n"
			);
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
				continue;
			} else if (smtString.substring(0, 3) !== "sat") {
				throw new Error("Failed to solve constraints.");
			}
			this.#currentExecutionPath = suggestedExecutionPath;
			const flatInputObject = Object.fromEntries([...smtString.matchAll(
				/\(define-fun ([\w_.@$]+) \(\) (?:Real[^\d\(]+\(?((?:- )?[\d\.]+)\??|String[^"]+"([^"]*)"|Bool[^\w]+(\w+))\)/g
			)].map(entry => {
				const name = entry[1];
				let value: any;
				switch (this.#parameterInfo.get(name)!.baseType) {
					case BaseSymbolicType.NUMBER:
						value = Number(entry[2].replaceAll(" ", ""));
						break;
					case BaseSymbolicType.STRING:
						value = parseSmtString(entry[3]);
						break;
					case BaseSymbolicType.BOOLEAN:
						value = entry[4] === "true";
						break;
					default:
						throw new Error("Unhandled base symbolic type.");
				}
				return [name, value];
			}));
			for (const parameterName of this.#parameterNames) if (!usedParameters.has(parameterName))
				flatInputObject[parameterName] = Math.floor(Math.random() * 201) - 100;
			let usedMockedCalls = 0;
			for (let i = mockedCalls.length - 1; i !== -1; --i) {
				const mockedCall = mockedCalls[i];
				if (usedMockedCalls === 0) {
					for (const parameterName of mockedCall.parameterNames) if (usedParameters.has(parameterName)) {
						usedMockedCalls = i + 1;
						break;
					}
					if (usedMockedCalls === 0) continue;
				}
				for (const parameterName of mockedCall.parameterNames) {
					if (!usedParameters.has(parameterName))
						flatInputObject[parameterName] = Math.floor(Math.random() * 201) - 100;
				}
			}
			const newInput = buildInputObject(flatInputObject);
			const newMockedCalls: InternalMockedCall[] = [];
			for (let i = 0; i !== usedMockedCalls; ++i) {
				const name = `__concolic$mock${i}`;
				const originalMockedCall = mockedCalls[i];
				newMockedCalls.push({
					key: originalMockedCall.key,
					parameterNames: originalMockedCall.parameterNames,
					value: newInput[name]
				});
				delete newInput[name];
			}
			return {mockedCalls, newValues: {input: newInput, mockedCalls: newMockedCalls}};
		}
	}

	#increaseCoveredAmount(cfgNode: CfgNode, isSecondaryBranch: boolean): void {
		this.#coveredAmount += this.#coverageKind === CoverageKind.STATEMENT
			? isSecondaryBranch ? cfgNode.secondaryStatementCount : cfgNode.primaryStatementCount
			: isCfgNodeBranchable(cfgNode) ? 1 : 0;
	}

	#generateDriverScript(input: any): void {
		FileSystem.writeFileSync(
			Path.join(this.#projectPath, "__concolic.ts"),
			TemplateFile.render(this.#concolicDriverTemplate, {
				sourceFilePath: this.#functionToTest.source.replace(/\.ts$/, ".js"),
				functionName: this.#functionToTest.name,
				params: this.#topLevelParameterNames.map(name => input[name]).join(", ")}
			),
			"utf8"
		);
		ChildProcess.execSync("tsc", {cwd: this.#projectPath, stdio: "ignore"});
	}

	#getCompiledFilePath(sourceFilePath: string): string {
		return Ts.ts.getOutputFileNames(
			this.#projectConfiguration, sourceFilePath.replaceAll('\\', '/'), false
		)[0];
	}

	#getFunctionData(functionPath: ResolvedFunctionPath): FunctionData {
		const key = makeResolvedFunctionPathKey(functionPath);
		let functionData = this.#functionDataMap.get(key);
		if (functionData === undefined) {
			const declaration
				= this.#project.getSourceFileOrThrow(functionPath.source).getFunctionOrThrow(functionPath.name);
			const cfg = generateCfgFromFunction(declaration);
			compactCfg(cfg);
			functionData = {declaration, cfg, breakpoints: getBreakpointsFromCfg(cfg)};
			this.#functionDataMap.set(key, functionData);
			this.#branchSelector.addCfg(cfg);
		}
		return functionData;
	}

	async #setBreakpoints(
		functionPath: ResolvedFunctionPath, setFunctions: Set<string>,
		websocket: DebuggerWebsocket, breakpointMap: {[id: string]: Breakpoint}
	): Promise<void> {
		const key = makeResolvedFunctionPathKey(functionPath);
		if (setFunctions.has(key)) return;
		setFunctions.add(key);
		const sourceFilePath = this.#project.getSourceFileOrThrow(functionPath.source).getFilePath();
		const compiledPath = this.#getCompiledFilePath(sourceFilePath);
		const compiledUrl = Url.pathToFileURL(compiledPath).toString();
		const sourceMapSourcePath = Path.relative(Path.dirname(compiledPath), sourceFilePath).replaceAll('\\', '/');
		let sourceFileData = this.#sourceFileDataMap.get(functionPath.source);
		if (sourceFileData === undefined) {
			const sourceMap = await new SourceMapConsumer(FileSystem.readFileSync(compiledPath + ".map", "utf8"));
			sourceFileData = {compiledPath, sourceMap};
			this.#sourceFileDataMap.set(functionPath.source, sourceFileData);
		}
		for (const breakpoint of this.#getFunctionData(functionPath).breakpoints) {
			const compiledLocation = sourceFileData.sourceMap.generatedPositionFor({
				source: sourceMapSourcePath, line: breakpoint.line, column: breakpoint.column - 1
			});
			websocket.sendCommand("Debugger.setBreakpointByUrl", {
				url: compiledUrl, lineNumber: compiledLocation.line! - 1, columnNumber: compiledLocation.column
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
		case Ts.SyntaxKind.WhileStatement: {
			const whileStatement = tsNode as Ts.WhileStatement;
			return isSecondary ? getNextNodeToExecute(whileStatement)! : whileStatement.getStatement();
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

function isCfgNodeBranchable(cfgNode: CfgNode): boolean {
	return cfgNode.isBranching && !(
		cfgNode.tsNode!.getKind() === Ts.SyntaxKind.WhileStatement
		&& (cfgNode.tsNode! as Ts.WhileStatement).getExpression().getKind() === Ts.SyntaxKind.TrueKeyword
	);
}

function getBranchingCondition(cfgNode: CfgNode, symbolicExecutor: SymbolicExecutor): SymbolicExpression {
	const tsNode = cfgNode.tsNode!;
	switch (tsNode.getKind()) {
		case Ts.SyntaxKind.IfStatement:
		case Ts.SyntaxKind.WhileStatement:
			return symbolicExecutor.evaluateExpression(
				(tsNode as Ts.IfStatement | Ts.WhileStatement).getExpression(), false, false
			);
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

function analyzeParameterType(tsType: Ts.Type): ParameterType {
	if (tsType.isNumber()) return {baseType: BaseSymbolicType.NUMBER, literalValues: [], literalOnly: false};
	if (tsType.isNumberLiteral())
		return {baseType: BaseSymbolicType.NUMBER, literalValues: [tsType.getLiteralValue()], literalOnly: true};
	if (tsType.isString()) return {baseType: BaseSymbolicType.STRING, literalValues: [], literalOnly: false};
	if (tsType.isStringLiteral())
		return {baseType: BaseSymbolicType.STRING, literalValues: [tsType.getLiteralValue()], literalOnly: true};
	if (tsType.isBoolean()) return {baseType: BaseSymbolicType.BOOLEAN, literalValues: [], literalOnly: false};
	if (tsType.isBooleanLiteral())
		return {baseType: BaseSymbolicType.BOOLEAN, literalValues: [tsType.getLiteralValue()], literalOnly: true};
	if (tsType.isUnion()) {
		const baseTypes = tsType.getUnionTypes().map(baseType => analyzeParameterType(baseType));
		if (baseTypes.some(baseType => baseType.baseType !== baseTypes[0].baseType))
			throw new Error("Union of different base types is not supported yet.");
		const literalValues = new Set<any>();
		let literalOnly = true;
		for (const baseType of baseTypes) {
			for (const value of baseType.literalValues) literalValues.add(value);
			literalOnly ||= baseType.literalOnly;
		}
		return {baseType: baseTypes[0].baseType, literalValues: [...literalValues], literalOnly};
	}
	if (tsType.isIntersection()) {
		const baseTypes = tsType.getIntersectionTypes().map(baseType => analyzeParameterType(baseType));
		if (baseTypes.some(baseType => baseType.baseType !== baseTypes[0].baseType))
			throw new Error("Intersection of different base types results in empty type.");
		const literalValues = new Set<any>();
		let literalOnly = false;
		for (const baseType of baseTypes) {
			if (literalOnly) {
				if (baseType.literalOnly) {
					const newLiteralValues: any[] = [];
					for (const value of baseType.literalValues)
						if (!literalValues.has(value)) newLiteralValues.push(value);
					literalValues.clear();
					for (const value of newLiteralValues) literalValues.add(value);
				}
			} else {
				if (baseType.literalOnly) {
					literalOnly = true;
					literalValues.clear();
				}
				for (const value of baseType.literalValues) literalValues.add(value);
			}
		}
		return {baseType: baseTypes[0].baseType, literalValues: [...literalValues], literalOnly};
	}
	throw new Error(`Unsupported parameter type \`${tsType.getText()}\`.`);
}

function collectParametersFromType(
	name: string, tsType: Ts.Type,
	parameterNames: Set<string>, parameterInfo: Map<string, ParameterType>
): void {
	if (tsType.isObject() || tsType.isInterface()) {
		for (const property of tsType.getProperties()) collectParametersFromType(
			name + '.' + property.getName(), property.getDeclarations()[0].getType(), parameterNames, parameterInfo
		);
	} else {
		parameterNames.add(name);
		parameterInfo.set(name, analyzeParameterType(tsType));
	}
}

function collectUsedParametersFromCondition(condition: SymbolicExpression, usedParameters: Set<string>): void {
	if (condition.kind === SymbolicExpressionKind.VARIABLE)
		usedParameters.add((condition as VariableSymbolicExpression).symbolicName);
	else
		for (const child of condition.getChildExpressions()) collectUsedParametersFromCondition(child, usedParameters);
}

function generateRandomInput(parameterNames: Set<string>, parameterInfo: Map<string, ParameterType>): any {
	return buildInputObject(Object.fromEntries([...parameterNames].map(
		parameterName => [parameterName, generateRandomValue(parameterInfo.get(parameterName)!)]
	)));
}

function generateRandomValue(type: ParameterType): any {
	if (type.literalValues.length !== 0)
		return type.literalValues[Math.floor(Math.random() * type.literalValues.length)];
	switch (type.baseType) {
		case BaseSymbolicType.NUMBER:
			return Math.floor(Math.random() * 201) - 100; // Integer from -100 to 100.
		case BaseSymbolicType.STRING:
			return String.fromCharCode(97 + Math.floor(Math.random() * 26)); // One lowercase character.
		case BaseSymbolicType.BOOLEAN:
			return Math.random() < 0.5;
		default:
			throw new Error("Unhandled base symbolic type.");
	}
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

function generateSmtForParameter(name: string, parameterInfo: Map<string, ParameterType>): string {
	const type = parameterInfo.get(name)!;
	switch (type.baseType) {
		case BaseSymbolicType.NUMBER: {
			let smt = `(declare-const ${name} Real)\n`;
			if (type.literalOnly) {
				smt += "(assert (or";
				for (const value of type.literalValues)
					smt += ` (= ${name} ${formatSmtNumber(value as number)})`;
				smt += "))\n";
			}
			return smt;
		}
		case BaseSymbolicType.STRING: {
			let smt = `(declare-const ${name} String)\n`;
			if (type.literalOnly) {
				smt += "(assert (or";
				for (const value of type.literalValues)
					smt += ` (= ${name} ${formatSmtString(value as string)})`;
				smt += "))\n";
			}
			return smt;
		}
		case BaseSymbolicType.BOOLEAN: {
			let smt = `(declare-const ${name} Bool)\n`;
			if (type.literalOnly) {
				smt += "(assert (or";
				for (const value of type.literalValues)
					smt += ` (= ${name} ${value as boolean})`;
				smt += "))\n";
			}
			return smt;
		}
		default:
			throw new Error("Unhandled base symbolic type.");
	}
}