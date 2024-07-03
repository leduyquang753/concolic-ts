import * as ChildProcess from "child_process";
import * as FileSystem from "fs";
import * as Http from "http";
import * as Path from "path";
import {SourceMapConsumer} from "source-map";
import * as Ts from "ts-morph";
import * as Url from "url";

import type {Breakpoint} from "#r/execution/Breakpoints";
import {getBreakpointsFromFunction} from "#r/execution/Breakpoints";
import DebuggerWebsocket from "./DebuggerWebsocket";

export default class Executor {
	#projectPath: string;
	#functionDeclaration: Ts.FunctionDeclaration;

	constructor(projectPath: string, functionDeclaration: Ts.FunctionDeclaration) {
		this.#projectPath = projectPath;
		this.#functionDeclaration = functionDeclaration;
	}

	async execute(): Promise<void> {
		const sourceFilePath = this.#functionDeclaration.getSourceFile().getFilePath();
		const compiledFilePath = Ts.ts.getOutputFileNames(
			Ts.ts.getParsedCommandLineOfConfigFile(this.#projectPath + "\\tsconfig.json", undefined, Ts.ts.sys as any)!,
			sourceFilePath.replaceAll('\\', '/'),
			false
		)[0];

		console.log("Starting debugger...");
		const process = ChildProcess.spawn("node", [
			"--inspect-brk=9339", "--enable-source-maps", compiledFilePath
		], {cwd: this.#projectPath, stdio: "pipe"});
		process.stdout!.on("data", data => {});
		process.stderr!.on("data", data => {});
		// Wait until the Node instance has finished startup, which posts a message to stderr.
		await new Promise(resolve => { process.stderr!.once("data", resolve); });
		const debuggerUrl = await new Promise<string>((resolve, reject) => {
			const request = Http.get("http://127.0.0.1:9339/json");
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
		});
		console.log(`Debugger started at URL: ${debuggerUrl}`);

		const websocket = new DebuggerWebsocket(debuggerUrl);
		await websocket.waitForConnection();
		console.log("Connected to the debugger.");
		let scriptId = "";
		let sourceMapPath = "";
		const parsingPromise = new Promise<void>(resolve => {
			const scriptUrl = Url.pathToFileURL(compiledFilePath).toString();
			const eventListener = (rawData: any): void => {
				const data = rawData as {scriptId: string, url: string, sourceMapURL: string};
				if (data.url === scriptUrl) {
					scriptId = data.scriptId;
					sourceMapPath = data.sourceMapURL;
					websocket.removeListener("Debugger.scriptParsed", eventListener);
					resolve();
				}
			};
			websocket.on("Debugger.scriptParsed", eventListener);
		});
		websocket.sendCommand("Runtime.enable");
		await websocket.getCommandResponse();
		websocket.sendCommand("Debugger.enable");
		await websocket.getCommandResponse();
		websocket.sendCommand("Runtime.runIfWaitingForDebugger");
		await Promise.all([parsingPromise, websocket.getCommandResponse()]);
		const sourceMapConsumer = await new SourceMapConsumer(
			FileSystem.readFileSync(Path.join(Path.dirname(compiledFilePath), sourceMapPath), "utf8")
		);
		const breakpointMap: {[id: string]: Breakpoint} = {};
		for (const breakpoint of getBreakpointsFromFunction(this.#functionDeclaration)) {
			const compiledLocation = sourceMapConsumer.generatedPositionFor({
				source: Path.basename(sourceFilePath), line: breakpoint.line, column: breakpoint.column - 1
			});
			websocket.sendCommand("Debugger.setBreakpoint", {
				location: {scriptId, lineNumber: compiledLocation.line! - 1, columnNumber: compiledLocation.column}
			});
			breakpointMap[(await websocket.getCommandResponse()).breakpointId as string] = breakpoint;
		}
		console.log("Set breakpoints, now running.");
		websocket.sendCommand("Debugger.resume");
		while (true) {
			const event = await websocket.waitForAnyEvent();
			if (event.method === "Debugger.paused") {
				const hitBreakpoint = breakpointMap[event.params.hitBreakpoints[0]];
				console.log(`Breakpoint hit at line ${hitBreakpoint.line}, column ${hitBreakpoint.column}.`);
				websocket.sendCommand("Debugger.resume");
			} else if (event.method === "Runtime.executionContextDestroyed") {
				console.log("Script finished.");
				break;
			}
		}
		websocket.close();
	}
}