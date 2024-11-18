import FastifyMultipart from "@fastify/multipart";
import FastifyStatic from "@fastify/static";
import FastifyWebsocket from "@fastify/websocket";
import * as ZipJs from "@zip.js/zip.js";
import {Buffer} from "buffer";
import * as ChildProcess from "child_process";
import Fastify from "fastify";
import * as FileSystem from "fs";
import * as Path from "path";
import {Shescape} from "shescape";
import * as Ts from "ts-morph";

import type {ResolvedFunctionPath} from "#r/analysis/FunctionResolver";
import TestabilityAnalysis from "#r/analysis/TestabilityAnalysis";
import CodeTransformer from "#r/execution/CodeTransformer";
import CoverageKind from "#r/execution/CoverageKind";
import Executor from "#r/execution/Executor";
import type {TestCase} from "#r/execution/Executor";
import StatusStore from "#r/utilities/StatusStore";
import config from "./config.js";

type FunctionEntry = {
	name: string,
	testable: boolean,
	calledFunctions: ResolvedFunctionPath[]
};
type SourceFileEntry = {
	kind: "file",
	name: string,
	functions: FunctionEntry[]
};
type FolderEntry = {
	kind: "folder",
	name: string,
	entries: (FolderEntry | SourceFileEntry)[]
};
type ProjectBasicInfo = {id: string, name: string};
type ProjectStatus = {status: "new"}
	| {status: "taskRunning", taskId: string, taskKind: string}
	| {status: "generated", succeeded: boolean};
type ProjectInfo = ProjectBasicInfo & ProjectStatus;

const projectIdSchema = {type: "object", properties: {id: {type: "string", pattern: "^[a-z0-9]{10}$"}}};

(async () => {
const statusStore = new StatusStore();
const shescape = new Shescape({shell: true});

const server = Fastify();

server.register(FastifyWebsocket, {options: {maxPayload: 1 << 10}});
server.register(FastifyMultipart, {limits: {files: 1, fileSize: 100 << 20}, attachFieldsToBody: "keyValues"});
server.register(FastifyStatic, {root: config.storagePath, serve: false});

server.get("/status", {websocket: true}, (socket, request) => {
	statusStore.onSocketConnection(socket);
});

function getProjectInfo(projectId: string): ProjectInfo {
	const projectPath = Path.join(config.storagePath, projectId);
	const currentTask = statusStore.currentTask;
	const resultPath = Path.join(projectPath, "generationResult.json");
	return {
		...(JSON.parse(FileSystem.readFileSync(Path.join(projectPath, "info.json"), "utf8")) as ProjectBasicInfo),
		...(
			currentTask === null || currentTask.projectId !== projectId
			? FileSystem.existsSync(resultPath)
				? {
					status: "generated",
					succeeded: (JSON.parse(
						FileSystem.readFileSync(resultPath, "utf8")
					) as {status: string}).status === "succeeded"
				}
				: {status: "new"}
			: {status: "taskRunning", taskId: currentTask.taskId, taskKind: currentTask.taskKind}
		)
	};
}

server.get("/projects", (request, reply) => {
	return {projects: FileSystem.readdirSync(config.storagePath).map(id => getProjectInfo(id))};
});

server.post("/projects", {schema: {consumes: ["multipart/form-data"], body: {
	type: "object",
	required: ["name", "contents"],
	properties: {
		name: {type: "string", minLength: 1, maxLength: 100},
		contents: {type: "object"}
	}
}}}, async (request, reply) => {
	if (statusStore.hasRunningTask) {
		reply.statusCode = 503;
		return {error: "A task is already running."};
	}
	const params = request.body as {name: string, contents: Buffer};
	let projectId: string = "";
	let projectPath: string = "";
	while (true) {
		projectId = generateId();
		projectPath = Path.join(config.storagePath, projectId);
		if (!FileSystem.existsSync(projectPath)) break;
	}
	FileSystem.mkdirSync(projectPath);
	FileSystem.writeFileSync(
		Path.join(projectPath, "info.json"),
		JSON.stringify({id: projectId, name: params.name}),
		"utf8"
	);
	const taskId = generateId();
	statusStore.putTask({projectId, taskId, taskKind: "upload"});

	(async () => { // Task body.

	const originalPath = Path.join(projectPath, "original");
	const concolicPath = Path.join(projectPath, "concolic");
	const testPath = Path.join(projectPath, "test");

	statusStore.updateTaskProgress("Extracting files...");
	FileSystem.mkdirSync(originalPath, {recursive: true});
	const zipReader = new ZipJs.ZipReader(new ZipJs.BlobReader(new Blob([params.contents])));
	for (const entry of await zipReader.getEntries()) {
		if (entry.filename.match(/^node_modules(?:\/|$)/) !== null) continue;
		const entryPath = Path.join(originalPath, entry.filename);
		if (entry.directory) FileSystem.mkdirSync(entryPath);
		else FileSystem.writeFileSync(entryPath, await entry.getData!(new ZipJs.Uint8ArrayWriter()));
	}

	statusStore.updateTaskProgress("Setting up project...");
	FileSystem.cpSync(originalPath, concolicPath, {recursive: true});
	FileSystem.cpSync(originalPath, testPath, {recursive: true});
	ChildProcess.spawnSync("npm", ["ci"], {cwd: originalPath, shell: true, stdio: "ignore"});
	ChildProcess.spawnSync(
		"npm", ["install", "@vitest/coverage-v8"], {cwd: originalPath, shell: true, stdio: "ignore"}
	);
	FileSystem.symlinkSync(Path.join(originalPath, "node_modules"), Path.join(concolicPath, "node_modules"));
	FileSystem.symlinkSync(Path.join(originalPath, "node_modules"), Path.join(testPath, "node_modules"));
	statusStore.finishTask();

	})(); // Task body.

	return {projectId, taskId};
});

server.delete("/projects/:id", {schema: {params: projectIdSchema}}, (request, reply) => {
	if (statusStore.hasRunningTask) {
		reply.statusCode = 503;
		return {error: "A task is already running."};
	}
	const projectId = (request.params as {id: string}).id;
	const projectPath = Path.join(config.storagePath, projectId);
	if (!FileSystem.existsSync(projectPath)) {
		reply.statusCode = 404;
		return {error: "Project not found."};
	}
	statusStore.putTask({projectId, taskId: generateId(), taskKind: "delete"});
	FileSystem.rmSync(projectPath, {recursive: true});
	statusStore.finishTask();
	reply.send();
});

function getFolderEntry(testabilityAnalysis: TestabilityAnalysis, directory: Ts.Directory): FolderEntry {
	return {kind: "folder", name: Path.basename(directory.getPath()), entries: [
		...directory.getDirectories()
			.filter(directory => Path.basename(directory.getPath()) !== "node_modules")
			.map(directory => getFolderEntry(testabilityAnalysis, directory)),
		...directory.getSourceFiles().map((sourceFile: Ts.SourceFile): SourceFileEntry => ({
			kind: "file",
			name: Path.basename(sourceFile.getFilePath()),
			functions: sourceFile.getFunctions().map(
				func => ({functionDeclaration: func, analysisResult: testabilityAnalysis.analyzeFunction(func)})
			).filter(
				entry => entry.analysisResult !== null
			).map(
				entry => ({
					name: entry.functionDeclaration.getNameOrThrow(),
					testable: entry.functionDeclaration.isExported(),
					calledFunctions: entry.analysisResult!.calledFunctions
				})
			)
		})).filter(entry => entry.name !== "__concolic.ts" && entry.functions.length !== 0)
	]};
}

server.get("/projects/:id/functions", {schema: {params: projectIdSchema}}, async (request, reply) => {
	if (statusStore.hasRunningTask) {
		reply.statusCode = 503;
		return {error: "A task is already running."};
	}
	const projectPath = Path.join(config.storagePath, (request.params as {id: string}).id);
	if (!FileSystem.existsSync(projectPath)) {
		reply.statusCode = 404;
		return {error: "Project not found."};
	}
	const originalPath = Path.join(projectPath, "original");
	const project = new Ts.Project({tsConfigFilePath: Path.join(originalPath, "tsconfig.json")});
	const testabilityAnalysis = new TestabilityAnalysis(originalPath);
	return {
		kind: "directory", name: "[Root]",
		entries: project.getDirectories()
			.filter(directory => Path.basename(directory.getPath()) !== "node_modules")
			.map(directory => getFolderEntry(testabilityAnalysis, directory))
	};
});

server.post("/projects/:id/generate", {schema: {params: projectIdSchema, body: {
	type: "object",
	required: ["functionsToTest", "coverageKind", "coverageTarget", "maxSearchDepth", "maxContextSize", "timeLimit"],
	properties: {
		functionsToTest: {type: "array", items: {
			type: "object",
			required: [
				"filePath", "functionName",
				"concolicDriverTemplate", "testDriverTemplate",
				"mockedFunctions"
			],
			properties: {
				filePath: {type: "string"},
				functionName: {type: "string"},
				concolicDriverTemplate: {type: "string"},
				testDriverTemplate: {type: "string"},
				mockedFunctions: {type: "array", items: {
					type: "object",
					required: ["source", "container", "name"],
					properties: {
						source: {type: "string"},
						container: {anyOf: [{type: "string"}, {type: "null"}]},
						name: {type: "string"}
					}
				}}
			}
		}},
		coverageKind: {enum: ["statement", "branch", "predicate"]},
		coverageTarget: {type: "number", minimum: 0, maximum: 100}, // Percent.
		maxSearchDepth: {type: "integer", minimum: 5},
		maxContextSize: {type: "integer", minimum: 5},
		timeLimit: {type: "integer", minimum: 0, maximum: 86400} // Seconds for each unit.
	}
}}}, async (request, reply) => {
	if (statusStore.hasRunningTask) {
		reply.statusCode = 503;
		return {error: "A task is already running."};
	}
	const projectId = (request.params as {id: string}).id;
	const projectPath = Path.join(config.storagePath, projectId);
	if (!FileSystem.existsSync(projectPath)) {
		reply.statusCode = 404;
		return {error: "Project not found."};
	}
	const params = request.body as {
		functionsToTest: {
			filePath: string, functionName: string,
			concolicDriverTemplate: string, testDriverTemplate: string,
			mockedFunctions: ResolvedFunctionPath[]
		}[],
		coverageKind: "statement" | "branch" | "predicate",
		coverageTarget: number,
		maxSearchDepth: number,
		maxContextSize: number,
		timeLimit: number
	};
	const coverageKind
		= params.coverageKind === "statement" ? CoverageKind.STATEMENT
		: params.coverageKind === "branch" ? CoverageKind.BRANCH
		: CoverageKind.PREDICATE;
	const taskId = generateId();
	statusStore.putTask({projectId, taskId, taskKind: "generate"});

	(async () => { // Task body.

	try {
		// Save the request data for later reexecutions.
		FileSystem.writeFileSync(Path.join(projectPath, "generationInput.json"), JSON.stringify(params), "utf8");
		// Clear old results.
		FileSystem.rmSync(Path.join(projectPath, "generationResult.json"), {force: true});

		const originalPath = Path.join(projectPath, "original");
		const concolicPath = Path.join(projectPath, "concolic");
		const testPath = Path.join(projectPath, "test");

		statusStore.updateTaskProgress("Preparing for generation...");
		// Ensure the concolic driver exists to prevent failure when resolving its compiled path.
		const driverPath = Path.join(concolicPath, "__concolic.ts");
		if (!FileSystem.existsSync(driverPath)) FileSystem.writeFileSync(driverPath, "", "utf8");

		{
			const originalProject = new Ts.Project({tsConfigFilePath: Path.join(originalPath, "tsconfig.json")});
			for (const func of params.functionsToTest) {
				const sourceFile = originalProject.getSourceFile(Path.join(originalPath, func.filePath));
				if (sourceFile === undefined) throw new Error(`Source file \`${func.filePath}\` not found.`);
				if (sourceFile.getFunction(func.functionName) === undefined)
					throw new Error(`Function \`${func.functionName}\` not found in source file \`${func.filePath}\`.`);
			}
		}

		// Clean up old generated test files.
		for (const name of FileSystem.readdirSync(testPath).filter(
			name => name.match(/^concolic\d+\.spec\.ts$/) !== null
		)) FileSystem.rmSync(Path.join(testPath, name));

		const result: {
			status: string,
			coverageKind: string,
			coverageTarget: number,
			generationResults: {
				filePath: string, functionName: string, testCases: TestCase[], coverage: number, time: number
			}[]
		} = {
			status: "succeeded",
			coverageKind: params.coverageKind, coverageTarget: params.coverageTarget,
			generationResults: []
		};
		let functionNumber = 1;
		for (const func of params.functionsToTest) {
			const functionProgressString
				= `Generating for function ${functionNumber} / ${params.functionsToTest.length}:\n`
				+ `${func.functionName} | ${func.filePath}\n`;
			statusStore.updateTaskProgress(functionProgressString + "Transforming code...");
			await new CodeTransformer(originalPath, concolicPath, coverageKind, func.mockedFunctions).transform();
			const project = new Ts.Project({tsConfigFilePath: Path.join(concolicPath, "tsconfig.json")});
			const {testCases, testDriver, coverage, time} = await new Executor(
				concolicPath, project, {source: func.filePath, container: null, name: func.functionName},
				func.concolicDriverTemplate, func.testDriverTemplate,
				coverageKind, params.coverageTarget, params.maxSearchDepth, params.maxContextSize, params.timeLimit
			).execute((currentTestCount, currentCoverage) => {
				statusStore.updateTaskProgress(
					functionProgressString
					+ `Tests generated: ${currentTestCount}\n`
					+ `Coverage: ${formatPercentage(currentCoverage)} `
					+ `/ ${formatPercentage(params.coverageTarget / 100)}`
				);
			});
			result.generationResults.push({
				filePath: func.filePath, functionName: func.functionName, testCases, coverage, time
			});
			FileSystem.writeFileSync(Path.join(testPath, `concolic${functionNumber}.spec.ts`), testDriver, "utf8");
			++functionNumber;
		}

		statusStore.updateTaskProgress("Running generated tests...");
		ChildProcess.spawnSync("npx", [
			"vitest", "run", "concolic", "--root", shescape.quote(testPath),
			"--coverage", "--coverage.reporter", "lcov",
			"--coverage.reportsDirectory", shescape.quote(Path.join(testPath, "coverage"))
		], {shell: true, stdio: "ignore"});

		// Save the result.
		FileSystem.writeFileSync(Path.join(projectPath, "generationResult.json"), JSON.stringify(result), "utf8");
	} catch (e) {
		console.error(e);
		FileSystem.writeFileSync(Path.join(projectPath, "generationResult.json"), JSON.stringify({
			status: "failed",
			exceptionMessage: (e as Error).message,
			fullExceptionInfo: (e as Error).toString()
		}), "utf8");
	}
	statusStore.finishTask();

	})(); // Task body.

	return {taskId};
});

server.get("/projects/:id/result", {schema: {params: projectIdSchema}}, (request, reply) => {
	const projectPath = Path.join(config.storagePath, (request.params as {id: string}).id);
	if (!FileSystem.existsSync(projectPath)) {
		reply.statusCode = 404;
		return {error: "Project not found."};
	}
	const resultPath = Path.join(projectPath, "generationResult.json");
	if (FileSystem.existsSync(resultPath)) return JSON.parse(FileSystem.readFileSync(resultPath, "utf8"));
	return {status: FileSystem.existsSync(Path.join(projectPath, "generationInput.json"))
		? "generating" : "notGenerated"
	};
});
server.get("/projects/:id/coverage/*", {schema: {params: projectIdSchema}}, (request, reply) => {
	const projectId = (request.params as {id: string}).id;
	const projectPath = Path.join(config.storagePath, projectId);
	if (!FileSystem.existsSync(projectPath)) {
		reply.callNotFound();
		return;
	}
	reply.sendFile(projectId + '/test/coverage/lcov-report/' + (request.params as {"*": string})["*"]);
});
server.get("/projects/:id/tests", {schema: {params: projectIdSchema}}, async (request, reply) => {
	const projectPath = Path.join(config.storagePath, (request.params as {id: string}).id);
	if (!FileSystem.existsSync(projectPath)) {
		reply.statusCode = 404;
		return {error: "Project not found."};
	}
	const resultPath = Path.join(projectPath, "generationResult.json");
	if (
		!FileSystem.existsSync(resultPath)
		|| (JSON.parse(FileSystem.readFileSync(resultPath, "utf8")) as {status: string}).status !== "succeeded"
	) {
		reply.statusCode = 404;
		return {error: "No generation results."};
	}
	const testPath = Path.join(projectPath, "test");
	const blobWriter = new ZipJs.BlobWriter();
	const zipWriter = new ZipJs.ZipWriter(blobWriter);
	for (const name of FileSystem.readdirSync(testPath).filter(
		name => name.match(/^concolic\d+\.spec\.ts$/) !== null
	)) await zipWriter.add(name, new ZipJs.TextReader(FileSystem.readFileSync(Path.join(testPath, name), "utf8")));
	await zipWriter.close();
	reply.type("application/zip");
	return Buffer.from(await (await blobWriter.getData()).arrayBuffer());
});
server.get("/projects/:id/last-generation-params", {schema: {params: projectIdSchema}}, (request, reply) => {
	const projectPath = Path.join(config.storagePath, (request.params as {id: string}).id);
	if (!FileSystem.existsSync(projectPath)) {
		reply.statusCode = 404;
		return {error: "Project not found."};
	}
	const inputPath = Path.join(projectPath, "generationInput.json");
	return {params: FileSystem.existsSync(inputPath) ? JSON.parse(FileSystem.readFileSync(inputPath, "utf8")) : null};
});

await server.listen({port: config.serverPort});
})();

// 10 random lower case characters or digits.
function generateId(): string {
	const codePoints: number[] = [];
	for (let i = 0; i !== 10; ++i) {
		const index = Math.floor(Math.random() * 36);
		codePoints.push((index < 26 ? 97 : 22) + index);
	}
	return String.fromCodePoint(...codePoints);
}

function formatPercentage(ratio: number): string {
	const unitString = Math.round(ratio * 10000).toString().padStart(3, '0');
	return unitString.substring(0, unitString.length-2) + '.' + unitString.substring(unitString.length-2) + '%';
}