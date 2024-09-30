import * as ZipJs from "@zip.js/zip.js";
import {Buffer} from "buffer";
import * as ChildProcess from "child_process";
import Fastify from "fastify";
import * as FileSystem from "fs";
import * as Path from "path";
import {Shescape} from "shescape";
import * as Ts from "ts-morph";

import Executor from "#r/execution/Executor";
import {getTestableFunctions} from "#r/project/Analysis";
import config from "./config.js";

type SourceFileEntry = {
	kind: "file",
	name: string,
	functions: string[]
};
type FolderEntry = {
	kind: "folder",
	name: string,
	entries: (FolderEntry | SourceFileEntry)[]
};

(async () => {
// Ensure the concolic driver exists to prevent failure when resolving its compiled path.
FileSystem.writeFileSync(Path.join(config.concolicProjectPath, "driver.ts"), "", "utf8");

const shescape = new Shescape({shell: true});
const project = new Ts.Project({tsConfigFilePath: config.concolicProjectPath + "\\tsconfig.json"});

const server = Fastify();

function getFolderEntry(directory: Ts.Directory): FolderEntry {
	return {kind: "folder", name: Path.basename(directory.getPath()), entries: [
		...directory.getDirectories().map(getFolderEntry),
		...directory.getSourceFiles().map((sourceFile: Ts.SourceFile): SourceFileEntry => ({
			kind: "file",
			name: Path.basename(sourceFile.getFilePath()),
			functions: getTestableFunctions(sourceFile).map(func => func.getName()!)
		})).filter(entry => entry.name !== "__concolic.ts" && entry.functions.length !== 0)
	]};
}

server.get("/functions", async (request, reply) => {
	return {kind: "directory", name: "[Root]", entries: project.getDirectories().map(getFolderEntry)};
});

server.post("/generate", {schema: {body: {
	type: "object",
	required: ["filePath", "functionName", "concolicDriverTemplate", "testDriverTemplate"],
	properties: {
		filePath: {type: "string"},
		functionName: {type: "string"},
		concolicDriverTemplate: {type: "string"},
		testDriverTemplate: {type: "string"}
	}
}}}, async (request, reply) => {
	const params = request.body as {
		filePath: string, functionName: string, concolicDriverTemplate: string, testDriverTemplate: string
	};
	const sourceFile = project.getSourceFile(Path.join(config.concolicProjectPath, params.filePath));
	if (sourceFile === undefined) {
		reply.statusCode = 404;
		return {error: "Source file not found."};
	}
	if (sourceFile.getFunction(params.functionName) === undefined) {
		reply.statusCode = 404;
		return {error: "Function not found."};
	}
	try {
		const {testCases, testDriver} = await new Executor(
			config.concolicProjectPath, project, params.filePath, params.functionName,
			params.concolicDriverTemplate, params.testDriverTemplate
		).execute();
		FileSystem.writeFileSync(Path.join(config.testProjectPath, "concolic.spec.ts"), testDriver, "utf8");
		ChildProcess.spawnSync("npx", [
			"vitest", "run", "concolic", "--root", shescape.quote(config.testProjectPath),
			"--coverage", "--coverage.reporter", "json", "--coverage.reporter", "json-summary",
			"--coverage.reportsDirectory", shescape.quote(Path.join(config.testProjectPath, "coverage"))
		], {shell: true});
		const testSourceFilePath = Path.join(config.testProjectPath, params.filePath);
		return {
			testCases,
			coverageSummary: JSON.parse(
				FileSystem.readFileSync(Path.join(config.testProjectPath, "coverage/coverage-summary.json"), "utf8")
			)[testSourceFilePath],
			detailedCoverage: JSON.parse(
				FileSystem.readFileSync(Path.join(config.testProjectPath, "coverage/coverage-final.json"), "utf8")
			)[testSourceFilePath],
			sourceCode: FileSystem.readFileSync(testSourceFilePath, "utf8")
		};
	} catch (e) {
		console.error(e);
		throw e;
	}
});

await server.listen({port: config.serverPort});
})();