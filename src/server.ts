import FastifyStatic from "@fastify/static";
import * as ZipJs from "@zip.js/zip.js";
import {Buffer} from "buffer";
import * as ChildProcess from "child_process";
import Fastify from "fastify";
import * as FileSystem from "fs";
import * as Path from "path";
import {Shescape} from "shescape";
import * as Ts from "ts-morph";

import {transformProject} from "#r/execution/CodeTransformer";
import CoverageKind from "#r/execution/CoverageKind";
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

const server = Fastify();

server.register(FastifyStatic, {
	root: Path.join(config.testProjectPath, "coverage/lcov-report"), prefix: "/coverage/"
});
server.get("/coverage", (request, reply) => { reply.redirect("/coverage/"); });

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
	const project = new Ts.Project({tsConfigFilePath: Path.join(config.concolicProjectPath, "tsconfig.json")});
	return {kind: "directory", name: "[Root]", entries: project.getDirectories().map(getFolderEntry)};
});

server.post("/generate", {schema: {body: {
	type: "object",
	required: ["functionsToTest", "coverageKind", "coverageTarget", "maxSearchDepth", "maxContextSize", "timeLimit"],
	properties: {
		functionsToTest: {
			type: "array",
			items: {
				type: "object",
				required: ["filePath", "functionName", "concolicDriverTemplate", "testDriverTemplate"],
				properties: {
					filePath: {type: "string"},
					functionName: {type: "string"},
					concolicDriverTemplate: {type: "string"},
					testDriverTemplate: {type: "string"}
				}
			}
		},
		coverageKind: {enum: ["statement", "branch", "predicate"]},
		coverageTarget: {type: "number", minimum: 0, maximum: 100}, // Percent.
		maxSearchDepth: {type: "integer", minimum: 5},
		maxContextSize: {type: "integer", minimum: 5},
		timeLimit: {type: "integer", minimum: 0, maximum: 86400} // Seconds for each unit.
	}
}}}, async (request, reply) => {
	const params = request.body as {
		functionsToTest: {
			filePath: string, functionName: string, concolicDriverTemplate: string, testDriverTemplate: string
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
	try {
		await transformProject(config.originalProjectPath, config.concolicProjectPath, coverageKind);
		const project = new Ts.Project({tsConfigFilePath: Path.join(config.concolicProjectPath, "tsconfig.json")});
		for (const func of params.functionsToTest) {
			const sourceFile = project.getSourceFile(Path.join(config.concolicProjectPath, func.filePath));
			if (sourceFile === undefined) {
				reply.statusCode = 404;
				return {error: "Source file not found."};
			}
			if (sourceFile.getFunction(func.functionName) === undefined) {
				reply.statusCode = 404;
				return {error: "Function not found."};
			}
		}
		// Clean up old generated test files.
		for (const name of FileSystem.readdirSync(config.testProjectPath).filter(
			name => name.match(/^concolic\d+\.spec\.ts$/) !== null
		)) FileSystem.rmSync(Path.join(config.testProjectPath, name));
		const result: {
			coverageKind: string,
			coverageTarget: number,
			generationResults: {
				filePath: string, functionName: string, testCases: any[], coverage: number, time: number
			}[]
		} = {coverageKind: params.coverageKind, coverageTarget: params.coverageTarget, generationResults: []};
		let fileNumber = 0;
		for (const func of params.functionsToTest) {
			const {testCases, testDriver, coverage, time} = await new Executor(
				config.concolicProjectPath, project, func.filePath, func.functionName,
				func.concolicDriverTemplate, func.testDriverTemplate,
				coverageKind, params.coverageTarget, params.maxSearchDepth, params.maxContextSize, params.timeLimit
			).execute();
			result.generationResults.push({
				filePath: func.filePath, functionName: func.functionName, testCases, coverage, time
			});
			++fileNumber;
			FileSystem.writeFileSync(
				Path.join(config.testProjectPath, `concolic${fileNumber}.spec.ts`), testDriver, "utf8"
			);
		}
		ChildProcess.spawnSync("npx", [
			"vitest", "run", "concolic", "--root", shescape.quote(config.testProjectPath),
			"--coverage", "--coverage.reporter", "lcov",
			"--coverage.reportsDirectory", shescape.quote(Path.join(config.testProjectPath, "coverage"))
		], {shell: true});
		return result;
	} catch (e) {
		console.error(e);
		throw e;
	}
});

await server.listen({port: config.serverPort});
})();