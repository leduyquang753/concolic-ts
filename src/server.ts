import {Buffer} from "buffer";
import * as ZipJs from "@zip.js/zip.js";
import Fastify from "fastify";
import * as Path from "path";
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
const project = new Ts.Project({tsConfigFilePath: config.projectPath + "\\tsconfig.json"});

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
	const sourceFile = project.getSourceFile(config.projectPath + "/" + params.filePath);
	if (sourceFile === undefined) {
		reply.statusCode = 404;
		return {error: "Source file not found."};
	}
	if (sourceFile.getFunction(params.functionName) === undefined) {
		reply.statusCode = 404;
		return {error: "Function not found."};
	}
	try {
		const testDrivers = await new Executor(
			config.projectPath, sourceFile, params.functionName,
			params.concolicDriverTemplate, params.testDriverTemplate
		).execute();
		const zipFileWriter = new ZipJs.BlobWriter();
		const zipWriter = new ZipJs.ZipWriter(zipFileWriter);
		let i = 0;
		for (const testDriver of testDrivers) {
			++i;
			await zipWriter.add(`test${i}.ts`, new ZipJs.TextReader(testDriver));
		}
		zipWriter.close();
		reply.type("application/zip");
		return Buffer.from(await (await zipFileWriter.getData()).arrayBuffer());
	} catch (e) {
		console.error(e);
		throw e;
	}
});

await server.listen({port: config.serverPort});
})();