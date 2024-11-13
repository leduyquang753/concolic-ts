import * as FileSystem from "fs";
import * as Path from "path";
import * as Ts from "ts-morph";
import Executor from "#r/execution/Executor";

(async () => {
	const projectPath = "D:\\Code\\TS analyzer\\Test TS project\\Concolic";
	const project = new Ts.Project({tsConfigFilePath: Path.join(projectPath, "tsconfig.json")});
	const sourceFile = project.getSourceFileOrThrow(Path.join(projectPath, "main.ts"));
	/*
	const cfg = generateCfgFromFunction(functionDeclaration);
	compactCfg(cfg);
	*/
	/*
	console.log("Breakpoints:");
	for (const breakpoint of getBreakpointsFromFunction(functionDeclaration))
		console.log(`Line: ${breakpoint.line} | Column: ${breakpoint.column} | Secondary: ${breakpoint.isSecondaryBranch}`);
	*/
	const result = await new Executor(
		projectPath, project, "main.ts", "test",
		FileSystem.readFileSync(Path.join(projectPath, "driver.ts.template"), "utf8"),
		FileSystem.readFileSync(Path.join(projectPath, "test.spec.ts.template"), "utf8")
	).execute();
	console.log(`Path constraints: ${result.solverCalls} solved; ${result.cachedSolverResults} cached.`);
	FileSystem.writeFileSync("T:\\test.ts", result.testDriver, "utf8");
})();