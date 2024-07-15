import {Project} from "ts-morph";

import {compactCfg} from "#r/cfg/Cfg";
import {generateCfgFromFunction} from "#r/cfg/CfgGenerator";
import Executor from "#r/execution/Executor";

(async () => {

const projectPath = "D:\\Code\\TS analyzer\\Test TS project";
const project = new Project({tsConfigFilePath: projectPath + "\\tsconfig.json"});
const functionDeclaration = project.getSourceFileOrThrow(projectPath + "\\test.ts").getFunctionOrThrow("test");
//const cfg = generateCfgFromFunction(functionDeclaration);
await new Executor(projectPath, functionDeclaration).execute();
/*
console.log("Breakpoints:");
for (const breakpoint of getBreakpointsFromFunction(functionDeclaration))
	console.log(`Line: ${breakpoint.line} | Column: ${breakpoint.column} | Secondary: ${breakpoint.isSecondaryBranch}`);
*/

})();