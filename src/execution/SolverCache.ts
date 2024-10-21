import makeSqliteConnection, {Database} from "better-sqlite3";
import * as FileSystem from "fs";
import {xxHash32 as hash} from "js-xxhash";
import * as Path from "path";
import * as Ts from "ts-morph";

export type SolverResult = any | "infeasible" | null;
export type CacheNode = {
	id: number,
	codeHash: number,
	solverResult: SolverResult,
	children: (number | null)[]
};

export default class SolverCache {
	#projectPath: string;
	#database: Database;

	constructor(projectPath: string) {
		this.#projectPath = projectPath;
		const databasePath = Path.join(projectPath, "solverCache.db");
		const databaseInitialized = FileSystem.existsSync(databasePath);
		this.#database = makeSqliteConnection(databasePath);
		this.#database.pragma("journal_mode = WAL");
		if (!databaseInitialized) this.#database.exec(
			"CREATE TABLE functions(name PRIMARY KEY, signatureHash);"
			+ "CREATE TABLE rootIdMap(functionId INT PRIMARY KEY, rootId);"
			+ "CREATE TABLE nodes(functionId, data);"
		);
	}

	getInfoForFunction(functionDeclaration: Ts.FunctionDeclaration): {functionId: number, rootNode: CacheNode} {
		const name
			= Path.relative(this.#projectPath, functionDeclaration.getSourceFile().getFilePath())
			+ "|" + functionDeclaration.getName();
		const signatureHash = hash(
			functionDeclaration.getName()
			+ "|" + functionDeclaration.getReturnTypeNode()!.getText()
			+ "|" + functionDeclaration.getParameters().map(parameter => parameter.getText()).join("|")
		);
		const functionResult = this.#database.prepare<[string], {rowid: number, signatureHash: number}>(
			"SELECT rowid, signatureHash FROM functions WHERE name = ?"
		).get(name);
		if (functionResult === undefined) {
			const functionId = this.#database.prepare<[string, number]>(
				"INSERT INTO functions(name, signatureHash) VALUES (?, ?)"
			).run(name, signatureHash).lastInsertRowid as number;
			const newNode = {
				id: -1,
				codeHash: 0,
				solverResult: null,
				children: [null, null]
			};
			newNode.id = this.insertOrUpdateNode(functionId, newNode);
			this.#database.prepare<[number, number]>(
				"INSERT INTO rootIdMap(functionId, rootId) VALUES (?, ?)"
			).run(functionId, newNode.id);
			return {functionId, rootNode: newNode};
		} else {
			if (functionResult.signatureHash === signatureHash) return {
				functionId: functionResult.rowid,
				rootNode: this.getNode(
					this.#database.prepare<[number], {rootId: number}>(
						"SELECT rootId from rootIdMap WHERE functionId = ?"
					).get(functionResult.rowid)!.rootId
				)
			};
			this.#database.prepare<[number]>("DELETE FROM nodes WHERE functionId = ?").run(functionResult.rowid);
			const newNode = {
				id: -1,
				codeHash: 0,
				solverResult: null,
				children: [null, null]
			};
			newNode.id = this.insertOrUpdateNode(functionResult.rowid, newNode);
			this.#database.prepare<[number, number]>(
				"UPDATE functions SET signatureHash = ? WHERE rowid = ?"
			).run(signatureHash, functionResult.rowid);
			this.#database.prepare<[number, number]>(
				"UPDATE rootIdMap SET rootId = ? WHERE functionId = ?"
			).run(newNode.id, functionResult.rowid);
			return {functionId: functionResult.rowid, rootNode: newNode};
		}
	}

	getNode(id: number): CacheNode {
		const result = this.#database.prepare<[number], {data: string}>(
			"SELECT data FROM nodes WHERE rowid = ?"
		).get(id);
		if (result === undefined) throw new Error(`No node with ID ${id} exists in cache.`);
		const node = JSON.parse(result.data) as CacheNode;
		node.id = id;
		return node;
	}

	// If ID is not positive, adds a new node.
	insertOrUpdateNode(functionId: number, node: CacheNode): number {
		const data = JSON.stringify({
			codeHash: node.codeHash,
			solverResult: node.solverResult,
			children: node.children
		});
		if (node.id > 0) {
			if (this.#database.prepare<[string, number]>(
				"UPDATE nodes SET data = ? WHERE rowid = ?"
			).run(data, node.id).changes === 0)
				throw new Error(`No node with ID ${node.id} exists in cache.`);
			return node.id;
		} else {
			const result = this.#database.prepare<[number, string]>(
				"INSERT INTO nodes(functionId, data) VALUES (?, ?)"
			).run(functionId, data);
			if (result.changes === 0) throw new Error("Failed to insert node to cache.");
			return result.lastInsertRowid as number;
		}
	}

	close(): void {
		this.#database.close();
	}
}