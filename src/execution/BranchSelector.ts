import type {Cfg} from "#r/cfg/Cfg";
import {iterateCfg} from "#r/cfg/Cfg";
import type CfgNode from "#r/cfg/CfgNode";
import SymbolicExpression from "#r/symbolic/expressions/SymbolicExpression";

export type ExecutionEntry = {
	parentCalls: string,
	cfgNode: CfgNode,
	isSecondaryBranch: boolean,
	branchingCondition: SymbolicExpression // Not negated even when it's secondary branch.
};
type ExecutionNode = {
	parent: ExecutionNode | null,
	parentCalls: string,
	cfgNode: CfgNode,
	isSecondaryBranch: boolean,
	branchingCondition: SymbolicExpression,
	isCovered: boolean,
	children: (ExecutionNode | null)[] // Always has 2 elements corresponding to at most 2 branches.
};

export default class BranchSelector {
	#maxSearchDepth: number;
	#maxContextLength: number;

	#dominatorMap: Map<number, Set<number>> = new Map<number, Set<number>>();
	#executionTreeRoot: ExecutionNode;
	#coveredContexts: Set<string> = new Set<string>();

	#contextLength: number = 1;
	#currentSearchDepth: number = 0;
	#currentNodes: ExecutionNode[] = [];
	#nextNodes: ExecutionNode[] = [];

	get contextLength(): number {
		return this.#contextLength;
	}

	constructor(maxSearchDepth: number, maxContextLength: number) {
		this.#maxSearchDepth = maxSearchDepth;
		this.#maxContextLength = maxContextLength;
		this.#executionTreeRoot = {
			parent: null,
			parentCalls: "",
			cfgNode: null!,
			isSecondaryBranch: false,
			branchingCondition: null!, // Won't be used.
			isCovered: true,
			children: [null, null]
		};
	}

	addCfg(cfg: Cfg) {
		const allNodes = [...iterateCfg(cfg)];
		const allBranches: number[] = [];
		const branchesToIterate: number[] = [];
		for (const node of allNodes) {
			const nodeBranches = getBranchKeys(node);
			allBranches.push(...nodeBranches);
			if (node !== cfg.beginNode) branchesToIterate.push(...nodeBranches);
		}
		const predecessorMap = new Map<number, number[]>();
		for (const branch of allBranches) predecessorMap.set(branch, []);
		for (const node of allNodes) {
			if (node.primaryNext !== null) for (const branch of getBranchKeys(node.primaryNext))
				predecessorMap.get(branch)!.push(makeBranchKey(node, false));
			if (node.secondaryNext !== null) for (const branch of getBranchKeys(node.secondaryNext))
				predecessorMap.get(branch)!.push(makeBranchKey(node, true));
		}
		const dominatorMap = new Map<number, Set<number>>();
		const beginBranchKey = makeBranchKey(cfg.beginNode, false);
		dominatorMap.set(beginBranchKey, new Set<number>([beginBranchKey]));
		for (const branch of branchesToIterate) dominatorMap.set(branch, new Set<number>(allBranches));
		for (let hasChanges = true; hasChanges;) {
			hasChanges = false;
			for (const branch of branchesToIterate) {
				let newDominatorSet: Set<number> | null = null;
				for (const predecessor of predecessorMap.get(branch)!) {
					const predecessorDominators = dominatorMap.get(predecessor)!;
					if (newDominatorSet === null) {
						newDominatorSet = new Set<number>(predecessorDominators);
					} else {
						const newerDominatorSet = new Set<number>();
						for (const dominator of newDominatorSet)
							if (predecessorDominators.has(dominator)) newerDominatorSet.add(dominator);
						newDominatorSet = newerDominatorSet;
					}
				}
				if (newDominatorSet === null) newDominatorSet = new Set<number>();
				newDominatorSet.add(branch);
				if (!hasChanges) {
					const oldDominatorSet = dominatorMap.get(branch)!;
					if (oldDominatorSet.size !== newDominatorSet.size) {
						hasChanges = true;
					} else {
						for (const dominator of oldDominatorSet) if (!newDominatorSet.has(dominator)) {
							hasChanges = true;
							break;
						}
					}
				}
				dominatorMap.set(branch, newDominatorSet);
			}
		}
		for (const [key, value] of dominatorMap) this.#dominatorMap.set(key, value);
	}

	getNextExecutionPath(): {path: ExecutionEntry[], context: string} | null {
		while (true) {
			if (this.#currentNodes.length === 0) {
				++this.#currentSearchDepth;
				this.#currentNodes = this.#nextNodes;
				this.#nextNodes = [];
				if (this.#currentNodes.length === 0 || this.#currentSearchDepth > this.#maxSearchDepth) {
					if (this.#contextLength === this.#maxContextLength) return null;
					++this.#contextLength;
					this.#currentSearchDepth = 0;
					this.#currentNodes = [this.#executionTreeRoot];
				}
			}
			const randomIndex = Math.floor(Math.random() * this.#currentNodes.length);
			const currentNode = this.#currentNodes[randomIndex];
			this.#currentNodes[randomIndex] = this.#currentNodes.at(-1)!;
			this.#currentNodes.pop();
			this.#nextNodes.push(...currentNode.children.filter(node => node !== null) as ExecutionNode[]);
			if (currentNode.isCovered) continue;

			let context = currentNode.cfgNode.id + ' ';
			{
				const dominators = this.#dominatorMap.get(
					makeBranchKey(currentNode.cfgNode, currentNode.isSecondaryBranch)
				)!;
				let currentContextLength = 1;
				let currentContextNode = currentNode.parent;
				while (currentContextNode !== null && currentContextLength !== this.#contextLength) {
					if (currentContextNode !== this.#executionTreeRoot && (
						currentContextNode.parentCalls !== currentNode.parentCalls
						|| !dominators.has(makeBranchKey(
							currentContextNode.cfgNode, currentContextNode.isSecondaryBranch
						)
					))) {
						context += currentContextNode.cfgNode.id + " ";
						++currentContextLength;
					}
					currentContextNode = currentContextNode.parent;
				}
			}
			if (this.#coveredContexts.has(context)) continue;

			currentNode.isCovered = true;
			const executionPath: ExecutionEntry[] = [];
			for (
				let currentPathNode: ExecutionNode = currentNode;
				currentPathNode !== this.#executionTreeRoot;
				currentPathNode = currentPathNode.parent!
			) executionPath.unshift({
				parentCalls: currentPathNode.parentCalls,
				cfgNode: currentPathNode.cfgNode,
				isSecondaryBranch: currentPathNode.isSecondaryBranch,
				branchingCondition: currentPathNode.branchingCondition
			});
			const lastEntry = executionPath.at(-1)!;
			lastEntry.isSecondaryBranch = !lastEntry.isSecondaryBranch;
			return {path: executionPath, context};
		}
	}

	markContextCovered(context: string): void {
		this.#coveredContexts.add(context);
	}

	addExecutionPath(executionPath: ExecutionEntry[]): void {
		let currentTreeNode = this.#executionTreeRoot;
		let depth = 0;
		for (const entry of executionPath) {
			const selectedChild = currentTreeNode.children[entry.isSecondaryBranch ? 1 : 0];
			if (selectedChild !== null) {
				currentTreeNode = selectedChild;
				continue;
			}
			const newNode: ExecutionNode = {
				parent: currentTreeNode,
				parentCalls: entry.parentCalls,
				cfgNode: entry.cfgNode,
				isSecondaryBranch: entry.isSecondaryBranch,
				branchingCondition: entry.branchingCondition,
				isCovered: false,
				children: [null, null]
			};
			currentTreeNode.children[entry.isSecondaryBranch ? 1 : 0] = newNode;
			const otherChild = currentTreeNode.children[entry.isSecondaryBranch ? 0 : 1];
			if (otherChild !== null) {
				newNode.isCovered = true;
				otherChild.isCovered = true;
			}
			currentTreeNode = newNode;
			if (depth === this.#currentSearchDepth) this.#currentNodes.push(newNode);
			++depth;
		}
	}
}

function makeBranchKey(cfgNode: CfgNode, isSecondaryBranch: boolean): number {
	return cfgNode.id*10 + (isSecondaryBranch ? 0 : 1);
}

function getBranchKeys(cfgNode: CfgNode): number[] {
	const nodeBranches: number[] = [];
	if (cfgNode.primaryNext !== null) nodeBranches.push(makeBranchKey(cfgNode, false));
	if (cfgNode.secondaryNext !== null) nodeBranches.push(makeBranchKey(cfgNode, true));
	return nodeBranches;
}