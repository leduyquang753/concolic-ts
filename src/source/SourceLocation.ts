// Line and column are zero-based to match the inspector protocol.

export type SourceLocation = {
	sourcePath: string,
	line: number,
	column: number
};