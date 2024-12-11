function a(a1: number, a2: number): number {
	return 1 - 3 * a2 + 3 * a1;
}
function b(a1: number, a2: number): number {
	return 3 * a2 - 6 * a1;
}
function c(a1: number): number {
	return 3 * a1;
}
function calcBezier(t: number, a1: number, a2: number): number {
	return ((a(a1, a2) * t + b(a1, a2)) * t + c(a1)) * t;
}
function getSlope(t: number, a1: number, a2: number): number {
	return 3 * a(a1, a2) * t * t + 2 * b(a1, a2) * t + c(a1);
}
export function getTforX(p0: number, p2: number, x: number): number {
	let aGuessT = x;

	for (let i = 0; i < 4; ++i) {
	  const currentSlope = getSlope(aGuessT, p0, p2);

	  if (currentSlope === 0) {
		return aGuessT;
	  }

	  const currentX = calcBezier(aGuessT, p0, p2) - x;

	  aGuessT -= currentX / currentSlope;
	}

	return aGuessT;
}

export function bezierEasing(p0: number, p1: number, p2: number, p3: number, x: number): number {
	return p0 === p1 && p2 === p3 ? x : calcBezier(getTforX(p0, p2, x), p1, p3);
}