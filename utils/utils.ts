export function clamp(val: number, min: number, max: number): number {
  return val < min ? min : val > max ? max : val;
}

/**
 * Clamp a number to between 0 and 255.
 */
export function clampColor(val: number): number {
  return clamp(val, 0, 255);
}