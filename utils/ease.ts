const c1 = 1.70158;
const PI = 3.14159265358979;

/**
 * Ease in-out back
 *
 * http://cubic-bezier.com/#0.68,-0.6,0.32,1.6
 */
export function easeInOutBack(x: number): number {
  const c2 = c1 * 1.525

  return x < 0.5
    ? (Math.pow(2 * x, 2) * ((c2 + 1) * 2 * x - c2)) / 2
    : (Math.pow(2 * x - 2, 2) * ((c2 + 1) * (x * 2 - 2) + c2) + 2) / 2
}

/**
 * Ease in elastic
 */
export function easeInElastic(x: number): number {
  const c4 = (2 * PI) / 3

  return x === 0
    ? 0
    : x === 1
      ? 1
      : -Math.pow(2, 10 * x - 10) * Math.sin((x * 10 - 10.75) * c4)
}

/**
 * Ease out elastic
 */
export function easeOutElastic(x: number): number {
  const c4 = (2 * PI) / 3

  return x === 0
    ? 0
    : x === 1
      ? 1
      : Math.pow(2, -10 * x) * Math.sin((x * 10 - 0.75) * c4) + 1
}

/**
 * Ease in-out elastic
 */
export function easeInOutElastic(x: number): number {
  const c5 = (2 * PI) / 4.5

  return x === 0
    ? 0
    : x === 1
      ? 1
      : x < 0.5
        ? -(Math.pow(2, 20 * x - 10) * Math.sin((20 * x - 11.125) * c5)) / 2
        : (Math.pow(2, -20 * x + 10) * Math.sin((20 * x - 11.125) * c5)) / 2 + 1
}

/**
 * Ease out bounce
 */
export function easeOutBounce(x: number): number {
  const n1 = 7.5625
  const d1 = 2.75
  
  if (x < 1 / d1) {
    return n1 * x * x
  }
  
  if (x < 2 / d1) {
    return n1 * (x -= 1.5 / d1) * x + 0.75
  } 
  
  if (x < 2.5 / d1) {
    return n1 * (x -= 2.25 / d1) * x + 0.9375
  }

  return n1 * (x -= 2.625 / d1) * x + 0.984375
}

/**
 * Ease in-out bounce 
 */
export function easeInOutBounce(x: number): number {
  return x < 0.5
    ? (1 - easeOutBounce(1 - 2 * x)) / 2
    : (1 + easeOutBounce(2 * x - 1)) / 2
}
