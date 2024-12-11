type Vec = {x: number, y: number};
type Line = {p1: Vec, p2: Vec};

export function slope(p1: Vec, p2: Vec): number {
  return (p2.y - p1.y) / (p2.x - p1.x);
}

export function intersect({p1: v1, p2: v2}: Line, {p1: v3, p2: v4}: Line): Vec {
  const {x: x1, y: y1} = v1, {x: x3, y: y3} = v3;
  
  const vertical1 = v1.x === v2.x;
  const vertical2 = v3.x === v4.x;
  if (vertical1 && vertical2) return {x: 0, y: 0};
  
  const m1 = slope(v1, v2);
  const m3 = slope(v3, v4);

  // first line is vertical
  const b3 = y3 - (m3 * x3);

  if (vertical1) {
    return {x: x1, y: (m3 * x1) + b3};
  }

  // second line is vertical
  const b1 = y1 - (m1 * x1)

  if (vertical2) {
    return {x: x3, y: (m1 * x3) + b1};
  }

  // lines are parallel
  if (m1 === m3) {
    return {x: 0, y: 0};
  }

  // calculate intersection point
  const x = (b3 - b1) / (m1 - m3);
  const y = (m1 * x) + b1;

  return {x, y};
}
