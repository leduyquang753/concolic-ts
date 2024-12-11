import { clamp } from './utils'

/**
 * Convert HSL to RGB.
 */
export function hslToRgb(
	hue: number, saturation: number, lightness: number, alpha: number
): {red: number, green: number, blue: number, alpha: number} {
  lightness = clamp(lightness, 0, 1)
  saturation = clamp(saturation, 0, 1)
  alpha = clamp(alpha, 0, 1)

  const chroma = (1 - Math.abs(2 * lightness - 1)) * saturation
  const x = chroma * (1 - Math.abs((hue / 60) % 2 - 1))
  const m = lightness - chroma / 2

  let red = 0
  let green = 0
  let blue = 0

  if (0 <= hue && hue < 60) {
    red = chroma
    green = x
    blue = 0
  } else if (60 <= hue && hue < 120) {
    red = x
    green = chroma
    blue = 0
  } else if (120 <= hue && hue < 180) {
    red = 0
    green = chroma
    blue = x
  } else if (180 <= hue && hue < 240) {
    red = 0
    green = x
    blue = chroma
  } else if (240 <= hue && hue < 300) {
    red = x
    green = 0
    blue = chroma
  } else if (300 <= hue && hue < 360) {
    red = chroma
    green = 0
    blue = x
  }

  red = (red + m) * 255;
  green = (green + m) * 255;
  blue = (blue + m) * 255;

  return {red, green, blue, alpha};
}