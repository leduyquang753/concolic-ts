const specialStringSmtCharacters = new Set<string>(['\\', '"', '\r', '\n']);
for (let i = 0; i !== 32; ++i) specialStringSmtCharacters.add(String.fromCodePoint(i));

export function formatSmtNumber(n: number): string {
	return n < 0 ? `(- ${formatSmtNumberForAbsolutePart(-n)})` : formatSmtNumberForAbsolutePart(n);
}

export function formatSmtString(s: string): string {
	let smt = '"';
	for (const c of s) smt += specialStringSmtCharacters.has(c) ? `\\u{${c.codePointAt(0)!.toString(16)}}`: c;
	smt += '"';
	return smt;
}

export function parseSmtString(smt: string): string {
	let s = "";
	for (let i = 0; i < smt.length; ++i) {
		if (smt[i] === '\\' && i !== smt.length - 1 && smt[i+1] === 'u') {
			let codePointString = "";
			if (smt[i+2] === '{') {
				i += 3;
				while (smt[i] !== '}') {
					codePointString += smt[i];
					++i;
				}
				++i;
			} else {
				i += 2;
				for (let j = 0; j !== 4; ++j) {
					codePointString += smt[i];
					++i;
				}
			}
			s += String.fromCodePoint(Number.parseInt(codePointString, 16));
		} else {
			s += smt[i];
		}
	}
	return s;
}

function formatSmtNumberForAbsolutePart(n: number): string {
	const s = n.toString();
	return s.indexOf('.') === -1 ? s + ".0" : s;
}