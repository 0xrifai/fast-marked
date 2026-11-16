// Driver for the fast-marked entry: reads every case from the input
// directory, renders each one on its own with parse() from parse.js,
// and writes the HTML strings (one per case, in the cases' order) to
// the output directory as a JSON array.
//
// The harness runs `node /bot/main.ts` under node 22. Inside a
// container the cases live at /input/cases.json and the result goes to
// /output/html.json; outside a container the MAKEFUN_INPUT_DIR and
// MAKEFUN_OUTPUT_DIR environment variables stand in for /input and
// /output.

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(
  readFileSync(join(inputDir, 'cases.json'), 'utf8'),
) as { id: string; markdown: string }[];

const html: string[] = new Array(cases.length);
for (let i = 0; i < cases.length; i++) {
  html[i] = parse(cases[i].markdown);
}

mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
