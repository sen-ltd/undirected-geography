// Rebuild the results block of README.md from runs/ (no number is typed by hand).
//
//   node tools/report.mts
import { readFileSync, writeFileSync, existsSync } from 'node:fs';

const lit = JSON.parse(readFileSync('runs/literature.json', 'utf8'));
const sweep = JSON.parse(readFileSync('runs/sweep.json', 'utf8'));
const smallest: { k: number; n: number; found: boolean; recheck: number | null; seconds: number }[] = existsSync('runs/smallest.jsonl')
  ? readFileSync('runs/smallest.jsonl', 'utf8').trim().split('\n').map((l) => JSON.parse(l))
  : [];
const f = (x: number) => x.toLocaleString('en-US');
const star = (k: number) => (k === 0 ? '0' : k === 1 ? '\\*' : `\\*${k}`);
const items: { id: string; ok: boolean; got: string }[] = lit.items;

let out = '### The paper\n\n';
out += `${items.filter((x) => x.ok).length} of ${items.length} items agree. Failing:\n\n`;
for (const it of items.filter((x) => !x.ok)) out += `- \`${it.id}\`: ${it.got.replace(/\*/g, '\\*')}\n`;
out += '\nThe high-nimber construction, value of the token on N_n by variant:\n\n';
const cons: { variant: string; n: number; vertices: number; value: number | null; nodes: number }[] = lit.construction;
const ns = [...new Set(cons.map((c) => c.n))].sort((a, b) => a - b);
out += `| variant | ${ns.map((n) => `n=${n}`).join(' | ')} |\n|---|${ns.map(() => '---:').join('|')}|\n`;
for (const v of [...new Set(cons.map((c) => c.variant))]) {
  out += `| ${v} | ${ns.map((n) => {
    const c = cons.find((x) => x.variant === v && x.n === n);
    return c ? (c.value === null ? '?' : star(c.value)) : '';
  }).join(' | ')} |\n`;
}
const drawn = cons.filter((c) => c.variant.startsWith('as drawn'));
out += `\nVertices (as drawn): ${drawn.map((c) => `${c.n}: ${f(c.vertices)}`).join(', ')}; search nodes: ${drawn.map((c) => f(c.nodes)).join(', ')}.\n\n`;
out += 'All passing items:\n\n';
for (const it of items.filter((x) => x.ok)) out += `- \`${it.id}\`: ${it.got.replace(/\*/g, '\\*')}\n`;

out += '\n### Every connected graph up to ' + sweep.N + ' vertices\n\n';
const maxV = Math.max(...sweep.rows.map((r: { maxValue: number }) => r.maxValue));
out += `| n | graphs | (graph, start) pairs | ${Array.from({ length: maxV + 1 }, (_, k) => `value ${star(k)}`).join(' | ')} | FSU mismatches | subcubic starts | B&B mismatches | max tests |\n`;
out += `|---:|---:|---:|${Array.from({ length: maxV + 1 }, () => '---:').join('|')}|---:|---:|---:|---:|\n`;
for (const r of sweep.rows) {
  out += `| ${r.n} | ${f(r.graphs)} | ${f(r.pairs)} | ${Array.from({ length: maxV + 1 }, (_, k) => (r.byValue[k] ? f(r.byValue[k]) : '')).join(' | ')} | ${r.fsuMismatch} | ${f(r.subcubicPairs)} | ${r.bnbMismatch} | ${r.bnbMaxTests} |\n`;
}
const tot = (k: string) => sweep.rows.reduce((a: number, r: Record<string, number>) => a + r[k], 0);
out += `\nTotal: ${f(tot('graphs'))} graphs, ${f(tot('pairs'))} (graph, start) pairs, ${tot('fsuMismatch')} exceptions to the matching theorem; ${f(tot('subcubicPairs'))} subcubic starts, ${tot('bnbMismatch')} branch-and-bound mismatches.\n\n`;
out += '**Fewest vertices for a position worth \\*k:**\n\n| k | exact (sweep) | found by local search |\n|---:|---:|---:|\n';
const ks = new Set<number>([...sweep.smallest.map((w: { value: number }) => w.value), ...smallest.map((s) => s.k)]);
for (const k of [...ks].sort((a, b) => a - b)) {
  const w = sweep.smallest.find((x: { value: number }) => x.value === k);
  const hits = smallest.filter((s) => s.k === k && s.found && s.recheck === k).map((s) => s.n);
  const misses = smallest.filter((s) => s.k === k && !s.found).map((s) => `${s.n} (none in ${s.seconds.toFixed(0)} s)`);
  const exact = w ? String(w.n) : k === maxV + 1 && hits.includes(sweep.N + 1) ? `${sweep.N + 1} (none ≤ ${sweep.N})` : `> ${sweep.N}`;
  out += `| ${k} | ${exact} | ${[...hits.map(String), ...misses].join(', ')} |\n`;
}
out += '\nA tree needs 2^k vertices (its root needs subtrees worth 0, …, k−1).\n';

const readme = readFileSync('README.md', 'utf8');
const a = readme.indexOf('<!-- results:start -->');
const b = readme.indexOf('<!-- results:end -->');
writeFileSync('README.md', `${readme.slice(0, a)}<!-- results:start -->\n${out}<!-- results:end -->${readme.slice(b + '<!-- results:end -->'.length)}`);
console.log(out);
