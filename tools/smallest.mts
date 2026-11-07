// Upper bounds for "the fewest vertices a position of value *k can have", beyond the
// exhaustive sweep (tools/sweep.mts proves the lower bounds up to 9 vertices).
//
//   node tools/smallest.mts <k> <n> <seconds> [seed]   → appends to runs/smallest.jsonl
//
// Local search over graphs on n vertices: flip one edge at a time and keep the flip
// unless the score drops. Score = (largest Grundy value of any start, how many starts
// reach it, sum of all start values). Every reported witness is re-checked by
// Solver.grundy in src/ (an independent implementation from the bitmask DP here).
import { appendFileSync, mkdirSync } from 'node:fs';
import { Solver, fullSet, without, graphFromEdges } from '../src/geography.ts';
import { mulberry32 } from '../src/presets.ts';

const K = Number(process.argv[2] ?? 5);
const N = Number(process.argv[3] ?? 10);
const SECONDS = Number(process.argv[4] ?? 60);
const SEED = Number(process.argv[5] ?? 1);
mkdirSync('runs', { recursive: true });
const rnd = mulberry32(SEED * 7919 + N * 31 + K);
const size = 1 << N;
const memo = new Int8Array(size * N);

function values(g: number[]): number[] {
  memo.fill(-1);
  const grundy = (A: number, v: number): number => {
    const idx = A * N + v;
    if (memo[idx] >= 0) return memo[idx];
    let seen = 0;
    let nb = g[v] & A;
    while (nb) {
      const u = 31 - Math.clz32(nb & -nb);
      nb &= nb - 1;
      seen |= 1 << grundy(A & ~(1 << u), u);
    }
    let m = 0;
    while (seen & (1 << m)) m++;
    memo[idx] = m;
    return m;
  };
  return Array.from({ length: N }, (_, s) => grundy((size - 1) & ~(1 << s), s));
}
const score = (vals: number[]): number[] => {
  const mx = Math.max(...vals);
  return [mx, vals.filter((x) => x === mx).length, vals.reduce((a, b) => a + b, 0)];
};
const cmp = (a: number[], b: number[]) => (a[0] - b[0]) || (a[1] - b[1]) || (a[2] - b[2]);

const t0 = Date.now();
let restarts = 0, evals = 0, found: { edges: [number, number][]; s: number } | null = null;
while (!found && Date.now() - t0 < SECONDS * 1000) {
  restarts++;
  const g = new Array(N).fill(0);
  for (let a = 0; a < N; a++) for (let b = a + 1; b < N; b++) if (rnd() < 0.35) {
    g[a] |= 1 << b;
    g[b] |= 1 << a;
  }
  let cur = score(values(g));
  evals++;
  for (let step = 0; step < 4000 && !found && Date.now() - t0 < SECONDS * 1000; step++) {
    const a = Math.floor(rnd() * N), b = Math.floor(rnd() * N);
    if (a === b) continue;
    g[a] ^= 1 << b;
    g[b] ^= 1 << a;
    const vals = values(g);
    evals++;
    const sc = score(vals);
    if (cmp(sc, cur) >= 0 || rnd() < 0.02) {
      cur = sc;
      if (sc[0] >= K) {
        const edges: [number, number][] = [];
        for (let x = 0; x < N; x++) for (let y = x + 1; y < N; y++) if (g[x] & (1 << y)) edges.push([x, y]);
        found = { edges, s: vals.indexOf(sc[0]) };
      }
    } else {
      g[a] ^= 1 << b;
      g[b] ^= 1 << a;
    }
  }
}
const seconds = (Date.now() - t0) / 1000;
let recheck: number | null = null;
if (found) {
  const G = graphFromEdges(N, found.edges);
  recheck = new Solver(G).grundy(without(fullSet(N), found.s), found.s);
}
const rec = { k: K, n: N, seed: SEED, found: !!found, recheck, ...(found ?? {}), restarts, evals, seconds };
appendFileSync('runs/smallest.jsonl', JSON.stringify(rec) + '\n');
console.log(JSON.stringify(rec));
