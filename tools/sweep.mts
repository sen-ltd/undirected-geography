// Every position whose token component has at most N vertices, i.e. every
// (connected graph, start vertex) pair up to isomorphism of the graph:
//
//   node tools/sweep.mts 9        → runs/sweep.json
//
// For each pair it computes the exact Grundy value by search, and checks
//   - Fraenkel–Scheinerman–Ullman: value > 0  ⇔  ν(G) > ν(G − s), with the matching
//     number ν taken by an exhaustive bitmask recursion (no blossoms involved);
//   - Burke–Ferland–Teng's branch-and-bound on every graph of maximum degree ≤ 3,
//     counting how many winnability tests it uses.
// It also records the smallest graph carrying each nimber, and the counts by value.
import { writeFileSync, mkdirSync } from 'node:fs';
import { connectedGraphs } from './graphs.mts';

const N = Number(process.argv[2] ?? 8);
mkdirSync('runs', { recursive: true });

const popcount = (x: number): number => {
  let c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
};

interface Row {
  n: number;
  graphs: number;
  pairs: number;
  pPairs: number;
  byValue: number[];
  maxValue: number;
  fsuMismatch: number;
  subcubicGraphs: number;
  subcubicPairs: number;
  bnbMismatch: number;
  bnbMaxTests: number;
  bnbTotalTests: number;
  exactNodes: number;
  maxValueSubcubic: number;
  graphsWithAllP: number;
  graphsWithNoP: number;
}

const rows: Row[] = [];
const firstWitness: { value: number; n: number; edges: [number, number][]; s: number; degS: number; m: number }[] = [];
const t0 = Date.now();
const all = connectedGraphs(N);
console.log(`graphs: ${all.map((x) => x.length).join(', ')} (${((Date.now() - t0) / 1000).toFixed(1)} s)`);

for (let n = 1; n <= N; n++) {
  const size = 1 << n;
  const memo = new Int8Array(size * n);
  const nu = new Int8Array(size);
  const row: Row = {
    n, graphs: 0, pairs: 0, pPairs: 0, byValue: [], maxValue: 0, fsuMismatch: 0, subcubicGraphs: 0, subcubicPairs: 0,
    bnbMismatch: 0, bnbMaxTests: 0, bnbTotalTests: 0, exactNodes: 0, maxValueSubcubic: 0, graphsWithAllP: 0, graphsWithNoP: 0,
  };
  for (const g of all[n]) {
    row.graphs++;
    memo.fill(-1);
    // ν(mask) by exhaustive recursion: the lowest vertex is unmatched or matched to a neighbour
    nu[0] = 0;
    for (let mask = 1; mask < size; mask++) {
      const i = 31 - Math.clz32(mask & -mask);
      const rest = mask & ~(1 << i);
      let best = nu[rest];
      let nb = g[i] & rest;
      while (nb) {
        const j = 31 - Math.clz32(nb & -nb);
        nb &= nb - 1;
        const x = 1 + nu[rest & ~(1 << j)];
        if (x > best) best = x;
      }
      nu[mask] = best;
    }
    // grundy(A, v): token on v, A = other vertices still in play
    const grundy = (A: number, v: number): number => {
      const idx = A * n + v;
      if (memo[idx] >= 0) return memo[idx];
      row.exactNodes++;
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
    let tests = 0;
    const win = (A: number, v: number): boolean => {
      tests++;
      return nu[A | (1 << v)] > nu[A];
    };
    const bnb = (A: number, v: number): number => {
      const opts: number[] = [];
      let nb = g[v] & A;
      while (nb) {
        const u = 31 - Math.clz32(nb & -nb);
        nb &= nb - 1;
        opts.push(u);
      }
      if (opts.length === 0) return 0;
      if (opts.length === 1) return win(A & ~(1 << opts[0]), opts[0]) ? 0 : 1;
      if (opts.length === 2) {
        const [a, b] = opts;
        const wa = win(A & ~(1 << a), a);
        const wb = win(A & ~(1 << b), b);
        if (wa && wb) return 0;
        if (!wa && !wb) return 1;
        const w = wa ? a : b;
        return 3 - bnb(A & ~(1 << w), w);
      }
      if (opts.length > 3) throw new Error('degree > 3');
      const s = new Set(opts.map((u) => bnb(A & ~(1 << u), u)));
      let m = 0;
      while (s.has(m)) m++;
      return m;
    };
    const subcubic = g.every((m) => popcount(m) <= 3);
    if (subcubic) row.subcubicGraphs++;
    const full = size - 1;
    let pCount = 0;
    for (let s = 0; s < n; s++) {
      const A = full & ~(1 << s);
      const val = grundy(A, s);
      row.pairs++;
      row.byValue[val] = (row.byValue[val] ?? 0) + 1;
      if (val === 0) {
        row.pPairs++;
        pCount++;
      }
      if (val > row.maxValue) row.maxValue = val;
      const fsu = nu[full] > nu[A];
      if (fsu !== val > 0) row.fsuMismatch++;
      if (subcubic) {
        row.subcubicPairs++;
        tests = 0;
        const b = bnb(A, s);
        if (b !== val) row.bnbMismatch++;
        row.bnbTotalTests += tests;
        if (tests > row.bnbMaxTests) row.bnbMaxTests = tests;
        if (val > row.maxValueSubcubic) row.maxValueSubcubic = val;
      }
      if (!firstWitness.some((w) => w.value === val)) {
        const edges: [number, number][] = [];
        for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) if (g[a] & (1 << b)) edges.push([a, b]);
        firstWitness.push({ value: val, n, edges, s, degS: popcount(g[s]), m: edges.length });
      }
    }
    if (pCount === n) row.graphsWithAllP++;
    if (pCount === 0) row.graphsWithNoP++;
  }
  // among the smallest witnesses, prefer fewest edges (first found is arbitrary)
  rows.push(row);
  console.log(JSON.stringify(row), `${((Date.now() - t0) / 1000).toFixed(1)} s`);
}

// fewest-edge witness for each value at its smallest order
const fewest: typeof firstWitness = [];
for (const w of firstWitness.sort((a, b) => a.value - b.value)) {
  let bestW = w;
  for (const g of all[w.n]) {
    const edges: [number, number][] = [];
    for (let a = 0; a < w.n; a++) for (let b = a + 1; b < w.n; b++) if (g[a] & (1 << b)) edges.push([a, b]);
    if (edges.length >= bestW.m) continue;
    // re-evaluate quickly by brute force on this graph
    const n = w.n;
    const memo = new Map<number, number>();
    const gr = (A: number, v: number): number => {
      const k = A * 16 + v;
      const h = memo.get(k);
      if (h !== undefined) return h;
      let seen = 0;
      for (let u = 0; u < n; u++) if (g[v] & A & (1 << u)) seen |= 1 << gr(A & ~(1 << u), u);
      let m = 0;
      while (seen & (1 << m)) m++;
      memo.set(k, m);
      return m;
    };
    for (let s = 0; s < n; s++) {
      if (gr(((1 << n) - 1) & ~(1 << s), s) === w.value) {
        bestW = { value: w.value, n, edges, s, degS: popcount(g[s]), m: edges.length };
        break;
      }
    }
  }
  fewest.push(bestW);
}

writeFileSync('runs/sweep.json', JSON.stringify({ N, rows, smallest: fewest, seconds: (Date.now() - t0) / 1000 }, null, 1) + '\n');
console.log('smallest:', JSON.stringify(fewest));
