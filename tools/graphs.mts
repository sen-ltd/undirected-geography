// Every connected graph on n ≤ 10 vertices up to isomorphism, as adjacency bitmasks.
//
// Graphs on n vertices grow from those on n − 1 by adding a vertex joined to a
// non-empty subset of the old ones. Copies are merged by an exact canonical form:
// vertices are split into cells by iterated degree refinement, then the
// lexicographically least column-major adjacency string over all orderings that
// respect the cells is taken (refinement only prunes orderings; prefixes that are
// already larger than the best are cut). Results are cached in runs/.cache.
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';

export type MaskGraph = number[]; // adj[v] = bitmask of neighbours

const popcount = (x: number): number => {
  let c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
};

function refine(g: MaskGraph): number[] {
  const n = g.length;
  let col = g.map(popcount);
  for (let round = 0; round < n; round++) {
    const sig = g.map((m, v) => {
      const ns: number[] = [];
      for (let u = 0; u < n; u++) if (m & (1 << u)) ns.push(col[u]);
      return `${col[v]}:${ns.sort((a, b) => a - b).join(',')}`;
    });
    const order = [...new Set(sig)].sort();
    const next = sig.map((s) => order.indexOf(s));
    const same = new Set(next).size === new Set(col).size;
    col = next;
    if (same) break;
  }
  return col;
}

export function certificate(g: MaskGraph): string {
  const n = g.length;
  const col = refine(g);
  const cellOf: number[] = [];
  const cells = [...new Set(col)].sort((a, b) => a - b).map((c) => col.map((x, v) => (x === c ? v : -1)).filter((v) => v >= 0));
  cells.forEach((cell, ci) => {
    for (let i = 0; i < cell.length; i++) cellOf.push(ci);
  });
  const total = (n * (n - 1)) / 2;
  const best = new Uint8Array(total).fill(2);
  const cur = new Uint8Array(total);
  const order: number[] = [];
  const used = new Uint8Array(n);
  // position k takes a vertex from cell cellOf[k]; it appends bits (0,k)…(k−1,k)
  let updates = 0;
  // `less` = the prefix placed so far is already smaller than best's prefix. When a
  // leaf below replaces best, the prefix becomes equal to best's, so it is reset.
  const rec = (k: number, lessIn: boolean) => {
    if (k === n) {
      if (lessIn) {
        best.set(cur);
        updates++;
      }
      return;
    }
    let less = lessIn;
    const cell = cells[cellOf[k]];
    const off = (k * (k - 1)) / 2;
    for (const v of cell) {
      if (used[v]) continue;
      let l = less;
      let cut = false;
      for (let i = 0; i < k; i++) {
        const bit = (g[order[i]] >> v) & 1;
        cur[off + i] = bit;
        if (!l) {
          if (bit < best[off + i]) l = true;
          else if (bit > best[off + i]) {
            cut = true;
            break;
          }
        }
      }
      if (cut) continue;
      used[v] = 1;
      order.push(v);
      const before = updates;
      rec(k + 1, l);
      if (updates !== before) less = false;
      order.pop();
      used[v] = 0;
    }
  };
  rec(0, false);
  return `${n}:${col.slice().sort((a, b) => a - b).join('.')}:${best.join('')}`;
}

export function connectedGraphs(maxN: number): MaskGraph[][] {
  mkdirSync('runs/.cache', { recursive: true });
  const out: MaskGraph[][] = [[], [[0]]];
  for (let n = 2; n <= maxN; n++) {
    const cache = `runs/.cache/connected-${n}.txt`;
    if (existsSync(cache)) {
      out.push(readFileSync(cache, 'utf8').trim().split('\n').map((l) => l.split(' ').map((x) => parseInt(x, 36))));
      continue;
    }
    const seen = new Map<string, MaskGraph>();
    for (const h of out[n - 1]) {
      for (let mask = 1; mask < 1 << (n - 1); mask++) {
        const g = h.slice();
        for (let v = 0; v < n - 1; v++) if (mask & (1 << v)) g[v] |= 1 << (n - 1);
        g.push(mask);
        const c = certificate(g);
        if (!seen.has(c)) seen.set(c, g);
      }
    }
    const list = [...seen.values()];
    writeFileSync(cache, list.map((g) => g.map((m) => m.toString(36)).join(' ')).join('\n') + '\n');
    out.push(list);
  }
  return out;
}
