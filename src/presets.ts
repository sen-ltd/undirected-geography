// Boards for the demo and the checks: named graphs with drawing coordinates.
import { type Graph, graphFromEdges } from './geography.ts';
import { nimberConstruction, reduction, starTree, AS_DRAWN, AS_PRINTED, type Digraph } from './constructions.ts';

export interface Board {
  id: string;
  name: string;
  note: string;
  g: Graph;
  start: number;
  xy: [number, number][];
}

export function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export function cube(): Graph {
  const es: [number, number][] = [];
  for (let v = 0; v < 8; v++) for (const b of [1, 2, 4]) if ((v ^ b) > v) es.push([v, v ^ b]);
  return graphFromEdges(8, es);
}

export function petersen(): Graph {
  const es: [number, number][] = [];
  for (let i = 0; i < 5; i++) {
    es.push([i, (i + 1) % 5]);
    es.push([i, i + 5]);
    es.push([5 + i, 5 + ((i + 2) % 5)]);
  }
  return graphFromEdges(10, es);
}

/** The dodecahedron: outer 5-cycle 0–4, middle 10-cycle 5–14, inner 5-cycle 15–19. */
export function dodecahedron(): Graph {
  const es: [number, number][] = [];
  for (let i = 0; i < 5; i++) {
    es.push([i, (i + 1) % 5]);
    es.push([i, 5 + 2 * i]);
    es.push([15 + i, 15 + ((i + 1) % 5)]);
    es.push([15 + i, 5 + 2 * i + 1]);
  }
  for (let i = 0; i < 10; i++) es.push([5 + i, 5 + ((i + 1) % 10)]);
  return graphFromEdges(20, es);
}

export function grid(w: number, h: number): Graph {
  const es: [number, number][] = [];
  for (let y = 0; y < h; y++)
    for (let x = 0; x < w; x++) {
      if (x + 1 < w) es.push([y * w + x, y * w + x + 1]);
      if (y + 1 < h) es.push([y * w + x, (y + 1) * w + x]);
    }
  return graphFromEdges(w * h, es);
}

/** A random graph of maximum degree 3 (random edges added while both ends have room). */
export function randomSubcubic(n: number, rnd: () => number): Graph {
  const deg = new Array(n).fill(0);
  const es: [number, number][] = [];
  const seen = new Set<string>();
  for (let tries = 0; tries < n * 12; tries++) {
    const a = Math.floor(rnd() * n), b = Math.floor(rnd() * n);
    if (a === b || deg[a] >= 3 || deg[b] >= 3) continue;
    const k = a < b ? `${a},${b}` : `${b},${a}`;
    if (seen.has(k)) continue;
    seen.add(k);
    deg[a]++;
    deg[b]++;
    es.push([a, b]);
  }
  return graphFromEdges(n, es);
}

// ---------------------------------------------------------------------------
// layout
// ---------------------------------------------------------------------------

const circle = (n: number, r = 0.42, phase = -Math.PI / 2, cx = 0.5, cy = 0.5): [number, number][] =>
  Array.from({ length: n }, (_, i) => [cx + r * Math.cos(phase + (2 * Math.PI * i) / n), cy + r * Math.sin(phase + (2 * Math.PI * i) / n)]);

/** Force-directed layout in [0,1]^2 (deterministic). */
export function springLayout(g: Graph, seed = 1, init?: [number, number][], iters = 400): [number, number][] {
  const rnd = mulberry32(seed);
  const n = g.n;
  const p: [number, number][] = init ? init.map((q) => [q[0], q[1]]) : Array.from({ length: n }, () => [rnd(), rnd()]);
  const k = Math.sqrt(1 / Math.max(n, 1)) * 0.9;
  for (let it = 0; it < iters; it++) {
    const t = 0.08 * (1 - it / iters) + 0.002;
    const d: [number, number][] = p.map(() => [0, 0]);
    for (let i = 0; i < n; i++)
      for (let j = i + 1; j < n; j++) {
        let dx = p[i][0] - p[j][0], dy = p[i][1] - p[j][1];
        let dist = Math.hypot(dx, dy);
        if (dist < 1e-6) {
          dx = rnd() - 0.5;
          dy = rnd() - 0.5;
          dist = 1e-3;
        }
        const f = (k * k) / dist;
        d[i][0] += (dx / dist) * f;
        d[i][1] += (dy / dist) * f;
        d[j][0] -= (dx / dist) * f;
        d[j][1] -= (dy / dist) * f;
      }
    for (let i = 0; i < n; i++)
      for (const j of g.adj[i]) {
        if (j < i) continue;
        const dx = p[i][0] - p[j][0], dy = p[i][1] - p[j][1];
        const dist = Math.max(Math.hypot(dx, dy), 1e-6);
        const f = (dist * dist) / k;
        d[i][0] -= (dx / dist) * f;
        d[i][1] -= (dy / dist) * f;
        d[j][0] += (dx / dist) * f;
        d[j][1] += (dy / dist) * f;
      }
    for (let i = 0; i < n; i++) {
      const len = Math.max(Math.hypot(d[i][0], d[i][1]), 1e-9);
      p[i][0] += (d[i][0] / len) * Math.min(len, t);
      p[i][1] += (d[i][1] / len) * Math.min(len, t);
    }
  }
  return normalise(p);
}

function normalise(p: [number, number][]): [number, number][] {
  const xs = p.map((q) => q[0]), ys = p.map((q) => q[1]);
  const x0 = Math.min(...xs), x1 = Math.max(...xs), y0 = Math.min(...ys), y1 = Math.max(...ys);
  const s = Math.max(x1 - x0, y1 - y0, 1e-9);
  return p.map(([x, y]) => [0.06 + (0.88 * (x - x0 + (s - (x1 - x0)) / 2)) / s, 0.06 + (0.88 * (y - y0 + (s - (y1 - y0)) / 2)) / s]);
}

/** Layered drawing of a rooted tree. */
function treeLayout(g: Graph, root: number): [number, number][] {
  const depth = new Array(g.n).fill(-1);
  const kids: number[][] = Array.from({ length: g.n }, () => []);
  depth[root] = 0;
  const q = [root];
  while (q.length) {
    const v = q.shift()!;
    for (const u of g.adj[v]) if (depth[u] < 0) {
      depth[u] = depth[v] + 1;
      kids[v].push(u);
      q.push(u);
    }
  }
  const xy: [number, number][] = new Array(g.n).fill(null).map(() => [0, 0]);
  let leaf = 0;
  const place = (v: number): number => {
    if (kids[v].length === 0) {
      xy[v] = [leaf++, depth[v]];
      return xy[v][0];
    }
    const xs = kids[v].map(place);
    xy[v] = [(Math.min(...xs) + Math.max(...xs)) / 2, depth[v]];
    return xy[v][0];
  };
  place(root);
  return normalise(xy);
}

// ---------------------------------------------------------------------------
// the demo boards
// ---------------------------------------------------------------------------

/** The smallest graph with a *3 start (6 vertices; a tree needs 8). Found by tools/sweep.mts. */
export function smallestStar3(): Graph {
  return graphFromEdges(6, [[0, 1], [0, 2], [0, 3], [1, 4], [1, 5], [2, 5]]);
}

export function boards(): Board[] {
  const out: Board[] = [];
  const add = (id: string, name: string, note: string, g: Graph, start: number, xy?: [number, number][]) =>
    out.push({ id, name, note, g, start, xy: xy ?? springLayout(g, 7) });

  {
    const g = grid(5, 4);
    add('grid', '5 × 4 grid', 'A grid. The matching tells who wins from every vertex; the search gives the nimbers.', g, 0,
      Array.from({ length: 20 }, (_, i) => [0.12 + (i % 5) * 0.19, 0.18 + Math.floor(i / 5) * 0.21] as [number, number]));
  }
  add('dodecahedron', 'Dodecahedron', 'Dual of the icosahedron, a triangulation: degree 3, so the branch-and-bound needs only matchings.', dodecahedron(), 0,
    (() => {
      const o = circle(5, 0.44), m = circle(10, 0.31, -Math.PI / 2), inn = circle(5, 0.16, -Math.PI / 2 + Math.PI / 5);
      const xy: [number, number][] = [...o];
      for (let i = 0; i < 10; i++) xy.push(m[i]);
      for (let i = 0; i < 5; i++) xy.push(inn[i]);
      return xy;
    })());
  add('petersen', 'Petersen graph', 'Every vertex looks the same; a perfect matching exists, so the first player wins from anywhere.', petersen(), 0,
    [...circle(5, 0.42), ...circle(5, 0.2)]);
  {
    const { g, s } = starTree(4);
    add('tree4', 't(4): tree of value *4', 'Observation in Burke–Ferland–Teng: a tree needs 2^k vertices for *k.', g, s, treeLayout(g, s));
  }
  add('small3', 'smallest *3 (6 vertices)', 'Found by searching every connected graph: *3 needs 6 vertices, a tree needs 8.', smallestStar3(), 0);
  {
    // Lichtenstein–Sipser-style digraph: a directed triangle with a chord, reduced
    const d: Digraph = { n: 3, arcs: [[0, 1], [1, 2], [2, 0], [0, 2]] };
    const { g, s } = reduction(d, 0, true);
    add('gadget', 'directed edges made undirected', 'The reduction: each arc x → y becomes a 10-vertex gadget that cannot be crossed backwards profitably. Start value is * iff the directed game is lost.', g, s, springLayout(g, 3, undefined, 600));
  }
  {
    const { g, s } = nimberConstruction(6, AS_DRAWN);
    add('nim6', 'value *6 (construction, as drawn)', 'Section 5 construction with every edge the figures show: the token on N6 has value *6.', g, s, springLayout(g, 11, undefined, 700));
  }
  {
    const { g, s } = nimberConstruction(6, AS_PRINTED);
    add('nim6p', 'value *6? (Algorithm 1, as printed)', 'Algorithm 1 exactly as printed. It omits N_i–M_i, N_i–P_i, N_4–R_4 and the *3 tree on N_4; the token on N6 is worth *2.', g, s, springLayout(g, 11, undefined, 700));
  }
  {
    const rnd = mulberry32(42);
    const n = 14;
    const es: [number, number][] = [];
    for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) if (rnd() < 0.22) es.push([a, b]);
    add('random', 'random graph (14 vertices)', 'A random graph.', graphFromEdges(n, es), 0);
  }
  return out;
}
