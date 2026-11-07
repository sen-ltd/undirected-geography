// Undirected Vertex Geography.
//
// A position is an undirected graph and a token on one vertex. A move slides the
// token to a neighbour and deletes the vertex it left. Whoever cannot move loses.
//
// Three ways to look at a position live here:
//   - Solver.grundy: the exact Grundy value (nimber) by memoised search. The game
//     only depends on the component of the token, so the memo key is the token and
//     that component.
//   - wins: the Fraenkel–Scheinerman–Ullman (1993) test. The player to move wins
//     iff the token's vertex is in every maximum matching, i.e. iff removing it
//     lowers the matching number. Polynomial (Edmonds' blossom algorithm).
//   - Solver.branchAndBound: Burke–Ferland–Teng (2021, Thm "Following the Winning
//     Way"): on graphs of maximum degree 3 the Grundy value needs only O(n)
//     winnability tests.

export interface Graph {
  n: number;
  adj: number[][];
  labels?: string[];
}

export type Bits = Uint32Array;

export function graphFromEdges(n: number, es: [number, number][], labels?: string[]): Graph {
  const adj: number[][] = Array.from({ length: n }, () => []);
  for (const [a, b] of es) {
    if (a === b || adj[a].includes(b)) continue;
    adj[a].push(b);
    adj[b].push(a);
  }
  for (const ns of adj) ns.sort((x, y) => x - y);
  return labels ? { n, adj, labels } : { n, adj };
}

export function edgesOf(g: Graph): [number, number][] {
  const out: [number, number][] = [];
  for (let v = 0; v < g.n; v++) for (const u of g.adj[v]) if (u > v) out.push([v, u]);
  return out;
}

export function maxDegree(g: Graph): number {
  return g.adj.reduce((m, ns) => Math.max(m, ns.length), 0);
}

// ---------------------------------------------------------------------------
// bitsets
// ---------------------------------------------------------------------------

export function words(n: number): number {
  return (n + 31) >>> 5;
}
export function fullSet(n: number): Bits {
  const b = new Uint32Array(words(n));
  for (let v = 0; v < n; v++) b[v >>> 5] |= 1 << (v & 31);
  return b;
}
export const has = (b: Bits, v: number): boolean => (b[v >>> 5] & (1 << (v & 31))) !== 0;
export function without(b: Bits, ...vs: number[]): Bits {
  const c = b.slice();
  for (const v of vs) c[v >>> 5] &= ~(1 << (v & 31));
  return c;
}
export function members(b: Bits, n: number): number[] {
  const out: number[] = [];
  for (let v = 0; v < n; v++) if (has(b, v)) out.push(v);
  return out;
}
const keyOf = (b: Bits): string => Array.prototype.join.call(b, ',');

/** Vertices of `alive` reachable from v (v itself included, whether or not it is in `alive`). */
export function component(g: Graph, alive: Bits, v: number): Bits {
  const c = new Uint32Array(alive.length);
  c[v >>> 5] |= 1 << (v & 31);
  const stack = [v];
  while (stack.length) {
    const x = stack.pop()!;
    for (const u of g.adj[x]) {
      if (has(alive, u) && !has(c, u)) {
        c[u >>> 5] |= 1 << (u & 31);
        stack.push(u);
      }
    }
  }
  return c;
}

// ---------------------------------------------------------------------------
// maximum matching (Edmonds' blossom algorithm, O(V^3))
// ---------------------------------------------------------------------------

/** A maximum matching of the subgraph induced by `alive`; mate[v] = partner or -1. */
export function maximumMatching(g: Graph, alive: Bits): Int32Array {
  const n = g.n;
  const mate = new Int32Array(n).fill(-1);
  const p = new Int32Array(n);
  const base = new Int32Array(n);
  const used = new Uint8Array(n);
  const blossom = new Uint8Array(n);
  const q = new Int32Array(n);
  const lca = (a0: number, b0: number): number => {
    const seen = new Uint8Array(n);
    let a = a0;
    for (;;) {
      a = base[a];
      seen[a] = 1;
      if (mate[a] === -1) break;
      a = p[mate[a]];
    }
    let b = b0;
    for (;;) {
      b = base[b];
      if (seen[b]) return b;
      b = p[mate[b]];
    }
  };
  const markPath = (v0: number, b: number, child0: number) => {
    let v = v0;
    let child = child0;
    while (base[v] !== b) {
      blossom[base[v]] = blossom[base[mate[v]]] = 1;
      p[v] = child;
      child = mate[v];
      v = p[mate[v]];
    }
  };
  const findPath = (root: number): number => {
    used.fill(0);
    p.fill(-1);
    for (let i = 0; i < n; i++) base[i] = i;
    used[root] = 1;
    let qh = 0;
    let qt = 0;
    q[qt++] = root;
    while (qh < qt) {
      const v = q[qh++];
      for (const to of g.adj[v]) {
        if (!has(alive, to)) continue;
        if (base[v] === base[to] || mate[v] === to) continue;
        if (to === root || (mate[to] !== -1 && p[mate[to]] !== -1)) {
          const cur = lca(v, to);
          blossom.fill(0);
          markPath(v, cur, to);
          markPath(to, cur, v);
          for (let i = 0; i < n; i++) {
            if (has(alive, i) && blossom[base[i]]) {
              base[i] = cur;
              if (!used[i]) {
                used[i] = 1;
                q[qt++] = i;
              }
            }
          }
        } else if (p[to] === -1) {
          p[to] = v;
          if (mate[to] === -1) return to;
          used[mate[to]] = 1;
          q[qt++] = mate[to];
        }
      }
    }
    return -1;
  };
  // greedy start
  for (let v = 0; v < n; v++) {
    if (!has(alive, v) || mate[v] !== -1) continue;
    for (const u of g.adj[v]) {
      if (has(alive, u) && mate[u] === -1) {
        mate[v] = u;
        mate[u] = v;
        break;
      }
    }
  }
  for (let v = 0; v < n; v++) {
    if (!has(alive, v) || mate[v] !== -1) continue;
    let t = findPath(v);
    while (t !== -1) {
      const pv = p[t];
      const ppv = mate[pv];
      mate[t] = pv;
      mate[pv] = t;
      t = ppv;
    }
  }
  return mate;
}

export function matchingNumber(g: Graph, alive: Bits): number {
  const mate = maximumMatching(g, alive);
  let c = 0;
  for (let v = 0; v < g.n; v++) if (mate[v] > v) c++;
  return c;
}

/**
 * Fraenkel–Scheinerman–Ullman: with the token on v and `alive` the other vertices
 * still in the game, the player to move wins iff v lies in every maximum matching of
 * the token's component, i.e. iff deleting v lowers the matching number.
 */
export function wins(g: Graph, alive: Bits, v: number): boolean {
  const c = component(g, alive, v);
  return matchingNumber(g, c) > matchingNumber(g, without(c, v));
}

/** Moves that leave the opponent in a lost position, found with matchings only. */
export function winningMoves(g: Graph, alive: Bits, v: number): number[] {
  const rest = without(alive, v);
  return g.adj[v].filter((u) => has(rest, u) && !wins(g, without(rest, u), u));
}

// ---------------------------------------------------------------------------
// exact Grundy values
// ---------------------------------------------------------------------------

export class BudgetExceeded extends Error {}

export function mex(vals: Iterable<number>): number {
  const s = new Set(vals);
  let m = 0;
  while (s.has(m)) m++;
  return m;
}

export class Solver {
  readonly g: Graph;
  readonly memo = new Map<string, number>();
  nodes = 0;
  matchingCalls = 0;
  budget: number;

  constructor(g: Graph, budget = Infinity) {
    this.g = g;
    this.budget = budget;
  }

  /** Grundy value with the token on v; `alive` = vertices still in play other than v. */
  grundy(alive: Bits, v: number): number {
    const g = this.g;
    const opts: number[] = [];
    for (const u of g.adj[v]) if (has(alive, u)) opts.push(u);
    if (opts.length === 0) return 0;
    const comp = without(component(g, alive, v), v);
    const key = `${v}|${keyOf(comp)}`;
    const hit = this.memo.get(key);
    if (hit !== undefined) return hit;
    if (++this.nodes > this.budget) throw new BudgetExceeded();
    const vals = opts.map((u) => this.grundy(without(comp, u), u));
    const r = mex(vals);
    this.memo.set(key, r);
    return r;
  }

  /** Grundy value of every legal move from (alive, v). */
  options(alive: Bits, v: number): { to: number; value: number }[] {
    const rest = without(alive, v);
    return this.g.adj[v].filter((u) => has(rest, u)).map((u) => ({ to: u, value: this.grundy(without(rest, u), u) }));
  }

  private win(alive: Bits, v: number): boolean {
    this.matchingCalls++;
    return wins(this.g, alive, v);
  }

  /**
   * Burke–Ferland–Teng's branch-and-bound for maximum degree 3. With one option the
   * value is * iff that option is lost for the opponent; with two, [win, win] → 0, [lose, lose] → *, and
   * otherwise 3 − (value of the winning option), which recurses into a single
   * smaller position; with three, the mex of three degree-≤2 positions.
   * Returns null if a vertex with more than three options is met.
   */
  branchAndBound(alive: Bits, v: number): number | null {
    const g = this.g;
    const opts = g.adj[v].filter((u) => has(alive, u));
    if (opts.length === 0) return 0;
    if (opts.length > 3) return null;
    if (opts.length === 1) {
      const u = opts[0];
      return this.win(without(alive, u), u) ? 0 : 1;
    }
    if (opts.length === 2) {
      const [a, b] = opts;
      const wa = this.win(without(alive, a), a);
      const wb = this.win(without(alive, b), b);
      if (wa && wb) return 0;
      if (!wa && !wb) return 1;
      const w = wa ? a : b;
      const x = this.branchAndBound(without(alive, w), w);
      return x === null ? null : 3 - x;
    }
    const vals: number[] = [];
    for (const u of opts) {
      const x = this.branchAndBound(without(alive, u), u);
      if (x === null) return null;
      vals.push(x);
    }
    return mex(vals);
  }
}

/** Grundy value of (g, s) with every vertex in play. */
export function grundyAt(g: Graph, s: number, budget = Infinity): number {
  return new Solver(g, budget).grundy(without(fullSet(g.n), s), s);
}
