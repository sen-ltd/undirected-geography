import { describe, it, expect } from 'vitest';
import {
  Solver, fullSet, without, wins, winningMoves, graphFromEdges, maximumMatching, matchingNumber, grundyAt, type Graph,
} from '../src/geography.ts';
import { starTree, reduction, directedWins, nimberConstruction, AS_DRAWN, AS_PRINTED, type Digraph } from '../src/constructions.ts';
import { boards, mulberry32, randomSubcubic, smallestStar3, petersen, dodecahedron } from '../src/presets.ts';
import { connectedGraphs } from '../tools/graphs.mts';

function randomGraph(n: number, p: number, rnd: () => number): Graph {
  const es: [number, number][] = [];
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) if (rnd() < p) es.push([a, b]);
  return graphFromEdges(n, es);
}

/** Matching number by exhaustive recursion on bitmasks (no blossoms). */
function nuBrute(g: Graph): number {
  const memo = new Map<number, number>();
  const rec = (mask: number): number => {
    if (mask === 0) return 0;
    const hit = memo.get(mask);
    if (hit !== undefined) return hit;
    const i = 31 - Math.clz32(mask & -mask);
    const rest = mask & ~(1 << i);
    let best = rec(rest);
    for (const j of g.adj[i]) if (rest & (1 << j)) best = Math.max(best, 1 + rec(rest & ~(1 << j)));
    memo.set(mask, best);
    return best;
  };
  return rec((1 << g.n) - 1);
}

describe('maximum matching', () => {
  it("Edmonds' algorithm agrees with exhaustive search and returns a valid matching", () => {
    const rnd = mulberry32(5);
    for (let k = 0; k < 300; k++) {
      const n = 2 + Math.floor(rnd() * 13);
      const g = randomGraph(n, 0.1 + rnd() * 0.5, rnd);
      const mate = maximumMatching(g, fullSet(n));
      for (let v = 0; v < n; v++) if (mate[v] >= 0) {
        expect(mate[mate[v]]).toBe(v);
        expect(g.adj[v]).toContain(mate[v]);
      }
      expect(matchingNumber(g, fullSet(n))).toBe(nuBrute(g));
    }
  });
  it('handles odd cycles (blossoms)', () => {
    // two triangles joined by a path: ν = 3
    const g = graphFromEdges(7, [[0, 1], [1, 2], [2, 0], [2, 3], [3, 4], [4, 5], [5, 6], [6, 4]]);
    expect(matchingNumber(g, fullSet(7))).toBe(3);
    expect(matchingNumber(petersen(), fullSet(10))).toBe(5);
    expect(matchingNumber(dodecahedron(), fullSet(20))).toBe(10);
  });
});

describe('Fraenkel–Scheinerman–Ullman', () => {
  it('the player to move wins iff the token is in every maximum matching', () => {
    const rnd = mulberry32(11);
    for (let k = 0; k < 250; k++) {
      const n = 1 + Math.floor(rnd() * 12);
      const g = randomGraph(n, 0.15 + rnd() * 0.4, rnd);
      const s = Math.floor(rnd() * n);
      const alive = without(fullSet(n), s);
      expect(wins(g, alive, s)).toBe(new Solver(g).grundy(alive, s) > 0);
    }
  });
  it('the matching moves lead to positions of value 0', () => {
    const rnd = mulberry32(12);
    for (let k = 0; k < 120; k++) {
      const n = 4 + Math.floor(rnd() * 10);
      const g = randomGraph(n, 0.3, rnd);
      const s = Math.floor(rnd() * n);
      const alive = without(fullSet(n), s);
      const sv = new Solver(g);
      const exactWinning = sv.options(alive, s).filter((o) => o.value === 0).map((o) => o.to);
      expect(winningMoves(g, alive, s).sort()).toEqual(exactWinning.sort());
    }
  });
  it('a perfect matching means the first player wins from every vertex', () => {
    const g = petersen();
    for (let s = 0; s < 10; s++) expect(grundyAt(g, s)).toBeGreaterThan(0);
  });
});

describe('Grundy values', () => {
  it('only the component of the token matters', () => {
    const a = graphFromEdges(4, [[0, 1], [0, 2], [1, 3]]);
    const b = graphFromEdges(9, [[0, 1], [0, 2], [1, 3], [4, 5], [5, 6], [6, 7], [7, 8], [8, 4]]);
    expect(grundyAt(a, 0)).toBe(2);
    expect(grundyAt(b, 0)).toBe(2);
  });
  it('t(k) is worth *k with 2^k vertices', () => {
    for (let k = 0; k <= 7; k++) {
      const { g, s } = starTree(k);
      expect(g.n).toBe(2 ** k);
      expect(grundyAt(g, s)).toBe(k);
    }
  });
  it('the smallest witnesses: *3 on 6 vertices, *4 on 8, *5 on 10', () => {
    expect(grundyAt(smallestStar3(), 0)).toBe(3);
    const w4 = graphFromEdges(8, [[0, 1], [0, 2], [0, 3], [0, 7], [1, 4], [1, 5], [1, 7], [2, 6], [2, 7], [4, 7]]);
    expect(grundyAt(w4, 0)).toBe(4);
    const w5 = graphFromEdges(10, [[0, 1], [0, 6], [0, 9], [1, 2], [1, 3], [1, 5], [1, 6], [1, 8], [2, 5], [3, 5], [3, 9], [4, 5], [4, 6], [4, 7], [4, 9], [5, 6], [5, 9], [6, 7], [6, 9]]);
    expect(grundyAt(w5, 9)).toBe(5);
  });
});

describe('branch-and-bound on maximum degree 3', () => {
  it('agrees with exact search', () => {
    const rnd = mulberry32(21);
    for (let k = 0; k < 120; k++) {
      const n = 6 + Math.floor(rnd() * 16);
      const g = randomSubcubic(n, rnd);
      const s = Math.floor(rnd() * n);
      const sv = new Solver(g);
      const alive = without(fullSet(n), s);
      expect(sv.branchAndBound(alive, s)).toBe(sv.grundy(alive, s));
    }
  });
  it('returns null when a vertex has four options', () => {
    const g = graphFromEdges(5, [[0, 1], [0, 2], [0, 3], [0, 4]]);
    expect(new Solver(g).branchAndBound(without(fullSet(5), 0), 0)).toBeNull();
  });
});

describe('Burke–Ferland–Teng constructions', () => {
  it('the edge gadget: r(G, s) is * iff (G, s) is lost in directed Geography', () => {
    const digraphs: Digraph[] = [];
    const pairs: [number, number][] = [[0, 1], [1, 0], [0, 2], [2, 0], [1, 2], [2, 1]];
    for (let m = 0; m < 64; m++) digraphs.push({ n: 3, arcs: pairs.filter((_, i) => m & (1 << i)) });
    for (const d of digraphs)
      for (let s = 0; s < 3; s++) {
        const { g, s: s2 } = reduction(d, s);
        const x = grundyAt(g, s2);
        expect(x === 1).toBe(!directedWins(d, s));
        expect(x).toBeGreaterThan(0);
        const pre = reduction(d, s, true);
        expect(grundyAt(pre.g, pre.s)).toBe(x === 1 ? 1 : 2);
      }
  });
  it('the high-nimber construction gives *n as drawn, not as printed', () => {
    const drawn = [4, 5, 6, 7].map((n) => {
      const { g, s } = nimberConstruction(n, AS_DRAWN);
      return grundyAt(g, s);
    });
    const printed = [4, 5, 6, 7].map((n) => {
      const { g, s } = nimberConstruction(n, AS_PRINTED);
      return grundyAt(g, s);
    });
    expect(drawn).toEqual([4, 5, 6, 7]);
    expect(printed).toEqual([0, 1, 2, 1]);
  });
  it('vertex count of the construction as drawn is 5n² − 15n − 4', () => {
    for (let n = 4; n <= 9; n++) expect(nimberConstruction(n, AS_DRAWN).g.n).toBe(5 * n * n - 15 * n - 4);
  });
});

describe('graphs and boards', () => {
  it('connected graphs up to 7 vertices match OEIS A001349', () => {
    expect(connectedGraphs(7).map((x) => x.length)).toEqual([0, 1, 1, 2, 6, 21, 112, 853]);
  });
  it('every demo board evaluates its start position within the demo budget', () => {
    for (const b of boards()) {
      const sv = new Solver(b.g, 400_000);
      const x = sv.grundy(without(fullSet(b.g.n), b.start), b.start);
      expect(x > 0).toBe(wins(b.g, without(fullSet(b.g.n), b.start), b.start));
      expect(b.xy.length).toBe(b.g.n);
    }
  });
});
