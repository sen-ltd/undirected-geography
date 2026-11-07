// Recompute the checkable claims of
//
//   [BFT21] K. W. Burke, M. Ferland, S.-H. Teng, "Winning the War by (Strategically)
//           Losing Battles: Settling the Complexity of Grundy-Values in Undirected
//           Geography", FOCS 2021, arXiv:2106.02114 (read from the TeX source)
//   [FSU93] A. S. Fraenkel, E. R. Scheinerman, D. Ullman, "Undirected edge
//           geography", Theoret. Comput. Sci. 112 (1993) — the matching theorem as
//           restated in [BFT21, appendix "Winning Undirected Geography by Matching"]
//
//   node tools/verify.mts [maxN]      → runs/literature.json
//
// Every value below is an exact Grundy value from Solver.grundy (memoised search,
// no matchings); matchings appear only where a claim is about them.
import { writeFileSync, mkdirSync } from 'node:fs';
import {
  Solver, fullSet, without, wins, winningMoves, graphFromEdges, maxDegree, has, BudgetExceeded, type Graph, type Bits,
} from '../src/geography.ts';
import {
  starTree, reduction, directedWins, nimberConstruction, AS_PRINTED, AS_DRAWN, type Digraph, type Variant,
} from '../src/constructions.ts';
import { dodecahedron, cube, petersen, randomSubcubic, mulberry32 } from '../src/presets.ts';

mkdirSync('runs', { recursive: true });
const MAXN = Number(process.argv[2] ?? 9);

interface Item { id: string; where: string; claim: string; got: string; ok: boolean; note?: string }
const items: Item[] = [];
function check(id: string, where: string, claim: string, ok: boolean, got: string, note?: string): void {
  items.push({ id, where, claim, got, ok, ...(note ? { note } : {}) });
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${id} ${where}: ${claim} → ${got}${note ? ` (${note})` : ''}`);
}
const star = (k: number) => (k === 0 ? '0' : k === 1 ? '*' : `*${k}`);
const t0 = Date.now();
const value = (g: Graph, alive: Bits, v: number, sv = new Solver(g)) => sv.grundy(without(alive, v), v);

// ---------------------------------------------------------------------------
// Observation "Logarithmic nimber in trees": t(k) has 2^k vertices, maximum degree k, value *k
// ---------------------------------------------------------------------------
{
  const got: string[] = [];
  let ok = true;
  for (let k = 0; k <= 10; k++) {
    const { g, s } = starTree(k);
    const x = value(g, fullSet(g.n), s);
    const deg = g.adj[s].length;
    got.push(`t(${k}): ${g.n} vertices, deg ${deg}, ${star(x)}`);
    ok &&= x === k && g.n === 2 ** k && deg === k;
  }
  check('obs-tree', '[BFT21] Obs. "Logarithmic nimber in trees"', 't(k) has 2^k vertices, root degree k, value *k (k ≤ 10)', ok, got.slice(-3).join('; '));
}

// ---------------------------------------------------------------------------
// The reduction of Thm "Complexity Separation" with the edge gadget, the lemmas
// "Wrong Way" and "Correct Way", and the prelude corollary, on every digraph with up to 3 vertices and a sample of 4
// ---------------------------------------------------------------------------
{
  const digraphs: Digraph[] = [];
  for (let n = 1; n <= 3; n++) {
    const pairs: [number, number][] = [];
    for (let x = 0; x < n; x++) for (let y = 0; y < n; y++) if (x !== y) pairs.push([x, y]);
    for (let m = 0; m < 1 << pairs.length; m++) digraphs.push({ n, arcs: pairs.filter((_, i) => m & (1 << i)) });
  }
  {
    const rnd = mulberry32(387);
    const pairs: [number, number][] = [];
    for (let x = 0; x < 4; x++) for (let y = 0; y < 4; y++) if (x !== y) pairs.push([x, y]);
    for (let k = 0; k < 400; k++) digraphs.push({ n: 4, arcs: pairs.filter(() => rnd() < 0.45) });
  }
  let positions = 0;
  let thm = 0, wrong = 0, correct = 0, prelude = 0, gadgets = 0, gadgetChecks = 0;
  const wrongVals = new Set<number>();
  let maxV = 0;
  for (const d of digraphs) {
    for (let s = 0; s < d.n; s++) {
      positions++;
      const P = !directedWins(d, s);
      const { g, s: s2 } = reduction(d, s);
      maxV = Math.max(maxV, g.n);
      const sv = new Solver(g);
      const full = fullSet(g.n);
      const x = sv.grundy(without(full, s2), s2);
      if ((x === 1) === P && x > 0) thm++;
      const pre = reduction(d, s, true);
      const xp = value(pre.g, fullSet(pre.g.n), pre.s);
      if (xp === (x === 1 ? 1 : 2)) prelude++;
    }
    // Lemmas, once per digraph (they do not depend on s)
    const { g } = reduction(d, 0);
    const sv = new Solver(g);
    const full = fullSet(g.n);
    const lab = (k: number, x: string) => g.labels!.indexOf(`e${k}.${x}`);
    d.arcs.forEach(([x, y], k) => {
      gadgets++;
      const vx = g.labels!.indexOf(`v${x}`), vy = g.labels!.indexOf(`v${y}`);
      const a = lab(k, 'a'), b = lab(k, 'b'), c = lab(k, 'c'), dd = lab(k, 'd');
      // Lemma 3.2 (Wrong Way): (G'_y, d) ∈ {*2, *3}
      const w = sv.grundy(without(full, vy, dd), dd);
      wrongVals.add(w);
      if (w === 2 || w === 3) wrong++;
      // Lemma 3.3 (Correct Way): (G'_x, a) = *  ⇔  y reached through the gadget is *
      const atA = sv.grundy(without(full, vx, a), a);
      const atY = sv.grundy(without(full, vx, a, b, c, dd, vy), vy);
      gadgetChecks++;
      if ((atA === 1) === (atY === 1)) correct++;
    });
  }
  check('thm-reduction', '[BFT21] Thm "Complexity Separation"', 'r(G,s) = * if (G,s) ∈ P, and ∈ N \\ {*} if (G,s) ∈ N', thm === positions,
    `${thm} / ${positions} positions (every digraph on ≤ 3 vertices, 400 random on 4; reduced graphs up to ${maxV} vertices)`);
  check('lem-wrong-way', '[BFT21] Lemma "Wrong Way"', 'moving y → d gives *2 or *3', wrong === gadgets,
    `${wrong} / ${gadgets} gadgets; values seen: ${[...wrongVals].sort().map(star).join(', ')}`);
  check('lem-correct-way', '[BFT21] Lemma "Correct Way"', 'd → y is * exactly when x → a is *', correct === gadgetChecks, `${correct} / ${gadgetChecks} gadgets`);
  check('cor-prelude', '[BFT21] Cor. (prelude gadget)', 'with the prelude, start is * if s is *, else *2', prelude === positions, `${prelude} / ${positions}`);
}

// ---------------------------------------------------------------------------
// Thm "Following the Winning Way": branch-and-bound = exact on max degree 3
// ---------------------------------------------------------------------------
{
  const rnd = mulberry32(2106);
  let n0 = 0, agree = 0, maxCalls = 0, maxNodes = 0;
  const per: string[] = [];
  for (const n of [12, 16, 20, 24, 28]) {
    let calls = 0, nodes = 0, cnt = 0;
    for (let k = 0; k < 40; k++) {
      const g = randomSubcubic(n, rnd);
      const s = Math.floor(rnd() * n);
      const sv = new Solver(g);
      const exact = sv.grundy(without(fullSet(n), s), s);
      const bb = sv.branchAndBound(without(fullSet(n), s), s);
      n0++;
      cnt++;
      if (bb === exact) agree++;
      calls += sv.matchingCalls;
      nodes += sv.nodes;
      maxCalls = Math.max(maxCalls, sv.matchingCalls);
      maxNodes = Math.max(maxNodes, sv.nodes);
    }
    per.push(`n=${n}: ${(calls / cnt).toFixed(1)} winnability tests vs ${(nodes / cnt).toFixed(0)} search nodes`);
  }
  check('thm-bnb-random', '[BFT21] Thm "Following the Winning Way"', 'branch-and-bound equals the Grundy value on max-degree-3 graphs', agree === n0,
    `${agree} / ${n0} random subcubic graphs, n = 12…28; ${per.join('; ')}`);
  const named: [string, Graph][] = [['cube', cube()], ['Petersen', petersen()], ['dodecahedron', dodecahedron()]];
  const got: string[] = [];
  let ok = true;
  for (const [nm, g] of named) {
    const sv = new Solver(g);
    const exact = sv.grundy(without(fullSet(g.n), 0), 0);
    const bb = sv.branchAndBound(without(fullSet(g.n), 0), 0);
    ok &&= exact === bb;
    got.push(`${nm} ${star(exact)} (${sv.matchingCalls} tests, ${sv.nodes} nodes)`);
  }
  check('cor-dual-triangulation', '[BFT21] Cor. "Alternation Paths"', 'duals of triangulations (cube, dodecahedron; also Petersen): branch-and-bound = exact', ok, got.join('; '));
}

// ---------------------------------------------------------------------------
// [FSU93] as restated in [BFT21, appendix]: the matching strategy wins in actual play
// ---------------------------------------------------------------------------
{
  const rnd = mulberry32(1993);
  let games = 0, ok = 0;
  for (let k = 0; k < 300; k++) {
    const n = 8 + Math.floor(rnd() * 10);
    const es: [number, number][] = [];
    for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) if (rnd() < 0.3) es.push([a, b]);
    const g = graphFromEdges(n, es);
    const s = Math.floor(rnd() * n);
    let alive = without(fullSet(n), s);
    if (!wins(g, alive, s)) continue;
    games++;
    // winner follows the matching, loser plays at random; the winner must never get stuck
    let v = s, turn = 0, stuckWinner = false;
    for (;;) {
      const moves = g.adj[v].filter((u) => has(alive, u));
      if (moves.length === 0) {
        stuckWinner = turn === 0;
        break;
      }
      const u = turn === 0 ? winningMoves(g, alive, v)[0] : moves[Math.floor(rnd() * moves.length)];
      if (u === undefined) {
        stuckWinner = true;
        break;
      }
      alive = without(alive, u);
      v = u;
      turn ^= 1;
    }
    if (!stuckWinner) ok++;
  }
  check('fsu-play', '[FSU93] / [BFT21] Thm "A Matching-Based Characterization"', 'from a winning start, moving along a maximum matching never loses', ok === games,
    `${ok} / ${games} random games (8–17 vertices, opponent random)`);
}

// ---------------------------------------------------------------------------
// Section 5: the nimber construction, as printed (Algorithm 1) and as drawn
// ---------------------------------------------------------------------------
const construction: Record<string, unknown>[] = [];
{
  const variants: [string, Variant][] = [
    ['as drawn (figures)', AS_DRAWN],
    ['as printed (Algorithm 1)', AS_PRINTED],
    ['Alg. 1 + N_i–M_i, N_i–P_i', { nmp: true, n4r4: false, tree3: false }],
    ['Alg. 1 + N_4–R_4', { nmp: false, n4r4: true, tree3: false }],
    ['Alg. 1 + *3 on N_4', { nmp: false, n4r4: false, tree3: true }],
    ['drawn − N_4–R_4', { nmp: true, n4r4: false, tree3: true }],
    ['drawn − *3 on N_4', { nmp: true, n4r4: true, tree3: false }],
    ['drawn − N_i–M_i, N_i–P_i', { nmp: false, n4r4: true, tree3: true }],
  ];
  for (const [name, vt] of variants) {
    const vals: (number | null)[] = [];
    for (let n = 4; n <= MAXN; n++) {
      const { g, s } = nimberConstruction(n, vt);
      const sv = new Solver(g, 3e7);
      const t = Date.now();
      let x: number | null = null;
      try {
        x = sv.grundy(without(fullSet(g.n), s), s);
      } catch (e) {
        if (!(e instanceof BudgetExceeded)) throw e;
      }
      vals.push(x);
      construction.push({ variant: name, n, vertices: g.n, edges: g.adj.reduce((a, b) => a + b.length, 0) / 2, maxDegree: maxDegree(g), value: x, nodes: sv.nodes, ms: Date.now() - t });
      console.log(`  ${name} n=${n}: ${g.n} vertices, value ${x === null ? '?' : star(x)}, ${sv.nodes} nodes, ${Date.now() - t} ms`);
      if (x === null) break;
    }
    if (name.startsWith('as drawn')) {
      const ok = vals.every((x, i) => x === i + 4);
      check('thm-constructability', '[BFT21] Thm "Right Amount of Stars"', 'the token on N_n has value *n (construction as drawn)', ok,
        vals.map((x, i) => `n=${i + 4}: ${x === null ? '?' : star(x)}`).join(', '));
    }
    if (name.startsWith('as printed')) {
      const ok = vals.every((x, i) => x === i + 4);
      check('alg-1', '[BFT21] Algorithm 1', 'Algorithm 1 as printed yields *n at N_n', ok, vals.map((x, i) => `n=${i + 4}: ${x === null ? '?' : star(x)}`).join(', '),
        ok ? undefined : 'Algorithm 1 never adds the edges N_i–M_i, N_i–P_i, the edge N_4–R_4 or a *3 tree on N_4; the figures and lemmas use all three');
    }
  }
}

// ---------------------------------------------------------------------------
// The lemmas of Section 5 on the construction as drawn: every set of removed N vertices
// ---------------------------------------------------------------------------
{
  const n = Math.min(MAXN, 8);
  const { g, N } = nimberConstruction(n, AS_DRAWN);
  const sv = new Solver(g);
  const full = fullSet(g.n);
  const id = (l: string) => g.labels!.indexOf(l);
  const ranks = [...N.keys()];
  let grounded = 0, groundedN = 0, rToN = 0, rToNN = 0, mOK = 0, mN = 0, pOK = 0, pN = 0, parOK = 0, parN = 0, ihOK = 0, ihN = 0, n12 = 0, n12N = 0;
  const parityFails: string[] = [];
  for (let mask = 0; mask < 1 << ranks.length; mask++) {
    const removed = ranks.filter((_, i) => mask & (1 << i));
    const base = without(full, ...removed.map((r) => N.get(r)!));
    for (const k of ranks) {
      if (removed.includes(k)) continue;
      const Nk = N.get(k)!;
      const Rk = id(`R${k}`);
      // Lemma 5.2 (Grounded): N_k → R_k is a move to 0
      groundedN++;
      if (sv.grundy(without(base, Nk, Rk), Rk) === 0) grounded++;
      // Lemma 5.3: R_k → N_k is a move to 0 (R_k left behind)
      rToNN++;
      if (sv.grundy(without(base, Rk, Nk), Nk) === 0) rToN++;
      const lowerRemoved = removed.some((r) => r < k);
      if (k >= 5) {
        // Lemma 5.4 (Skip *2): N_k → M_k is * iff no lower N removed, else *3
        const Mk = id(`M${k}`), Pk = id(`P${k}`);
        mN++;
        if (sv.grundy(without(base, Nk, Mk), Mk) === (lowerRemoved ? 3 : 1)) mOK++;
        // Lemma 5.5 (Skip *): P_k is *2 iff no lower N removed, else *3
        pN++;
        if (sv.grundy(without(base, Nk, Pk), Pk) === (lowerRemoved ? 3 : 2)) pOK++;
      }
      const val = sv.grundy(without(base, Nk), Nk);
      if (!removed.some((r) => r <= k)) {
        // Lemma 5.6: only higher N removed → at least *4; Thm 5.8's induction: exactly *k
        n12N++;
        if (val >= 4) n12++;
        ihN++;
        if (val === k) ihOK++;
      }
      const lowerList = removed.filter((r) => r < k);
      if (lowerList.length) {
        // Lemma 5.7 (Parity): j = lowest removed rank; count remaining N_p with p > j (token included)
        const j = Math.min(...lowerList);
        const remaining = ranks.filter((p) => p > j && !removed.includes(p)).length;
        parN++;
        const want = remaining % 2 === 1 ? 1 : 2;
        if (val === want) parOK++;
        else if (parityFails.length < 4) parityFails.push(`removed {${removed.join(',')}}, token N${k}: ${star(val)} (lemma says ${star(want)})`);
      }
    }
  }
  const where = `construction as drawn, n = ${n}, all ${1 << ranks.length} sets of removed N vertices`;
  check('lem-grounded', '[BFT21] Lemma "Grounded"', 'N_k → R_k is a move to 0', grounded === groundedN, `${grounded} / ${groundedN}`, where);
  check('lem-r-to-n', '[BFT21] Lemma (R_p → N_p)', 'R_k → N_k is a move to 0', rToN === rToNN, `${rToN} / ${rToNN}`);
  check('lem-skip2', '[BFT21] Lemma "Skip *2"', 'N_k → M_k is * iff no lower N is gone, else *3', mOK === mN, `${mOK} / ${mN}`);
  check('lem-skip1', '[BFT21] Lemma "Skip *"', 'N_k → P_k is *2 iff no lower N is gone, else *3', pOK === pN, `${pOK} / ${pN}`);
  check('lem-not1or2', '[BFT21] Lemma (at least *4)', 'with only higher N gone, N_k is at least *4', n12 === n12N, `${n12} / ${n12N}`);
  check('lem-parity', '[BFT21] Lemma "Parity"', 'with a lower N gone, N_k is * or *2 by the parity of the N above the lowest gone', parOK === parN,
    `${parOK} / ${parN}`, parityFails.length ? parityFails.join('; ') : undefined);
  check('thm-induction', '[BFT21] Thm "Right Amount of Stars" (induction)', 'with only higher N gone, N_k is *k', ihOK === ihN, `${ihOK} / ${ihN}`);
}

const ok = items.filter((x) => x.ok).length;
console.log(`\n${ok} / ${items.length} items agree (${((Date.now() - t0) / 1000).toFixed(1)} s)`);
writeFileSync('runs/literature.json', JSON.stringify({ items, construction, seconds: (Date.now() - t0) / 1000 }, null, 1) + '\n');
