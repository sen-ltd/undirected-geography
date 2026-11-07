// The positions Burke, Ferland and Teng (arXiv:2106.02114) build, written out
// vertex by vertex so that their values can be computed rather than argued.
import { type Graph, graphFromEdges } from './geography.ts';

/** Incremental graph builder with labels. */
export class Builder {
  labels: string[] = [];
  es: [number, number][] = [];
  private byName = new Map<string, number>();

  vertex(label: string): number {
    const id = this.labels.length;
    this.labels.push(label);
    if (!this.byName.has(label)) this.byName.set(label, id);
    return id;
  }
  id(label: string): number {
    const v = this.byName.get(label);
    if (v === undefined) throw new Error(`no vertex ${label}`);
    return v;
  }
  edge(a: number, b: number): void {
    this.es.push([a, b]);
  }
  build(): Graph {
    return graphFromEdges(this.labels.length, this.es, this.labels);
  }

  /**
   * Observation "Logarithmic nimber in trees": t(k) has a root whose children are
   * the roots of t(k−1), …, t(0); 2^k vertices, value *k. Returns the root.
   */
  tree(k: number, prefix: string): number {
    const root = this.vertex(`${prefix}`);
    for (let j = k - 1; j >= 0; j--) this.edge(root, this.tree(j, `${prefix}.${j}`));
    return root;
  }
}

export function starTree(k: number): { g: Graph; s: number } {
  const b = new Builder();
  const s = b.tree(k, `t${k}`);
  return { g: b.build(), s };
}

/** A directed graph for Generalized Geography: n vertices and arcs (x → y). */
export interface Digraph {
  n: number;
  arcs: [number, number][];
}

/**
 * Plain Generalized Geography on a digraph: does the player to move win with the
 * token on s? (Exhaustive; for checking the reduction on small digraphs.)
 */
export function directedWins(d: Digraph, s: number): boolean {
  const out: number[][] = Array.from({ length: d.n }, () => []);
  for (const [x, y] of d.arcs) out[x].push(y);
  const memo = new Map<number, boolean>();
  const rec = (used: number, v: number): boolean => {
    const key = used * 32 + v;
    const hit = memo.get(key);
    if (hit !== undefined) return hit;
    let r = false;
    for (const u of out[v]) if (!(used & (1 << u)) && !rec(used | (1 << u), u)) r = true;
    memo.set(key, r);
    return r;
  };
  return rec(1 << s, s);
}

/**
 * The reduction r(G, s) of Theorem "Complexity Separation": every vertex v gets a
 * pendant v0, and every arc (x, y) becomes the gadget
 *   x – a – b – c – d – y,  a – a0,  c – c0,  d – d0,  b – f – d.
 * With `prelude`, start – start0, start – p, p – p0, p – s is put in front of s and
 * the token starts on "start".
 */
export function reduction(d: Digraph, s: number, prelude = false): { g: Graph; s: number } {
  const b = new Builder();
  const vs: number[] = [];
  for (let v = 0; v < d.n; v++) {
    vs.push(b.vertex(`v${v}`));
    b.edge(vs[v], b.vertex(`v${v}_0`));
  }
  d.arcs.forEach(([x, y], k) => {
    const g = (name: string) => b.vertex(`e${k}.${name}`);
    const a = g('a'), a0 = g('a0'), bb = g('b'), c = g('c'), c0 = g('c0'), f = g('f'), dd = g('d'), d0 = g('d0');
    b.edge(vs[x], a);
    b.edge(a, a0);
    b.edge(a, bb);
    b.edge(bb, c);
    b.edge(c, c0);
    b.edge(bb, f);
    b.edge(c, dd);
    b.edge(dd, d0);
    b.edge(f, dd);
    b.edge(dd, vs[y]);
  });
  if (!prelude) return { g: b.build(), s: vs[s] };
  const start = b.vertex('start');
  const p = b.vertex('pre');
  b.edge(start, b.vertex('start_0'));
  b.edge(start, p);
  b.edge(p, b.vertex('pre_0'));
  b.edge(p, vs[s]);
  return { g: b.build(), s: start };
}

/**
 * The nimber construction (Section "Undirected Geography with Polynomial Grundy
 * Values"). Algorithm 1 as printed leaves out three things that Figures 2–4 and
 * the lemmas use; each can be switched on separately:
 *   nmp    the edges N_i – M_i and N_i – P_i for i ≥ 5 ("N_i is connected to its
 *          own *2 gadget and its own * gadget", Fig. 3);
 *   n4r4   the edge N_4 – R_4 (the loop adds N_i – R_i only from i = 5);
 *   tree3  a *3 tree on N_4 (the loop adds *3 trees only from i = 5, but the base
 *          case says N_4 "has moves to 0 through *3").
 */
export interface Variant {
  nmp: boolean;
  n4r4: boolean;
  tree3: boolean;
}
export const AS_PRINTED: Variant = { nmp: false, n4r4: false, tree3: false };
export const AS_DRAWN: Variant = { nmp: true, n4r4: true, tree3: true };

export interface Construction {
  g: Graph;
  s: number;
  N: Map<number, number>;
}

export function nimberConstruction(n: number, variant: Variant = AS_DRAWN): Construction {
  const b = new Builder();
  const N = new Map<number, number>();
  if (n <= 3) {
    const s = b.tree(n, `t${n}`);
    return { g: b.build(), s, N };
  }
  const R = new Map<number, number>();
  N.set(4, b.vertex('N4'));
  R.set(4, b.vertex('R4'));
  if (variant.n4r4) b.edge(N.get(4)!, R.get(4)!);
  for (let i = 5; i <= n; i++) {
    const Ni = b.vertex(`N${i}`), Mi = b.vertex(`M${i}`), Pi = b.vertex(`P${i}`), Ri = b.vertex(`R${i}`);
    const Mi0 = b.vertex(`M${i}_0`), Pi0 = b.vertex(`P${i}_0`);
    N.set(i, Ni);
    R.set(i, Ri);
    b.edge(Ni, Ri);
    b.edge(Mi, Mi0);
    b.edge(Pi, Pi0);
    if (variant.nmp) {
      b.edge(Ni, Mi);
      b.edge(Ni, Pi);
    }
    b.edge(Ni, b.tree(3, `N${i}*3`));
    for (let j = 4; j <= i - 1; j++) {
      const p = (x: string) => b.vertex(`P${i},${j}${x}`);
      const pa = p('a'), pb = p('b'), pc = p('c'), pd = p('d'), pe = p('e'), pf = p('f');
      const m = (x: string) => b.vertex(`M${i},${j}${x}`);
      const ma = m('a'), mb = m('b'), mc = m('c'), md = m('d');
      b.edge(Pi, pa);
      b.edge(pa, pb);
      b.edge(pa, pc);
      b.edge(pc, pd);
      b.edge(pc, pe);
      b.edge(pe, pf);
      b.edge(pf, R.get(j)!);
      b.edge(Ni, N.get(j)!);
      b.edge(Mi, ma);
      b.edge(ma, mb);
      b.edge(ma, mc);
      b.edge(mc, md);
      b.edge(md, R.get(j)!);
    }
    b.edge(Mi, b.tree(2, `M${i}*2`));
    b.edge(Pi, b.tree(1, `P${i}*1`));
  }
  b.edge(N.get(4)!, b.tree(1, 'N4*1'));
  b.edge(N.get(4)!, b.tree(2, 'N4*2'));
  if (variant.tree3) b.edge(N.get(4)!, b.tree(3, 'N4*3'));
  return { g: b.build(), s: N.get(n)!, N };
}
