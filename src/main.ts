import './style.css';
import {
  Solver, BudgetExceeded, fullSet, without, has, component, maximumMatching, matchingNumber, maxDegree, type Bits,
} from './geography.ts';
import { boards, type Board } from './presets.ts';

const $ = <T extends HTMLElement>(id: string) => document.getElementById(id) as T;
const svg = $('board') as unknown as SVGSVGElement;
const boardSel = $<HTMLSelectElement>('boardSel');
const youSel = $<HTMLSelectElement>('youSel');
const hints = $<HTMLInputElement>('hints');
const matchChk = $<HTMLInputElement>('matchChk');
const statusEl = $('status');
const valueEl = $('value');
const movesEl = $('moves');

const BOARDS = boards();
const BUDGET = 400_000;
const star = (k: number) => (k === 0 ? '0' : k === 1 ? '*' : `*${k}`);

interface State {
  board: Board;
  start: number;
  path: number[]; // token positions, path[0] = start
  solver: Solver;
  picking: boolean;
}
let st: State;

function aliveOf(s: State): Bits {
  return without(fullSet(s.board.g.n), ...s.path);
}
const token = (s: State) => s.path[s.path.length - 1];
const moverIsFirst = (s: State) => (s.path.length - 1) % 2 === 0;

function humanToMove(s: State): boolean {
  const you = youSel.value;
  if (you === 'both') return true;
  return (you === 'first') === moverIsFirst(s);
}

function load(id: string, start?: number) {
  const board = BOARDS.find((b) => b.id === id)!;
  st = { board, start: start ?? board.start, path: [start ?? board.start], solver: new Solver(board.g, BUDGET), picking: false };
  render();
  maybeComputer();
}

/** Grundy values of the legal moves, or null if the search budget runs out. */
function optionValues(s: State): { to: number; value: number | null }[] {
  const alive = aliveOf(s);
  const v = token(s);
  const out: { to: number; value: number | null }[] = [];
  for (const u of s.board.g.adj[v]) {
    if (!has(alive, u)) continue;
    let value: number | null = null;
    try {
      s.solver.budget = s.solver.nodes + BUDGET;
      value = s.solver.grundy(without(alive, u), u);
    } catch (e) {
      if (!(e instanceof BudgetExceeded)) throw e;
    }
    out.push({ to: u, value });
  }
  return out;
}

/** Winnability of the opponent after each move, from matchings only. */
function opponentWins(s: State, u: number): boolean {
  const alive = without(aliveOf(s), u);
  const c = component(s.board.g, alive, u);
  return matchingNumber(s.board.g, c) > matchingNumber(s.board.g, without(c, u));
}

function render() {
  const s = st;
  const { g, xy } = s.board;
  const W = 760, H = 600;
  svg.setAttribute('viewBox', `0 0 ${W} ${H}`);
  const P = (v: number): [number, number] => [xy[v][0] * W, xy[v][1] * H];
  const alive = aliveOf(s);
  const v = token(s);
  const comp = component(g, alive, v);
  const mate = maximumMatching(g, comp);
  const opts = optionValues(s);
  const optBy = new Map(opts.map((o) => [o.to, o]));
  const human = humanToMove(s);
  const r = g.n > 60 ? 6 : g.n > 30 ? 9 : 13;
  let h = '';
  const inTrail = new Set<string>();
  for (let i = 1; i < s.path.length; i++) {
    const a = s.path[i - 1], b = s.path[i];
    inTrail.add(a < b ? `${a},${b}` : `${b},${a}`);
  }
  for (let a = 0; a < g.n; a++)
    for (const b of g.adj[a]) {
      if (b < a) continue;
      const [x1, y1] = P(a), [x2, y2] = P(b);
      const live = (has(alive, a) || a === v) && (has(alive, b) || b === v);
      const cls = inTrail.has(`${a},${b}`) ? 'trail' : live ? 'edge' : 'edge dead';
      h += `<line class="${cls === 'trail' ? 'edge trail' : cls}" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"/>`;
      if (matchChk.checked && live && mate[a] === b) h += `<line class="edge match" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}"/>`;
    }
  for (let u = 0; u < g.n; u++) {
    const [x, y] = P(u);
    const gone = !has(alive, u) && u !== v;
    const o = optBy.get(u);
    let cls = 'vtx';
    if (gone) cls += ' gone';
    else if (u === v) cls += ' token';
    else if (matchChk.checked && has(comp, u) && mate[u] === -1) cls += ' unmatched';
    if (s.picking) cls += ' pick';
    else if (o && human) cls += ' movable';
    h += `<circle class="${cls}" data-v="${u}" cx="${x}" cy="${y}" r="${u === v ? r + 3 : r}"/>`;
    if (o && hints.checked && !s.picking) {
      const win = o.value === 0 || (o.value === null && !opponentWins(s, u));
      const label = o.value === null ? (win ? '0' : '≠0') : star(o.value);
      h += `<text class="mark ${win ? 'win' : 'lose'}" x="${x}" y="${y - r - 9}">${label}</text>`;
    }
    if (g.n <= 30 && g.labels && !gone) h += `<text class="lbl" x="${x + r + 2}" y="${y + r + 6}">${g.labels[u]}</text>`;
  }
  svg.innerHTML = h;

  // side panel
  const deg3 = maxDegree(g) <= 3;
  const nu = matchingNumber(g, comp);
  const nuWithout = matchingNumber(g, without(comp, v));
  const winsNow = nu > nuWithout;
  let exact: number | null = null;
  try {
    s.solver.budget = s.solver.nodes + BUDGET;
    exact = s.solver.grundy(without(alive, v), v);
  } catch (e) {
    if (!(e instanceof BudgetExceeded)) throw e;
  }
  let bnb = '';
  if (deg3) {
    const t = new Solver(g);
    const x = t.branchAndBound(without(alive, v), v);
    bnb = `<dt>branch-and-bound</dt><dd>${x === null ? '—' : star(x)} with ${t.matchingCalls} winnability tests</dd>`;
  }
  const who = moverIsFirst(s) ? 'first player' : 'second player';
  valueEl.innerHTML = `
    <div class="big">${exact === null ? '?' : star(exact)} <span class="dim">Grundy value, ${who} to move</span></div>
    <p class="verdict">${opts.length === 0 ? `No move: the ${who} loses.` : winsNow ? `The player to move <strong class="win-t">wins</strong>.` : `The player to move <strong class="lose-t">loses</strong>.`}</p>
    <dl class="kv">
      <dt>ν(component)</dt><dd>${nu}</dd>
      <dt>ν(component − token)</dt><dd>${nuWithout} ${winsNow ? '(smaller: token is in every maximum matching)' : '(same: some maximum matching misses the token)'}</dd>
      <dt>search nodes</dt><dd>${s.solver.nodes.toLocaleString()}${exact === null ? ' (budget hit)' : ''}</dd>
      ${bnb}
      <dt>vertices left</dt><dd>${members(comp, g.n)} in the token's component, ${g.n} on the board</dd>
    </dl>
    <p class="small dim">${s.board.note}</p>`;
  movesEl.innerHTML = opts.length
    ? `<table>${opts
        .map((o) => {
          const win = o.value === 0 || (o.value === null && !opponentWins(s, o.to));
          const name = g.labels ? g.labels[o.to] : String(o.to);
          return `<tr><td>→ ${name}</td><td class="${win ? 'w' : 'l'}">${o.value === null ? (win ? '0' : '≠0') : star(o.value)}</td><td class="${win ? 'w' : 'l'}">${win ? 'winning' : 'losing'}</td></tr>`;
        })
        .join('')}</table>`
    : '<span class="dim">no legal move</span>';
  statusEl.innerHTML = s.picking
    ? 'Click a vertex to put the token there.'
    : opts.length === 0
      ? `Game over: the <strong>${moverIsFirst(s) ? 'second' : 'first'} player</strong> wins after ${s.path.length - 1} moves.`
      : human
        ? `Your move: click a highlighted neighbour of the token.`
        : 'Computer is thinking…';
}

function members(b: Bits, n: number): number {
  let c = 0;
  for (let i = 0; i < n; i++) if (has(b, i)) c++;
  return c;
}

function play(u: number) {
  st.path.push(u);
  render();
  maybeComputer();
}

function maybeComputer() {
  const s = st;
  if (youSel.value === 'both' || humanToMove(s)) return;
  const opts = optionValues(s);
  if (opts.length === 0) return;
  setTimeout(() => {
    if (st !== s || humanToMove(s)) return;
    // win by matching; otherwise pick the move with the largest value (hardest to answer)
    const winning = opts.filter((o) => !opponentWins(s, o.to));
    const pool = winning.length ? winning : opts.slice().sort((a, b) => (b.value ?? 0) - (a.value ?? 0));
    play(pool[0].to);
  }, 380);
}

svg.addEventListener('click', (e) => {
  const t = (e.target as Element).closest('[data-v]');
  if (!t) return;
  const u = Number(t.getAttribute('data-v'));
  if (st.picking) {
    load(st.board.id, u);
    return;
  }
  if (!humanToMove(st)) return;
  const alive = aliveOf(st);
  if (st.board.g.adj[token(st)].includes(u) && has(alive, u)) play(u);
});

for (const b of BOARDS) {
  const o = document.createElement('option');
  o.value = b.id;
  o.textContent = b.name;
  boardSel.append(o);
}
boardSel.addEventListener('change', () => load(boardSel.value));
youSel.addEventListener('change', () => {
  render();
  maybeComputer();
});
hints.addEventListener('change', render);
matchChk.addEventListener('change', render);
$('restart').addEventListener('click', () => load(st.board.id, st.start));
$('undo').addEventListener('click', () => {
  if (st.path.length <= 1) return;
  st.path.pop();
  if (youSel.value !== 'both' && !humanToMove(st) && st.path.length > 1) st.path.pop();
  render();
  maybeComputer();
});
$('pick').addEventListener('click', () => {
  st = { ...st, path: [st.path[0]], picking: true };
  render();
});

const params = new URLSearchParams(location.search);
const initial = BOARDS.find((b) => b.id === params.get('board'))?.id ?? BOARDS[0].id;
boardSel.value = initial;
load(initial);
