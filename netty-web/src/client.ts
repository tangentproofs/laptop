/**
 * The three panes.
 *
 * Netty's calculation window is a proof pane, a context pane and a
 * suggestions pane. This draws those three from the state the kernel sends,
 * and turns a click into one line of the kernel's script language: a click on
 * a suggestion is `apply #N`, a click on a line's number is `focus N`, and a
 * click on a part of the line before the focus is `zoom` and the name the kernel
 * gave that part — a number for a main operand, `start:length` for a contiguous
 * segment of an association. Nothing about a proof is decided here, and nothing
 * here composes a part's name: `LineView.zooms` carries it, so a click cannot
 * mean a different part from the one a suggestion's site or a script zoom means.
 * That is also what the site highlight rests on: a suggestion carries the part
 * it would rewrite (`SuggestionView.site`), named the same way, so pointing at a
 * suggestion lights up that very part of the line before the focus.
 *
 * `state.lines` is the proof after the kernel's display collapses, so a line
 * the collapses hide simply does not arrive and a line they lift arrives with
 * a smaller `depth`. Each line still carries its own index in the document,
 * which is what `focus N` names, so nothing here has to know about them.
 */

import type { LineView, Op, PartView, Response, StateView, SuggestionView } from './protocol.js';
import {
  PICKER_EXAMPLES, examplesBase, parseCalcTheorems, theoremToScript,
  loadExamplesManifest,
  type CalcTheorem, type ExamplesManifest, type ManifestItem,
} from './calc-load.js';
import { appendHighlighted } from './highlight.js';

/** The state the kernel last sent. */
let state: StateView | null = null;
/** What to say above the panes, and whether it is a complaint. */
let note = '';
let noteIsError = false;
/** Whether the panes are drawn as the command line prints them. */
let asText = false;
/** What the direct-entry and start rows hold, kept across a redraw. */
const typed = { start: '', direct: '', ty: 'boolean', startConn: '⇐', directConn: '' };
/** Book .calc currently loaded (source kept for optional reference). */
let bookExample: { name: string; text: string; theorem: string } | null = null;
/** Theorems parsed from the last fetched .calc (for the theorem picker). */
let bookTheorems: CalcTheorem[] = [];
/** Hierarchical examples list (manifest.json); null until fetched. */
let examplesManifest: ExamplesManifest | null = null;



/** Make an element. */
function el<K extends keyof HTMLElementTagNameMap>(
  tag: K,
  attrs: Record<string, string> = {},
  ...children: (Node | string)[]
): HTMLElementTagNameMap[K] {
  const node = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') node.className = v;
    else node.setAttribute(k, v);
  }
  for (const c of children) node.append(c);
  return node;
}

/** API path relative to the page URL so a subpath deploy (e.g. /netty/)
 * POSTs to /netty/api, not /api. Nginx strips /netty/ before proxying. */
function apiUrl(): string {
  const base = window.location.pathname.endsWith('/')
    ? window.location.pathname
    : window.location.pathname.replace(/\/[^/]*$/, '/');
  return new URL('api', window.location.origin + base).pathname;
}

/**
 * When true, `send` keeps the current note (manifest FAIL/MISSING status)
 * instead of replacing it with a transient apply error or clearing it on OK.
 * Set around loadBookCalc replays so the status bar stays honest.
 */
let holdStatusNote = false;

/** Ask the kernel, then redraw. A refused request leaves the state alone and
 * says why, which is what the kernel's answer already carries. */
async function send(op: Op, arg = ''): Promise<Response | null> {
  let answer: Response;
  try {
    const res = await fetch(apiUrl(), {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ op, arg }),
    });
    answer = (await res.json()) as Response;
  } catch (e) {
    if (!holdStatusNote) {
      note = `the server: ${String(e)}`;
      noteIsError = true;
    }
    draw();
    return null;
  }
  if (answer.state) state = answer.state;
  if (!holdStatusNote) {
    note = answer.ok ? '' : answer.error;
    noteIsError = !answer.ok;
  }
  draw();
  return answer;
}

/** Run one line of the script language. */
const cmd = (line: string) => send('cmd', line);

/** Options for loading a book .calc into the proof pane. */
type LoadCalcOpts = {
  /**
   * When false/omitted (PASS): every apply must succeed; gaps refuse the load.
   * When true (FAIL): unresolvable hints become `direct` and failed applies
   * fall back to `direct` so broken steps show as red ! gaps.
   */
  allowGaps?: boolean;
  /**
   * When true (MISSING): put only the goal in the proof pane and show the stub
   * in the book-source panel. Do not replay apply/direct steps — apply-by-law
   * name scans the full suggestion list, and direct of a huge intermediate
   * expression can hang the kernel while building suggestions.
   */
  displayOnly?: boolean;
  /** Manifest status for the status line (`FAIL` / `MISSING`). */
  status?: string;
  /** Manifest blocker / next-step text for the status line (no status prefix). */
  reason?: string;
};

/** Serial so a late reply from an older load cannot overwrite a newer pick. */
let loadGen = 0;

/** Manifest status line: `MISSING: "ex5a" — law gap — …`. */
function statusNote(tag: string, name: string, reason: string, detail = ''): string {
  const why = reason ? ` — ${reason}` : '';
  const extra = detail ? ` (${detail})` : '';
  return `${tag}: “${name}”${why}${extra}`;
}

/** Replay Netty script lines into the kernel (proof pane).
 * Strict: every `apply` must succeed — no silent `direct` fallback.
 * With allowGaps: a failed `apply LAW : CONN EXPR` falls back to `direct CONN EXPR`
 * so FAIL calcs still open with red ! gaps for inspection. */
async function replayScript(lines: string[], allowGaps = false): Promise<boolean> {
  await send('reset');
  for (const line of lines) {
    const t = line.trim();
    if (t === '' || t.startsWith('#')) continue;
    const word = t.split(/\s+/)[0] ?? '';
    if (word === 'proof' || word === 'suggest' || word === 'context') continue;
    const a = await send('cmd', t);
    if (a === null) return false;
    if (!a.ok) {
      if (allowGaps && word === 'apply') {
        // `apply LAW : CONN EXPR` or `apply LAW : CONN EXPR with …` → direct CONN EXPR
        const m = t.match(/^apply\s+[^:]+:\s*([=≡⇒⇐≤≥⟹⟸])\s+(.+?)(?:\s+with\s+.+)?$/);
        if (m) {
          const d = await send('cmd', `direct ${m[1]} ${m[2]!.trim()}`);
          if (d === null || !d.ok) return false;
          continue;
        }
      }
      return false;
    }
  }
  return true;
}

/** Script lines that start a proof (state/spec/start) — no apply/direct steps. */
function startOnlyScript(script: string[]): string[] {
  return script.filter((l) => {
    const w = l.trim().split(/\s+/)[0] ?? '';
    return w !== 'apply' && w !== 'direct';
  });
}

/** Fetch a .calc and load its first (or named) theorem into the proof editor.
 * PASS: strict apply-only. FAIL: allowGaps. MISSING: displayOnly (goal + stub). */
async function loadBookCalc(
  file: string, label: string, theoremIndex = 0, opts: LoadCalcOpts = {},
): Promise<void> {
  const allowGaps = opts.allowGaps === true;
  const displayOnly = opts.displayOnly === true;
  const tag = opts.status ?? '';
  const reason = opts.reason ?? '';
  const gen = ++loadGen;
  const stillCurrent = () => gen === loadGen;
  // PASS clears any prior hold; FAIL/MISSING hold the status through replay.
  holdStatusNote = tag !== '';

  // Show manifest status immediately so a slow/hung step cannot leave a prior
  // FAIL message or the generic hint on the bar. holdStatusNote keeps send()
  // from overwriting it with apply errors or clearing it on OK mid-replay.
  if (tag) {
    note = statusNote(tag, label, reason, 'loading…');
    noteIsError = true;
    draw();
  }

  try {
    const res = await fetch(examplesBase() + file);
    if (!stillCurrent()) return;
    if (!res.ok) throw new Error(`HTTP ${res.status}`);
    const text = await res.text();
    if (!stillCurrent()) return;
    bookTheorems = parseCalcTheorems(text);
    if (bookTheorems.length === 0) {
      bookExample = { name: label, text, theorem: '' };
      note = tag
        ? statusNote(tag, label, reason, 'no theorem/refine blocks found')
        : `${label}: no theorem/refine blocks found to load`;
      noteIsError = true;
      draw();
      return;
    }
    const idx = Math.max(0, Math.min(theoremIndex, bookTheorems.length - 1));
    const th = bookTheorems[idx]!;
    bookExample = { name: label, text, theorem: th.name };

    // MISSING: goal only — never apply-by-law-name / step-direct (hang risk).
    if (displayOnly) {
      const full = theoremToScript(th, false);
      const goal = full === null ? [] : startOnlyScript(full);
      const ok = await replayScript(goal, false);
      if (!stillCurrent()) return;
      note = statusNote(
        tag || 'MISSING',
        th.name,
        reason,
        ok ? 'stub — steps not auto-applied' : 'stub — goal failed to open',
      );
      noteIsError = true;
      draw();
      return;
    }

    const script = theoremToScript(th, !allowGaps);
    if (script === null) {
      // Strict PASS path: refuse. (allowGaps never returns null.)
      note = `“${th.name}” has hints Netty cannot apply yet — not loaded as a proof`;
      noteIsError = true;
      draw();
      return;
    }
    const ok = await replayScript(script, allowGaps);
    if (!stillCurrent()) return;
    const gappy = state !== null && state.lines.some((l) => l.gap);
    if (allowGaps) {
      const st = tag || 'INSPECT';
      const hasStep = script.some((l) => l.startsWith('apply') || l.startsWith('direct'));
      let detail = '';
      if (!ok) detail = 'failed to open';
      else if (gappy) detail = 'loaded with gaps (!)';
      else if (!hasStep) detail = 'not yet proved (goal shown)';
      else detail = 'loaded (inspect mode)';
      note = statusNote(st, th.name, reason, detail);
      noteIsError = true;
      draw();
      return;
    }
    if (ok && !gappy) {
      note = `loaded “${th.name}” — every step applied (${idx + 1}/${bookTheorems.length} in ${label})`;
      noteIsError = false;
    } else {
      note = gappy
        ? `“${th.name}” left a gap (!) — not a valid Netty session`
        : `“${th.name}” failed to apply a step — not a valid Netty session`;
      noteIsError = true;
      await send('reset');
      if (!stillCurrent()) return;
    }
    draw();
  } catch (e) {
    if (!stillCurrent()) return;
    note = tag
      ? statusNote(tag, label, reason, String(e))
      : `book example: ${String(e)}`;
    noteIsError = true;
    draw();
  } finally {
    if (gen === loadGen) holdStatusNote = false;
  }
}


/** The directions of a type, as the kernel writes them. */
const DIRECTIONS: Record<string, string[]> = {
  boolean: ['⇒', '=', '⇐'],
  number: ['≤', '=', '≥'],
};

/** The row that starts a proof: a type, a direction and the first line. */
function startRow(): HTMLElement {
  const ty = el('select', { class: 'ty', title: 'the type of the proof' });
  for (const t of ['boolean', 'number']) {
    const o = el('option', { value: t }, t);
    if (t === typed.ty) o.setAttribute('selected', 'selected');
    ty.append(o);
  }
  const dir = el('select', { class: 'conn', title: 'the direction of the proof' });
  const fill = () => {
    dir.replaceChildren();
    for (const d of DIRECTIONS[ty.value] ?? []) {
      const o = el('option', { value: d }, d);
      if (d === typed.startConn) o.setAttribute('selected', 'selected');
      dir.append(o);
    }
  };
  fill();
  ty.addEventListener('change', () => {
    typed.ty = ty.value;
    typed.startConn = DIRECTIONS[ty.value]?.[2] ?? '=';
    fill();
  });
  dir.addEventListener('change', () => { typed.startConn = dir.value; });
  const text = el('input', {
    class: 'expr', type: 'text', spellcheck: 'false',
    placeholder: 'the first line, e.g. a ⇒ (b ⇒ a)', value: typed.start,
  });
  text.addEventListener('input', () => { typed.start = text.value; });
  const go = el('button', { class: 'go' }, 'start');
  const run = () => {
    if (text.value.trim() === '') return;
    typed.start = '';
    void cmd(`start ${ty.value} ${dir.value} ${text.value}`);
  };
  go.addEventListener('click', run);
  text.addEventListener('keydown', (e) => { if (e.key === 'Enter') run(); });
  return el('div', { class: 'entry' },
    el('span', { class: 'gutter' }, ''), el('span', { class: 'caret' }, '›'), ty, dir, text, go);
}

/** The row at the focus: type the next line in directly, which leaves a gap
 * for a law to close later. */
function directRow(s: StateView, depth: number): HTMLElement {
  const conn = el('select', { class: 'conn', title: 'the connective in the margin' });
  for (const c of s.conns) {
    const o = el('option', { value: c }, c);
    if (c === typed.directConn) o.setAttribute('selected', 'selected');
    conn.append(o);
  }
  conn.addEventListener('change', () => { typed.directConn = conn.value; });
  const text = el('input', {
    class: 'expr', type: 'text', spellcheck: 'false', id: 'direct',
    placeholder: 'or type the next line here', value: typed.direct,
  });
  text.addEventListener('input', () => { typed.direct = text.value; });
  const go = el('button', { class: 'go' }, 'enter');
  const run = () => {
    if (text.value.trim() === '') return;
    typed.direct = '';
    void cmd(`direct ${conn.value} ${text.value}`);
  };
  go.addEventListener('click', run);
  text.addEventListener('keydown', (e) => { if (e.key === 'Enter') run(); });
  return el('div', { class: 'entry', style: `--depth: ${depth}` },
    el('span', { class: 'gutter' }, ''), el('span', { class: 'caret' }, '›'), conn, text, go);
}

/** A button that zooms in to one part of the line, named as the kernel names
 * it. `zoom ${z.name}` is the script line; nothing here builds that name. */
function zoomButton(z: PartView, extra = ''): HTMLElement {
  const b = el('button', {
    class: `operand zoom${extra === '' ? '' : ' ' + extra}`,
    title: `zoom in to ${z.text} — zoom ${z.name}`,
    'data-part': z.name,
  }, z.text);
  b.addEventListener('click', () => void cmd(`zoom ${z.name}`));
  return b;
}

/** A line's formula, drawn as its main operands with the main operator
 * between them. Where the line can be zoomed in to, each operand is a
 * button: clicking it is the document's "click on a subexpression". A run of
 * two or more operands has no place of its own in the line, so it is offered
 * below it instead (`segmentsRow`). */
function formula(l: LineView): HTMLElement {
  const box = el('span', { class: 'formula' });
  if (l.parts.length === 0 || (!l.zoomable && l.parts.length < 2 && l.kind !== 'neg')) {
    const atom = el('span', { class: 'atom' });
    appendHighlighted(atom, l.expr);
    box.append(atom);
    return box;
  }
  // The single-operand zoom targets, by which operand they are. A line that
  // cannot be zoomed in to has none, and its operands are drawn as plain text.
  const single = new Map<number, PartView>();
  for (const z of l.zooms) if (z.len === 1) single.set(z.start, z);
  // Each operand, and each operator written between two of them, says which
  // operand it is, so that `showSite` can light up a run of them without
  // knowing how the line was drawn.
  const piece = (text: string, i: number): HTMLElement => {
    const z = single.get(i);
    let node: HTMLElement;
    if (z === undefined) {
      node = el('span', { class: 'operand' });
      appendHighlighted(node, text);
    } else {
      node = zoomButton(z);
      node.textContent = '';
      appendHighlighted(node, z.text);
    }
    node.setAttribute('data-operand', String(i));
    return node;
  };
  if (l.kind === 'neg') {
    box.append(el('span', { class: 'op' }, l.op), piece(l.parts[0] ?? '', 0));
    return box;
  }
  // A word or mark a form writes for itself. Where it stands before one of the
  // pieces it says so, as the operator between two operands does, so that
  // `showSite` can light up a piece by the mark that introduces it.
  const word = (w: string, before?: number): HTMLElement => {
    const node = el('span', before === undefined ? { class: 'op' }
      : { class: 'op', 'data-op-before': String(before) });
    appendHighlighted(node, w);
    return node;
  };
  // `if … then … else … fi` writes its own four words around its three pieces:
  // the condition and the two branches, each a zoom target of its own.
  if (l.kind === 'cond') {
    box.append(word('if '), piece(l.parts[0] ?? '', 0));
    box.append(word(' then ', 1), piece(l.parts[1] ?? '', 1));
    box.append(word(' else ', 2), piece(l.parts[2] ?? '', 2));
    box.append(word(' fi'));
    return box;
  }
  // `∀ids: d· b` writes its own `:` and `·` around its two pieces, the domain and
  // the body. `op` carries the quantifier and the names it binds — those are not
  // expressions and are not zoom targets; the domain and the body are.
  if (l.kind === 'quant') {
    box.append(word(`${l.op}: `), piece(l.parts[0] ?? '', 0));
    box.append(word('· ', 1), piece(l.parts[1] ?? '', 1));
    return box;
  }
  // `:` is written tight on its left, as `Expr.renderAt` writes it; every other
  // operator has a space on both sides.
  const between = l.op === ':' ? `${l.op} ` : ` ${l.op} `;
  l.parts.forEach((p, i) => {
    if (i > 0) box.append(word(between, i));
    box.append(piece(p, i));
  });
  return box;
}

/** Light up the part of the line before the focus that a suggestion would
 * rewrite, and nothing else; `null` clears it.
 *
 * The site is one of the kernel's parts, in the same shape and under the same
 * name as the zoom targets, so what is lit is exactly what a click on that part
 * would open: the whole formula for a whole-line step, one operand for a step on
 * one, and a run of operands with the operators between them for a step on a
 * run — whose dashed button under the line lights up with it.
 *
 * This writes classes rather than redrawing, because a redraw under the pointer
 * would take the row being pointed at out of the document. */
function showSite(site: PartView | null): void {
  for (const n of document.querySelectorAll('.site')) n.classList.remove('site');
  if (site === null) return;
  const row = document.querySelector('.line.focused');
  const box = row?.querySelector('.formula');
  if (box == null) return;
  if (site.len === 0) {
    box.classList.add('site');
    return;
  }
  for (let i = site.start; i < site.start + site.len; i++) {
    box.querySelector(`[data-operand="${i}"]`)?.classList.add('site');
    if (i > site.start) box.querySelector(`[data-op-before="${i}"]`)?.classList.add('site');
  }
  if (site.len > 1) {
    row?.nextElementSibling?.querySelector(`.segment[data-part="${site.name}"]`)
      ?.classList.add('site');
  }
}

/** The zoom targets that are runs of *two or more* main operands: the
 * contiguous segments of an association, which the document reads as parts of
 * the line just as it reads the single operands. A run has nowhere in the line
 * to be clicked — its operands are not adjacent to one button — so each gets one
 * here, under the line it belongs to. `null` when the line offers none, which is
 * every line whose main operator is not an association of three or more. */
function segmentsRow(l: LineView): HTMLElement | null {
  const runs = l.zooms.filter((z) => z.len > 1);
  if (runs.length === 0) return null;
  const row = el('div', { class: 'entry segments', style: `--depth: ${l.depth}` },
    el('span', { class: 'gutter' }, ''),
    el('span', { class: 'caret' }, ''),
    el('span', { class: 'margin' }, ''),
    el('span', { class: 'runs-label' }, 'runs:'));
  for (const z of runs) row.append(zoomButton(z, 'segment'));
  return row;
}

/** One line of the proof. `l.depth` is the depth the kernel says to draw it
 * at, which the display collapses may have lifted; `depth` is the innermost
 * open level's, which is what says whether moving the focus to this line would
 * close a subproof. */
function lineRow(l: LineView, depth: number): HTMLElement {
  const row = el('div', {
    class: ['line', l.focused ? 'focused' : '', l.gap ? 'gapped' : ''].filter(Boolean).join(' '),
    style: `--depth: ${l.depth}`,
  });
  const gutter = el('button', {
    class: 'gutter' + (l.focusable ? ' movable' : ''),
    title: !l.focusable
      ? 'this subproof was closed before the lines below it were written; going back into it would take those lines with it'
      : l.reopens
        ? 'move the focus here, going back into this subproof'
        : l.depth < depth
          ? 'move the focus here, closing the subproofs below this line'
          : 'move the focus here',
  }, String(l.index));
  if (l.focusable) gutter.addEventListener('click', () => void cmd(`focus ${l.index}`));
  row.append(gutter);
  if (l.gap) {
    row.setAttribute('title', l.premise !== ''
      ? `a gap: the step below needs ${l.premise}`
      : 'a gap: the step below is not licensed by a law');
  }
  row.append(el('span', { class: 'caret' }, l.focused ? '›' : ''));
  row.append(l.dir !== ''
    ? el('span', { class: 'margin direction', title: 'the direction of this level' }, `[${l.dir}]`)
    : el('span', { class: 'margin' }, l.conn));
  row.append(formula(l));
  row.append(l.gap
    ? el('span', { class: 'note gap', title: 'no law justifies this step' }, '!')
    : el('span', { class: 'note', title: l.note === '' ? '' : 'the law that justifies the next line' }, l.note));
  return row;
}

/** The proof pane. */
function proofPane(s: StateView | null): HTMLElement {
  const pane = el('section', { class: 'pane proof' },
    el('h2', {}, 'proof', el('span', { class: 'sub' }, s === null || !s.started ? '' : `level ${s.depth}, ${s.ty} ${s.dir}`)));
  const body = el('div', { class: 'body' });
  if (s === null) {
    body.append(el('p', { class: 'quiet' }, 'talking to the kernel…'));
  } else if (asText) {
    body.append(el('pre', {}, s.proofPane));
  } else if (!s.started) {
    body.append(el('p', { class: 'quiet' }, 'no proof yet: give the first line, or pick an example.'));
    body.append(startRow());
  } else {
    for (const l of s.lines) {
      body.append(lineRow(l, s.depth));
      const runs = segmentsRow(l);
      if (runs !== null) body.append(runs);
      if (l.focused) body.append(directRow(s, l.depth));
    }
  }
  pane.append(body);
  if (s !== null && s.started) {
    pane.append(el('div', { class: 'outcome' + (s.proved ? ' proved' : '') }, s.outcome));
  }
  return pane;
}

/** The context pane: the laws zooming in has added. */
function contextPane(s: StateView | null): HTMLElement {
  const pane = el('section', { class: 'pane context' },
    el('h2', {}, 'context',
      el('span', { class: 'sub' }, s === null ? '' : `${s.context.length} from the zoom, ${s.lawCount} loaded`)));
  const body = el('div', { class: 'body' });
  if (s === null || asText) {
    body.append(el('pre', {}, s?.contextPane ?? ''));
  } else if (s.context.length === 0) {
    body.append(el('p', { class: 'quiet' }, 'no context: zooming in to a part gains what the operands outside it say.'));
  } else {
    for (const c of s.context) body.append(el('div', { class: 'law' }, c));
  }
  pane.append(body);
  return pane;
}

/** One suggestion: what a law would write next. */
/** The document's small dialog box: one field per law variable the match left
 * unconstrained, and a button that sends `apply #N with x := …`. It is opened by
 * clicking the greyed row itself — the row stays greyed, because the step is not
 * takeable until the fields are filled — and it is a sibling of the row rather
 * than a child, a form inside a button being no form at all. */
function holeDialog(g: SuggestionView, row: HTMLElement): void {
  const open = row.nextElementSibling;
  if (open !== null && open.classList.contains('holes')) {
    open.remove();
    return;
  }
  document.querySelectorAll('.holes').forEach((f) => f.remove());
  const form = el('form', { class: 'holes' });
  const fields = g.holes.map((h) => {
    const input = el('input', {
      type: 'text', name: h, size: '10', autocomplete: 'off',
      'aria-label': `what ${h} is`, placeholder: 'expression',
    });
    form.append(el('label', {}, `${h} :=`, input));
    return [h, input] as const;
  });
  form.append(el('button', { type: 'submit', class: 'go' }, 'apply'));
  form.append(el('button', { type: 'button', class: 'drop' }, 'cancel'));
  form.addEventListener('submit', (ev) => {
    ev.preventDefault();
    const given = fields.filter(([, i]) => i.value.trim() !== '');
    if (given.length !== fields.length) return;
    const withClause = given.map(([h, i]) => `${h} := ${i.value.trim()}`).join(', ');
    void cmd(`apply #${g.index} with ${withClause}`);
  });
  form.querySelector('.drop')?.addEventListener('click', () => form.remove());
  form.addEventListener('keydown', (ev) => {
    if (ev.key === 'Escape') { form.remove(); row.focus(); }
  });
  row.after(form);
  fields[0]?.[1].focus();
}

function suggestionRow(g: SuggestionView): HTMLElement {
  const blocked = g.holes.length > 0;
  // A conditional law whose premise nothing in force settles is still a step,
  // but it leaves the document's warning sign. The row says what it would leave
  // to prove, before it is taken.
  const gappy = g.premise !== '';
  const row = el('button', {
    class: 'suggestion' + (blocked ? ' blocked' : '') + (gappy ? ' gappy' : ''),
    title: blocked
      ? `${g.holes.join(', ')} unconstrained: this law needs more than the line to \
settle it — click to say what ${g.holes.join(', ')} ${g.holes.length === 1 ? 'is' : 'are'}`
      : gappy
        ? `apply #${g.index} — ${g.law}, leaving ${g.premise} to prove`
        : `apply #${g.index} — ${g.law}`,
  });
  row.append(el('span', { class: 'gutter' }, String(g.index)));
  row.append(el('span', { class: 'margin' }, g.op));
  row.append(el('span', { class: 'formula' }, g.result));
  row.append(el('span', { class: 'note' },
    blocked ? `${g.law} (${g.holes.join(', ')}?)`
      : gappy ? `${g.law} ! ${g.premise}`
        : g.law));
  row.addEventListener('click', () =>
    blocked ? holeDialog(g, row) : void cmd(`apply #${g.index}`));
  // Pointing at a suggestion — or reaching it with the keyboard — lights up the
  // part of the line it would rewrite. A disabled row gets the listeners too:
  // the browser sends it no pointer events, but its neighbours' leaving clears
  // the highlight anyway, and a greyed step still has a site worth seeing when
  // the pointer is over the pane.
  row.addEventListener('pointerenter', () => showSite(g.site));
  row.addEventListener('pointerleave', () => showSite(null));
  row.addEventListener('focus', () => showSite(g.site));
  row.addEventListener('blur', () => showSite(null));
  return row;
}

/** The suggestions pane. */
function suggestPane(s: StateView | null): HTMLElement {
  const pane = el('section', { class: 'pane suggest' },
    el('h2', {}, 'suggestions',
      el('span', { class: 'sub' }, s === null ? '' : `${s.suggestions.length}`)));
  const body = el('div', { class: 'body' });
  if (s === null || asText) {
    body.append(el('pre', {}, s?.suggestPane ?? ''));
  } else if (!s.started) {
    body.append(el('p', { class: 'quiet' }, 'the suggestions are what each law would write after the focus.'));
  } else if (s.suggestions.length === 0) {
    body.append(el('p', { class: 'quiet' }, 'no law applies to the line before the focus.'));
  } else {
    for (const g of s.suggestions) body.append(suggestionRow(g));
  }
  pane.append(body);
  return pane;
}

/** Hand the proof file to the browser to keep. */
function download(text: string): void {
  const url = URL.createObjectURL(new Blob([text], { type: 'application/json' }));
  const a = el('a', { href: url, download: 'proof.netty.json' });
  document.body.append(a);
  a.click();
  a.remove();
  setTimeout(() => URL.revokeObjectURL(url), 10_000);
}


/** Blocker / next-step text for tooltips and status (no status prefix). */
function itemReason(it: ManifestItem): string {
  const bits: string[] = [];
  if (it.blocker) bits.push(it.blocker);
  if (it.nextStep) bits.push(it.nextStep);
  return bits.length > 0 ? bits.join(' — ') : (it.bookRef || it.title);
}

/** Open a calc or demo from the hierarchical list.
 * PASS: strict apply-only. FAIL: load with gaps. MISSING: display-only stub. */
function chooseExample(it: ManifestItem): void {
  if ((it.kind ?? 'calc') === 'demo') {
    if (it.status !== 'pass') return;
    const demoId = it.id.startsWith('demo:') ? it.id.slice(5) : it.id;
    bookExample = null;
    bookTheorems = [];
    void send('demo', demoId);
    return;
  }
  const reason = itemReason(it);
  if (it.status === 'pass') {
    if (!it.path) return;
    void loadBookCalc(it.path, it.title, 0, { allowGaps: false });
    return;
  }
  if (it.status === 'fail') {
    if (!it.path) {
      note = statusNote('FAIL', it.title, reason, 'no .calc path');
      noteIsError = true;
      bookExample = { name: it.title, text: `# FAIL — ${it.bookRef}\n# ${reason}\n`, theorem: '' };
      draw();
      return;
    }
    void loadBookCalc(it.path, it.title, 0, {
      allowGaps: true, status: 'FAIL', reason,
    });
    return;
  }
  if (it.status === 'missing') {
    if (!it.path) {
      note = statusNote('MISSING', it.title, reason, 'no .calc stub yet');
      noteIsError = true;
      bookExample = {
        name: it.title,
        text: `# MISSING — ${it.bookRef}\n# ${reason}\n# No .calc stub yet.\n`,
        theorem: '',
      };
      draw();
      return;
    }
    void loadBookCalc(it.path, it.title, 0, {
      displayOnly: true, status: 'MISSING', reason,
    });
  }
}

/**
 * Hierarchical examples control: details panel with chapter → section groups.
 * PASS / FAIL / MISSING are all clickable; OUT_OF_SCOPE is omitted.
 * Distinct classes keep colouring (`ex-pass` / `ex-fail` / `ex-missing`).
 * Falls back to the flat PASS-only list if the manifest has not loaded yet.
 */
function examplesPicker(): HTMLElement {
  const wrap = el('div', { class: 'examples-picker' });
  const summary = el('summary', { class: 'examples-summary' }, 'examples…');
  const panel = el('div', { class: 'examples-panel' });
  const root = el('details', {
    class: 'examples-menu',
    title: 'load a book example or demo (PASS apply-only; FAIL/MISSING open for inspection)',
  });
  root.append(summary, panel);

  const fill = (m: ExamplesManifest | null) => {
    panel.replaceChildren();
    if (!m) {
      // Flat fallback until manifest arrives (PASS book + demos).
      const list = el('ul', { class: 'examples-flat' });
      for (const ex of PICKER_EXAMPLES) {
        const li = el('li');
        const b = el('button', { type: 'button', class: 'ex-pass' }, ex.label);
        b.addEventListener('click', () => {
          root.open = false;
          if (ex.kind === 'calc') void loadBookCalc(ex.file, ex.label, 0, { allowGaps: false });
          else {
            bookExample = null;
            bookTheorems = [];
            void send('demo', ex.id);
          }
        });
        li.append(b);
        list.append(li);
      }
      panel.append(list);
      return;
    }
    for (const g of m.groups) {
      const gdet = el('details', { class: 'ex-group' });
      if (g.id === 'ch1' || g.id === 'demos') gdet.setAttribute('open', '');
      gdet.append(el('summary', {}, g.title));
      for (const s of g.sections) {
        const sdet = el('details', { class: 'ex-section' });
        sdet.setAttribute('open', '');
        sdet.append(el('summary', {}, s.title));
        const ul = el('ul', { class: 'ex-items' });
        for (const it of s.items) {
          if (it.status === 'out_of_scope') continue;
          const li = el('li', { class: `ex-${it.status}` });
          const label = it.title.length > 64 ? it.title.slice(0, 61) + '…' : it.title;
          const why = itemReason(it);
          const btnClass =
            it.status === 'pass' ? 'ex-pass'
              : it.status === 'fail' ? 'ex-fail'
                : 'ex-missing';
          const shown = it.status === 'pass' ? label : `${label} (${it.status})`;
          const b = el('button', {
            type: 'button',
            class: btnClass,
            title: `${it.bookRef} — ${why}`,
          }, shown);
          b.addEventListener('click', () => {
            root.open = false;
            chooseExample(it);
          });
          li.append(b);
          ul.append(li);
        }
        if (ul.childNodes.length) {
          sdet.append(ul);
          gdet.append(sdet);
        }
      }
      if (gdet.querySelector('.ex-items')) panel.append(gdet);
    }
  };

  fill(examplesManifest);
  if (examplesManifest === null) {
    void loadExamplesManifest().then((m) => {
      examplesManifest = m;
      // Only refill if this picker is still mounted (draw() rebuilds the toolbar).
      if (wrap.isConnected) fill(m);
    }).catch(() => { /* keep flat fallback */ });
  }

  wrap.append(root);
  return wrap;
}

/** The toolbar. */
function toolbar(s: StateView | null): HTMLElement {
  const bar = el('nav', { class: 'toolbar' });
  const button = (label: string, title: string, run: () => void, off = false) => {
    const b = el('button', { title }, label);
    if (off) b.setAttribute('disabled', 'disabled');
    b.addEventListener('click', run);
    bar.append(b);
    return b;
  };
  // Hierarchical Examples picker (chapter → section → proof); PASS/FAIL/MISSING open.
  bar.append(examplesPicker());
  button('new', 'start again with the same laws', () => void send('reset'));
  button('undo (u)', 'undo one command', () => void cmd('undo'), s === null || !s.canUndo);
  button('zoom out (o)', 'zoom out of this subproof', () => void cmd('out'), s === null || !s.canZoomOut);
  button('save', 'save the proof as a file', () => {
    void send('save').then((a) => { if (a?.ok) download(a.save); });
  });
  const file = el('input', { type: 'file', accept: '.json,application/json', id: 'load' });
  file.addEventListener('change', () => {
    const f = file.files?.[0];
    if (f) void f.text().then((t) => send('load', t));
    file.value = '';
  });
  bar.append(el('label', { class: 'load', title: 'load a proof file' }, 'load', file));
  button(asText ? 'panes: text' : 'panes: lines', 'draw the panes as the command line prints them', () => {
    asText = !asText;
    draw();
  });
  return bar;
}

/** Draw everything. */
function draw(): void {
  const root = document.getElementById('app');
  if (root === null) return;
  const s = state;
  const kids: (Node | string)[] = [
    el('header', {},
      el('div', { class: 'site-bar' },
        el('a', { class: 'brand', href: '/' }, 'aPToP ', el('span', {}, '/ LaPToP')),
        el('nav', { class: 'site-nav', 'aria-label': 'Primary' },
          el('span', { class: 'nav-local' },
            el('a', { href: '/' }, 'Home'),
            el('a', { href: '/netty/', 'aria-current': 'page' }, 'Netty'),
            el('a', { href: '/interp/' }, 'Interpreter'),
            el('a', { href: '/examples/' }, 'Examples')),
          el('span', { class: 'nav-hehner' },
            el('a', {
              class: 'ext book',
              href: 'https://www.cs.toronto.edu/~hehner/aPToP/',
              target: '_blank',
              rel: 'noopener',
            }, 'aPToP book (free)'),
            el('a', {
              class: 'ext course',
              href: 'https://www.cs.utoronto.ca/~hehner/FMSD/',
              target: '_blank',
              rel: 'noopener',
            }, 'Video Course')))),
      el('div', { class: 'netty-bar' },
        el('h1', {}, 'Netty'),
        el('span', { class: 'tagline' }, 'a prover’s assistant for calculational proofs'),
        toolbar(s))),
    note === ''
      ? el('div', { class: 'note-bar quiet' },
          'examples…: PASS loads cleanly; FAIL opens with gaps; MISSING shows the stub (goal only); click a suggestion to take it')
      : el('div', { class: 'note-bar' + (noteIsError ? ' error' : '') }, note),
  ];
  if (bookExample !== null) {
    const summary = bookExample.theorem
      ? `Book source: ${bookExample.name} · ${bookExample.theorem}`
      : `Book source: ${bookExample.name}`;
    kids.push(el('details', { class: 'book-calc' },
      el('summary', {}, summary),
      el('pre', {}, bookExample.text)));
  }
  kids.push(el('main', { class: 'panes' }, proofPane(s), contextPane(s), suggestPane(s)));
  root.replaceChildren(...kids);
}

/** The keys the document's own description gives to the mouse. */
function keys(e: KeyboardEvent): void {
  const target = e.target as HTMLElement | null;
  if (target !== null && (target.tagName === 'INPUT' || target.tagName === 'SELECT')) return;
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  const s = state;
  if (s === null) return;
  if (/^[0-9]$/.test(e.key)) {
    const g = s.suggestions[Number(e.key)];
    if (g !== undefined && g.holes.length === 0) void cmd(`apply #${g.index}`);
    else if (g !== undefined) {
      // A row with a free variable wants the dialog, not a refusal.
      const row = document.querySelectorAll<HTMLElement>('.suggestion')[Number(e.key)];
      if (row !== undefined) holeDialog(g, row);
    }
    e.preventDefault();
  } else if (e.key === 'u') {
    if (s.canUndo) void cmd('undo');
    e.preventDefault();
  } else if (e.key === 'o') {
    if (s.canZoomOut) void cmd('out');
    e.preventDefault();
  } else if (e.key === 'Enter') {
    document.getElementById('direct')?.focus();
    e.preventDefault();
  }
}

document.addEventListener('keydown', keys);
draw();
void send('state');
