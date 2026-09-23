/**
 * The three panes.
 *
 * Netty's calculation window is a proof pane, a context pane and a
 * suggestions pane. This draws those three from the state the kernel sends,
 * and turns a click into one line of the kernel's script language: a click on
 * a suggestion is `apply #N`, a click on a main operand is `zoom N`, a click
 * on a line's number is `focus N`. Nothing about a proof is decided here.
 */

import type { LineView, Op, Response, StateView, SuggestionView } from './protocol.js';

/** The state the kernel last sent. */
let state: StateView | null = null;
/** What to say above the panes, and whether it is a complaint. */
let note = '';
let noteIsError = false;
/** Whether the panes are drawn as the command line prints them. */
let asText = false;
/** What the direct-entry and start rows hold, kept across a redraw. */
const typed = { start: '', direct: '', ty: 'boolean', startConn: '⇐', directConn: '' };

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

/** Ask the kernel, then redraw. A refused request leaves the state alone and
 * says why, which is what the kernel's answer already carries. */
async function send(op: Op, arg = ''): Promise<Response | null> {
  let answer: Response;
  try {
    const res = await fetch('/api', {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ op, arg }),
    });
    answer = (await res.json()) as Response;
  } catch (e) {
    note = `the server: ${String(e)}`;
    noteIsError = true;
    draw();
    return null;
  }
  if (answer.state) state = answer.state;
  note = answer.ok ? '' : answer.error;
  noteIsError = !answer.ok;
  draw();
  return answer;
}

/** Run one line of the script language. */
const cmd = (line: string) => send('cmd', line);

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

/** A line's formula, drawn as its main operands with the main operator
 * between them. Where the line can be zoomed in to, each operand is a
 * button: clicking it is the document's "click on a subexpression". */
function formula(l: LineView): HTMLElement {
  const box = el('span', { class: 'formula' });
  if (l.parts.length === 0 || (!l.zoomable && l.parts.length < 2 && l.kind !== 'neg')) {
    box.append(el('span', { class: 'atom' }, l.expr));
    return box;
  }
  const piece = (text: string, i: number): Node => {
    if (!l.zoomable) return el('span', { class: 'operand' }, text);
    const b = el('button', {
      class: 'operand zoom', title: `zoom in to ${text}`,
    }, text);
    b.addEventListener('click', () => void cmd(`zoom ${i}`));
    return b;
  };
  if (l.kind === 'neg') {
    box.append(el('span', { class: 'op' }, l.op), piece(l.parts[0] ?? '', 0));
    return box;
  }
  l.parts.forEach((p, i) => {
    if (i > 0) box.append(el('span', { class: 'op' }, ` ${l.op} `));
    box.append(piece(p, i));
  });
  return box;
}

/** One line of the proof. */
function lineRow(l: LineView): HTMLElement {
  const row = el('div', {
    class: ['line', l.focused ? 'focused' : '', l.gap ? 'gapped' : ''].filter(Boolean).join(' '),
    style: `--depth: ${l.depth}`,
  });
  const gutter = el('button', {
    class: 'gutter' + (l.focusable ? ' movable' : ''),
    title: l.focusable ? 'move the focus here' : 'the focus moves only within the innermost level',
  }, String(l.index));
  if (l.focusable) gutter.addEventListener('click', () => void cmd(`focus ${l.index}`));
  row.append(gutter);
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
    body.append(el('p', { class: 'quiet' }, 'no proof yet: give the first line, or replay a demonstration.'));
    body.append(startRow());
  } else {
    for (const l of s.lines) {
      body.append(lineRow(l));
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
    body.append(el('p', { class: 'quiet' }, 'no context: zooming in to an operand gains what the others say.'));
  } else {
    for (const c of s.context) body.append(el('div', { class: 'law' }, c));
  }
  pane.append(body);
  return pane;
}

/** One suggestion: what a law would write next. */
function suggestionRow(g: SuggestionView): HTMLElement {
  const blocked = g.holes.length > 0;
  const row = el('button', {
    class: 'suggestion' + (blocked ? ' blocked' : ''),
    title: blocked
      ? `${g.holes.join(', ')} unconstrained: this law needs more than the line to settle it`
      : `apply #${g.index} — ${g.law}`,
  });
  if (blocked) row.setAttribute('disabled', 'disabled');
  row.append(el('span', { class: 'gutter' }, String(g.index)));
  row.append(el('span', { class: 'margin' }, g.op));
  row.append(el('span', { class: 'formula' }, g.result));
  row.append(el('span', { class: 'note' }, blocked ? `${g.law} (${g.holes.join(', ')}?)` : g.law));
  if (!blocked) row.addEventListener('click', () => void cmd(`apply #${g.index}`));
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
  const demos = el('select', { class: 'demos', title: 'replay a demonstration of the document' });
  demos.append(el('option', { value: '' }, 'demonstration…'));
  for (const d of ['portation', 'discharge', 'gap']) demos.append(el('option', { value: d }, d));
  demos.addEventListener('change', () => {
    if (demos.value !== '') void send('demo', demos.value);
    demos.value = '';
  });
  bar.append(demos);
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
  root.replaceChildren(
    el('header', {},
      el('h1', {}, 'Netty'),
      el('span', { class: 'tagline' }, 'a prover’s assistant for calculational proofs'),
      toolbar(s)),
    note === ''
      ? el('div', { class: 'note-bar quiet' },
          'click a suggestion to take it, a subexpression to zoom in, a line number to move the focus')
      : el('div', { class: 'note-bar' + (noteIsError ? ' error' : '') }, note),
    el('main', { class: 'panes' }, proofPane(s), contextPane(s), suggestPane(s)),
  );
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
