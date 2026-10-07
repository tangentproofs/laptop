/**
 * CM6 mount helper for the aPToP highlighter (CDN only), optional
 * keyboard expansions, and a mobile-friendly symbol sheet.
 *
 * Highlighting: a ViewPlugin re-tokenizes visible lines with aptopToken and
 * applies site.css classes (`.cm-aptop-keyword`, …). We do not rely on
 * HighlightStyle + Lezer tags — esm.sh can load two copies of
 * @lezer/highlight, so tag identity fails and tokens stay uncolored.
 */
import { aptopToken, KEYWORDS, TOKEN_CLASS } from './aptop.js';
import { expansions, expansionGroups } from './expansions.js';

export { KEYWORDS, expansions, expansionGroups, TOKEN_CLASS };

/** Common aPToP symbols for the insert sheet — glyph + plain name only. */
export const SYMBOL_SHEET = [
  { glyph: '∧', name: 'and' },
  { glyph: '∨', name: 'or' },
  { glyph: '¬', name: 'not' },
  { glyph: '⇒', name: 'implies' },
  { glyph: '⇐', name: 'implied by' },
  { glyph: '≡', name: 'equivalent' },
  { glyph: '≢', name: 'not equivalent' },
  { glyph: '⊤', name: 'true' },
  { glyph: '⊥', name: 'false' },
  { glyph: '≠', name: 'not equal' },
  { glyph: '≤', name: 'less or equal' },
  { glyph: '≥', name: 'greater or equal' },
  { glyph: '×', name: 'times' },
  { glyph: '·', name: 'dot' },
  { glyph: '′', name: 'prime' },
  { glyph: '″', name: 'double prime' },
  { glyph: '∀', name: 'for all' },
  { glyph: '∃', name: 'exists' },
  { glyph: '∈', name: 'in' },
  { glyph: '∉', name: 'not in' },
  { glyph: '∪', name: 'union' },
  { glyph: '∩', name: 'intersection' },
  { glyph: '⊆', name: 'subset' },
  { glyph: '∘', name: 'compose' },
  { glyph: '⟹', name: 'long implies' },
  { glyph: '⟸', name: 'long implied by' },
  { glyph: '→', name: 'to' },
  { glyph: '←', name: 'from' },
  { glyph: '⊢', name: 'turnstile' },
  { glyph: '∞', name: 'infinity' },
  { glyph: '□', name: 'box' },
  { glyph: '◇', name: 'diamond' },
];

const _expKeys = Object.keys(expansions);
const _hasLonger = new Set();
for (const k of _expKeys)
  for (const k2 of _expKeys)
    if (k !== k2 && k2.startsWith(k)) { _hasLonger.add(k); break; }
const _allPrefixes = new Set();
for (const k of _expKeys)
  for (let i = 1; i < k.length; i++)
    _allPrefixes.add(k.substring(0, i));

/** Quiet desktop input handlers: typed escapes → Unicode (not advertised in UI). */
function expansionExtensions(isolateHistory, EditorView) {
  const expansionInput = EditorView.inputHandler.of((view, from, _to, text) => {
    if (text.length !== 1) return false;
    const start = Math.max(0, from - 20);
    const before = view.state.doc.sliceString(start, from);
    const bsIdx = before.lastIndexOf('\\');
    if (bsIdx < 0) return false;
    const bsPos = start + bsIdx;
    const codeSoFar = before.substring(bsIdx + 1);
    const fullCode = codeSoFar + text;

    if (fullCode in expansions) {
      if (!_hasLonger.has(fullCode)) {
        view.dispatch({
          changes: { from: bsPos, to: from, insert: expansions[fullCode] },
          annotations: isolateHistory.of('full'),
        });
        return true;
      }
      return false;
    }

    if (_allPrefixes.has(fullCode)) return false;

    if (codeSoFar in expansions) {
      view.dispatch({
        changes: { from: bsPos, to: from, insert: expansions[codeSoFar] + text },
        annotations: isolateHistory.of('full'),
      });
      return true;
    }

    return false;
  });

  const blockExpansionInput = EditorView.inputHandler.of((view, from, _to, text) => {
    if (text !== '}') return false;
    const start = Math.max(0, from - 100);
    const before = view.state.doc.sliceString(start, from);
    const caret = before.lastIndexOf('\\^{');
    const under = before.lastIndexOf('\\_{');
    const idx = Math.max(caret, under);
    if (idx < 0) return false;
    const prefix = before[idx + 1];
    const content = before.substring(idx + 3);
    const converted = [...content].map((ch) => expansions[prefix + ch] ?? ch).join('');
    const absPos = start + idx;
    view.dispatch({
      changes: { from: absPos, to: from, insert: converted },
      annotations: isolateHistory.of('full'),
    });
    return true;
  });

  return [expansionInput, blockExpansionInput];
}

/** Minimal StringStream for aptopToken (same surface CM StreamLanguage uses). */
function stringStream(line) {
  let pos = 0;
  let start = 0;
  return {
    eol: () => pos >= line.length,
    sol: () => pos === 0,
    peek: () => line.charAt(pos) || undefined,
    next: () => (pos < line.length ? line.charAt(pos++) : undefined),
    eat: (match) => {
      const ch = line.charAt(pos);
      if (!ch) return undefined;
      const ok = typeof match === 'string' ? ch === match
        : match instanceof RegExp ? match.test(ch) : match(ch);
      if (ok) { pos++; return ch; }
      return undefined;
    },
    eatWhile: (match) => {
      const startPos = pos;
      while (pos < line.length) {
        const ch = line.charAt(pos);
        const ok = typeof match === 'string' ? ch === match
          : match instanceof RegExp ? match.test(ch) : match(ch);
        if (!ok) break;
        pos++;
      }
      return pos > startPos;
    },
    eatSpace: () => {
      const m = /^[ \t\r\n]+/.exec(line.slice(pos));
      if (!m) return false;
      pos += m[0].length;
      return true;
    },
    match: (pat, consume = true, caseInsensitive = false) => {
      if (typeof pat === 'string') {
        const slice = line.slice(pos, pos + pat.length);
        const a = caseInsensitive ? slice.toLowerCase() : slice;
        const b = caseInsensitive ? pat.toLowerCase() : pat;
        if (a === b) {
          if (consume !== false) pos += pat.length;
          return true;
        }
        return null;
      }
      const flags = pat.flags.includes('g') ? pat.flags : pat.flags + 'g';
      const re = new RegExp(pat.source, caseInsensitive && !flags.includes('i') ? flags + 'i' : flags);
      re.lastIndex = 0;
      const m = re.exec(line.slice(pos));
      if (!m || m.index !== 0) return null;
      if (consume !== false) pos += m[0].length;
      return m;
    },
    current: () => line.slice(start, pos),
    get pos() { return pos; },
    set pos(v) { pos = v; },
    get start() { return start; },
    set start(v) { start = v; },
  };
}

/**
 * Build CM6 Decoration marks from aptopToken → site.css `.cm-aptop-*` classes.
 */
function aptopHighlightExtension(RangeSetBuilder, Decoration, ViewPlugin) {
  const markCache = new Map();
  function mark(cls) {
    let m = markCache.get(cls);
    if (!m) {
      m = Decoration.mark({ class: cls });
      markCache.set(cls, m);
    }
    return m;
  }

  function buildDecos(view) {
    const builder = new RangeSetBuilder();
    for (const { from, to } of view.visibleRanges) {
      let pos = from;
      while (pos < to) {
        const line = view.state.doc.lineAt(pos);
        const stream = stringStream(line.text);
        while (!stream.eol()) {
          stream.start = stream.pos;
          const kind = aptopToken(stream);
          // aptopToken may eat space and return null without advancing past non-space
          if (stream.pos === stream.start) {
            stream.next();
            continue;
          }
          if (kind) {
            const cls = TOKEN_CLASS[kind];
            if (cls) {
              builder.add(line.from + stream.start, line.from + stream.pos, mark(cls));
            }
          }
        }
        pos = line.to + 1;
      }
    }
    return builder.finish();
  }

  return ViewPlugin.fromClass(class {
    constructor(view) {
      this.decorations = buildDecos(view);
    }
    update(update) {
      if (update.docChanged || update.viewportChanged)
        this.decorations = buildDecos(update.view);
    }
  }, { decorations: (v) => v.decorations });
}

/** Insert text at the cursor of a CM6 view (or replace the selection). */
export function insertIntoEditor(view, text) {
  if (!view) return;
  const { from, to } = view.state.selection.main;
  view.dispatch({
    changes: { from, to, insert: text },
    selection: { anchor: from + text.length },
  });
  view.focus();
}

/**
 * One Symbols control for the whole editor.
 *
 * mode:
 *   - "dock"  — always-visible side panel (desktop / Netty-suggestions style)
 *   - "sheet" — one button + popover / bottom sheet (mobile)
 *   - "auto"  — dock when viewport ≥ 900px, sheet otherwise (default)
 *
 * @param {HTMLElement} host
 * @param {() => import('@codemirror/view').EditorView | null} getView
 * @param {{ mode?: 'dock'|'sheet'|'auto' }} [opts]
 */
export function mountSymbolSheet(host, getView, opts = {}) {
  const modeOpt = opts.mode || 'auto';
  host.classList.add('sym-host');
  host.replaceChildren();

  const panel = document.createElement('div');
  panel.className = 'sym-panel';
  panel.setAttribute('role', 'region');
  panel.setAttribute('aria-label', 'Common aPToP symbols');

  const head = document.createElement('div');
  head.className = 'sym-panel-head';
  head.innerHTML = '<span>Symbols</span>';
  const close = document.createElement('button');
  close.type = 'button';
  close.className = 'sym-panel-close';
  close.setAttribute('aria-label', 'Close symbols');
  close.textContent = '×';
  head.append(close);
  panel.append(head);

  const grid = document.createElement('div');
  grid.className = 'sym-panel-grid';
  for (const { glyph, name } of SYMBOL_SHEET) {
    const cell = document.createElement('button');
    cell.type = 'button';
    cell.className = 'sym-panel-cell';
    cell.title = name;
    cell.innerHTML = `<span class="glyph">${glyph}</span><span class="name">${name}</span>`;
    cell.addEventListener('click', () => {
      insertIntoEditor(getView(), glyph);
      if (host.classList.contains('is-sheet') && window.matchMedia('(max-width: 899px)').matches) {
        setOpen(false);
      }
    });
    grid.append(cell);
  }
  panel.append(grid);

  const hint = document.createElement('p');
  hint.className = 'sym-panel-hint';
  hint.textContent = 'Click a symbol to insert it at the cursor.';
  panel.append(hint);

  const btn = document.createElement('button');
  btn.type = 'button';
  btn.className = 'sym-sheet-btn';
  btn.setAttribute('aria-haspopup', 'dialog');
  btn.setAttribute('aria-expanded', 'false');
  btn.textContent = 'Symbols';
  btn.title = 'Insert a common aPToP symbol';

  const backdrop = document.createElement('div');
  backdrop.className = 'sym-backdrop';
  backdrop.hidden = true;

  function isDockPreferred() {
    if (modeOpt === 'dock') return true;
    if (modeOpt === 'sheet') return false;
    return window.matchMedia('(min-width: 900px)').matches;
  }

  function applyLayout() {
    const dock = isDockPreferred();
    host.classList.toggle('is-dock', dock);
    host.classList.toggle('is-sheet', !dock);
    if (dock) {
      panel.hidden = false;
      backdrop.hidden = true;
      btn.hidden = true;
      btn.setAttribute('aria-expanded', 'false');
    } else {
      btn.hidden = false;
      if (btn.getAttribute('aria-expanded') !== 'true') {
        panel.hidden = true;
        backdrop.hidden = true;
      }
    }
  }

  function setOpen(open) {
    if (host.classList.contains('is-dock')) {
      panel.hidden = false;
      return;
    }
    panel.hidden = !open;
    backdrop.hidden = !open;
    btn.setAttribute('aria-expanded', open ? 'true' : 'false');
    if (open) panel.querySelector('.sym-panel-cell')?.focus();
  }

  btn.addEventListener('click', () => setOpen(panel.hidden));
  close.addEventListener('click', () => setOpen(false));
  backdrop.addEventListener('click', () => setOpen(false));
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape' && host.classList.contains('is-sheet') && !panel.hidden) setOpen(false);
  });
  window.addEventListener('resize', applyLayout);

  host.append(btn, backdrop, panel);
  applyLayout();
  return { button: btn, panel, setOpen, applyLayout };
}

/** @deprecated alias — use mountSymbolSheet */
export const mountSymbolDock = mountSymbolSheet;

/**
 * @param {HTMLElement} parent
 * @param {string} doc
 * @param {{ readOnly?: boolean, maxHeight?: string }} [opts]
 */
export async function mountAptopEditor(parent, doc, opts = {}) {
  const readOnly = opts.readOnly === true;
  const maxHeight = opts.maxHeight ?? '24rem';
  const [
    { EditorState, RangeSetBuilder },
    { EditorView, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter, Decoration, ViewPlugin },
    { defaultKeymap, history, historyKeymap, isolateHistory },
  ] = await Promise.all([
    import('https://esm.sh/@codemirror/state@6'),
    import('https://esm.sh/@codemirror/view@6'),
    import('https://esm.sh/@codemirror/commands@6'),
  ]);

  const dark = EditorView.theme({
    '&': { backgroundColor: '#272822', color: '#f8f8f2', maxHeight },
    '.cm-content': {
      caretColor: '#f8f8f2',
      fontFamily: 'ui-monospace, Menlo, Consolas, monospace',
      fontSize: '0.9rem',
    },
    '&.cm-focused .cm-cursor': { borderLeftColor: '#f8f8f2' },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground, ::selection': {
      backgroundColor: '#49483e !important',
    },
    '.cm-gutters': { backgroundColor: '#272822', color: '#75715e', border: 'none' },
    '.cm-activeLine': { backgroundColor: '#3e3d32' },
    '.cm-activeLineGutter': { backgroundColor: '#3e3d32' },
  }, { dark: true });

  const extensions = [
    lineNumbers(),
    highlightActiveLine(),
    highlightActiveLineGutter(),
    history(),
    keymap.of([...defaultKeymap, ...historyKeymap]),
    aptopHighlightExtension(RangeSetBuilder, Decoration, ViewPlugin),
    dark,
    EditorView.lineWrapping,
    EditorView.editable.of(!readOnly),
    EditorState.readOnly.of(readOnly),
  ];

  if (!readOnly) {
    extensions.push(...expansionExtensions(isolateHistory, EditorView));
  }

  const state = EditorState.create({ doc, extensions });
  return new EditorView({ state, parent });
}
