/**
 * Tiny CM6 mount helper for the aPToP highlighter (CDN only) + \xx expansions.
 */
import { aptopToken, KEYWORDS } from './aptop.js';
import { expansions } from './expansions.js';

export { KEYWORDS, expansions };

const _expKeys = Object.keys(expansions);
const _hasLonger = new Set();
for (const k of _expKeys)
  for (const k2 of _expKeys)
    if (k !== k2 && k2.startsWith(k)) { _hasLonger.add(k); break; }
const _allPrefixes = new Set();
for (const k of _expKeys)
  for (let i = 1; i < k.length; i++)
    _allPrefixes.add(k.substring(0, i));

/** Build CM6 input handlers for \code → Unicode (mirrors platform ui-edit.mts). */
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

async function loadStreamLang() {
  const { StreamLanguage } = await import(
    'https://esm.sh/@codemirror/language@6?deps=@codemirror/state@6,@codemirror/view@6'
  );
  return StreamLanguage.define({
    name: 'aptop',
    token(stream) {
      const t = aptopToken(stream);
      if (t === 'comment') return 'comment';
      if (t === 'operator') return 'operator';
      if (t === 'number') return 'number';
      if (t === 'keyword') return 'keyword';
      if (t === 'bool') return 'atom';
      if (t === 'variable') return 'variableName';
      return null;
    },
    languageData: { commentTokens: { line: '--' } },
  });
}

/**
 * @param {HTMLElement} parent
 * @param {string} doc
 * @param {{ readOnly?: boolean, maxHeight?: string }} [opts]
 * @returns {Promise<import('https://esm.sh/@codemirror/view@6').EditorView>}
 */
export async function mountAptopEditor(parent, doc, opts = {}) {
  const readOnly = opts.readOnly === true;
  const maxHeight = opts.maxHeight ?? '24rem';
  const [
    { EditorState },
    { EditorView, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter },
    { defaultKeymap, history, historyKeymap, isolateHistory },
    { syntaxHighlighting, defaultHighlightStyle },
  ] = await Promise.all([
    import('https://esm.sh/@codemirror/state@6'),
    import('https://esm.sh/@codemirror/view@6'),
    import('https://esm.sh/@codemirror/commands@6'),
    import('https://esm.sh/@codemirror/language@6?deps=@codemirror/state@6,@codemirror/view@6'),
  ]);

  const lang = await loadStreamLang();

  const dark = EditorView.theme({
    '&': { backgroundColor: '#121820', color: '#e7ecf1', maxHeight },
    '.cm-content': {
      caretColor: '#e7ecf1',
      fontFamily: 'ui-monospace, Menlo, Consolas, monospace',
      fontSize: '0.9rem',
    },
    '&.cm-focused .cm-cursor': { borderLeftColor: '#6cb6ff' },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground, ::selection': {
      backgroundColor: '#2a3542 !important',
    },
    '.cm-gutters': { backgroundColor: '#0f1419', color: '#697098', border: 'none' },
    '.cm-activeLine': { backgroundColor: '#1a222c' },
    '.cm-activeLineGutter': { backgroundColor: '#1a222c' },
    '.cm-keyword': { color: '#c792ea', fontWeight: '600' },
    '.cm-operator': { color: '#89ddff' },
    '.cm-number': { color: '#f78c6c' },
    '.cm-comment': { color: '#697098', fontStyle: 'italic' },
    '.cm-atom': { color: '#c3e88d' },
    '.cm-variableName': { color: '#e7ecf1' },
  }, { dark: true });

  const extensions = [
    lineNumbers(),
    highlightActiveLine(),
    highlightActiveLineGutter(),
    history(),
    keymap.of([...defaultKeymap, ...historyKeymap]),
    lang,
    syntaxHighlighting(defaultHighlightStyle, { fallback: true }),
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
