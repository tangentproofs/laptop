/**
 * Tiny CM6 mount helper for the aPToP highlighter (CDN only).
 * Import from interp/examples pages as a module.
 */
import { aptopToken, KEYWORDS } from './aptop.js';

export { KEYWORDS };

async function loadStreamLang() {
  const { StreamLanguage } = await import('https://esm.sh/@codemirror/language@6?deps=@codemirror/state@6,@codemirror/view@6');
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
 * @param {{ readOnly?: boolean }} [opts]
 */
export async function mountAptopEditor(parent, doc, opts = {}) {
  const readOnly = opts.readOnly !== false;
  const [
    { EditorState },
    { EditorView, keymap, lineNumbers, highlightActiveLine, highlightActiveLineGutter },
    { defaultKeymap, history, historyKeymap },
    { syntaxHighlighting, defaultHighlightStyle },
  ] = await Promise.all([
    import('https://esm.sh/@codemirror/state@6'),
    import('https://esm.sh/@codemirror/view@6'),
    import('https://esm.sh/@codemirror/commands@6'),
    import('https://esm.sh/@codemirror/language@6?deps=@codemirror/state@6,@codemirror/view@6'),
  ]);

  const lang = await loadStreamLang();

  const dark = EditorView.theme({
    '&': { backgroundColor: '#121820', color: '#e7ecf1', maxHeight: '24rem' },
    '.cm-content': { caretColor: '#e7ecf1', fontFamily: 'ui-monospace, Menlo, Consolas, monospace', fontSize: '0.9rem' },
    '&.cm-focused .cm-cursor': { borderLeftColor: '#6cb6ff' },
    '&.cm-focused .cm-selectionBackground, .cm-selectionBackground, ::selection': {
      backgroundColor: '#2a3542 !important',
    },
    '.cm-gutters': { backgroundColor: '#0f1419', color: '#697098', border: 'none' },
    '.cm-activeLine': { backgroundColor: '#1a222c' },
    '.cm-activeLineGutter': { backgroundColor: '#1a222c' },
    // StreamLanguage tag → class styling (lezer highlight tags as CSS)
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

  const state = EditorState.create({ doc, extensions });
  return new EditorView({ state, parent });
}
