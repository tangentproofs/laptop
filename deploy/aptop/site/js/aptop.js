/**
 * aPToP interpreter-language highlighter for CodeMirror 6 (CDN / no npm).
 *
 * Keywords match LaPToP/ProgramTheory/InterpreterLangSyntax.lean `keywords`.
 * Comments: `--` to end of line. Operators include ASCII and book glyphs.
 *
 * Usage (esm.sh):
 *   import { aptop } from './aptop.js';
 *   import { EditorView, basicSetup } from '…';
 *   new EditorView({ extensions: [basicSetup, aptop(), EditorView.editable.of(false), …] });
 */

/** Keyword list from InterpreterLangSyntax.lean. */
export const KEYWORDS = [
  'ok', 'tick', 'ensure', 'assert', 'if', 'then', 'else', 'fi', 'while', 'do', 'od',
  'new', 'in', 'end', 'or', 'and', 'not', 'true', 'false', 'div', 'mod',
  'exit', 'when', 'for', 'var', 'proc', 'print', 'rand',
];

const KW = new Set(KEYWORDS);

/** Multi-character operators, longest first (ASCII + book). */
const OPS = [
  ';..', '-->', '<--', '<==', '==', ':=', '=>', '<=', '>=', '!=', '||', '/\\', '\\/',
  '⇐', '⇒', '≡', '⟹', '⟸', '∧', '∨', '≠', '≤', '≥', '¬',
];

function isIdStart(ch) {
  return /[A-Za-z_]/.test(ch);
}
function isIdCont(ch) {
  return /[A-Za-z0-9_]/.test(ch);
}
function isDigit(ch) {
  return /[0-9]/.test(ch);
}

/**
 * StreamLanguage-compatible tokenizer (CodeMirror 6 StreamLanguage.define).
 * Also works as a plain next-token scanner for tests.
 */
export function aptopToken(stream) {
  if (stream.eatSpace()) return null;

  // Line comment `--` (but not `-->`); stop at newline.
  if (stream.match(/^--(?!>)/)) {
    while (!stream.eol()) {
      const ch = stream.peek();
      if (ch === '\n' || ch === '\r') break;
      stream.next();
    }
    return 'comment';
  }

  // Multi-char operators
  for (const op of OPS) {
    if (stream.match(op)) return 'operator';
  }

  // Single-char punctuation / ops
  if (stream.match(/^[.!?:;,+\-*/%=<>#\[\](){}]/)) return 'operator';

  // Numbers
  if (isDigit(stream.peek())) {
    stream.match(/^[0-9]+/);
    return 'number';
  }

  // Identifiers / keywords
  if (isIdStart(stream.peek())) {
    stream.match(/^[A-Za-z_][A-Za-z0-9_]*/);
    const w = stream.current();
    if (KW.has(w)) {
      if (w === 'true' || w === 'false') return 'bool';
      return 'keyword';
    }
    return 'variable';
  }

  stream.next();
  return null;
}

/** CSS class map used by StreamLanguage. */
const TOKEN_CLASS = {
  comment: 'cm-aptop-comment',
  operator: 'cm-aptop-operator',
  number: 'cm-aptop-number',
  keyword: 'cm-aptop-keyword',
  bool: 'cm-aptop-bool',
  variable: 'cm-aptop-variable',
};

/**
 * Build a CodeMirror 6 LanguageSupport via StreamLanguage (dynamic import).
 * Returns a Promise of an Extension (or LanguageSupport).
 */
export async function aptop() {
  const { StreamLanguage } = await import('https://esm.sh/@codemirror/language@6');
  const lang = StreamLanguage.define({
    name: 'aptop',
    token(stream) {
      const t = aptopToken(stream);
      return t == null ? null : TOKEN_CLASS[t] ?? t;
    },
    languageData: {
      commentTokens: { line: '--' },
    },
  });
  return lang;
}

/**
 * Mount a read-only (or editable) editor into `parent`.
 * @param {HTMLElement} parent
 * @param {string} doc
 * @param {{ readOnly?: boolean }} [opts]
 */
export async function mountAptopEditor(parent, doc, opts = {}) {
  const readOnly = opts.readOnly !== false;
  const [
    { EditorView, basicSetup },
    { EditorState },
  ] = await Promise.all([
    import('https://esm.sh/@codemirror/basic-setup@0.20.0'),
    import('https://esm.sh/@codemirror/state@6'),
  ]);
  // basic-setup 0.20 re-exports; prefer explicit CM6 pieces if basicSetup shape differs
  let extensions;
  try {
    const lang = await aptop();
    const { keymap } = await import('https://esm.sh/@codemirror/view@6');
    const { defaultKeymap, history, historyKeymap } = await import('https://esm.sh/@codemirror/commands@6');
    const { HighlightStyle, syntaxHighlighting } = await import('https://esm.sh/@codemirror/language@6');
    const { tags } = await import('https://esm.sh/@lezer/highlight@1');

    // StreamLanguage returns class names as style tags via CSS we ship in site.css.
    // Also add a dark theme for the chrome.
    const dark = EditorView.theme({
      '&': { backgroundColor: '#121820', color: '#e7ecf1' },
      '.cm-content': { caretColor: '#e7ecf1' },
      '&.cm-focused .cm-cursor': { borderLeftColor: '#6cb6ff' },
      '&.cm-focused .cm-selectionBackground, .cm-selectionBackground': {
        backgroundColor: '#2a3542',
      },
      '.cm-gutters': { backgroundColor: '#0f1419', color: '#697098', border: 'none' },
    }, { dark: true });

    extensions = [
      history(),
      keymap.of([...defaultKeymap, ...historyKeymap]),
      lang,
      dark,
      EditorView.lineWrapping,
      EditorView.editable.of(!readOnly),
      EditorState.readOnly.of(readOnly),
    ];
    // silence unused
    void basicSetup; void HighlightStyle; void syntaxHighlighting; void tags;
  } catch (e) {
    console.error('aptop editor setup failed', e);
    parent.textContent = doc;
    return null;
  }

  const state = EditorState.create({ doc, extensions });
  const view = new EditorView({ state, parent });
  return view;
}
