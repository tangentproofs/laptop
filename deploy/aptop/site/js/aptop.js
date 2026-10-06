/**
 * aPToP interpreter-language highlighter for CodeMirror 6 (CDN / no npm).
 *
 * Keywords match LaPToP/ProgramTheory/InterpreterLangSyntax.lean `keywords`.
 * Comments: `--` to end of line. Operators include ASCII and book glyphs.
 * Strings: "…" or '…'.
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
 * Returns: comment | operator | number | keyword | bool | variable | string | null
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

  // Strings (double or single quoted)
  const q = stream.peek();
  if (q === '"' || q === "'") {
    const quote = stream.next();
    while (!stream.eol()) {
      const ch = stream.next();
      if (ch === '\\') {
        if (!stream.eol()) stream.next();
        continue;
      }
      if (ch === quote) break;
    }
    return 'string';
  }

  // Multi-char operators (Hehner \/ = or, /\ = and)
  for (const op of OPS) {
    if (stream.match(op)) {
      if (op === '∨' || op === '\\/') return 'or';
      if (op === '∧' || op === '/\\') return 'and';
      return 'operator';
    }
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

/**
 * CSS classes in site.css — used when StreamLanguage returns these names
 * and they are applied as highlight classes (see aptop-editor.js).
 */
export const TOKEN_CLASS = {
  comment: 'cm-aptop-comment',
  operator: 'cm-aptop-operator',
  number: 'cm-aptop-number',
  keyword: 'cm-aptop-keyword',
  bool: 'cm-aptop-bool',
  variable: 'cm-aptop-variable',
  string: 'cm-aptop-string',
  or: 'cm-aptop-or',
  and: 'cm-aptop-and',
};

/**
 * Build a CodeMirror 6 LanguageSupport via StreamLanguage (dynamic import).
 * Prefer mountAptopEditor from aptop-editor.js for the live site.
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
