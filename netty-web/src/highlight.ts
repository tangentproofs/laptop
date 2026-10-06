/**
 * Lightweight aPToP expression highlighter for Netty proof panes.
 * Same token classes as deploy/aptop/site/js/aptop.js (`.cm-aptop-*`).
 */

const KEYWORDS = new Set([
  'ok', 'tick', 'ensure', 'assert', 'if', 'then', 'else', 'fi', 'while', 'do', 'od',
  'new', 'in', 'end', 'or', 'and', 'not', 'true', 'false', 'div', 'mod',
  'exit', 'when', 'for', 'var', 'proc', 'print', 'rand',
]);

const BOOLS = new Set(['true', 'false', '⊤', '⊥', 'T', 'F']);

const OPS = [
  ';..', '-->', '<--', '<==', '==', ':=', '=>', '<=', '>=', '!=', '||', '/\\', '\\/',
  '⇐', '⇒', '≡', '⟹', '⟸', '∧', '∨', '≠', '≤', '≥', '¬', '⧧',
];

export type TokenKind =
  | 'comment' | 'operator' | 'number' | 'keyword' | 'bool' | 'variable' | 'string'
  | 'or' | 'and';

export const TOKEN_CLASS: Record<TokenKind, string> = {
  comment: 'cm-aptop-comment',
  operator: 'cm-aptop-operator',
  number: 'cm-aptop-number',
  keyword: 'cm-aptop-keyword',
  bool: 'cm-aptop-bool',
  variable: 'cm-aptop-variable',
  string: 'cm-aptop-string',
  /** Hehner \/ (∨) — bigger/bolder in CSS */
  or: 'cm-aptop-or',
  /** Hehner /\ (∧) — lighter relative to or */
  and: 'cm-aptop-and',
};

type Piece = { text: string; kind: TokenKind | null };

/** Tokenize an aPToP / Netty expression string into colored pieces. */
export function tokenizeExpr(src: string): Piece[] {
  const out: Piece[] = [];
  let i = 0;
  const push = (text: string, kind: TokenKind | null) => {
    if (text === '') return;
    out.push({ text, kind });
  };
  while (i < src.length) {
    const ch = src[i]!;
    if (/\s/.test(ch)) {
      let j = i + 1;
      while (j < src.length && /\s/.test(src[j]!)) j++;
      push(src.slice(i, j), null);
      i = j;
      continue;
    }
    if (ch === '-' && src[i + 1] === '-' && src[i + 2] !== '>') {
      push(src.slice(i), 'comment');
      break;
    }
    if (ch === '"' || ch === "'") {
      let j = i + 1;
      while (j < src.length) {
        if (src[j] === '\\') { j += 2; continue; }
        if (src[j] === ch) { j++; break; }
        j++;
      }
      push(src.slice(i, j), 'string');
      i = j;
      continue;
    }
    let matched = false;
    for (const op of OPS) {
      if (src.startsWith(op, i)) {
        // Hehner: \/ (∨) bigger/bolder; /\ (∧) lighter — high contrast
        let kind: TokenKind = 'operator';
        if (op === '∨' || op === '\\/') kind = 'or';
        else if (op === '∧' || op === '/\\') kind = 'and';
        push(op, kind);
        i += op.length;
        matched = true;
        break;
      }
    }
    if (matched) continue;
    if (/^[.!?:;,+\-*/%=<>#\[\](){}]/.test(ch)) {
      push(ch, 'operator');
      i++;
      continue;
    }
    if (/[0-9]/.test(ch)) {
      let j = i + 1;
      while (j < src.length && /[0-9]/.test(src[j]!)) j++;
      push(src.slice(i, j), 'number');
      i = j;
      continue;
    }
    // Book constants ⊤ ⊥ and identifiers
    if (ch === '⊤' || ch === '⊥') {
      push(ch, 'bool');
      i++;
      continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      let j = i + 1;
      while (j < src.length && /[A-Za-z0-9_′']/.test(src[j]!)) j++;
      const w = src.slice(i, j);
      if (BOOLS.has(w)) push(w, 'bool');
      else if (KEYWORDS.has(w)) push(w, 'keyword');
      else push(w, 'variable');
      i = j;
      continue;
    }
    push(ch, null);
    i++;
  }
  return out;
}

/** Append highlighted tokens into `parent`. */
export function appendHighlighted(parent: HTMLElement, src: string): void {
  for (const p of tokenizeExpr(src)) {
    if (p.kind === null) {
      parent.append(document.createTextNode(p.text));
    } else {
      const span = document.createElement('span');
      span.className = TOKEN_CLASS[p.kind];
      span.textContent = p.text;
      parent.append(span);
    }
  }
}
