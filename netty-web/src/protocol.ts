/**
 * The protocol `lake exe netty --serve` speaks.
 *
 * These are the shapes `Netty/Api.lean` writes, and nothing here may decide
 * anything about a proof: the document model, the law matching, the
 * suggestions and what a proof proves all live in Lean, and this package draws
 * what the kernel says. One request is one JSON object on the kernel's
 * standard input; one answer is one line of JSON on its standard output.
 */

/** A line of the proof, as it is drawn. */
export interface LineView {
  /** Its index in the document, which is what `focus N` calls it. */
  index: number;
  /** How deeply it is nested in subproofs. */
  depth: number;
  /** The margin connective, or `''` on the first line of a level. */
  conn: string;
  /** The direction of the level this line opens, or `''`. */
  dir: string;
  /** The whole line, rendered. */
  expr: string;
  /** Whether `op` is written before the one operand, between them, or not. */
  kind: 'neg' | 'bin' | 'atom';
  /** The main operator's symbol, or `''`. */
  op: string;
  /** The main operands, rendered as they stand in `expr`. */
  parts: string[];
  /** What produced the line: a law's name, `zoom in`, `direct entry`, … */
  why: string;
  /** Whether the step to the next line is unjustified. */
  gap: boolean;
  /** What is written at the end of the line: the law that justifies the step
   * to the next one, or `!` for a gap. */
  note: string;
  /** Whether the focus sits just after this line. */
  focused: boolean;
  /** Whether the focus may be moved here. */
  focusable: boolean;
  /** Whether a click on one of `parts` may zoom in to it. */
  zoomable: boolean;
}

/** A suggestion for the line after the focus. */
export interface SuggestionView {
  /** Its number, which is what `apply #N` calls it. */
  index: number;
  /** The law it comes from. */
  law: string;
  /** The connective it would put in the margin. */
  op: string;
  /** The line it would write. */
  result: string;
  /** Law variables the match left unconstrained; a suggestion with any of
   * these cannot be applied. */
  holes: string[];
}

/** The whole state of a session: everything the three panes draw. */
export interface StateView {
  started: boolean;
  focus: number;
  depth: number;
  /** `'boolean'`, `'number'` or `''`. */
  ty: string;
  /** The direction of the innermost open level, as written at its type. */
  dir: string;
  /** The connectives that level's direction allows in the margin. */
  conns: string[];
  lines: LineView[];
  /** The laws the zoom stack has added, innermost level first. */
  context: string[];
  suggestions: SuggestionView[];
  /** What the proof proves, or why it does not prove anything yet. */
  outcome: string;
  proved: boolean;
  canUndo: boolean;
  canZoomOut: boolean;
  lawCount: number;
  /** The panes as `lake exe netty` prints them, for the text view. */
  proofPane: string;
  contextPane: string;
  suggestPane: string;
}

/** What a request may ask for. */
export type Op = 'state' | 'cmd' | 'demo' | 'reset' | 'save' | 'load';

/** One request. */
export interface Request {
  id?: number;
  op: Op;
  /** A script line, a demonstration's name, or the text of a proof file. */
  arg?: string;
}

/** One answer: the session after the request — unchanged, when it failed. */
export interface Response {
  id: number;
  ok: boolean;
  error: string;
  state: StateView;
  /** The text of a proof file, for `save`; `''` otherwise. */
  save: string;
}

/** The requests the web server will forward. */
export const OPS: readonly Op[] = ['state', 'cmd', 'demo', 'reset', 'save', 'load'];
