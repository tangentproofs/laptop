/**
 * The protocol `lake exe netty --serve` speaks.
 *
 * These are the shapes `Netty/Api.lean` writes, and nothing here may decide
 * anything about a proof: the document model, the law matching, the
 * suggestions and what a proof proves all live in Lean, and this package draws
 * what the kernel says. One request is one JSON object on the kernel's
 * standard input; one answer is one line of JSON on its standard output.
 */

/** A part of a line: a zoom target on the line before the focus
 * (`LineView.zooms`), or the place a suggestion would rewrite
 * (`SuggestionView.site`).
 *
 * `name` is what the script language calls the part, so a click sends
 * `zoom ${name}` and nothing here composes that string: the kernel names its own
 * parts, which is what keeps a click, a suggestion's site and a script zoom from
 * meaning different things by the same part. A single main operand is named by
 * its number and has `len === 1`; a contiguous segment of an association is
 * named `start:length` and has `len > 1`; the whole line has `len === 0` and is
 * never a zoom target, being the level one is already on. */
export interface PartView {
  /** What `zoom` calls it: `'1'`, or `'1:2'` for a segment. */
  name: string;
  /** The part, rendered as it stands in the line. */
  text: string;
  /** Which main operand the run starts at; `0` for the whole line. */
  start: number;
  /** How many main operands it takes; `0` for the whole line. */
  len: number;
}

/** A line of the proof, as it is drawn — one of `Doc.shownLines`, the document
 * after the display collapses, so the lines a collapse hides are not here. */
export interface LineView {
  /** Its index in the document, which is what `focus N` calls it. */
  index: number;
  /** How deeply it is drawn in subproofs — its own depth, unless merging two
   * zooms into one lifted it a level. */
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
  /** The parts a click may zoom in to, in the kernel's own order: each main
   * operand, then each contiguous segment of the association. Empty unless this
   * line can be zoomed in to at all. */
  zooms: PartView[];
  /** What produced the line: a law's name, `zoom in`, `direct entry`, … */
  why: string;
  /** Whether the step to the next line is unjustified. */
  gap: boolean;
  /** What is written at the end of the line: the law that justifies the step
   * to the next one, or `!` for a gap. */
  note: string;
  /** Whether the focus sits just after this line. */
  focused: boolean;
  /** Whether the focus may be moved here. A line of an outer level may be: the
   * kernel closes the levels below it, as a run of zoom-outs would. */
  focusable: boolean;
  /** Whether moving the focus here would re-open a subproof that has been
   * zoomed out of, rather than stay in an open level or close down to one. */
  reopens: boolean;
  /** Whether this line can be zoomed in to: whether `zooms` offers anything. */
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
  /** The place on the line before the focus this step would rewrite: the whole
   * line, one of its main operands, or a contiguous run of them — named as the
   * zoom targets are named, because it is the same part of the same line. */
  site: PartView;
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
  /** The lines the display draws: every line of the document except the ones
   * the collapses hide. */
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
