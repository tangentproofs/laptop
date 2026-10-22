/**
 * The guided tutorial: short lessons played inside the real three panes.
 *
 * Nothing here decides whether a step is right. Every lesson starts its proof
 * with the kernel's own `start`, the learner takes each step by clicking the
 * real panes, and a step counts as done only when the state the kernel sends
 * back says so: which line the focus is on, at what depth, which law the line
 * above it names, what the context holds and what the proof proves. The
 * tutorial only reads that state, draws a card with what to do next, and makes
 * the thing to click pulse.
 */

import type { LineView, Response, StateView } from './protocol.js';

/** What the client lends the tutorial. */
export interface TutorialHost {
  send(op: 'reset' | 'cmd', arg?: string): Promise<Response | null>;
  state(): StateView | null;
  redraw(): void;
  /** Fill the start row (type, direction, first line) without starting. */
  prefillStart(ty: string, conn: string, text: string): void;
  /** Light up the part of the line a suggestion would rewrite. */
  showSite(site: import('./protocol.js').PartView | null): void;
}

/** What a step asks the learner to click. */
type Target =
  | { kind: 'start' }
  | { kind: 'suggestion'; law: string; result: string }
  | { kind: 'hole'; law: string; result: string }
  | { kind: 'zoom'; text: string }
  | { kind: 'out' }
  | { kind: 'undo' }
  | { kind: 'outcome' }
  | { kind: 'context' }
  | { kind: 'proof' }
  | { kind: 'suggestions' }
  | { kind: 'gap' };

interface Step {
  /** What to do, in plain words. `x ∧ y` between backquotes is drawn as a formula. */
  say: string;
  /** What to make pulse. */
  targets?: Target[];
  /** Done when the kernel's state says so. */
  done?: (s: StateView) => boolean;
  /** A step that only explains: done when the learner presses this button. */
  ack?: string;
  /** Kernel script lines sent (after a reset) when this step begins. */
  setup?: string[];
  /** Prefill the start row instead of starting (lesson 1). */
  prefill?: [string, string, string];
  /** Say what happened, once the step is done (shown on the next step). */
  then?: string;
}

interface Lesson {
  id: string;
  title: string;
  /** One line: what the lesson teaches. */
  teaches: string;
  /** What the finished proof proves, as the kernel will say it. */
  goal: string;
  /** The book reference, if the proof is the book's. */
  book?: string;
  steps: Step[];
  /** Said when the last step is done. */
  success: string;
  /** Pulse only after "show me" (the last lesson, done mostly unaided). */
  quiet?: boolean;
}

// ---------------------------------------------------------------------------
// Reading the kernel's state.

const focusedLine = (s: StateView): LineView | undefined => s.lines.find((l) => l.focused);

/** The line drawn just above the focused one: its note names the law that
 * justified the step to the focused line. */
function lineAbove(s: StateView): LineView | undefined {
  const i = s.lines.findIndex((l) => l.focused);
  return i > 0 ? s.lines[i - 1] : undefined;
}

/** The focus is on a line reading `expr`, at `depth`, reached by `law` (if
 * given), and no line of the proof is a gap unless `gap` allows it. */
function at(s: StateView, expr: string, depth: number, law?: string, gap = false): boolean {
  if (!s.started) return false;
  const f = focusedLine(s);
  if (f === undefined || f.expr !== expr || s.depth !== depth) return false;
  if (law !== undefined && lineAbove(s)?.note !== law) return false;
  if (!gap && s.lines.some((l) => l.gap)) return false;
  return true;
}

const proves = (s: StateView, what: string) => s.proved && s.depth === 0 && s.outcome === what;

/** What a step began from, so that a different state means "off the path". */
function signature(s: StateView | null): string {
  if (s === null) return '';
  return JSON.stringify([s.started, s.depth, s.focus,
    s.lines.map((l) => [l.index, l.depth, l.expr, l.note, l.gap])]);
}

// ---------------------------------------------------------------------------
// The lessons. Every expression below is written exactly as the kernel draws
// it; scripts/tutorial-e2e.mjs plays each lesson against the kernel.

export const LESSONS: Lesson[] = [
  {
    id: 'panes',
    title: 'The three panes',
    teaches: 'what a proof is here, and what each pane shows',
    goal: 'start a proof whose first line is `a ∧ ⊤`',
    steps: [
      {
        say: 'A proof in Ampheck is a calculation: a column of lines, each one '
          + 'connected to the line above it by a sign in the margin (`=`, `⇒` or `⇐`) '
          + 'and justified by a law. You write the first line; the laws write the rest.\n'
          + 'The first line is already typed for you: `a ∧ ⊤` (“a and true”), with `=` '
          + 'as the direction, meaning every step must keep the line equal. Press start.',
        prefill: ['boolean', '=', 'a ∧ ⊤'],
        targets: [{ kind: 'start' }],
        done: (s) => at(s, 'a ∧ ⊤', 0),
      },
      {
        say: 'The proof pane (left) holds your calculation. The bright row is the '
          + 'focus: the next line goes just under it. Its parts are buttons; you will '
          + 'use them in lesson 5.\n'
          + 'At the foot of the proof pane is what the calculation proves so far. With '
          + 'one line it only proves `a ∧ ⊤ = a ∧ ⊤`, which is true but says nothing. '
          + 'A goal is the statement you want that foot to say.',
        targets: [{ kind: 'proof' }, { kind: 'outcome' }],
        ack: 'Got it',
      },
      {
        say: 'The context pane (middle) lists facts you may use only inside a part '
          + 'of the line. It is empty now; lessons 5 to 7 fill it.\n'
          + 'The suggestions pane (right) lists every line a law could write next, '
          + 'best first. Each row shows the margin sign, the new line, and the law\'s '
          + 'name. Clicking a row takes that step, and the kernel checks it.\n'
          + 'A small reading tip: “or” (`∨`) is drawn big and bold, “and” (`∧`) small '
          + 'and grey, so you can tell them apart at a glance.',
        targets: [{ kind: 'context' }, { kind: 'suggestions' }],
        ack: 'Next',
      },
    ],
    success: 'That is the whole window. Next you take your first step.',
  },
  {
    id: 'one-law',
    title: 'Take one step',
    teaches: 'pick a suggestion to rewrite the line with a law',
    goal: '`a ∧ ⊤ = a`',
    steps: [
      {
        setup: ['start boolean = a ∧ ⊤'],
        say: '“a and true” is just a. The top suggestion writes `a`, by the law called identity '
          + '(`⊤ ∧ a ≡ a`). Point at it (or press and hold on a phone): the part of '
          + 'the line it rewrites lights up in yellow. Here it is the whole line. '
          + 'Click it.',
        targets: [{ kind: 'suggestion', law: 'identity', result: 'a' }],
        done: (s) => at(s, 'a', 0, 'identity') && proves(s, 'proves a ∧ ⊤ = a'),
      },
    ],
    success: 'The kernel wrote `a` under the first line and put the law\'s name, '
      + 'identity, at the end of the line it came from. The foot of the proof pane now '
      + 'says it proves `a ∧ ⊤ = a`. You can always press undo (or the u key) to take a '
      + 'step back.',
  },
  {
    id: 'choose',
    title: 'Choose among suggestions',
    teaches: 'find the one suggestion that writes the line you want',
    goal: '`¬(a ∧ b) = ¬a ∨ ¬b`',
    steps: [
      {
        setup: ['start boolean = ¬(a ∧ b)'],
        say: '“Not both” is “one or the other is false”. This time the top suggestion is not the one you want: it only swaps `a` and '
          + '`b` inside the brackets (the law symmetry). The law you need is duality, and '
          + 'it is offered twice, once writing `¬a ∨ ¬b` and once `¬b ∨ ¬a`. Both are '
          + 'correct steps, but only one reaches the goal. Click the duality row that '
          + 'writes `¬a ∨ ¬b`.\n'
          + 'Tip: the number keys 0 to 9 take the first ten suggestions.',
        targets: [{ kind: 'suggestion', law: 'duality', result: '¬a ∨ ¬b' }],
        done: (s) => at(s, '¬a ∨ ¬b', 0, 'duality') && proves(s, 'proves ¬(a ∧ b) = ¬a ∨ ¬b'),
      },
    ],
    success: 'One law can match a line in several ways, and each way is its own '
      + 'suggestion. Reading the new line in each row is how you choose.',
  },
  {
    id: 'fill-in',
    title: 'Fill in a law variable',
    teaches: 'supply what a law cannot guess from the line',
    goal: '`p ⇒ p ∨ q`',
    steps: [
      {
        setup: ['start boolean ⇒ p'],
        say: 'If p, then p or q. The direction is `⇒`: each line '
          + 'only has to follow from the one above.\n'
          + 'The law generalization says `a ⇒ a ∨ b`. Matching it to the line `p` fixes '
          + '`a` as `p`, but nothing in the line says what `b` should be, so its row is '
          + 'greyed and ends “(b?)”. Click that greyed row: a small box opens asking '
          + 'for `b`. Type `q` there and press apply.',
        targets: [{ kind: 'hole', law: 'generalization', result: 'p ∨ b' }],
        done: (s) => at(s, 'p ∨ q', 0, 'generalization') && proves(s, 'proves p ⇒ p ∨ q'),
      },
    ],
    success: 'You told the law what `b` is, and the kernel checked the step with '
      + '`q` in its place. Any formula would have been allowed there; the law holds '
      + 'for all of them.',
  },
  {
    id: 'zoom',
    title: 'Work inside a part',
    teaches: 'zoom in to a part of the line, rewrite it, and zoom out',
    goal: '`p ∨ ¬(q ∧ ⊤) = p ∨ ¬q`',
    steps: [
      {
        setup: ['start boolean = p ∨ ¬(q ∧ ⊤)'],
        say: 'The `q ∧ ⊤` you want to simplify is buried '
          + 'inside the right-hand part, and laws only reach the line\'s main parts.\n'
          + 'So open that part as a proof of its own: click `¬(q ∧ ⊤)` in the line.',
        targets: [{ kind: 'zoom', text: '¬(q ∧ ⊤)' }],
        done: (s) => at(s, '¬(q ∧ ⊤)', 1),
      },
      {
        then: 'You are one level deeper (the line is indented). The context pane now says '
          + '`¬p`: on the right of an “or” you may assume the left side is false, since '
          + 'otherwise this part would not matter. You will not need it here.',
        say: 'Now take identity, the suggestion that writes `¬q`. Point at it first: '
          + 'only `q ∧ ⊤` lights up, because that is the part it rewrites.',
        targets: [{ kind: 'suggestion', law: 'identity', result: '¬q' }],
        done: (s) => at(s, '¬q', 1, 'identity'),
      },
      {
        say: 'This part is done. Press zoom out (or the o key) to close it and put '
          + '`¬q` back where `¬(q ∧ ⊤)` stood.',
        targets: [{ kind: 'out' }],
        done: (s) => at(s, 'p ∨ ¬q', 0, 'identity') && proves(s, 'proves p ∨ ¬(q ∧ ⊤) = p ∨ ¬q'),
      },
    ],
    success: 'Zooming out wrote the outer line for you. A one-step part is drawn '
      + 'folded up, with its law on the outer line. Clicking a line number moves the '
      + 'focus back to that line, closing any parts below it.',
  },
  {
    id: 'context',
    title: 'Use the context',
    teaches: 'facts gained by zooming in, and proving a line true',
    goal: '`a ⇒ (b ⇒ a)`',
    book: 'aPToP §10.1, Exercise 6(r)',
    steps: [
      {
        setup: ['start boolean ⇐ a ⇒ (b ⇒ a)'],
        say: 'Prove the line outright by calculating it down to `⊤` (true). '
          + 'The direction is `⇐`: each line only has to be enough to give the one above, '
          + 'so reaching `⊤` proves the first line.\n'
          + 'Click the right-hand part `(b ⇒ a)` to zoom in to it.',
        targets: [{ kind: 'zoom', text: '(b ⇒ a)' }],
        done: (s) => at(s, 'b ⇒ a', 1) && s.context.includes('a'),
      },
      {
        then: 'The context pane says `a`. Inside the right side of an implication you may '
          + 'assume its left side, so here `a` counts as a law.',
        say: 'Use it: take the suggestion from the law named context that writes '
          + '`b ⇒ ⊤` (it replaces the `a` you may assume with `⊤`).',
        targets: [{ kind: 'suggestion', law: 'context', result: 'b ⇒ ⊤' }],
        done: (s) => at(s, 'b ⇒ ⊤', 1, 'context'),
      },
      {
        say: 'Anything implies true. Take base, the suggestion that writes `⊤`.',
        targets: [{ kind: 'suggestion', law: 'base', result: '⊤' }],
        done: (s) => at(s, '⊤', 1, 'base'),
      },
      {
        say: 'Zoom out to put `⊤` back in the outer line.',
        targets: [{ kind: 'out' }],
        done: (s) => at(s, 'a ⇒ ⊤', 0),
      },
      {
        say: 'One more base step finishes it: take the suggestion that writes `⊤`.',
        targets: [{ kind: 'suggestion', law: 'base', result: '⊤' }],
        done: (s) => at(s, '⊤', 0, 'base')
          && proves(s, 'proves a ⇒ (b ⇒ a) = ⊤, that is, proves a ⇒ (b ⇒ a)'),
      },
    ],
    success: 'The foot says “that is, proves `a ⇒ (b ⇒ a)`”: the line equals true, so '
      + 'it is a theorem. The context is what made the middle step possible.',
  },
  {
    id: 'conditional',
    title: 'Laws with a condition',
    teaches: 'a law that holds only when something else does, and the ! it can leave',
    goal: '`a ⇒ ((a ⇒ (b ⇒ c)) ⇒ (b ⇒ c))`',
    steps: [
      {
        setup: ['start boolean ⇐ (a ⇒ (b ⇒ c)) ⇒ (b ⇒ c)'],
        say: 'Some facts have a condition: `a ⇒ (b ⇒ c)` says “if a holds, then b implies '
          + 'c”. First see what happens when nothing says that a holds.\n'
          + 'Ampheck reads a chain of `⇒` from the left, so it draws this line with no '
          + 'brackets round its first part. Click the right-hand part `(b ⇒ c)` to zoom in.',
        targets: [{ kind: 'zoom', text: '(b ⇒ c)' }],
        done: (s) => at(s, 'b ⇒ c', 1) && s.context.includes('a ⇒ (b ⇒ c)'),
      },
      {
        then: 'The context holds the fact `a ⇒ (b ⇒ c)`.',
        say: 'Find the context suggestion that writes `c ⇒ c`. Its law name ends in a red '
          + '“! a”: the step is only right if `a` holds, and nothing here says it does. '
          + 'Take it anyway to see what happens.',
        targets: [{ kind: 'suggestion', law: 'context', result: 'c ⇒ c' }],
        done: (s) => at(s, 'c ⇒ c', 1, undefined, true)
          && s.lines.some((l) => l.gap && l.premise === 'a'),
      },
      {
        say: 'The kernel took the step but marked it with a red `!`: a gap. Point at the '
          + 'gapped line to read what is missing (`a`). A proof with a gap proves nothing '
          + 'until the gap is closed.\nNow the same step where `a` is known.',
        targets: [{ kind: 'gap' }],
        ack: 'Show me',
      },
      {
        setup: ['start boolean ⇐ a ⇒ ((a ⇒ (b ⇒ c)) ⇒ (b ⇒ c))'],
        say: 'The same line, with `a ⇒` in front. Zoom in to the right-hand part.',
        targets: [{ kind: 'zoom', text: '(a ⇒ (b ⇒ c) ⇒ (b ⇒ c))' }],
        done: (s) => at(s, 'a ⇒ (b ⇒ c) ⇒ (b ⇒ c)', 1) && s.context.includes('a'),
      },
      {
        then: 'The context now has `a`.',
        say: 'Zoom in once more, to `(b ⇒ c)`.',
        targets: [{ kind: 'zoom', text: '(b ⇒ c)' }],
        done: (s) => at(s, 'b ⇒ c', 2) && s.context.includes('a ⇒ (b ⇒ c)') && s.context.includes('a'),
      },
      {
        then: 'Both facts are in the context: `a ⇒ (b ⇒ c)` and `a`.',
        say: 'Take the context suggestion that writes `c ⇒ c` again. This time there is no '
          + 'red “! a”, because the context settles the condition.',
        targets: [{ kind: 'suggestion', law: 'context', result: 'c ⇒ c' }],
        done: (s) => at(s, 'c ⇒ c', 2, 'context'),
      },
      {
        say: 'No gap. Finish as in lesson 6. First, reflexive: anything implies itself, so '
          + 'take the suggestion that writes `⊤`.',
        targets: [{ kind: 'suggestion', law: 'reflexive', result: '⊤' }],
        done: (s) => at(s, '⊤', 2, 'reflexive'),
      },
      {
        say: 'Zoom out.',
        targets: [{ kind: 'out' }],
        done: (s) => at(s, 'a ⇒ (b ⇒ c) ⇒ ⊤', 1),
      },
      {
        say: 'Take base, which writes `⊤`.',
        targets: [{ kind: 'suggestion', law: 'base', result: '⊤' }],
        done: (s) => at(s, '⊤', 1, 'base'),
      },
      {
        say: 'Zoom out again.',
        targets: [{ kind: 'out' }],
        done: (s) => at(s, 'a ⇒ ⊤', 0),
      },
      {
        say: 'And base once more, to `⊤`.',
        targets: [{ kind: 'suggestion', law: 'base', result: '⊤' }],
        done: (s) => at(s, '⊤', 0, 'base')
          && proves(s, 'proves a ⇒ (a ⇒ (b ⇒ c) ⇒ (b ⇒ c)) ⇐ ⊤, that is, proves a ⇒ (a ⇒ (b ⇒ c) ⇒ (b ⇒ c))'),
      },
    ],
    success: 'A law with a condition is still a step, but it leaves a `!` until the '
      + 'condition is known. Here the context knew it, so the proof has no gaps: it is '
      + 'the rule “from a, and a implies b ⇒ c, conclude b ⇒ c”.',
  },
  {
    id: 'portation',
    title: 'A proof from the book',
    teaches: 'put it together: the book\'s first worked calculation',
    goal: '`a ∧ b ⇒ c = a ⇒ (b ⇒ c)`',
    book: 'aPToP §1.0.1, the Law of Portation',
    quiet: true,
    steps: [
      {
        setup: ['start boolean = a ∧ b ⇒ c'],
        say: 'Hehner\'s book opens its calculations with this one (§1.0.1):\n'
          + '`a ∧ b ⇒ c` = `¬(a ∧ b) ∨ c` = `¬a ∨ ¬b ∨ c` = `a ⇒ ¬b ∨ c` = `a ⇒ (b ⇒ c)`\n'
          + 'The book calls the first, third and fourth steps Material Implication; in '
          + 'Ampheck\'s law list that law is called inclusion. The second is duality.\n'
          + 'Step 1: write `¬(a ∧ b) ∨ c`. Press “show me” if you get stuck.',
        targets: [{ kind: 'suggestion', law: 'inclusion', result: '¬(a ∧ b) ∨ c' }],
        done: (s) => at(s, '¬(a ∧ b) ∨ c', 0, 'inclusion'),
      },
      {
        say: 'Step 2: write `¬a ∨ ¬b ∨ c` with duality. It rewrites only the left part.',
        targets: [{ kind: 'suggestion', law: 'duality', result: '¬a ∨ ¬b ∨ c' }],
        done: (s) => at(s, '¬a ∨ ¬b ∨ c', 0, 'duality'),
      },
      {
        then: 'A line with three parts joined by `∨` also offers its runs of two parts '
          + '(the dashed buttons under it), which you could zoom in to.',
        say: 'Step 3: write `a ⇒ ¬b ∨ c` with inclusion.',
        targets: [{ kind: 'suggestion', law: 'inclusion', result: 'a ⇒ ¬b ∨ c' }],
        done: (s) => at(s, 'a ⇒ ¬b ∨ c', 0, 'inclusion'),
      },
      {
        say: 'Step 4: write `a ⇒ (b ⇒ c)` with inclusion. It rewrites only the right part.',
        targets: [{ kind: 'suggestion', law: 'inclusion', result: 'a ⇒ (b ⇒ c)' }],
        done: (s) => at(s, 'a ⇒ (b ⇒ c)', 0, 'inclusion')
          && proves(s, 'proves a ∧ b ⇒ c = a ⇒ (b ⇒ c)'),
      },
    ],
    success: 'That is the book\'s calculation, every step checked by the kernel. More '
      + 'of the book\'s proofs are in the examples… menu: the plain ones load cleanly, '
      + 'and the ones marked fail or missing show what Ampheck cannot do yet. Or type '
      + 'your own first line after pressing new.',
  },
];

// ---------------------------------------------------------------------------
// Progress, kept in this browser.

const KEY = 'ampheck-tutorial-v1';

interface Progress { done: string[]; lesson: number }

function loadProgress(): Progress {
  try {
    const raw = localStorage.getItem(KEY);
    if (raw) {
      const p = JSON.parse(raw) as Partial<Progress>;
      return {
        done: Array.isArray(p.done) ? p.done.filter((x) => typeof x === 'string') : [],
        lesson: typeof p.lesson === 'number' ? p.lesson : 0,
      };
    }
  } catch { /* fall through */ }
  return { done: [], lesson: 0 };
}

function saveProgress(p: Progress): void {
  try { localStorage.setItem(KEY, JSON.stringify(p)); } catch { /* private mode */ }
}

// ---------------------------------------------------------------------------
// The tutorial's own state.

let host: TutorialHost | null = null;
let active = false;
let progress: Progress = loadProgress();
let lessonIx = 0;
let stepIx = 0;
/** The state the current step began from. */
let startSig = '';
/** Running a step's setup: answers are not judged. */
let settingUp = false;
let offPath = false;
let finished = false;
let setupError = '';
/** What the last step's `then` said, shown above the current step. */
let lastThen = '';
/** The last lesson pulses only after "show me". */
let showMe = false;
let showList = false;
/** Scroll the target into view on the next decorate. */
let wantScroll = false;

const unlocked = (i: number) => i === 0 || progress.done.includes(LESSONS[i - 1]!.id) || progress.done.includes(LESSONS[i]!.id);

export function isActive(): boolean { return active; }
export function isSettingUp(): boolean { return settingUp; }

export function initTutorial(h: TutorialHost): void {
  host = h;
  const open = () => {
    if (/^#tutorial/.test(location.hash) && !active) {
      progress = loadProgress();
      const m = location.hash.match(/^#tutorial-(\d+)$/);
      const n = m ? Number(m[1]) - 1 : progress.lesson;
      void startLesson(Math.max(0, Math.min(n, LESSONS.length - 1)));
    }
  };
  window.addEventListener('hashchange', open);
  // Clicks that change the page but not the kernel (opening the small box of a
  // greyed suggestion) still move the pulse.
  document.addEventListener('click', () => { if (active) setTimeout(decorate, 0); });
  open();
}

/** Open the tutorial at its current lesson. */
export function openTutorial(): void {
  if (!active) {
    progress = loadProgress();
    if (location.hash !== '#tutorial') history.replaceState(null, '', '#tutorial');
    void startLesson(progress.lesson);
  }
}

function closeTutorial(): void {
  active = false;
  if (/^#tutorial/.test(location.hash)) history.replaceState(null, '', location.pathname + location.search);
  host?.showSite(null);
  host?.redraw();
}

async function startLesson(i: number): Promise<void> {
  if (host === null) return;
  if (!unlocked(i)) i = progress.lesson;
  active = true;
  lessonIx = i;
  progress.lesson = i;
  saveProgress(progress);
  finished = false;
  showMe = false;
  await beginStep(0);
}

async function beginStep(j: number): Promise<void> {
  if (host === null) return;
  stepIx = j;
  offPath = false;
  showMe = false;
  // `then` describes the state a step begins in: what the step before did.
  lastThen = LESSONS[lessonIx]!.steps[j]!.then ?? '';
  setupError = '';
  const step = LESSONS[lessonIx]!.steps[j]!;
  if (step.setup !== undefined || step.prefill !== undefined || j === 0) {
    settingUp = true;
    try {
      const r = await host.send('reset');
      if (r === null || !r.ok) setupError = r?.error ?? 'the server did not answer';
      if (step.prefill !== undefined) host.prefillStart(...step.prefill);
      for (const line of step.setup ?? []) {
        if (setupError !== '') break;
        const a = await host.send('cmd', line);
        if (a === null || !a.ok) setupError = `${line}: ${a?.error ?? 'the server did not answer'}`;
      }
    } finally {
      settingUp = false;
    }
  }
  startSig = signature(host.state());
  wantScroll = true;
  host.redraw();
}

/** Called with every answer the kernel sends while the tutorial is open. */
export function onAnswer(): void {
  if (!active || settingUp || finished || host === null) return;
  const s = host.state();
  if (s === null) return;
  const lesson = LESSONS[lessonIx]!;
  const step = lesson.steps[stepIx]!;
  if (step.done !== undefined && step.done(s)) {
    void advance();
    return;
  }
  offPath = step.done !== undefined && signature(s) !== startSig;
  wantScroll = true;
}

async function advance(): Promise<void> {
  const lesson = LESSONS[lessonIx]!;
  if (stepIx + 1 < lesson.steps.length) {
    await beginStep(stepIx + 1);
    return;
  }
  finished = true;
  if (!progress.done.includes(lesson.id)) progress.done.push(lesson.id);
  if (lessonIx + 1 < LESSONS.length) progress.lesson = lessonIx + 1;
  saveProgress(progress);
  host?.showSite(null);
  host?.redraw();
}

// ---------------------------------------------------------------------------
// Drawing.

function el<K extends keyof HTMLElementTagNameMap>(
  tag: K, attrs: Record<string, string> = {}, ...children: (Node | string)[]
): HTMLElementTagNameMap[K] {
  const node = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === 'class') node.className = v;
    else node.setAttribute(k, v);
  }
  for (const c of children) node.append(c);
  return node;
}

/** Plain text with `formulas` in backquotes, and paragraphs on newlines. */
function prose(text: string, cls = 'tut-say'): HTMLElement {
  const box = el('div', { class: cls });
  for (const para of text.split('\n')) {
    const p = el('p');
    para.split('`').forEach((bit, i) => {
      if (bit === '') return;
      p.append(i % 2 === 1 ? el('code', { class: 'tut-f' }, bit) : bit);
    });
    box.append(p);
  }
  return box;
}

function button(label: string, cls: string, run: () => void, attrs: Record<string, string> = {}): HTMLButtonElement {
  const b = el('button', { type: 'button', class: cls, ...attrs }, label);
  b.addEventListener('click', run);
  return b;
}

/** The tutorial card, drawn by the client between the note bar and the panes. */
export function tutorialPanel(): HTMLElement | null {
  if (!active) return null;
  const lesson = LESSONS[lessonIx]!;
  const step = lesson.steps[stepIx]!;
  const card = el('section', { class: 'tutorial', 'aria-label': 'tutorial', 'data-lesson': String(lessonIx + 1), 'data-step': String(stepIx + 1) });

  const head = el('div', { class: 'tut-head' },
    el('span', { class: 'tut-kicker' }, `Tutorial · lesson ${lessonIx + 1} of ${LESSONS.length}`),
    el('strong', { class: 'tut-title' }, lesson.title),
  );
  const tools = el('span', { class: 'tut-tools' },
    button(showList ? 'hide lessons' : 'lessons', 'tut-small', () => { showList = !showList; host?.redraw(); }),
    button('restart lesson', 'tut-small', () => void startLesson(lessonIx)),
    button('close', 'tut-small', closeTutorial, { 'aria-label': 'close the tutorial' }));
  head.append(tools);
  card.append(head);

  if (showList) {
    const ol = el('ol', { class: 'tut-list' });
    LESSONS.forEach((l, i) => {
      const done = progress.done.includes(l.id);
      const open = unlocked(i);
      const b = button(`${done ? '✓ ' : ''}${l.title}`, 'tut-lesson' + (i === lessonIx ? ' current' : '') + (done ? ' done' : ''),
        () => { showList = false; void startLesson(i); },
        open ? { title: l.teaches } : { disabled: 'disabled', title: 'finish the lesson before it first' });
      ol.append(el('li', {}, b, el('span', { class: 'tut-teaches' }, ` ${l.teaches}`)));
    });
    card.append(ol);
    card.append(el('p', { class: 'tut-meta' },
      button('reset progress', 'tut-small', () => {
        if (!confirm('Forget which tutorial lessons you have finished?')) return;
        progress = { done: [], lesson: 0 };
        saveProgress(progress);
        showList = false;
        void startLesson(0);
      }),
      ' Progress is kept in this browser only.'));
  }

  const goal = el('p', { class: 'tut-goal' });
  goal.append(el('span', { class: 'tut-label' }, 'Goal: '));
  goal.append(prose(lesson.goal, 'tut-inline'));
  if (lesson.book) goal.append(el('span', { class: 'tut-book' }, ` · ${lesson.book}`));
  card.append(goal);

  // Progress dots for the steps.
  const dots = el('div', { class: 'tut-dots', 'aria-hidden': 'true' });
  lesson.steps.forEach((_, i) => dots.append(el('span', {
    class: 'tut-dot' + (finished || i < stepIx ? ' done' : i === stepIx ? ' now' : ''),
  })));
  card.append(dots);

  if (setupError !== '') {
    card.append(el('p', { class: 'tut-warn' }, `The kernel refused to set up this lesson (${setupError}). Press restart lesson to try again.`));
    return card;
  }

  if (finished) {
    card.append(el('p', { class: 'tut-success' }, '✓ Checked by the kernel. Lesson done.'));
    card.append(prose(lesson.success));
    const row = el('div', { class: 'tut-actions' });
    if (lessonIx + 1 < LESSONS.length) {
      row.append(button(`Next: ${LESSONS[lessonIx + 1]!.title}`, 'tut-go tut-cta', () => void startLesson(lessonIx + 1)));
    } else {
      row.append(el('span', { class: 'tut-success' }, 'That was the last lesson.'));
      row.append(button('back to Ampheck', 'tut-go', closeTutorial));
    }
    card.append(row);
    return card;
  }

  if (lastThen !== '') card.append(prose(lastThen, 'tut-then'));
  card.append(prose(step.say));
  if (offPath) {
    card.append(el('p', { class: 'tut-warn' },
      'The kernel accepted that, but it is not the step this lesson is after. Press undo (u) to go back, or restart lesson.'));
  }
  const row = el('div', { class: 'tut-actions' });
  if (step.ack !== undefined) {
    row.append(button(step.ack, 'tut-go tut-cta', () => void advance()));
  } else if (lesson.quiet && !showMe) {
    row.append(button('show me', 'tut-small', () => { showMe = true; wantScroll = true; host?.redraw(); }));
  }
  if (row.childNodes.length) card.append(row);
  return card;
}

/** Find the element a target names in the drawn panes. */
function find(t: Target, s: StateView | null): HTMLElement[] {
  const q = (sel: string) => Array.from(document.querySelectorAll<HTMLElement>(sel));
  switch (t.kind) {
    case 'start': return q('[data-tut="start"]');
    case 'out': return q('[data-tut="out"]');
    case 'undo': return q('[data-tut="undo"]');
    case 'outcome': return q('.pane.proof .outcome');
    case 'context': return q('.pane.context');
    case 'proof': return q('.pane.proof');
    case 'suggestions': return q('.pane.suggest');
    case 'gap': return q('.line.gapped');
    case 'zoom': {
      const f = s === null ? undefined : focusedLine(s);
      const z = f?.zooms.find((p) => p.text === t.text);
      if (z === undefined) return [];
      return q('.line.focused [data-part]').filter((n) => n.getAttribute('data-part') === z.name);
    }
    case 'suggestion':
    case 'hole': {
      const rows = q('.suggestion').filter((n) =>
        n.getAttribute('data-law') === t.law && n.getAttribute('data-result') === t.result);
      const row = rows[0];
      if (row === undefined) return [];
      if (t.kind === 'hole') {
        const box = row.nextElementSibling;
        if (box !== null && box.classList.contains('holes')) {
          const input = box.querySelector<HTMLInputElement>('input');
          const go = box.querySelector<HTMLElement>('button[type="submit"]');
          return [input, go].filter((x): x is HTMLElement => x != null);
        }
      }
      return [row];
    }
  }
}

/** After every draw: make the next thing to click pulse, light up the part of
 * the line a pulsing suggestion would rewrite, and bring it into view. */
export function decorate(): void {
  for (const n of document.querySelectorAll('.tut-target')) n.classList.remove('tut-target');
  if (!active || host === null || finished || setupError !== '') return;
  const lesson = LESSONS[lessonIx]!;
  const step = lesson.steps[stepIx]!;
  if (lesson.quiet && !showMe) { wantScroll = false; return; }
  const s = host.state();
  const targets = offPath ? [{ kind: 'undo' } as Target] : (step.targets ?? []);
  let first: HTMLElement | null = null;
  for (const t of targets) {
    for (const n of find(t, s)) {
      n.classList.add('tut-target');
      first ??= n;
    }
    if (t.kind === 'suggestion' && s !== null) {
      const g = s.suggestions.find((x) => x.law === t.law && x.result === t.result);
      if (g !== undefined) host.showSite(g.site);
    }
  }
  // The hole box: tell the learner what to type.
  const holeT = targets.find((t) => t.kind === 'hole');
  if (holeT !== undefined) {
    const input = document.querySelector<HTMLInputElement>('.holes input');
    if (input !== null && input.placeholder !== 'type q') input.placeholder = 'type q';
  }
  if (wantScroll && first !== null) {
    wantScroll = false;
    // Panes (not the card) hold most targets; bring the target to the middle of
    // its own scrolling pane, and the pane into the window on a phone.
    const pane = first.closest('.body');
    if (pane !== null && first.closest('.pane') !== null && !first.classList.contains('pane')) {
      const pr = pane.getBoundingClientRect();
      const r = first.getBoundingClientRect();
      pane.scrollTop += (r.top - pr.top) - pane.clientHeight / 2 + r.height / 2;
    }
    first.scrollIntoView({ block: 'center', inline: 'nearest' });
  }
}
