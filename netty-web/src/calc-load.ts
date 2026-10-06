/**
 * Load aPToP .calc book calculations into the Netty proof editor.
 *
 * The live site used to fetch .calc files and park them in a read-only
 * <pre> under the panes — so the improved proofs were visible but never
 * became a session. Here we parse each theorem/refine block into Netty
 * script lines (`start` + `apply` / `direct`) and replay them through the
 * kernel so the proof pane shows the calculation.
 */

export type BookCalc = { id: string; label: string; file: string };

/** Exact aPToP book / solution calculations under public/examples/. */
export const BOOK_CALCS: BookCalc[] = [
  { id: 'portation', label: 'Law of Portation (§1.0.1 worked)', file: 'examples/portation.calc' },
  { id: 'portation-top', label: 'Law of Portation → ⊤ (§1.0.1)', file: 'examples/portation-top.calc' },
  { id: 'ex5b', label: 'ex5b (excluded middle)', file: 'examples/ex5b.calc' },
  { id: 'ex6a', label: 'ex6a (specialization)', file: 'examples/ex6a.calc' },
  { id: 'ex6c', label: 'ex6c (portation)', file: 'examples/ex6c.calc' },
  { id: 'ex6i', label: 'ex6i (noncontradiction)', file: 'examples/ex6i.calc' },
  { id: 'ex6j', label: 'ex6j (inclusion)', file: 'examples/ex6j.calc' },
  { id: 'ex6r', label: 'ex6r (a⇒(b⇒a))', file: 'examples/ex6r.calc' },
  { id: 'ex7a', label: 'ex7a (if-then-else)', file: 'examples/ex7a.calc' },
  { id: 'ex12ab', label: 'ex12 (drink/drive)', file: 'examples/ex12ab.calc' },
  { id: 'ex121a', label: 'ex121a (substitution)', file: 'examples/ex121a.calc' },
  { id: 'ex121b', label: 'ex121b (substitution)', file: 'examples/ex121b.calc' },
  { id: 'ex121f', label: 'ex121f (x:=1. ok)', file: 'examples/ex121f.calc' },
  { id: 'ex121g', label: 'ex121g (x:=1. y:=2)', file: 'examples/ex121g.calc' },
  { id: 'ex136a', label: 'ex136a (binary := → ok)', file: 'examples/ex136a.calc' },
  { id: 'ex136b', label: 'ex136b (binary swap)', file: 'examples/ex136b.calc' },
  { id: 'ex137a', label: 'ex137a (int := → ok)', file: 'examples/ex137a.calc' },
  { id: 'ex137b', label: 'ex137b (int swap)', file: 'examples/ex137b.calc' },
  { id: 'ex139', label: 'ex139 (nat loop refine)', file: 'examples/ex139.calc' },
  { id: 'ex140-R', label: 'ex140 R refinement', file: 'examples/ex140-R.calc' },
];

/** Interactive demos still in the kernel; portation first, UI gadgets last. */
export const UI_DEMOS = [
  'portation', 'discharge', 'minimize', 'segment', 'segfold', 'gap', 'fold', 'merge',
];

export type CalcStep = {
  /** Margin connective for this line (`=` / `⇒` / …); empty on the first line. */
  conn: string;
  expr: string;
  /** Law / justification name, if the calc wrote one. */
  law: string;
};

export type CalcTheorem = {
  kind: 'theorem' | 'refine';
  name: string;
  claim: string;
  steps: CalcStep[];
};

const CONN = /^(=|≡|⇒|⇐|≤|≥|⟹|⟸)\s+/;

/** Split a calc body line into expression + trailing law name (2+ spaces). */
function splitExprLaw(body: string): { expr: string; law: string } {
  // Laws are written after a wide gap; keep × · ′ etc. inside the expression.
  const m = body.match(/^(.*?)(?:\s{2,}|\t+)([A-Za-z∀∃].*)$/);
  if (m) return { expr: m[1]!.trim(), law: m[2]!.trim() };
  return { expr: body.trim(), law: '' };
}

/** Parse theorem / refine blocks out of a .calc file. */
export function parseCalcTheorems(text: string): CalcTheorem[] {
  const lines = text.split(/\r?\n/);
  const out: CalcTheorem[] = [];
  let i = 0;
  while (i < lines.length) {
    const raw = lines[i] ?? '';
    const t = raw.trim();
    if (t.startsWith('#') || t === '' || t.startsWith('laws ') || t.startsWith('state ')
        || t.startsWith('spec ') || t.startsWith('extends ')) {
      i++;
      continue;
    }
    let kind: 'theorem' | 'refine' | null = null;
    let name = '';
    let claim = '';
    if (t.startsWith('theorem ')) {
      kind = 'theorem';
      const rest = t.slice('theorem '.length);
      const colon = rest.indexOf(':');
      if (colon < 0) { i++; continue; }
      name = rest.slice(0, colon).trim();
      claim = rest.slice(colon + 1).trim();
    } else if (t.startsWith('refine ')) {
      kind = 'refine';
      claim = t.slice('refine '.length).trim();
      name = claim.length > 40 ? claim.slice(0, 37) + '…' : claim;
    } else {
      i++;
      continue;
    }
    i++;
    const steps: CalcStep[] = [];
    while (i < lines.length) {
      const L = lines[i] ?? '';
      const trim = L.trim();
      if (trim === '' || trim.startsWith('#')) {
        // Blank/comment inside a calc ends the block only if we already have steps
        // and the next non-empty non-comment is a new directive — peek ahead.
        let j = i + 1;
        while (j < lines.length && ((lines[j] ?? '').trim() === '' || (lines[j] ?? '').trim().startsWith('#'))) j++;
        const next = (lines[j] ?? '').trim();
        if (steps.length > 0 && (next.startsWith('theorem ') || next.startsWith('refine ')
            || next.startsWith('state ') || next.startsWith('spec ') || next.startsWith('laws ')
            || next.startsWith('extends ') || next === '')) {
          break;
        }
        i++;
        continue;
      }
      if (trim.startsWith('theorem ') || trim.startsWith('refine ') || trim.startsWith('state ')
          || trim.startsWith('spec ') || trim.startsWith('laws ') || trim.startsWith('extends ')) {
        break;
      }
      const cm = trim.match(CONN);
      if (cm) {
        const { expr, law } = splitExprLaw(trim.slice(cm[0].length));
        steps.push({ conn: cm[1]!, expr, law });
      } else if (steps.length === 0 || L.startsWith(' ') || L.startsWith('\t')) {
        const { expr, law } = splitExprLaw(trim);
        steps.push({ conn: '', expr, law });
      } else {
        break;
      }
      i++;
    }
    if (steps.length > 0) out.push({ kind, name, claim, steps });
  }
  return out;
}

/**
 * Turn one theorem into Netty script lines.
 * Prefer `apply LAW : CONN EXPR`; fall back is handled by the replayer.
 */
export function theoremToScript(th: CalcTheorem): string[] {
  if (th.steps.length === 0) return [];
  const first = th.steps[0]!;
  // Equivalence claims and = steps use `=`; otherwise keep a friendly default.
  const startDir = th.claim.includes('≡') || th.steps.every((s) => !s.conn || s.conn === '=' || s.conn === '≡')
    ? '='
    : '⇐';
  const lines: string[] = [`start ${startDir} ${first.expr}`];
  for (let k = 1; k < th.steps.length; k++) {
    const s = th.steps[k]!;
    const conn = s.conn === '≡' ? '=' : (s.conn || '=');
    // In .calc, the law sits on the *source* line (justifying the step to the next).
    const law = th.steps[k - 1]?.law || '';
    if (law) lines.push(`apply ${law} : ${conn} ${s.expr}`);
    else lines.push(`direct ${conn} ${s.expr}`);
  }
  return lines;
}

/** Base URL for examples relative to the /netty/ page. */
export function examplesBase(): string {
  const base = window.location.pathname.endsWith('/')
    ? window.location.pathname
    : window.location.pathname.replace(/\/[^/]*$/, '/');
  return base;
}
