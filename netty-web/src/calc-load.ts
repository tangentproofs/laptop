/**
 * Load aPToP .calc book calculations into the Netty proof editor.
 *
 * Parses theorem/refine blocks into Netty script lines (`state` / `spec` /
 * `start` + `apply`) and replays them through the kernel. Book hint phrases
 * are mapped to Netty law names via LAW_ALIASES so exact book text can still
 * `apply`. There is no silent `direct` fallback for book loads: every step
 * must apply.
 */

export type BookCalc = { id: string; label: string; file: string };

/**
 * Built-in kernel demos kept in the single Examples picker.
 * Labels are human-readable; ids are what `demo` expects.
 */
export type DemoExample = { id: string; label: string; kind: 'demo' };

/** A picker entry: either a book .calc or a kernel demo. */
export type PickerExample =
  | { kind: 'calc'; id: string; label: string; file: string }
  | DemoExample;

/**
 * Book → Netty law-name synonyms (case-insensitive lookup).
 * Multi-application phrases ("twice", "3 times") are stripped by resolveLawHint
 * and cannot be replayed as a single interactive `apply` — those calcs stay out
 * of the picker until rewritten with intermediate steps (#54–#56).
 */
export const LAW_ALIASES: Record<string, string> = {
  'material implication': 'inclusion',
  'inclusion': 'inclusion',
  'duality': 'duality',
  'law of excluded middle': 'excluded middle',
  'excluded middle': 'excluded middle',
  'double negation': 'double negation',
  'reflexivity of =': 'reflexive',
  'reflexive': 'reflexive',
  'idempotence': 'idempotent',
  'idempotent': 'idempotent',
  'idempotence of ∨': 'idempotent',
  'idempotence of ∧': 'idempotent',
  'symmetry of ∨': 'symmetry',
  'symmetry of ∧': 'symmetry',
  'symmetry': 'symmetry',
  'portation': 'portation',
  'specialization': 'specialization',
  'generalization': 'generalization',
  'noncontradiction': 'noncontradiction',
  'base': 'base',
  'base law': 'base',
  'case analysis': 'case analysis',
  'case idempotent': 'case idempotent',
  'context': 'context',
  'discharge': 'discharge',
  'associative': 'associative',
  'associativity': 'associative',
  'absorption': 'absorption',
  'substitution law': 'substitution law',
  'assignment': 'assignment',
  'ok': 'ok',
  'rewrite last assignment': 'assignment',
  'expand last assignment': 'assignment',
  'sequential composition': 'sequential composition',
  'one point': 'one point',
  'vacuous quantifier': 'vacuous quantifier',
  'arithmetic': 'arithmetic',
  'binary algebra': 'binary algebra',
};

/** Normalize a book hint to a Netty law name, or null if it cannot be applied as one step. */
export function resolveLawHint(raw: string): string | null {
  let h = raw.trim();
  if (!h) return null;
  // Strip trailing ", twice" / ", N times" / ", or …" — multi-step book phrasing.
  if (/,\s*(twice|\d+\s+times)\s*$/i.test(h)) return null;
  if (/,\s*or\b/i.test(h)) {
    // "idempotence of ∨, or base law" → try first clause
    h = h.split(/,\s*or\b/i)[0]!.trim();
  }
  // "definition of P" / "definition of assignment…" — keep as-is for kernel rules
  const key = h.toLowerCase();
  if (LAW_ALIASES[key]) return LAW_ALIASES[key]!;
  if (/^definition of /i.test(h)) return h; // kernel: definition of <spec>
  // Already a Netty name (lowercase words)?
  if (/^[a-z][a-z0-9 ]*$/.test(key) && key.length < 40) return key;
  return null;
}

/**
 * Working book calcs for the picker (every step must `apply` with aliases).
 * Exercise numbers / section cites live in the .calc files, not in labels.
 * Updated after audit — only PASS entries.
 */
export const BOOK_CALCS: BookCalc[] = [
  { id: 'portation', label: 'Law of Portation', file: 'examples/portation.calc' },
  { id: 'ex5b', label: 'Excluded middle', file: 'examples/ex5b.calc' },
  { id: 'ex5c', label: 'Simplify x ⇒ ¬x', file: 'examples/ex5c.calc' },
  { id: 'ex5d', label: 'Simplify x ⇐ ¬x', file: 'examples/ex5d.calc' },
  { id: 'ex5f', label: 'Simplify x ⧧ ¬x', file: 'examples/ex5f.calc' },
  { id: 'ex6a', label: 'Specialization then generalization', file: 'examples/ex6a.calc' },
  { id: 'ex6c', label: 'Portation and noncontradiction', file: 'examples/ex6c.calc' },
  { id: 'ex6g', label: 'a ∧ ¬b ⇒ a ∨ b', file: 'examples/ex6g.calc' },
  { id: 'ex6i', label: 'Contradiction implies anything', file: 'examples/ex6i.calc' },
  { id: 'ex6j', label: 'Either a ⇒ b or b ⇒ a', file: 'examples/ex6j.calc' },
  { id: 'ex6r', label: 'Portation proves a ⇒ (b ⇒ a)', file: 'examples/ex6r.calc' },
  { id: 'ex7a', label: 'If-then-else by case analysis', file: 'examples/ex7a.calc' },
  { id: 'ex12ab', label: 'Don\'t drink and drive', file: 'examples/ex12ab.calc' },
  { id: 'ex12ae', label: 'Don\'t drink and drive ≡ ¬drink ∨ ¬drive', file: 'examples/ex12ae.calc' },
  { id: 'ex12bc', label: 'drink ⇒ ¬drive ≡ drive ⇒ ¬drink', file: 'examples/ex12bc.calc' },
  { id: 'ex121a', label: 'Substitution after x:= y+1', file: 'examples/ex121a.calc' },
  { id: 'ex121b', label: 'Substitution into a conjunction', file: 'examples/ex121b.calc' },
  { id: 'ex121f', label: 'Assignment then ok', file: 'examples/ex121f.calc' },
  { id: 'ex121g', label: 'Two assignments', file: 'examples/ex121g.calc' },
];

/** Kernel demos in the same picker (valid complete sessions). */
export const DEMO_EXAMPLES: DemoExample[] = [
  { kind: 'demo', id: 'portation', label: 'Portation (kernel demo)' },
  { kind: 'demo', id: 'discharge', label: 'Discharge with context' },
  { kind: 'demo', id: 'minimize', label: 'Apply a law to a part' },
  { kind: 'demo', id: 'segment', label: 'Segment of an association' },
  { kind: 'demo', id: 'fold', label: 'Fold an association' },
  { kind: 'demo', id: 'merge', label: 'Merge adjacent steps' },
];

/** Single Examples menu: book calcs then kernel demos. */
export const PICKER_EXAMPLES: PickerExample[] = [
  ...BOOK_CALCS.map((b): PickerExample => ({ kind: 'calc', ...b })),
  ...DEMO_EXAMPLES,
];


/** Hierarchical examples manifest (data-driven picker). */
export type ManifestStatus = 'pass' | 'fail' | 'missing' | 'out_of_scope';

export type ManifestItem = {
  id: string;
  title: string;
  bookRef: string;
  status: ManifestStatus;
  kind?: 'calc' | 'demo';
  path?: string;
  blocker?: string;
  nextStep?: string;
};

export type ManifestSection = { id: string; title: string; items: ManifestItem[] };
export type ManifestGroup = { id: string; title: string; sections: ManifestSection[] };
export type ExamplesManifest = { version: number; source?: string; groups: ManifestGroup[] };

/** Fetch `examples/manifest.json` (relative to the Netty page). */
export async function loadExamplesManifest(): Promise<ExamplesManifest> {
  const res = await fetch(examplesBase() + 'examples/manifest.json');
  if (!res.ok) throw new Error(`manifest HTTP ${res.status}`);
  return (await res.json()) as ExamplesManifest;
}

/** Book calcs that are audit PASS (loadable). Prefer manifest when available. */
export function passCalcsFromManifest(m: ExamplesManifest): BookCalc[] {
  const out: BookCalc[] = [];
  for (const g of m.groups) {
    if (g.id === 'demos') continue;
    for (const s of g.sections) {
      for (const it of s.items) {
        if (it.status === 'pass' && it.path && (it.kind ?? 'calc') === 'calc') {
          out.push({ id: it.id, label: it.title, file: it.path });
        }
      }
    }
  }
  return out;
}

/** @deprecated use DEMO_EXAMPLES / PICKER_EXAMPLES */
export const UI_DEMOS = DEMO_EXAMPLES.map((d) => d.id);

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
  /** Program state lines preceding the theorem (`state x, y: int`). */
  state: string[];
  /** Spec lines preceding the theorem (`spec R = …`). */
  specs: string[];
};

const CONN = /^(=|≡|⇒|⇐|≤|≥|⟹|⟸)\s+/;

/** Split a calc body line into expression + trailing law name (2+ spaces). */
function splitExprLaw(body: string): { expr: string; law: string } {
  const m = body.match(/^(.*?)(?:\s{2,}|\t+)([A-Za-z∀∃].*)$/);
  if (m) return { expr: m[1]!.trim(), law: m[2]!.trim() };
  return { expr: body.trim(), law: '' };
}

/** Parse theorem / refine blocks out of a .calc file (with preceding state/spec). */
export function parseCalcTheorems(text: string): CalcTheorem[] {
  const lines = text.split(/\r?\n/);
  const out: CalcTheorem[] = [];
  let i = 0;
  let state: string[] = [];
  let specs: string[] = [];
  while (i < lines.length) {
    const raw = lines[i] ?? '';
    const t = raw.trim();
    if (t.startsWith('#') || t === '' || t.startsWith('laws ') || t.startsWith('extends ')) {
      i++;
      continue;
    }
    if (t.startsWith('state ')) {
      state = [...state, t];
      i++;
      continue;
    }
    if (t.startsWith('spec ')) {
      specs = [...specs, t];
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
    if (steps.length > 0) {
      out.push({ kind, name, claim, steps, state: [...state], specs: [...specs] });
    }
  }
  return out;
}

/**
 * Turn one theorem into Netty script lines.
 * Uses LAW_ALIASES; returns null for a step whose hint cannot resolve to one law
 * when `strict` (default true). With strict=false, unresolvable hints become
 * `direct` (audit / legacy only — not used for the picker load path).
 */
export function theoremToScript(th: CalcTheorem, strict = true): string[] | null {
  if (th.steps.length === 0) return [];
  const first = th.steps[0]!;
  // Forward ⇒ calculations start in ⇒; backward ⇐ in ⇐; pure equivalences in =.
  const conns = th.steps.map((s) => s.conn).filter(Boolean);
  const startDir =
    conns.some((c) => c === '⇒' || c === '⟹') ? '⇒' :
    conns.some((c) => c === '⇐' || c === '⟸') ? '⇐' :
    '=';
  const lines: string[] = [
    ...th.state,
    ...th.specs,
    `start ${startDir} ${first.expr}`,
  ];
  for (let k = 1; k < th.steps.length; k++) {
    const s = th.steps[k]!;
    const conn = s.conn === '≡' ? '=' : (s.conn || '=');
    const rawLaw = th.steps[k - 1]?.law || '';
    const law = resolveLawHint(rawLaw);
    if (law) {
      let withClause = '';
      // generalization: a ⇒ a ∨ b leaves hole b — pin it from the target line.
      if (law === 'generalization') {
        const m = s.expr.match(/^(.+)\s*∨\s*(.+)$/);
        if (m) withClause = ` with b := ${m[2]!.trim()}`;
      }
      lines.push(`apply ${law} : ${conn} ${s.expr}${withClause}`);
    } else if (strict) {
      return null;
    } else if (rawLaw) {
      lines.push(`direct ${conn} ${s.expr}`);
    } else {
      lines.push(`direct ${conn} ${s.expr}`);
    }
  }
  return lines;
}

/** Describe why theoremToScript would reject a theorem (for audit). */
export function scriptFailureReason(th: CalcTheorem): string | null {
  if (th.steps.length === 0) return 'no steps';
  for (let k = 1; k < th.steps.length; k++) {
    const rawLaw = th.steps[k - 1]?.law || '';
    if (!rawLaw) return `step ${k}: empty hint (would need direct)`;
    if (!resolveLawHint(rawLaw)) return `step ${k}: unresolved hint “${rawLaw}”`;
  }
  return null;
}

/** Base URL for examples relative to the /netty/ page. */
export function examplesBase(): string {
  const base = window.location.pathname.endsWith('/')
    ? window.location.pathname
    : window.location.pathname.replace(/\/[^/]*$/, '/');
  return base;
}
