/**
 * Symbol table for aPToP editors (ported from platform web/js/expansions.mts,
 * plus book glyphs). Quiet desktop typing + the Symbols sheet both use this.
 */

/** @typedef {{ label: string, codes: Record<string, string> }} ExpansionGroup */

/** @type {ExpansionGroup[]} */
export const expansionGroups = [
  { label: 'Symbols', codes: {
    '\\': '\\',
    '(': '⟨', ')': '⟩',
    '<<': '«', '>>': '»',
    'ra': '→', 'la': '←', 'up': '↑', 'dn': '↓',
    // aPToP large implication / equivalence (book margin ops)
    '=>': '⇒', 'impliedby': '⇐', 'from': '⇐', 'equiv': '≡', '==': '≡',
    's1': '░', 's2': '▒', 's3': '▓', 's4': '█',
  }},

  { label: 'Math', codes: {
    '<=': '≤', '>=': '≥', 'le': '≤', 'ge': '≥', 'ne': '≠', 'neq': '≠',
    'and': '∧', 'or': '∨', 'not': '¬',
    'imp': '→', 'xor': '⊕', 'turn': '⊢',
    'all': '∀', 'ex': '∃', 'exists': '∃', 'forall': '∀',
    'I': '⊤', 'O': '⊥', 'top': '⊤', 'bot': '⊥',
    'in': '∈', 'st': '∋', 'nin': '∉',
    'cup': '∪', 'cap': '∩',
    'sub': '⊆', 'sup': '⊇', 'subset': '⊂',
    'sqrt': '√', 'mul': '×', 'times': '×', 'div': '÷',
    'circ': '∘', 'deg': '°',
    // aPToP / program-theory glyphs
    'cdot': '·', 'dot': '·', 'bullet': '·',
    'prime': '′', "'": '′',
    'dprime': '″', "''": '″',
    'tprime': '‴',
    'box': '□', 'diamond': '◇',
    'll': '⟸', 'gg': '⟹',
    'to': '→', 'gets': '←',
    'neqv': '≢', 'cong': '≅',
    'inf': '∞', 'oo': '∞',
    'empty': '∅', 'nabla': '∇',
    'pm': '±', 'mp': '∓',
    // aPToP unequal (not-equals variant used in some texts)
    'neqch': '⧧',
  }},

  { label: 'Games', codes: {
    'wk': '♔', 'wq': '♕', 'wr': '♖', 'wb': '♗', 'wn': '♘', 'wp': '♙',
    'bk': '♚', 'bq': '♛', 'br': '♜', 'bb': '♝', 'bn': '♞', 'bp': '♟',
    'clubs': '♣', 'hearts': '♥', 'spades': '♠', 'diamonds': '♦',
  }},

  { label: 'Superscript', codes: {
    '^0': '⁰', '^1': '¹', '^2': '²', '^3': '³', '^4': '⁴',
    '^5': '⁵', '^6': '⁶', '^7': '⁷', '^8': '⁸', '^9': '⁹',
    '^+': '⁺', '^-': '⁻', '^=': '⁼', '^(': '⁽', '^)': '⁾',
    '^a': 'ᵃ', '^b': 'ᵇ', '^c': 'ᶜ', '^d': 'ᵈ', '^e': 'ᵉ',
    '^f': 'ᶠ', '^g': 'ᵍ', '^h': 'ʰ', '^i': 'ⁱ', '^j': 'ʲ',
    '^k': 'ᵏ', '^l': 'ˡ', '^m': 'ᵐ', '^n': 'ⁿ', '^o': 'ᵒ',
    '^p': 'ᵖ', '^r': 'ʳ', '^s': 'ˢ', '^t': 'ᵗ', '^u': 'ᵘ',
    '^v': 'ᵛ', '^w': 'ʷ', '^x': 'ˣ', '^y': 'ʸ', '^z': 'ᶻ',
  }},

  { label: 'Subscript', codes: {
    '_0': '₀', '_1': '₁', '_2': '₂', '_3': '₃', '_4': '₄',
    '_5': '₅', '_6': '₆', '_7': '₇', '_8': '₈', '_9': '₉',
    '_+': '₊', '_-': '₋', '_=': '₌', '_(': '₍', '_)': '₎',
    '_a': 'ₐ', '_e': 'ₑ', '_h': 'ₕ', '_i': 'ᵢ', '_j': 'ⱼ',
    '_k': 'ₖ', '_l': 'ₗ', '_m': 'ₘ', '_n': 'ₙ', '_o': 'ₒ',
    '_p': 'ₚ', '_r': 'ᵣ', '_s': 'ₛ', '_t': 'ₜ', '_u': 'ᵤ',
    '_v': 'ᵥ', '_x': 'ₓ',
  }},

  { label: 'Greek', codes: {
    'alpha': 'α', 'Alpha': 'Α', 'beta': 'β', 'Beta': 'Β',
    'gamma': 'γ', 'Gamma': 'Γ', 'delta': 'δ', 'Delta': 'Δ',
    'epsilon': 'ε', 'Epsilon': 'Ε', 'zeta': 'ζ', 'Zeta': 'Ζ',
    'eta': 'η', 'Eta': 'Η', 'theta': 'θ', 'Theta': 'Θ',
    'iota': 'ι', 'Iota': 'Ι', 'kappa': 'κ', 'Kappa': 'Κ',
    'lambda': 'λ', 'Lambda': 'Λ', 'mu': 'μ', 'Mu': 'Μ',
    'nu': 'ν', 'Nu': 'Ν', 'xi': 'ξ', 'Xi': 'Ξ',
    'omicron': 'ο', 'Omicron': 'Ο', 'pi': 'π', 'Pi': 'Π',
    'rho': 'ρ', 'Rho': 'Ρ', 'sigma': 'σ', 'Sigma': 'Σ',
    'tau': 'τ', 'Tau': 'Τ', 'upsilon': 'υ', 'Upsilon': 'Υ',
    'phi': 'φ', 'Phi': 'Φ', 'chi': 'χ', 'Chi': 'Χ',
    'psi': 'ψ', 'Psi': 'Ψ', 'omega': 'ω', 'Omega': 'Ω',
  }},

  { label: 'Blackboard bold', codes: {
    'bbA': '𝔸', 'bbB': '𝔹', 'bbC': 'ℂ', 'bbD': '𝔻', 'bbE': '𝔼',
    'bbF': '𝔽', 'bbG': '𝔾', 'bbH': 'ℍ', 'bbI': '𝕀', 'bbJ': '𝕁',
    'bbK': '𝕂', 'bbL': '𝕃', 'bbM': '𝕄', 'bbN': 'ℕ', 'bbO': '𝕆',
    'bbP': 'ℙ', 'bbQ': 'ℚ', 'bbR': 'ℝ', 'bbS': '𝕊', 'bbT': '𝕋',
    'bbU': '𝕌', 'bbV': '𝕍', 'bbW': '𝕎', 'bbX': '𝕏', 'bbY': '𝕐',
    'bbZ': 'ℤ',
  }},
];

/** Flat map: code → symbol (no leading backslash). */
export const expansions = Object.fromEntries(
  expansionGroups.flatMap((g) => Object.entries(g.codes)),
);
