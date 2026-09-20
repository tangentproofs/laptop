
/-!
# Binary Theory

This module formalizes the laws of Section 1.0 (Binary Theory) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), as listed under
"Binary" in the reference section (§11.3.1).

## The model

Hehner's *binary* expressions take the two values `⊤` (a theorem) and `⊥` (an
antitheorem). We model binary values as Lean's `Bool`, with `⊤ = true` and
`⊥ = false`, and the book's operators as

| aPToP                   | here                          |
| ----------------------- | ----------------------------- |
| `⊤`, `⊥`                | `Binary.top`, `Binary.bot`    |
| `¬a`                    | `!a`                          |
| `a ∧ b`, `a ∨ b`        | `a && b`, `a || b`            |
| `a ⇒ b`                 | `Binary.imp a b`              |
| `a ⇐ b`                 | `Binary.rimp a b`             |
| `a = b`, `a ⧧ b`        | `a == b`, `a != b`            |
| `if a then b else c`    | `bif a then b else c`         |

A law that the book states as a theorem (such as `a ∨ ¬a`) is stated here as
the equation `… = true`; a law stated as an equation is a `Bool` equation.
Every law is a finite truth-table check, so each proof case-splits on the
variables and evaluates (`revert …; decide`).

Later in the book, binary expressions over program variables become
*predicates* on states; that step is taken in the Program Theory chapter, not
here.
-/

namespace LaPToP.BasicTheories

/-- A *binary* value (aPToP §1.0): `⊤` or `⊥`, modelled as `Bool`. -/
abbrev Binary := Bool

namespace Binary

/-- `⊤`, the binary value "top", the theorem. -/
abbrev top : Binary := true

/-- `⊥`, the binary value "bottom", the antitheorem. -/
abbrev bot : Binary := false

/-- `a ⇒ b`, implication ("if `a` then `b`"): `¬a ∨ b`. -/
abbrev imp (a b : Binary) : Binary := !a || b

/-- `a ⇐ b`, reverse implication ("`a` if `b`"): `b ⇒ a`. -/
abbrev rimp (a b : Binary) : Binary := imp b a

variable (a b c d e : Binary)

/-! ### Binary -/

/-- `⊤` is a theorem. -/
theorem top_eq : top = true := rfl

/-- `¬⊥` is a theorem. -/
theorem not_bot : (!bot) = true := rfl

/-- `⊤ ⧧ ⊥`. -/
theorem top_ne_bot : (top != bot) = true := rfl

/-! ### Mirror and Double Negation -/

/-- `a ⇐ b = b ⇒ a` (Mirror). -/
theorem rimp_eq_imp : rimp a b = imp b a := rfl

/-- `¬¬a = a` (Double Negation). -/
theorem not_not : (!!a) = a := by revert a; decide

/-! ### Excluded Middle and Noncontradiction -/

/-- `a ∨ ¬a` (Excluded Middle). -/
theorem excluded_middle : (a || !a) = true := by revert a; decide

/-- `¬(a ∧ ¬a)` (Noncontradiction). -/
theorem noncontradiction : (!(a && !a)) = true := by revert a; decide

/-! ### Base -/

/-- `¬(a ∧ ⊥)` (Base). -/
theorem not_and_bot : (!(a && bot)) = true := by revert a; decide

/-- `a ∨ ⊤` (Base). -/
theorem or_top : (a || top) = true := by revert a; decide

/-- `a ⇒ ⊤` (Base). -/
theorem imp_top : imp a top = true := by revert a; decide

/-- `⊥ ⇒ a` (Base). -/
theorem bot_imp : imp bot a = true := by revert a; decide

/-! ### Identity -/

/-- `⊤ ∧ a = a` (Identity). -/
theorem top_and : (top && a) = a := by revert a; decide

/-- `⊥ ∨ a = a` (Identity). -/
theorem bot_or : (bot || a) = a := by revert a; decide

/-- `⊤ ⇒ a = a` (Identity). -/
theorem top_imp : imp top a = a := by revert a; decide

/-- `(⊤ = a) = a` (Identity). -/
theorem top_beq : (top == a) = a := by revert a; decide

/-! ### Idempotent and Reflexive -/

/-- `a ∧ a = a` (Idempotent). -/
theorem and_self : (a && a) = a := by revert a; decide

/-- `a ∨ a = a` (Idempotent). -/
theorem or_self : (a || a) = a := by revert a; decide

/-- `a ⇒ a` (Reflexive). -/
theorem imp_self : imp a a = true := by revert a; decide

/-- `a = a` (Reflexive). -/
theorem beq_self : (a == a) = true := by revert a; decide

/-! ### Indirect Proof, Specialization, Generalization -/

/-- `(¬a ⇒ ⊥) = a` (Indirect Proof). -/
theorem not_imp_bot : imp (!a) bot = a := by revert a; decide

/-- `(¬a ⇒ a) = a` (Indirect Proof). -/
theorem not_imp_self : imp (!a) a = a := by revert a; decide

/-- `a ∧ b ⇒ a` (Specialization). -/
theorem and_imp_left : imp (a && b) a = true := by revert a b; decide

/-- `a ⇒ a ∨ b` (Generalization). -/
theorem imp_or_left : imp a (a || b) = true := by revert a b; decide

/-! ### Associative -/

/-- `a ∧ (b ∧ c) = (a ∧ b) ∧ c` (Associative). -/
theorem and_assoc : (a && (b && c)) = ((a && b) && c) := by revert a b c; decide

/-- `a ∨ (b ∨ c) = (a ∨ b) ∨ c` (Associative). -/
theorem or_assoc : (a || (b || c)) = ((a || b) || c) := by revert a b c; decide

/-- `(a = (b = c)) = ((a = b) = c)` (Associative). -/
theorem beq_assoc : (a == (b == c)) = ((a == b) == c) := by revert a b c; decide

/-- `a ⧧ (b ⧧ c) = (a ⧧ b) ⧧ c` (Associative). -/
theorem bne_assoc : (a != (b != c)) = ((a != b) != c) := by revert a b c; decide

/-- `(a = (b ⧧ c)) = ((a = b) ⧧ c)` (Associative). -/
theorem beq_bne_assoc : (a == (b != c)) = ((a == b) != c) := by revert a b c; decide

/-! ### Symmetry (Commutative) -/

/-- `a ∧ b = b ∧ a` (Symmetry). -/
theorem and_comm : (a && b) = (b && a) := by revert a b; decide

/-- `a ∨ b = b ∨ a` (Symmetry). -/
theorem or_comm : (a || b) = (b || a) := by revert a b; decide

/-- `(a = b) = (b = a)` (Symmetry). -/
theorem beq_comm : (a == b) = (b == a) := by revert a b; decide

/-- `a ⧧ b = b ⧧ a` (Symmetry). -/
theorem bne_comm : (a != b) = (b != a) := by revert a b; decide

/-! ### Antisymmetry and Discharge -/

/-- `(a ⇒ b) ∧ (b ⇒ a) = (a = b)` (Antisymmetry, Double Implication). -/
theorem imp_and_imp : (imp a b && imp b a) = (a == b) := by revert a b; decide

/-- `a ∧ (a ⇒ b) = a ∧ b` (Discharge). -/
theorem and_imp_self : (a && imp a b) = (a && b) := by revert a b; decide

/-- `a ⇒ (a ∧ b) = a ⇒ b` (Discharge). -/
theorem imp_and_self : imp a (a && b) = imp a b := by revert a b; decide

/-! ### Antimonotonic and Monotonic -/

/-- `a ⇒ b = ¬a ⇐ ¬b` (Antimonotonic, Contrapositive). -/
theorem imp_eq_rimp_not : imp a b = rimp (!a) (!b) := by revert a b; decide

/-- `a ⇒ b ⇒ ((a ⇒ c) ⇐ (b ⇒ c))` (Antimonotonic). -/
theorem imp_rimp_imp : imp (imp a b) (rimp (imp a c) (imp b c)) = true := by
  revert a b c; decide

/-- `a ⇒ b ⇒ (a ∧ c ⇒ b ∧ c)` (Monotonic). -/
theorem imp_and_right : imp (imp a b) (imp (a && c) (b && c)) = true := by
  revert a b c; decide

/-- `a ⇒ b ⇒ (a ∨ c ⇒ b ∨ c)` (Monotonic). -/
theorem imp_or_right : imp (imp a b) (imp (a || c) (b || c)) = true := by
  revert a b c; decide

/-- `a ⇒ b ⇒ ((c ⇒ a) ⇒ (c ⇒ b))` (Monotonic). -/
theorem imp_imp_left : imp (imp a b) (imp (imp c a) (imp c b)) = true := by
  revert a b c; decide

/-! ### Duality -/

/-- `¬(a ∧ b) = ¬a ∨ ¬b` (Duality). -/
theorem not_and : (!(a && b)) = (!a || !b) := by revert a b; decide

/-- `¬(a ∨ b) = ¬a ∧ ¬b` (Duality). -/
theorem not_or : (!(a || b)) = (!a && !b) := by revert a b; decide

/-! ### Exclusion -/

/-- `(a ⇒ ¬b) = (b ⇒ ¬a)` (Exclusion, Contrapositive). -/
theorem imp_not_comm : imp a (!b) = imp b (!a) := by revert a b; decide

/-- `(a = ¬b) = (a ⧧ b)` (Exclusion). -/
theorem beq_not : (a == !b) = (a != b) := by revert a b; decide

/-- `(a ⧧ b) = (¬a = b)` (Exclusion). -/
theorem bne_eq_not_beq : (a != b) = (!a == b) := by revert a b; decide

/-! ### Inclusion -/

/-- `a ⇒ b = ¬a ∨ b` (Inclusion, Material Implication). -/
theorem imp_eq_not_or : imp a b = (!a || b) := rfl

/-- `a ⇒ b = (a ∧ b = a)` (Inclusion). -/
theorem imp_eq_and_beq : imp a b = ((a && b) == a) := by revert a b; decide

/-- `a ⇒ b = (a ∨ b = b)` (Inclusion). -/
theorem imp_eq_or_beq : imp a b = ((a || b) == b) := by revert a b; decide

/-! ### Absorption -/

/-- `a ∧ (a ∨ b) = a` (Absorption). -/
theorem and_or_self : (a && (a || b)) = a := by revert a b; decide

/-- `a ∨ (a ∧ b) = a` (Absorption). -/
theorem or_and_self : (a || (a && b)) = a := by revert a b; decide

/-! ### Direct Proof -/

/-- `(a ⇒ b) ∧ a ⇒ b` (Direct Proof, modus ponens). -/
theorem modus_ponens : imp (imp a b && a) b = true := by revert a b; decide

/-- `(a ⇒ b) ∧ ¬b ⇒ ¬a` (Direct Proof, modus tollens). -/
theorem modus_tollens : imp (imp a b && !b) (!a) = true := by revert a b; decide

/-- `(a ∨ b) ∧ ¬a ⇒ b` (Direct Proof, disjunctive syllogism). -/
theorem or_and_not_imp : imp ((a || b) && !a) b = true := by revert a b; decide

/-! ### Transitive -/

/-- `(a ∧ b) ∧ (b ∧ c) ⇒ (a ∧ c)` (Transitive). -/
theorem and_and_trans : imp ((a && b) && (b && c)) (a && c) = true := by revert a b c; decide

/-- `(a ⇒ b) ∧ (b ⇒ c) ⇒ (a ⇒ c)` (Transitive). -/
theorem imp_trans : imp (imp a b && imp b c) (imp a c) = true := by revert a b c; decide

/-- `(a = b) ∧ (b = c) ⇒ (a = c)` (Transitive). -/
theorem beq_trans : imp ((a == b) && (b == c)) (a == c) = true := by revert a b c; decide

/-- `(a ⇒ b) ∧ (b = c) ⇒ (a ⇒ c)` (Transitive). -/
theorem imp_beq_trans : imp (imp a b && (b == c)) (imp a c) = true := by revert a b c; decide

/-- `(a = b) ∧ (b ⇒ c) ⇒ (a ⇒ c)` (Transitive). -/
theorem beq_imp_trans : imp ((a == b) && imp b c) (imp a c) = true := by revert a b c; decide

/-! ### Distributive (Factoring) -/

/-- `a ∧ (b ∧ c) = (a ∧ b) ∧ (a ∧ c)` (Distributive). -/
theorem and_and_distrib : (a && (b && c)) = ((a && b) && (a && c)) := by revert a b c; decide

/-- `a ∧ (b ∨ c) = (a ∧ b) ∨ (a ∧ c)` (Distributive). -/
theorem and_or_distrib : (a && (b || c)) = ((a && b) || (a && c)) := by revert a b c; decide

/-- `a ∨ (b ∧ c) = (a ∨ b) ∧ (a ∨ c)` (Distributive). -/
theorem or_and_distrib : (a || (b && c)) = ((a || b) && (a || c)) := by revert a b c; decide

/-- `a ∨ (b ∨ c) = (a ∨ b) ∨ (a ∨ c)` (Distributive). -/
theorem or_or_distrib : (a || (b || c)) = ((a || b) || (a || c)) := by revert a b c; decide

/-- `a ∨ (b ⇒ c) = (a ∨ b) ⇒ (a ∨ c)` (Distributive). -/
theorem or_imp_distrib : (a || imp b c) = imp (a || b) (a || c) := by revert a b c; decide

/-- `(a ∨ (b = c)) = ((a ∨ b) = (a ∨ c))` (Distributive). -/
theorem or_beq_distrib : (a || (b == c)) = ((a || b) == (a || c)) := by revert a b c; decide

/-- `a ⇒ (b ∧ c) = (a ⇒ b) ∧ (a ⇒ c)` (Distributive). -/
theorem imp_and_distrib : imp a (b && c) = (imp a b && imp a c) := by revert a b c; decide

/-- `a ⇒ (b ∨ c) = (a ⇒ b) ∨ (a ⇒ c)` (Distributive). -/
theorem imp_or_distrib : imp a (b || c) = (imp a b || imp a c) := by revert a b c; decide

/-- `a ⇒ (b ⇒ c) = (a ⇒ b) ⇒ (a ⇒ c)` (Distributive). -/
theorem imp_imp_distrib : imp a (imp b c) = imp (imp a b) (imp a c) := by revert a b c; decide

/-- `(a ⇒ (b = c)) = ((a ⇒ b) = (a ⇒ c))` (Distributive). -/
theorem imp_beq_distrib : imp a (b == c) = (imp a b == imp a c) := by revert a b c; decide

/-! ### Antidistributive and Portation -/

/-- `(a ∧ b ⇒ c) = (a ⇒ c) ∨ (b ⇒ c)` (Antidistributive). -/
theorem and_imp_antidistrib : imp (a && b) c = (imp a c || imp b c) := by revert a b c; decide

/-- `(a ∨ b ⇒ c) = (a ⇒ c) ∧ (b ⇒ c)` (Antidistributive). -/
theorem or_imp_antidistrib : imp (a || b) c = (imp a c && imp b c) := by revert a b c; decide

/-- `(a ∧ b ⇒ c) = (a ⇒ (b ⇒ c))` (Portation). -/
theorem and_imp_eq_imp_imp : imp (a && b) c = imp a (imp b c) := by revert a b c; decide

/-- `(a ∧ b ⇒ c) = (a ⇒ ¬b ∨ c)` (Portation). -/
theorem and_imp_eq_imp_not_or : imp (a && b) c = imp a (!b || c) := by revert a b c; decide

/-! ### Conflation -/

/-- `(a ⇒ b) ∧ (c ⇒ d) ⇒ (a ∧ c ⇒ b ∧ d)` (Conflation). -/
theorem imp_and_imp_and : imp (imp a b && imp c d) (imp (a && c) (b && d)) = true := by
  revert a b c d; decide

/-- `(a ⇒ b) ∧ (c ⇒ d) ⇒ (a ∨ c ⇒ b ∨ d)` (Conflation). -/
theorem imp_and_imp_or : imp (imp a b && imp c d) (imp (a || c) (b || d)) = true := by
  revert a b c d; decide

/-! ### Equality and Difference -/

/-- `(a = b) = (a ∧ b) ∨ (¬a ∧ ¬b)` (Equality). -/
theorem beq_eq_or : (a == b) = ((a && b) || (!a && !b)) := by revert a b; decide

/-- `(a ⧧ b) = (a ∧ ¬b) ∨ (¬a ∧ b)` (Difference). -/
theorem bne_eq_or : (a != b) = ((a && !b) || (!a && b)) := by revert a b; decide

/-! ### Resolution

The book writes Resolution as one continuing calculation
`a ∧ c ⇒ (a ∨ b) ∧ (¬b ∨ c) = (a ∧ ¬b) ∨ (b ∧ c) ⇒ a ∨ c`; its three steps are
the following three laws. -/

/-- `a ∧ c ⇒ (a ∨ b) ∧ (¬b ∨ c)` (Resolution, first step). -/
theorem resolution_left : imp (a && c) ((a || b) && (!b || c)) = true := by revert a b c; decide

/-- `(a ∨ b) ∧ (¬b ∨ c) = (a ∧ ¬b) ∨ (b ∧ c)` (Resolution, middle step). -/
theorem resolution_middle : ((a || b) && (!b || c)) = ((a && !b) || (b && c)) := by
  revert a b c; decide

/-- `(a ∧ ¬b) ∨ (b ∧ c) ⇒ a ∨ c` (Resolution, last step). -/
theorem resolution_right : imp ((a && !b) || (b && c)) (a || c) = true := by revert a b c; decide

/-! ### Case Creation and Case Analysis -/

/-- `a = if b then b ⇒ a else ¬b ⇒ a` (Case Creation). -/
theorem case_creation_imp : a = (bif b then imp b a else imp (!b) a) := by revert a b; decide

/-- `a = if b then b ∧ a else ¬b ∧ a` (Case Creation). -/
theorem case_creation_and : a = (bif b then b && a else !b && a) := by revert a b; decide

/-- `a = if b then b = a else b ⧧ a` (Case Creation). -/
theorem case_creation_beq : a = (bif b then b == a else b != a) := by revert a b; decide

/-- `if a then b else c = (a ∧ b) ∨ (¬a ∧ c)` (Case Analysis). -/
theorem cond_eq_or : (bif a then b else c) = ((a && b) || (!a && c)) := by revert a b c; decide

/-- `if a then b else c = (a ⇒ b) ∧ (¬a ⇒ c)` (Case Analysis). -/
theorem cond_eq_and : (bif a then b else c) = (imp a b && imp (!a) c) := by revert a b c; decide

/-! ### One Case -/

/-- `if a then ⊤ else b = a ∨ b` (One Case). -/
theorem cond_top_left : (bif a then top else b) = (a || b) := by revert a b; decide

/-- `if a then ⊥ else b = ¬a ∧ b` (One Case). -/
theorem cond_bot_left : (bif a then bot else b) = (!a && b) := by revert a b; decide

/-- `if a then b else ⊤ = a ⇒ b` (One Case). -/
theorem cond_top_right : (bif a then b else top) = imp a b := by revert a b; decide

/-- `if a then b else ⊥ = a ∧ b` (One Case). -/
theorem cond_bot_right : (bif a then b else bot) = (a && b) := by revert a b; decide

/-- `if a then b else ¬b = (a = b)` (One Case). -/
theorem cond_not_right : (bif a then b else !b) = (a == b) := by revert a b; decide

/-- `if a then ¬b else b = a ⧧ b` (One Case). -/
theorem cond_not_left : (bif a then !b else b) = (a != b) := by revert a b; decide

/-! ### Case Absorption -/

/-- `if a then b else c = if a then a ∧ b else c` (Case Absorption). -/
theorem cond_absorb_and : (bif a then b else c) = (bif a then a && b else c) := by
  revert a b c; decide

/-- `if a then b else c = if a then a ⇒ b else c` (Case Absorption). -/
theorem cond_absorb_imp : (bif a then b else c) = (bif a then imp a b else c) := by
  revert a b c; decide

/-- `if a then b else c = if a then a = b else c` (Case Absorption). -/
theorem cond_absorb_beq : (bif a then b else c) = (bif a then a == b else c) := by
  revert a b c; decide

/-- `if a then b else c = if a then b else ¬a ∧ c` (Case Absorption). -/
theorem cond_absorb_not_and : (bif a then b else c) = (bif a then b else !a && c) := by
  revert a b c; decide

/-- `if a then b else c = if a then b else a ∨ c` (Case Absorption). -/
theorem cond_absorb_or : (bif a then b else c) = (bif a then b else a || c) := by
  revert a b c; decide

/-- `if a then b else c = if a then b else a ⧧ c` (Case Absorption). -/
theorem cond_absorb_bne : (bif a then b else c) = (bif a then b else a != c) := by
  revert a b c; decide

/-! ### Case Distributive (Case Factoring)

The book states the last two laws for `∧` "and similarly replacing `∧` by any
of `∨ = ⧧ ⇒ ⇐`"; here they are stated once for an arbitrary binary operator
`f`, which covers all six. -/

/-- `¬ if a then b else c = if a then ¬b else ¬c` (Case Distributive). -/
theorem not_cond : (!(bif a then b else c)) = (bif a then !b else !c) := by revert a b c; decide

/-- `if a then b else c ∧ d = if a then b ∧ d else c ∧ d` (Case Distributive), for `∧`
and, in the same way, for any binary operator `f`. -/
theorem cond_op (f : Binary → Binary → Binary) :
    f (bif a then b else c) d = (bif a then f b d else f c d) := by
  cases a <;> rfl

/-- `if a then b ∧ c else d ∧ e = if a then b else d ∧ if a then c else e` (Case
Distributive), for `∧` and, in the same way, for any binary operator `f`. -/
theorem cond_op_cond (f : Binary → Binary → Binary) :
    (bif a then f b c else f d e) = f (bif a then b else d) (bif a then c else e) := by
  cases a <;> rfl

/-- The `∧` instance of `cond_op`, as printed in the book. -/
theorem cond_and : ((bif a then b else c) && d) = (bif a then b && d else c && d) :=
  cond_op a b c d (· && ·)

/-- The `∧` instance of `cond_op_cond`, as printed in the book. -/
theorem cond_and_cond :
    (bif a then b && c else d && e) = ((bif a then b else d) && (bif a then c else e)) :=
  cond_op_cond a b c d e (· && ·)

end Binary

end LaPToP.BasicTheories
