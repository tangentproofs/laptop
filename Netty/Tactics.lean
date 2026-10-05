import Lean

/-!
# The tactics the translation of a calculation uses

The translation (`Netty.ToLean`) proves each step of a calculation from the Lean
twin of the law it names. What it needs besides the twins is small and fixed:

* the margin relations `Imp`/`Rimp` and their `Trans` instances, so the links
  of a calculation chain into one proof;
* `netty_ac`, which shows that two ways of writing a formula differ only by
  how an association is bracketed, the order of a symmetric operator's
  operands, or a unit — which is all that separates the place a law matched,
  as the line writes it, from the law's own left side;
* the one-point simplification `Netty.Calc.onePoint`, the Lean side of the
  rules that eliminate an intermediate state (`substitution law`, `one point`):
  `∃x, … ∧ x = t ∧ …` is `… ∧ t = t ∧ …`, by `Netty.Calc.exists_eq_elim`;
* `netty_rule`, which proves a rule's step with that simplification;
* `netty_step`, Lean's automation, for the steps no law or rule justifies — the
  ones a calculation hints as `arithmetic` — and said to be.
-/

namespace Netty.Calc

/-- `a ⇒ b`, as a margin relation of a `calc` chain. -/
def Imp (a b : Prop) : Prop := a → b

/-- `a ⇐ b`, as a margin relation of a `calc` chain. -/
def Rimp (a b : Prop) : Prop := b → a

instance : Trans Imp Imp Imp := ⟨fun h g x => g (h x)⟩
instance : Trans Iff Imp Imp := ⟨fun h g x => g (h.mp x)⟩
instance : Trans Imp Iff Imp := ⟨fun h g x => g.mp (h x)⟩
instance : Trans Rimp Rimp Rimp := ⟨fun h g x => h (g x)⟩
instance : Trans Iff Rimp Rimp := ⟨fun h g x => h.mpr (g x)⟩
instance : Trans Rimp Iff Rimp := ⟨fun h g x => h (g.mpr x)⟩

instance : @Trans Int Int Int (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Int.le_trans⟩
instance : @Trans Int Int Int (· ≤ ·) (· < ·) (· < ·) := ⟨Int.lt_of_le_of_lt⟩
instance : @Trans Int Int Int (· < ·) (· ≤ ·) (· < ·) := ⟨Int.lt_of_lt_of_le⟩
instance : @Trans Int Int Int (· < ·) (· < ·) (· < ·) := ⟨Int.lt_trans⟩
instance : @Trans Int Int Int (· ≥ ·) (· ≥ ·) (· ≥ ·) := ⟨fun h g => Int.le_trans g h⟩
instance : @Trans Int Int Int (· ≥ ·) (· > ·) (· > ·) := ⟨fun h g => Int.lt_of_lt_of_le g h⟩
instance : @Trans Int Int Int (· > ·) (· ≥ ·) (· > ·) := ⟨fun h g => Int.lt_of_le_of_lt g h⟩
instance : @Trans Int Int Int (· > ·) (· > ·) (· > ·) := ⟨fun h g => Int.lt_trans g h⟩

/-- The one-point law: an existential whose body pins its variable is the body
at that value. -/
theorem exists_eq_elim {α : Sort u} {p : α → Prop} (t : α) (h : ∀ x, p x → x = t) :
    (∃ x, p x) = p t :=
  propext ⟨fun ⟨x, hx⟩ => h x hx ▸ hx, fun hp => ⟨t, hp⟩⟩

/-- `nat` is not empty. -/
theorem exists_nonneg : (∃ x : Int, 0 ≤ x) = True := eq_true ⟨0, Int.le_refl 0⟩

open Lean Meta in
/-- A proof of `x = t` from a proof `h` of `b`, when one of the conjuncts of `b`
is `x = t` or `t = x` with `t` free of `x`. -/
partial def findEq (x : Expr) (b h : Expr) : MetaM (Option (Expr × Expr)) := do
  let b ← whnfR b
  match_expr b with
  | And l r =>
      if let some res ← findEq x l (mkApp3 (mkConst ``And.left) l r h) then return some res
      findEq x r (mkApp3 (mkConst ``And.right) l r h)
  | Eq _ a c =>
      if a == x && !c.containsFVar x.fvarId! then return some (c, h)
      if c == x && !a.containsFVar x.fvarId! then return some (a, ← mkEqSymm h)
      return none
  | _ => return none

open Lean Meta Simp in
/-- `∃x, … ∧ x = t ∧ …` becomes `… ∧ t = t ∧ …`: the one-point rule, as a
simplification. -/
simproc_decl onePoint (Exists _) := fun e => do
  let_expr Exists α p := e | return .continue
  let p ← instantiateMVars p
  let .lam n ty body bi := p | return .continue
  let res? ← withLocalDecl n bi ty fun x => do
    let b := body.instantiate1 x
    withLocalDeclD `h b fun h => do
      match ← findEq x b h with
      | some (t, pf) =>
          if t.containsFVar x.fvarId! then return none
          let hl ← mkLambdaFVars #[x, h] pf
          return some (t, hl)
      | none => return none
  let some (t, hl) := res? | return .continue
  let pf ← mkAppOptM ``exists_eq_elim #[α, p, t, hl]
  return .visit { expr := (mkApp p t).headBeta, proof? := some pf }

/-! ### The twin of `arithmetic`

Two integer expressions whose polynomials are equal are equal: that is Lean's
own verified normalizer (`Lean.Grind.CommRing.Expr.denote_toPoly`), and a step
by arithmetic is proved by reflection — the two sides, read as
`Lean.Grind.CommRing.Expr`, normalize to the same polynomial by computation. A
comparison is first put in normal form (`0 ≤ p`, `p = 0`, `¬(p = 0)`) by the
lemmas below, and its polynomial compared the same way. -/

open Lean.Grind.CommRing in
/-- Equal polynomials, equal integers. -/
theorem ring_eq {ctx : Lean.RArray Int} (a b : Expr) (h : a.toPoly == b.toPoly) :
    a.denote ctx = b.denote ctx := by
  rw [← Expr.denote_toPoly, ← Expr.denote_toPoly, eq_of_beq h]

theorem ge_norm (a b : Int) : (a ≥ b) = (0 ≤ a - b - 0) := by apply propext; omega
theorem le_norm (a b : Int) : (a ≤ b) = (0 ≤ b - a - 0) := by apply propext; omega
theorem gt_norm (a b : Int) : (a > b) = (0 ≤ a - b - 1) := by apply propext; omega
theorem lt_norm (a b : Int) : (a < b) = (0 ≤ b - a - 1) := by apply propext; omega
theorem eq_norm (a b : Int) : (a = b) = (a - b - 0 = 0) := by apply propext; omega
theorem ne_norm (a b : Int) : (a ≠ b) = ¬(a - b - 0 = 0) := by apply propext; omega
theorem eq_zero_neg (p q : Int) (h : p = -q) : (p = 0) = (q = 0) := by apply propext; omega
theorem ne_zero_neg (p q : Int) (h : p = -q) : (¬(p = 0)) = ¬(q = 0) := by apply propext; omega

end Netty.Calc

/-- Prove that two formulas differ only by association, symmetry and units. -/
macro "netty_ac" : tactic =>
  `(tactic| first
    | rfl
    | exact Iff.rfl
    | (simp (config := { maxSteps := 4000 }) only [and_assoc, and_comm, and_left_comm, or_assoc, or_comm, or_left_comm,
        and_true, true_and, or_false, false_or, eq_comm, ne_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm,
        Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.add_zero, Int.zero_add,
        Int.mul_one, Int.one_mul]; done)
    | ac_rfl)

/-- Prove a rule's step: eliminate the intermediate states the step pins, by the
one-point rule, and the ones nothing mentions. -/
macro "netty_rule" : tactic =>
  `(tactic| first
    | rfl
    | (simp only [and_assoc, Netty.Calc.onePoint, exists_const, eq_self_iff_true, true_and,
        and_true, exists_and_left, exists_and_right, Netty.Calc.exists_nonneg]; done)
    | ((simp only [and_assoc, Netty.Calc.onePoint, exists_const, eq_self_iff_true, true_and,
        and_true, exists_and_left, exists_and_right, Netty.Calc.exists_nonneg]) <;>
       -- What is left of a guard over `nat` is the theorem's own hypothesis
       -- that the variable is at least zero, a numeral, or a sum or product of
       -- those.
       (first
         | netty_ac
         | (simp only [*, and_true, true_and, Int.reduceLE, Int.le_refl, Int.add_nonneg,
             Int.mul_nonneg]; done)
         | ((simp only [*, and_true, true_and, Int.reduceLE, Int.le_refl, Int.add_nonneg,
             Int.mul_nonneg]) <;> netty_ac))))

/-- Prove one link of a translated calculation by Lean's automation: for the
steps no law or rule justifies. -/
macro "netty_step" : tactic =>
  `(tactic| ((try simp only [Netty.Calc.Imp, Netty.Calc.Rimp]) <;>
             first
               | grind
               | (simp <;> grind)
               | omega
               | (simp only [and_assoc, exists_and_left, exists_and_right, exists_eq_left,
                    exists_eq_right, exists_const, Netty.Calc.onePoint] <;>
                  first | grind | (simp <;> grind) | omega)
               | ((repeat' (first | apply exists_congr | apply forall_congr' | intro))
                    <;> first | grind | (simp <;> grind) | omega)))
