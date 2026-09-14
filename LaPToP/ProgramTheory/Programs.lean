import LaPToP.ProgramTheory.Specifications
import LaPToP.DataStructures.Lists

/-!
# Programs and program development

This module formalizes Section 4.0.3 (Programs), Section 4.1.0 (Refinement
Laws) and Section 4.1.1 (List Summation) of Eric Hehner's *A Practical Theory
of Programming* (aPToP).

## The model

"A program is an implemented specification." The book lists five programming
notations: `ok` is a program; `x:= e` is a program; `if b then P else Q` and
`P. Q` are programs when their operands are; and "an implementable
specification that is refined by a program is a program". `Spec.IsProgram` is
the inductive predicate with exactly these five rules, over states
`State Var Val`. Two honesty notes: the book restricts `e` and `b` to
*implemented expressions* of the initial values (an expression-language
restriction that has no counterpart in this semantic model — any function of
the prestate is allowed); and the implementability hypothesis in the last rule
is redundant, since a specification refined by an implementable one is
implementable (`Spec.IsProgram.refine'`).

The Refinement Laws — by Steps, by Parts, by Cases — are theorems about
`Spec.Refines`, resting on monotonicity of `if`, `.` and `∧`.

For List Summation the state variables are `s` (the sum so far) and `n` (the
number of items summed), both integer-valued; the book takes `n` natural and
remarks that `n;..#L` is "defined only for `n ≤ #L`", so that `0 ≤ n ≤ #L` is
implicit in the specifications. We make that bound explicit, as the book
itself suggests ("for those who were uncomfortable about the use of implicit
information"). `Σ L [n;..#L]` is the sum of the items of `L` from index `n`
on. The four refinements of the development are proved; the last one refines
`D` in terms of `B` again — a recursive call, which is not a program in the
sense of this chapter until execution time and termination are treated (§4.2)
and recursion is justified (§6).
-/

namespace LaPToP.ProgramTheory

open LaPToP.BasicTheories LaPToP.DataStructures

universe u v

namespace Spec

/-! ### Programs (aPToP §4.0.3) -/

section Programs

variable {Var : Type u} {Val : Type v} [DecidableEq Var]

/-- "A program is an implemented specification": (a) `ok` is a program;
(b) `x:= e` is a program; (c) `if b then P else Q` is a program when `P`, `Q`
are; (d) `P. Q` is a program when `P`, `Q` are; (e) an implementable
specification that is refined by a program is a program. -/
inductive IsProgram : Spec (State Var Val) → Prop
  /-- (a) `ok` is a program. -/
  | ok : IsProgram ok
  /-- (b) `x:= e` is a program. -/
  | assign (x : Var) (e : State Var Val → Val) : IsProgram (assign x e)
  /-- (c) `if b then P else Q` is a program when `P` and `Q` are. -/
  | cond (b : State Var Val → Prop) {P Q : Spec (State Var Val)} :
      IsProgram P → IsProgram Q → IsProgram (cond b P Q)
  /-- (d) `P. Q` is a program when `P` and `Q` are. -/
  | seq {P Q : Spec (State Var Val)} : IsProgram P → IsProgram Q → IsProgram (seq P Q)
  /-- (e) an implementable specification refined by a program is a program. -/
  | refine {P S : Spec (State Var Val)} : Implementable P → Refines P S → IsProgram S → IsProgram P

/-- Every program is implementable: "a computer can execute it". -/
theorem IsProgram.implementable {P : Spec (State Var Val)} (h : IsProgram P) : Implementable P := by
  induction h with
  | ok => exact implementable_ok
  | assign x e => exact implementable_assign x e
  | cond b _ _ ihP ihQ => exact implementable_cond b ihP ihQ
  | seq _ _ ihP ihQ => exact implementable_seq ihP ihQ
  | refine hP _ _ _ => exact hP

/-- Rule (e) without its implementability hypothesis, which is redundant: a
specification refined by a program is implementable. -/
theorem IsProgram.refine' {P S : Spec (State Var Val)} (h : Refines P S) (hS : IsProgram S) :
    IsProgram P :=
  IsProgram.refine (implementable_of_refines P S h hS.implementable) h hS

/-- `⊤` is a program (it is refined by `ok`). -/
theorem IsProgram.top : IsProgram (top : Spec (State Var Val)) :=
  IsProgram.refine' (top_refines _) IsProgram.ok

end Programs

/-! ### Refinement Laws (aPToP §4.1.0) -/

section RefinementLaws

variable {σ : Type u} {A B C D E F G P Q R : Spec σ} (b : σ → Prop)

/-- `if` is monotonic in both branches. -/
theorem refines_cond_mono (h₁ : Refines C E) (h₂ : Refines D F) :
    Refines (cond b C D) (cond b E F) := by
  rintro s s' (⟨hb, h⟩ | ⟨hb, h⟩)
  · exact Or.inl ⟨hb, h₁ s s' h⟩
  · exact Or.inr ⟨hb, h₂ s s' h⟩

/-- Sequential composition is monotonic in both operands. -/
theorem refines_seq_mono (h₁ : Refines B D) (h₂ : Refines C E) : Refines (seq B C) (seq D E) :=
  fun s s' ⟨t, hD, hE⟩ => ⟨t, h₁ s t hD, h₂ t s' hE⟩

/-- Conjunction is monotonic in both operands. -/
theorem refines_and_mono (h₁ : Refines A B) (h₂ : Refines C D) : Refines (and A C) (and B D) :=
  fun s s' ⟨hB, hD⟩ => ⟨h₁ s s' hB, h₂ s s' hD⟩

/-- Refinement by Steps: "if `A ⇐ if b then C else D` and `C ⇐ E` and `D ⇐ F`
are theorems, then `A ⇐ if b then E else F` is a theorem". -/
theorem steps_cond (hA : Refines A (cond b C D)) (hC : Refines C E) (hD : Refines D F) :
    Refines A (cond b E F) :=
  refines_trans _ _ _ hA (refines_cond_mono b hC hD)

/-- Refinement by Steps: "if `A ⇐ B. C` and `B ⇐ D` and `C ⇐ E` are theorems,
then `A ⇐ D. E` is a theorem". -/
theorem steps_seq (hA : Refines A (seq B C)) (hB : Refines B D) (hC : Refines C E) :
    Refines A (seq D E) :=
  refines_trans _ _ _ hA (refines_seq_mono hB hC)

/-- Refinement by Steps: "if `A ⇐ B` and `B ⇐ C` are theorems, then `A ⇐ C` is
a theorem" (transitivity). -/
theorem steps_trans (hA : Refines A B) (hB : Refines B C) : Refines A C :=
  refines_trans _ _ _ hA hB

/-- `if b then C∧F else D∧G` refines `(if b then C else D) ∧ (if b then F else G)`. -/
theorem cond_and_cond_refines :
    Refines (and (cond b C D) (cond b F G)) (cond b (and C F) (and D G)) := by
  rintro s s' (⟨hb, hC, hF⟩ | ⟨hb, hD, hG⟩)
  · exact ⟨Or.inl ⟨hb, hC⟩, Or.inl ⟨hb, hF⟩⟩
  · exact ⟨Or.inr ⟨hb, hD⟩, Or.inr ⟨hb, hG⟩⟩

/-- Refinement by Parts: "if `A ⇐ if b then C else D` and `E ⇐ if b then F else G`
are theorems, then `A∧E ⇐ if b then C∧F else D∧G` is a theorem". -/
theorem parts_cond (hA : Refines A (cond b C D)) (hE : Refines E (cond b F G)) :
    Refines (and A E) (cond b (and C F) (and D G)) :=
  refines_trans _ _ _ (refines_and_mono hA hE) (cond_and_cond_refines b)

/-- `(B∧E). (C∧F)` refines `(B. C) ∧ (E. F)`. -/
theorem seq_and_seq_refines : Refines (and (seq B C) (seq E F)) (seq (and B E) (and C F)) :=
  fun _ _ ⟨t, ⟨hB, hE⟩, hC, hF⟩ => ⟨⟨t, hB, hC⟩, ⟨t, hE, hF⟩⟩

/-- Refinement by Parts: "if `A ⇐ B. C` and `D ⇐ E. F` are theorems, then
`A∧D ⇐ B∧E. C∧F` is a theorem". -/
theorem parts_seq (hA : Refines A (seq B C)) (hD : Refines D (seq E F)) :
    Refines (and A D) (seq (and B E) (and C F)) :=
  refines_trans _ _ _ (refines_and_mono hA hD) seq_and_seq_refines

/-- Refinement by Parts: "if `A ⇐ B` and `C ⇐ D` are theorems, then `A∧C ⇐ B∧D`
is a theorem" (conflation). -/
theorem parts_and (hA : Refines A B) (hC : Refines C D) : Refines (and A C) (and B D) :=
  refines_and_mono hA hC

/-- Refinement by Cases: "`P ⇐ if b then Q else R` is a theorem if and only if
`P ⇐ b ∧ Q` and `P ⇐ ¬b ∧ R` are theorems". -/
theorem refines_cond_iff :
    Refines P (cond b Q R) ↔
      Refines P (and (fun s _ => b s) Q) ∧ Refines P (and (fun s _ => ¬ b s) R) := by
  constructor
  · intro h
    exact ⟨fun s s' ⟨hb, hQ⟩ => h s s' (Or.inl ⟨hb, hQ⟩), fun s s' ⟨hb, hR⟩ => h s s' (Or.inr ⟨hb, hR⟩)⟩
  · rintro ⟨h₁, h₂⟩ s s' (⟨hb, hQ⟩ | ⟨hb, hR⟩)
    · exact h₁ s s' ⟨hb, hQ⟩
    · exact h₂ s s' ⟨hb, hR⟩

end RefinementLaws

end Spec

namespace Examples

open Spec

/-- `x′≤x ⇐ if x=0 then x′=x else x′<x` proved by Refinement by Cases, from
`x′≤x ⇐ x=0 ∧ x′=x` and `x′≤x ⇐ x⧧0 ∧ x′<x`. -/
theorem refine₃_by_cases :
    Refines (fun s s' : St => s' V.x ≤ s V.x)
      (cond (fun s => s V.x = 0) (fun s s' => s' V.x = s V.x) (fun s s' => s' V.x < s V.x)) := by
  rw [refines_cond_iff]
  exact ⟨fun _ _ ⟨_, h⟩ => h.le, fun _ _ ⟨_, h⟩ => h.le⟩

end Examples

/-! ### List Summation (aPToP §4.1.1, Exercise 174)

"Write a program to find the sum of a list of numbers. Let `L` be the list of
numbers, and let `s` be a number variable whose final value will be the sum of
the items in `L`. ... We also need a variable to serve as index in the list,
saying how many items have been considered; let us take natural variable `n`
for that." -/

namespace ListSummation

open Spec

/-- The state variables: `s`, the sum so far, and `n`, the number of items summed. -/
inductive SV
  /-- The accumulator `s`. -/
  | s
  /-- The index `n`. -/
  | n
  deriving DecidableEq

/-- States over the two integer variables `s` and `n`. -/
abbrev St := State SV ℤ

variable (L : HList ℤ)

/-- `#L`, the length of the list, as an integer. -/
def len : ℤ := L.contents.length

/-- `Σ L [n;..#L]`, the sum of the items of `L` from index `n` on. -/
def sumFrom (n : ℤ) : ℤ := (L.contents.drop n.toNat).sum

/-- `Σ L [0;..#L] = ΣL`. -/
theorem sumFrom_zero : sumFrom L 0 = L.contents.sum := by simp [sumFrom]

/-- `Σ L [#L;..#L] = 0`. -/
theorem sumFrom_len : sumFrom L (len L) = 0 := by simp [sumFrom, len]

/-- `Σ L [n;..#L] = L n + Σ L [n+1;..#L]` for `0 ≤ n < #L`. -/
theorem sumFrom_succ {n : ℤ} (h0 : 0 ≤ n) (hn : n < len L) :
    sumFrom L n = L.at n.toNat + sumFrom L (n + 1) := by
  have hlt : n.toNat < L.contents.length := by simp only [len] at hn; omega
  simp only [sumFrom, HList.at, Str.at, List.drop_eq_getElem_cons hlt, List.sum_cons,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  have : (n + 1).toNat = n.toNat + 1 := by omega
  rw [this]

/-- The problem: `s′ = ΣL`. -/
def A : Spec St := fun _ st' => st' SV.s = L.contents.sum

/-- `0 ≤ n ≤ #L ⇒ s′ = s + Σ L [n;..#L]`: `n` items have been summed and the
rest remain to be summed (with the book's implicit bound on `n` made explicit). -/
def B : Spec St := fun st st' => 0 ≤ st SV.n ∧ st SV.n ≤ len L → st' SV.s = st SV.s + sumFrom L (st SV.n)

/-- `n=#L ⇒ B`. -/
def C : Spec St := fun st st' => st SV.n = len L → B L st st'

/-- `n⧧#L ⇒ B`. -/
def D : Spec St := fun st st' => st SV.n ≠ len L → B L st st'

/-- `s′ = ΣL ⇐ s:= 0. n:= 0. B`: "we must begin by assigning 0 to both `s` and
`n` ... we complete the task by adding the remaining items". Proved "by two
applications of the Substitution Law". -/
theorem refine_A : Refines (A L) (seq (assign SV.s fun _ => 0) (seq (assign SV.n fun _ => 0) (B L))) := by
  intro st st' h
  rw [assign_seq, assign_seq] at h
  have h' := h ⟨le_rfl, by simp [len]⟩
  simpa [A, sumFrom_zero] using h'

/-- `B ⇐ if n=#L then C else D` (Case Creation). -/
theorem refine_B : Refines (B L) (cond (fun st => st SV.n = len L) (C L) (D L)) := by
  rintro st st' (⟨hb, h⟩ | ⟨hb, h⟩)
  · exact h hb
  · exact h hb

/-- `C ⇐ ok`: "one is trivial" — all items have been summed. -/
theorem refine_C : Refines (C L) ok := by
  rintro st st' rfl hn ⟨-, -⟩
  rw [hn, sumFrom_len, add_zero]

/-- `D ⇐ s:= s + L n. n:= n+1. B`: "let us add one more item to the sum. To
complete the refinement, we must also add any remaining items." Proved "by two
applications of the Substitution Law". The right side refers to `B` again: a
recursive call. -/
theorem refine_D :
    Refines (D L)
      (seq (assign SV.s fun st => st SV.s + L.at (st SV.n).toNat)
        (seq (assign SV.n fun st => st SV.n + 1) (B L))) := by
  intro st st' h hne ⟨h0, hle⟩
  rw [assign_seq, assign_seq] at h
  have hlt : st SV.n < len L := lt_of_le_of_ne hle hne
  have h' := h ⟨by simp; omega, by simp; omega⟩
  simp only [Function.update_self, Function.update_of_ne (show SV.n ≠ SV.s by decide),
    Function.update_of_ne (show SV.s ≠ SV.n by decide)] at h'
  rw [h', sumFrom_succ L h0 hlt, add_assoc]

/-- The compiler's view, after macro-expanding `C` and `D` by Refinement by
Steps: `B ⇐ if n=#L then ok else s:= s + L n. n:= n+1. B`. -/
theorem refine_B_expanded :
    Refines (B L)
      (cond (fun st => st SV.n = len L) ok
        (seq (assign SV.s fun st => st SV.s + L.at (st SV.n).toNat)
          (seq (assign SV.n fun st => st SV.n + 1) (B L)))) :=
  steps_cond _ (refine_B L) (refine_C L) (refine_D L)

/-- `s′ = ΣL ⇐ s:= 0. n:= 0. if n=#L then ok else (s:= s + L n. n:= n+1. B)`,
the whole development assembled by Refinement by Steps. -/
theorem refine_A_expanded :
    Refines (A L)
      (seq (assign SV.s fun _ => 0)
        (seq (assign SV.n fun _ => 0)
          (cond (fun st => st SV.n = len L) ok
            (seq (assign SV.s fun st => st SV.s + L.at (st SV.n).toNat)
              (seq (assign SV.n fun st => st SV.n + 1) (B L)))))) :=
  steps_seq (refine_A L) (refines_refl _)
    (steps_seq (refines_refl _) (refines_refl _) (refine_B_expanded L))

/-- The specifications `A`, `B`, `C`, `D` are implementable (so rule (e) may
be applied to them once their solutions are programs). -/
theorem implementable_B : Implementable (B L) := fun st =>
  ⟨Function.update st SV.s (st SV.s + sumFrom L (st SV.n)), fun _ => by simp⟩

/-- `A` is implementable. -/
theorem implementable_A : Implementable (A L) := fun st =>
  ⟨Function.update st SV.s L.contents.sum, by simp [A]⟩

end ListSummation

end LaPToP.ProgramTheory
