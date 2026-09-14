import LaPToP.ProgramTheory.Time
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The while-loop

This module formalizes Section 5.2.0 (While-Loop) of Eric Hehner's
*A Practical Theory of Programming* (aPToP): the while-loop as a refinement
notation, the timed list-summation loop, and Exercise 320 (unbounded bound).

## The model

"We do not define the while-loop as a specification the way we have defined
previous programming notations. Instead, if `W` is an implementable
specification, we consider the refinement `W ⇐ while b do P od` to be an
alternative notation for the refinement `W ⇐ if b then P. W else ok`."

Accordingly `Spec.WhileRefines W b P` is *defined* as
`Refines W (cond b (seq P W) ok)`: it is a refinement notation, not a
specification `while b do P od`. The least-fixed-point account of loops, and
the law `while b do P od = t′≥t ∧ if b then P. t:= t+1. while b do P od else ok`
of the reference section, belong to Section 6.1.1 and are not formalized here.

The two examples use structure states with a time variable, as in
`LaPToP.ProgramTheory.Time`: `TLS = {t; s; n}` for the timed list summation
and `XY = {t; x; y}` with natural `x`, `y` for Exercise 320. As in the book,
the arbitrary values assigned to `y` in Exercise 320 are the values of an
arbitrary function `f : nat→nat` of `x`.
-/

namespace LaPToP.ProgramTheory

open LaPToP.BasicTheories LaPToP.DataStructures

universe u

namespace Spec

variable {σ : Type u}

/-- `W ⇐ while b do P od`, "an alternative notation for the refinement
`W ⇐ if b then P. W else ok`". -/
def WhileRefines (W : Spec σ) (b : σ → Prop) (P : Spec σ) : Prop :=
  Refines W (cond b (seq P W) ok)

variable (W : Spec σ) (b : σ → Prop) (P P' : Spec σ)

/-- The definition, unfolded. -/
theorem whileRefines_iff : WhileRefines W b P ↔ Refines W (cond b (seq P W) ok) := Iff.rfl

/-- By Refinement by Cases: `W ⇐ while b do P od` iff `W ⇐ b ∧ (P. W)` and `W ⇐ ¬b ∧ ok`. -/
theorem whileRefines_iff_cases :
    WhileRefines W b P ↔ Refines W (and (fun s _ => b s) (seq P W)) ∧ Refines W (and (fun s _ => ¬ b s) ok) :=
  refines_cond_iff b

/-- The body of a while-loop may be refined in place (Refinement by Steps). -/
theorem WhileRefines.mono (h : WhileRefines W b P') (hP : Refines P' P) : WhileRefines W b P :=
  steps_cond b h (refines_seq_mono hP (refines_refl W)) (refines_refl ok)

/-- A while-loop whose condition never holds is `ok`: `W ⇐ while ⊥ do P od` iff `W ⇐ ok`. -/
theorem whileRefines_false (hb : ∀ s, ¬ b s) : WhileRefines W b P ↔ Refines W ok := by
  constructor
  · intro h s s' hok; exact h s s' (Or.inr ⟨hb s, hok⟩)
  · rintro h s s' (⟨hbs, -⟩ | ⟨-, hok⟩)
    · exact absurd hbs (hb s)
    · exact h s s' hok

end Spec

/-! ### The timed list summation loop (aPToP §5.2.0) -/

namespace TimedListSummation

open Spec ListSummation

/-- A state with time `t`, the sum `s` and the index `n`. -/
structure TLS where
  /-- The time variable. -/
  t : ℕ∞
  /-- The accumulator `s`. -/
  s : ℤ
  /-- The index `n`. -/
  n : ℤ

/-- `s:= e`. -/
def assignS (e : TLS → ℤ) : Spec TLS := fun st st' => st' = { st with s := e st }

/-- `n:= e`. -/
def assignN (e : TLS → ℤ) : Spec TLS := fun st st' => st' = { st with n := e st }

/-- `t:= t+1`. -/
def tick : Spec TLS := fun st st' => st' = { st with t := st.t + 1 }

/-- Substitution Law for `s:= e`. -/
theorem assignS_seq (e : TLS → ℤ) (P : Spec TLS) : seq (assignS e) P = fun st st' => P { st with s := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Substitution Law for `n:= e`. -/
theorem assignN_seq (e : TLS → ℤ) (P : Spec TLS) : seq (assignN e) P = fun st st' => P { st with n := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Substitution Law for `t:= t+1`. -/
theorem tick_seq (P : Spec TLS) : seq tick P = fun st st' => P { st with t := st.t + 1 } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (L : HList ℤ)

/-- `s′ = s + Σ L [n;..#L] ∧ t′ = t + #L – n` (with the bound `0 ≤ n ≤ #L`
explicit, as in `ListSummation.B`). -/
def Bt : Spec TLS := fun st st' =>
  0 ≤ st.n ∧ st.n ≤ len L →
    st'.s = st.s + sumFrom L st.n ∧ st'.t = st.t + (((len L - st.n).toNat : ℕ) : ℕ∞)

/-- `(#L – (n+1)) + 1 = #L – n` for `n < #L`, in `ℕ∞`. -/
theorem cast_sub_succ_add_one {m n : ℤ} (h : n < m) :
    (((m - (n + 1)).toNat : ℕ) : ℕ∞) + 1 = (((m - n).toNat : ℕ) : ℕ∞) := by
  norm_cast; omega

/-- `s′ = s + Σ L [n;..#L] ∧ t′ = t + #L – n ⇐ while n⧧#L do s:= s + L n. n:= n+1. t:= t+1 od`,
the book's example, proved as `… ⇐ if n⧧#L then s:= s + L n. n:= n+1. t:= t+1. (…) else ok`. -/
theorem whileRefines_Bt :
    WhileRefines (Bt L) (fun st => st.n ≠ len L)
      (seq (assignS fun st => st.s + L.at st.n.toNat) (seq (assignN fun st => st.n + 1) tick)) := by
  rintro st st' (⟨hne, h⟩ | ⟨hb, hok⟩) ⟨h0, hle⟩
  · rw [← seq_assoc, ← seq_assoc, assignS_seq, assignN_seq, tick_seq] at h
    have hlt : st.n < len L := lt_of_le_of_ne hle hne
    obtain ⟨hs, ht⟩ := h ⟨by simp; omega, by simp; omega⟩
    simp only at hs ht
    refine ⟨?_, ?_⟩
    · rw [hs, sumFrom_succ L h0 hlt, add_assoc]
    · rw [ht, add_assoc, add_comm 1, cast_sub_succ_add_one hlt]
  · have hb' : st.n = len L := not_not.1 hb
    simp only [Spec.ok] at hok
    rw [hok, hb', sumFrom_len, sub_self]
    simp

end TimedListSummation

/-! ### Exercise 320: unbounded bound (aPToP §5.2.0) -/

namespace UnboundedBound

open Spec

/-- A state with time `t` and natural variables `x`, `y`. -/
structure XY where
  /-- The time variable. -/
  t : ℕ∞
  /-- The natural variable `x`. -/
  x : ℕ
  /-- The natural variable `y`. -/
  y : ℕ

/-- `x:= e`. -/
def assignX (e : XY → ℕ) : Spec XY := fun st st' => st' = { st with x := e st }

/-- `y:= e`. -/
def assignY (e : XY → ℕ) : Spec XY := fun st st' => st' = { st with y := e st }

/-- `t:= t+1`. -/
def tick : Spec XY := fun st st' => st' = { st with t := st.t + 1 }

/-- Substitution Law for `x:= e`. -/
theorem assignX_seq (e : XY → ℕ) (P : Spec XY) : seq (assignX e) P = fun st st' => P { st with x := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Substitution Law for `y:= e`. -/
theorem assignY_seq (e : XY → ℕ) (P : Spec XY) : seq (assignY e) P = fun st st' => P { st with y := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Substitution Law for `t:= t+1`. -/
theorem tick_seq (P : Spec XY) : seq tick P = fun st st' => P { st with t := st.t + 1 } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (f : ℕ → ℕ)

/-- `Σ f [0;..x]`, "the sum of the first `x` values of `f`". -/
def sumF (x : ℕ) : ℕ := ∑ i ∈ Finset.range x, f i

/-- `Σ f [0;..x+1] = Σ f [0;..x] + f x`. -/
theorem sumF_succ (x : ℕ) : sumF f (x + 1) = sumF f x + f x := Finset.sum_range_succ f x

/-- `t′ = t + x + y + s` where `s = Σ f [0;..x]`: the execution time is
"`x + y + (the sum of x arbitrary natural numbers)`". -/
def E : Spec XY := fun st st' => st'.t = st.t + ((st.x + st.y + sumF f st.x : ℕ) : ℕ∞)

/-- The loop body: `if y>0 then y:= y–1. t:= t+1 else x:= x–1. y:= f x. t:= t+1`. -/
def body : Spec XY :=
  cond (fun st => 0 < st.y) (seq (assignY fun st => st.y - 1) tick)
    (seq (assignX fun st => st.x - 1) (seq (assignY fun st => f st.x) tick))

/-- The book's refinement, "in three cases":
`t′ = t+x+y+s ⇐ if x=y=0 then ok else if y>0 then y:= y–1. t:= t+1. t′ = t+x+y+s
else x:= x–1. y:= f x. t:= t+1. t′ = t+x+y+s`. -/
theorem refine_E :
    Refines (E f)
      (cond (fun st => st.x = 0 ∧ st.y = 0) ok
        (cond (fun st => 0 < st.y) (seq (assignY fun st => st.y - 1) (seq tick (E f)))
          (seq (assignX fun st => st.x - 1) (seq (assignY fun st => f st.x) (seq tick (E f)))))) := by
  rintro st st' (⟨⟨hx, hy⟩, hok⟩ | ⟨hxy, ⟨hy, h⟩ | ⟨hy, h⟩⟩)
  · -- `x=y=0 ∧ ok ⇒ x=y=s=0 ∧ t′=t ⇒ t′ = t+x+y+s`
    simp only [Spec.ok] at hok
    subst hok
    simp [E, hx, hy, sumF]
  · -- `y>0 ∧ (y:= y–1. t:= t+1. t′ = t+x+y+s) = y>0 ∧ t′ = t+1+x+y–1+s ⇒ t′ = t+x+y+s`
    rw [assignY_seq, tick_seq] at h
    simp only [E] at h ⊢
    rw [h, add_assoc]
    congr 1
    norm_cast; omega
  · -- `x>0 ∧ y=0 ∧ (x:= x–1. y:= f x. t:= t+1. t′ = t+x+y+s) = … ⇒ t′ = t+x+y+s`
    rw [assignX_seq, assignY_seq, tick_seq] at h
    simp only [E] at h ⊢
    have hy0 : st.y = 0 := by omega
    have hx0 : 0 < st.x := by omega
    rw [h, add_assoc]
    congr 1
    have hsum : sumF f st.x = sumF f (st.x - 1) + f (st.x - 1) := by
      conv_lhs => rw [show st.x = st.x - 1 + 1 by omega]
      exact sumF_succ f _
    rw [hsum]
    norm_cast; omega

/-- The same refinement in while-loop notation:
`t′ = t+x+y+s ⇐ while ¬(x=y=0) do if y>0 then y:= y–1. t:= t+1 else x:= x–1. y:= f x. t:= t+1 od`. -/
theorem whileRefines_E : WhileRefines (E f) (fun st => ¬ (st.x = 0 ∧ st.y = 0)) (body f) := by
  unfold WhileRefines body
  rw [cond_seq, ← seq_assoc, ← seq_assoc, ← seq_assoc]
  intro st st' h
  refine refine_E f st st' ?_
  rcases h with ⟨hb, h⟩ | ⟨hb, h⟩
  · exact Or.inr ⟨hb, h⟩
  · exact Or.inl ⟨not_not.1 hb, h⟩

end UnboundedBound

end LaPToP.ProgramTheory
