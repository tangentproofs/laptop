import LaPToP.ProgramTheory.Programs
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic.NormNum

/-!
# Program Theory: time

This module formalizes Section 4.2 (Time) of Eric Hehner's *A Practical Theory
of Programming* (aPToP): the time variable, implementability with time, the
real-time and recursive-time measures on the book's example, and the four
specifications of Section 4.2.2 (Termination).

## The model

"To talk about time, we just add a time variable. We do not change the theory;
the time variable is treated just like any other variable, as part of the
state." The book's time domain for the recursive measure is `xnat`, the
naturals extended with `∞`; we use `ℕ∞` (`⊤ = ∞`) for both measures, so the
real-time example below counts unit costs rather than nonnegative reals.

A state with time is a structure `TSt` with a time `t : ℕ∞` and one integer
memory variable `x`, the state of the book's examples. Because `t` and `x`
have different types, the single-valued `State Var Val` model of Section 4.0
does not apply; assignments to `x` and to `t` are the relations `assignX` and
`assignT` (`σ′ = σ` with one field replaced), and they satisfy the same
Substitution Law as `Spec.assign`.

"Time cannot decrease, therefore a specification `S` with time is
implementable if and only if `∀σ· ∃σ′· S ∧ t′ ≥ t`" — `ImplementableT`.

The refinements `P ⇐ … P` proved here are the theorems the book states ("this
refinement is a theorem when `P = …`"); as in Section 4.1.1 the recursive call
is not yet a program in the sense of Section 4.0.3.
-/

namespace LaPToP.ProgramTheory

namespace Time

open Spec

/-- A state with a time variable `t` (an extended natural, `∞ = ⊤`) and one
integer memory variable `x`: the book's `σ = t; x`. -/
structure TSt where
  /-- The time variable. -/
  t : ℕ∞
  /-- The memory variable `x`. -/
  x : ℤ

/-- `x:= e`, for `e` an expression of the initial state. -/
def assignX (e : TSt → ℤ) : Spec TSt := fun s s' => s' = { s with x := e s }

/-- `t:= e`, for `e` an expression of the initial state. "Assignments to the
time variable are not executed; they are there for reasoning about time." -/
def assignT (e : TSt → ℕ∞) : Spec TSt := fun s s' => s' = { s with t := e s }

/-- `t:= t+1`, one unit of time. -/
def tick : Spec TSt := assignT fun s => s.t + 1

/-- The Substitution Law for `x:= e`: `x:= e. P = (substitute e for x in P)`. -/
theorem assignX_seq (e : TSt → ℤ) (P : Spec TSt) :
    seq (assignX e) P = fun s s' => P { s with x := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- The Substitution Law for `t:= e`. -/
theorem assignT_seq (e : TSt → ℕ∞) (P : Spec TSt) :
    seq (assignT e) P = fun s s' => P { s with t := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- The Substitution Law for `t:= t+1`. -/
theorem tick_seq (P : Spec TSt) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  assignT_seq _ P

/-! ### Implementability with time (aPToP §4.2) -/

/-- "A specification `S` with time is implementable if and only if
`∀σ· ∃σ′· S ∧ t′ ≥ t`": for each initial state there is a satisfactory final
state in which time has not decreased. -/
def ImplementableT (S : Spec TSt) : Prop := ∀ s, ∃ s', S s s' ∧ s.t ≤ s'.t

/-- Implementability with time is implementability of `S ∧ t′ ≥ t`. -/
theorem implementableT_iff (S : Spec TSt) :
    ImplementableT S ↔ Implementable (and S fun s s' => s.t ≤ s'.t) := Iff.rfl

/-- Implementable with time implies implementable. -/
theorem ImplementableT.implementable {S : Spec TSt} (h : ImplementableT S) : Implementable S :=
  fun s => let ⟨s', hS, _⟩ := h s; ⟨s', hS⟩

/-- `ok` is implementable with time. -/
theorem implementableT_ok : ImplementableT ok := fun s => ⟨s, rfl, le_rfl⟩

/-- `x:= e` is implementable with time. -/
theorem implementableT_assignX (e : TSt → ℤ) : ImplementableT (assignX e) :=
  fun _s => ⟨_, rfl, le_rfl⟩

/-- `t:= t+1` is implementable with time. -/
theorem implementableT_tick : ImplementableT tick := fun _s => ⟨_, rfl, le_self_add⟩

/-- `if b then P else Q` is implementable with time when `P`, `Q` are. -/
theorem implementableT_cond (b : TSt → Prop) {P Q : Spec TSt} (hP : ImplementableT P)
    (hQ : ImplementableT Q) : ImplementableT (cond b P Q) := fun s => by
  by_cases hb : b s
  · obtain ⟨s', h, ht⟩ := hP s; exact ⟨s', Or.inl ⟨hb, h⟩, ht⟩
  · obtain ⟨s', h, ht⟩ := hQ s; exact ⟨s', Or.inr ⟨hb, h⟩, ht⟩

/-- `P. Q` is implementable with time when `P`, `Q` are: time does not decrease
across the intermediate state. -/
theorem implementableT_seq {P Q : Spec TSt} (hP : ImplementableT P) (hQ : ImplementableT Q) :
    ImplementableT (seq P Q) := fun s =>
  let ⟨s'', h, ht⟩ := hP s
  let ⟨s', h', ht'⟩ := hQ s''
  ⟨s', ⟨s'', h, h'⟩, ht.trans ht'⟩

/-! ### The example `P ⇐ if x=0 then ok else x:= x–1. P` with time (aPToP §4.2.0–4.2.1) -/

/-- `(x–1).toNat + 1 = x.toNat` for `x ≥ 1`, in `ℕ∞`. -/
theorem cast_toNat_pred_add_one {x : ℤ} (hx : 1 ≤ x) :
    (((x - 1).toNat : ℕ) : ℕ∞) + 1 = (x.toNat : ℕ∞) := by
  norm_cast; omega

/-- Recursive time: `P = if x≥0 then x′=0 ∧ t′=t+x else t′=∞`. -/
def Prec : Spec TSt :=
  cond (fun s => 0 ≤ s.x) (fun s s' => s'.x = 0 ∧ s'.t = s.t + (s.x.toNat : ℕ∞)) fun _ s' => s'.t = ⊤

/-- `P ⇐ if x=0 then ok else x:= x–1. t:= t+1. P` (recursive time: "each
recursive call costs time 1; all else is free") is a theorem for
`P = if x≥0 then x′=0 ∧ t′=t+x else t′=∞`. -/
theorem refine_Prec :
    Refines Prec (cond (fun s => s.x = 0) ok (seq (assignX fun s => s.x - 1) (seq tick Prec))) := by
  rintro s s' (⟨hx, rfl⟩ | ⟨hx, h⟩)
  · exact Or.inl ⟨hx.ge, hx, by simp [hx]⟩
  · rw [assignX_seq, tick_seq] at h
    rcases h with ⟨h0, hx', ht⟩ | ⟨h0, ht⟩
    · simp only at h0 hx' ht
      refine Or.inl ⟨by omega, hx', ?_⟩
      rw [ht, add_assoc, add_comm 1, cast_toNat_pred_add_one (by omega)]
    · simp only at h0 ht
      exact Or.inr ⟨by omega, ht⟩

/-- Recursive time, the book's second form: `P = x′=0 ∧ if x≥0 then t′=t+x else t′=∞`. -/
def Prec' : Spec TSt :=
  and (fun _ s' => s'.x = 0)
    (cond (fun s => 0 ≤ s.x) (fun s s' => s'.t = s.t + (s.x.toNat : ℕ∞)) fun _ s' => s'.t = ⊤)

/-- The same refinement is a theorem for `P = x′=0 ∧ if x≥0 then t′=t+x else t′=∞`. -/
theorem refine_Prec' :
    Refines Prec' (cond (fun s => s.x = 0) ok (seq (assignX fun s => s.x - 1) (seq tick Prec'))) := by
  rintro s s' (⟨hx, rfl⟩ | ⟨hx, h⟩)
  · exact ⟨hx, Or.inl ⟨hx.ge, by simp [hx]⟩⟩
  · rw [assignX_seq, tick_seq] at h
    obtain ⟨hx', ⟨h0, ht⟩ | ⟨h0, ht⟩⟩ := h
    · simp only at h0 ht
      refine ⟨hx', Or.inl ⟨by omega, ?_⟩⟩
      show s'.t = s.t + _
      rw [ht, add_assoc, add_comm 1, cast_toNat_pred_add_one (by omega)]
    · simp only at h0 ht
      exact ⟨hx', Or.inr ⟨by omega, ht⟩⟩

/-- Real time, with the `if`, the assignment and the call each taking time 1:
`P = if x≥0 then x′=0 ∧ t′ = t + 3×x + 1 else t′=∞`. -/
def Preal : Spec TSt :=
  cond (fun s => 0 ≤ s.x) (fun s s' => s'.x = 0 ∧ s'.t = s.t + ((3 * s.x.toNat + 1 : ℕ) : ℕ∞))
    fun _ s' => s'.t = ⊤

/-- `P ⇐ t:= t+1. if x=0 then ok else t:= t+1. x:= x–1. t:= t+1. P` (real
time, unit costs) is a theorem for `P = if x≥0 then x′=0 ∧ t′ = t + 3×x + 1 else t′=∞`:
"when `x` starts with a nonnegative value, execution of this program sets `x`
to 0, and takes time `3×x + 1` to do so; when `x` starts with a negative value,
execution takes infinite time". -/
theorem refine_Preal :
    Refines Preal
      (seq tick (cond (fun s => s.x = 0) ok
        (seq tick (seq (assignX fun s => s.x - 1) (seq tick Preal))))) := by
  intro s s' h
  rw [tick_seq] at h
  rcases h with ⟨hx, rfl⟩ | ⟨hx, h⟩
  · simp only at hx
    exact Or.inl ⟨hx.ge, hx, by simp [hx]⟩
  · rw [tick_seq, assignX_seq, tick_seq] at h
    rcases h with ⟨h0, hx', ht⟩ | ⟨h0, ht⟩
    · simp only at h0 hx hx' ht
      refine Or.inl ⟨by omega, hx', ?_⟩
      rw [ht]
      have : ((3 * (s.x - 1).toNat + 1 : ℕ) : ℕ∞) + 1 + 1 + 1 = ((3 * s.x.toNat + 1 : ℕ) : ℕ∞) := by
        norm_cast; omega
      rw [← this]; ac_rfl
    · simp only at hx h0 ht
      refine Or.inr ⟨?_, ht⟩
      show ¬ 0 ≤ s.x
      omega

/-! ### Termination (aPToP §4.2.2)

"Here are four specifications, each of which says that variable `x` has final
value 2." -/

/-- (a) `x′=2`: "says nothing about when the final value is wanted". -/
def specA : Spec TSt := fun _ s' => s'.x = 2

/-- (b) `x′=2 ∧ t′<∞`: "insists that the final state be delivered at a finite time". -/
def specB : Spec TSt := fun _ s' => s'.x = 2 ∧ s'.t < ⊤

/-- (c) `x′=2 ∧ (t<∞ ⇒ t′<∞)`: "if the computation starts at a finite time, it
must end at a finite time". -/
def specC : Spec TSt := fun s s' => s'.x = 2 ∧ (s.t < ⊤ → s'.t < ⊤)

/-- (d) `x′=2 ∧ t′≤t+1`: "measuring time in seconds", at most one second. -/
def specD : Spec TSt := fun s s' => s'.x = 2 ∧ s'.t ≤ s.t + 1

/-- (a) can be refined by an infinite loop: `x′=2 ⇐ t:= t+1. x′=2`. "It may be an
unkind refinement, but the customer has no ground for complaint." -/
theorem refine_a : Refines specA (seq tick specA) := by
  intro s s' h; rw [tick_seq] at h; exact h

/-- (b) is unimplementable: "(b) ∧ t′≥t is unsatisfiable for t=∞". -/
theorem unsatisfiable_b (x : ℤ) : Unsatisfiable (and specB fun s s' => s.t ≤ s'.t) ⟨⊤, x⟩ :=
  fun ⟨_, ⟨_, ht⟩, hle⟩ => absurd (top_le_iff.1 hle ▸ ht) (lt_irrefl _)

/-- Hence (b) is not implementable with time; "the programmer has to reject (b)". -/
theorem not_implementableT_b : ¬ ImplementableT specB :=
  fun h => unsatisfiable_b 0 (h ⟨⊤, 0⟩)

/-- (c) is implementable. -/
theorem implementableT_c : ImplementableT specC := fun s =>
  ⟨{ s with x := 2 }, ⟨rfl, fun h => h⟩, le_rfl⟩

/-- (c) "can be refined with exactly the same construction as (a)":
`x′=2 ∧ (t<∞ ⇒ t′<∞) ⇐ t:= t+1. x′=2 ∧ (t<∞ ⇒ t′<∞)`. -/
theorem refine_c : Refines specC (seq tick specC) := by
  intro s s' h
  rw [tick_seq] at h
  obtain ⟨hx, ht⟩ := h
  exact ⟨hx, fun hs => ht (WithTop.add_lt_top.2 ⟨hs, WithTop.one_lt_top⟩)⟩

/-- (d) is implementable. -/
theorem implementableT_d : ImplementableT specD := fun _s =>
  ⟨{ _s with x := 2 }, ⟨rfl, le_self_add⟩, le_rfl⟩

/-- (d) is stronger than (c): a computation that takes at most a second ends
at a finite time if it starts at one. -/
theorem refines_c_d : Refines specC specD := fun _s _ ⟨hx, ht⟩ =>
  ⟨hx, fun hs => lt_of_le_of_lt ht (WithTop.add_lt_top.2 ⟨hs, WithTop.one_lt_top⟩)⟩

/-- For (d) "an infinite loop is no longer possible because
`x′=2 ∧ t′≤t+1 ⇐ t:= t+1. x′=2 ∧ t′≤t+1` is not a theorem". -/
theorem not_refine_d : ¬ Refines specD (seq tick specD) := fun h => by
  have := h ⟨0, 0⟩ ⟨2, 2⟩ (by rw [tick_seq]; exact ⟨rfl, by norm_num⟩)
  obtain ⟨-, ht⟩ := this
  exact absurd ht (by norm_num)

end Time

end LaPToP.ProgramTheory
