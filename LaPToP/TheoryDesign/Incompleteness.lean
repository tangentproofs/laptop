import LaPToP.TheoryDesign.DataTransformation

/-!
# Soundness and completeness of data transformation

This module formalizes Subsection 7.2.4 (Soundness and Completeness) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), Exercise 465.

"Data transformation is sound in the sense that a user cannot tell that a
transformation has been made; that was the criterion of its design. But it is
possible to find two specifications of identical behavior (from a user's point
of view) for which there is no data transformer to transform one into the
other. In that sense, data transformation is incomplete. Exercise 465
illustrates the problem. The user's variable is `i` and the implementer's
variable is `j`, both of type `0, 1, 2`. The operations are: `initialize = i′=0`;
`step = if j>0 then i:= i+1. j:= j–1 else ok`. ... If this were a practical
problem, we would notice that `initialize` can be refined, resolving the
nondeterminism. For example, `initialize ⇐ i:= 0. j:= 0`. We could then transform
`initialize` and `step` to get rid of `j`, replacing it with nothing. The
transformer is `j=0`. It transforms the implementation of `initialize` as
follows: `∀j· j=0 ⇒ ∃j′· j′=0 ∧ i′=j′=0 = i:= 0`. And it transforms `step` as
follows: `∀j· j=0 ⇒ ∃j′· j′=0 ∧ if j>0 then i:= i+1. j:= j–1 else ok = ok`. ...
But the theoretical problem is to replace `j` with binary variable `b` without
resolving the nondeterminism, so that `initialize` is transformed to `i′=0`;
`step` is transformed to `if b ∧ i<2 then i′ = i+1 else ok`. ... The
nondeterminism is maintained. But there is no transformer in variables `i`, `j`,
and `b` to do the job. That's because the initial value of `j` gives us `3`
different behaviors, but the initial value of binary variable `b` cannot
distinguish among these `3` behaviors."

## The model

`i` and `j` are `Fin 3` ("of type `0, 1, 2`"); `i:= i+1` and `j:= j–1` are
written on the values, so `step` is unsatisfiable at `i = 2`, `j > 0` (a state
the user cannot reach). "Replacing `j` with nothing" is the new implementer's
type `Unit`. The nonexistence theorem is proved for every transformer
`D : Fin 3 → Fin 3 → Bool → Prop` in the variables `i`, `j`, `b` (`transformU`,
which lets the transformer mention the user's variable), by finitely many
instances of the two transformed-specification equations; the transformed
`step` is read with `ok` in the else-branch also fixing `b′ = b`, and with `b′`
arbitrary when `i` is increased ("`b` is again assigned either of its two
values"). Soundness — "a user cannot tell that a transformation has been made" —
is `transform_spec` of Section 7.2.
-/

namespace LaPToP.TheoryDesign

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace Incompleteness

open Spec

/-- The user's and implementer's variables `i`, `j : 0, 1, 2`. -/
abbrev IJ := Fin 3 × Fin 3

/-- `initialize = i′=0` (`j′` arbitrary); named `init` since `initialize` is a Lean keyword. -/
def init : Spec IJ := fun _ s' => s'.1 = 0

/-- `step = if j>0 then i:= i+1. j:= j–1 else ok`. -/
def step : Spec IJ := fun s s' =>
  if 0 < s.2.val then s'.1.val = s.1.val + 1 ∧ s'.2.val = s.2.val - 1 else s' = s

/-! ### Resolving the nondeterminism: the transformer `j=0` -/

/-- `i:= 0. j:= 0`. -/
def initZero : Spec IJ := fun _ s' => s' = (0, 0)

/-- `initialize ⇐ i:= 0. j:= 0`. -/
theorem init_refines : Refines init initZero := by
  rintro _ _ rfl; rfl

/-- The transformer `j=0`, "replacing `j` with nothing". -/
def Dz (j : Fin 3) (_ : Unit) : Prop := j = 0

theorem isTransformer_Dz : IsTransformer Dz := fun _ => ⟨0, rfl⟩

/-- `∀j· j=0 ⇒ ∃j′· j′=0 ∧ i′=j′=0 = i:= 0`. -/
theorem transform_initZero : transform Dz initZero = fun _ s' : Fin 3 × Unit => s'.1 = 0 := by
  funext s s'
  apply propext
  simp only [transform, Dz, initZero]
  constructor
  · intro h
    obtain ⟨_, rfl, h2⟩ := h 0 rfl
    exact (Prod.mk.inj h2).1
  · rintro h _ rfl
    exact ⟨0, rfl, Prod.ext (by simpa using h) rfl⟩

/-- `∀j· j=0 ⇒ ∃j′· j′=0 ∧ if j>0 then i:= i+1. j:= j–1 else ok = ok`. -/
theorem transform_step : transform Dz step = (ok : Spec (Fin 3 × Unit)) := by
  funext s s'
  apply propext
  simp only [transform, Dz, step, Spec.ok]
  constructor
  · intro h
    obtain ⟨_, rfl, h2⟩ := h 0 rfl
    simp only [Fin.val_zero, lt_irrefl, if_false] at h2
    exact Prod.ext (Prod.mk.inj h2).1 rfl
  · rintro rfl _ rfl
    exact ⟨0, rfl, by simp⟩

/-! ### The theoretical problem: `j` replaced by a binary variable `b` -/

/-- The user's variable `i` with the new implementer's variable `b`. -/
abbrev IB := Fin 3 × Bool

/-- `initialize` transformed: `i′=0` (`b′` arbitrary). -/
def initB : Spec IB := fun _ s' => s'.1 = 0

/-- `step` transformed: `if b ∧ i<2 then i′ = i+1 else ok` (`b′` arbitrary when `i` is increased). -/
def stepB : Spec IB := fun s s' =>
  if s.2 = true ∧ s.1.val < 2 then s'.1.val = s.1.val + 1 else s' = s

/-- "There is no transformer in variables `i`, `j`, and `b` to do the job." -/
theorem no_transformer :
    ¬ ∃ D : Fin 3 → Fin 3 → Bool → Prop,
      IsTransformerU D ∧ transformU D init = initB ∧ transformU D step = stepB := by
  rintro ⟨D, hT, -, hS⟩
  have E : ∀ i b i' b', transformU D step (i, b) (i', b') ↔ stepB (i, b) (i', b') := fun i b i' b' =>
    iff_of_eq (congrFun (congrFun hS (i, b)) (i', b'))
  -- (a) `step` from `(1, b=⊥)` to `(1, ⊥)` is `ok`: every `j` with `D 1 j ⊥` is `0`
  have ha : ∀ j, D 1 j false → j = 0 := by
    intro j hj
    have h := (E 1 false 1 false).2 (by simp [stepB])
    obtain ⟨j', -, hs⟩ := h j hj
    simp only [step] at hs
    split_ifs at hs with hpos
    · simp at hs
    · exact Fin.ext (by omega)
  -- (b) `step` from `(0, ⊤)` to `(1, ⊥)` increases `i`: every `j` with `D 0 j ⊤` is `1`
  have hb : ∀ j, D 0 j true → j = 1 := by
    intro j hj
    have h := (E 0 true 1 false).2 (by simp [stepB])
    obtain ⟨j', hj', hs⟩ := h j hj
    simp only [step] at hs
    split_ifs at hs with hpos
    · have := ha j' hj'
      subst this
      exact Fin.ext (by simp at hs; omega)
    · simp at hs
  -- (c) `step` from `(0, ⊤)` to `(1, ⊤)`: `D 0 1 ⊤ → D 1 0 ⊤`
  have hc : ∀ j, D 0 j true → D 1 0 true := by
    intro j hj
    have h := (E 0 true 1 true).2 (by simp [stepB])
    obtain ⟨j', hj', hs⟩ := h j hj
    have hj1 := hb j hj
    subst hj1
    simp only [step] at hs
    split_ifs at hs with hpos
    · have : j' = 0 := Fin.ext (by simp at hs; omega)
      subst this
      exact hj'
    · simp at hpos
  -- (d) `step` from `(1, ⊤)` to `(2, ⊤)` increases `i`: every `j` with `D 1 j ⊤` is positive
  have hd : ¬ D 1 0 true := by
    intro h0
    have h := (E 1 true 2 true).2 (by simp [stepB])
    obtain ⟨j', -, hs⟩ := h 0 h0
    simp only [step] at hs
    split_ifs at hs with hpos
    · simp at hpos
    · simp at hs
  obtain ⟨j, hj⟩ := hT 0 true
  exact hd (hc j hj)

end Incompleteness

end LaPToP.TheoryDesign
