import LaPToP.ProgramTheory.FastExp

/-!
# Go To

This module formalizes Subsection 5.2.4 (Go To) of Eric Hehner's *A
Practical Theory of Programming* (aPToP).

"Suppose the fast exponentiation program `z′=x^y` of Subsection 4.2.6
Exercise 180 were written as follows, using `⦂` for labeling the target of a
`go to`:

    A⦂ z:= 1. if even y then go to C
              else B⦂ z:= z×x. y:= y–1.
                   C⦂ if y=0 then go to E
                      else D⦂ x:= x×x. y:= y/2.
                              if even y then go to D
                              else go to B

Straight from the program, what needs to be proved is the following:
`A ⇐ z:= 1. if even y then C else B`, `B ⇐ z:= z×x. y:= y–1. C`,
`C ⇐ if y=0 then E else D`, `D ⇐ x:= x×x. y:= y/2. if even y then D else B`
for appropriately defined `A`, `B`, `C`, `D`, and `E`. The difficulty with
`go to`, as with loop constructs, is inventing specifications that were not
recorded during program construction. In this example, the appropriate
specifications are: `B = odd y ⇒ z′=z×x^y`, `C = even y ⇒ z′=z×x^y`,
`D = even y ∧ y>0 ⇒ z′=z×x^y`."

## The model

The labels are specifications, and a `go to` is a call of the label's
specification (Section 6.1): the four refinements are proved on the state
of `LaPToP.ProgramTheory.FastExp`, with `A = z′=x^y` and `E = ok` (the book
leaves `A` and `E` to the reader; at `E` the computation is finished).
-/

namespace LaPToP.ProgramTheory

namespace GoTo

open Spec FastExp

/-- `A = z′=x^y`, the whole program. -/
def A : Spec ES := Z
/-- `B = odd y ⇒ z′=z×x^y`. -/
def B : Spec ES := guard (fun s => Odd s.y) P
/-- `C = even y ⇒ z′=z×x^y`. -/
def C : Spec ES := guard (fun s => Even s.y) P
/-- `D = even y ∧ y>0 ⇒ z′=z×x^y`. -/
def D : Spec ES := guard (fun s => Even s.y ∧ 0 < s.y) P
/-- `E = ok`: the end of the program. -/
def E : Spec ES := ok

/-- `A ⇐ z:= 1. if even y then C else B`. -/
theorem A_refines : Refines A (seq (assignZ fun _ => 1) (cond (fun s => Even s.y) C B)) := by
  intro s s' h
  rw [assignZ_seq] at h
  rcases h with ⟨he, h⟩ | ⟨he, h⟩
  · simpa [A, Z, P] using h he
  · simpa [A, Z, P] using h (Nat.not_even_iff_odd.mp he)

/-- `B ⇐ z:= z×x. y:= y–1. C`. -/
theorem B_refines : Refines B (seq (assignZ fun s => s.z * s.x) (seq (assignY fun s => s.y - 1) C)) := fast₄

/-- `C ⇐ if y=0 then E else D`. -/
theorem C_refines : Refines C (cond (fun s => s.y = 0) E D) := fast₃

/-- `D ⇐ x:= x×x. y:= y/2. if even y then D else B`. -/
theorem D_refines : Refines D (seq (assignX fun s => s.x * s.x) (seq (assignY fun s => s.y / 2) (cond (fun s => Even s.y) D B))) :=
  refines_trans _ _ _ fast₅ (refines_seq_mono (refines_refl _) (refines_seq_mono (refines_refl _) fast₆))

end GoTo

end LaPToP.ProgramTheory
