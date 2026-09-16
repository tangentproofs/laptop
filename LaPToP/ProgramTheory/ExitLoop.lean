import LaPToP.ProgramTheory.WhileLoop
import LaPToP.ProgramTheory.Scope

/-!
# Exit-loop

This module formalizes Section 5.2.1 (Exit-Loop) of Eric Hehner's *A
Practical Theory of Programming* (aPToP).

"Some languages provide a command to jump out of the middle of a loop.
Suppose the loop `do P od` with the additional syntax `exit when b` allowed
within `P`, where `b` is binary. ... As in Subsection 5.2.0, we consider
refinement by a loop with exits to be an alternative notation. For example,
if `L` is an implementable specification, then

    L ⇐ do A. exit when b. C od

is an alternative notation for `L ⇐ A. if b then ok else C. L`."

## The model

Exactly as for the while-loop (`LaPToP.ProgramTheory.WhileLoop`), the
exit-loop is *defined* to be its refinement structure: `ExitLoopRefines L A b C`
is `Refines L (seq A (cond b ok (seq C L)))`. An `exit n when b` out of nested
loops is handled, as the book does, by naming the inner loop: the deep-exit
example `P ⇐ do A. do B. exit 2 when c. D od. E od` is the pair `P ⇐ A. Q`,
`Q ⇐ B. if c then ok else D. Q` "for some appropriately defined `Q`", and the
deep-and-shallow example likewise. Proved: an exit at the top of the body is a
while-loop; the body may be refined in place; unrolling; the book's remark
that "a binary variable can be introduced for the purpose of recording
whether the goal has been reached, and tested at each iteration" — the
exit-loop is translated to `new done := ⊥· while ¬done do A. if b then
done:= ⊤ else C od`, justified by the while-loop rule; and a small example.
"Some refinement structures require the introduction of new variables and
even whole data structures to encode them as loops with exits" is not
formalized.
-/

namespace LaPToP.ProgramTheory

universe u

namespace Spec

variable {σ : Type u}

/-- `L ⇐ do A. exit when b. C od`, "an alternative notation for
`L ⇐ A. if b then ok else C. L`". -/
def ExitLoopRefines (L A : Spec σ) (b : σ → Prop) (C : Spec σ) : Prop :=
  Refines L (seq A (cond b ok (seq C L)))

variable (L A : Spec σ) (b : σ → Prop) (C : Spec σ)

/-- The definition, unfolded. -/
theorem exitLoopRefines_iff : ExitLoopRefines L A b C ↔ Refines L (seq A (cond b ok (seq C L))) := Iff.rfl

/-- Pointwise: after `A`, either `b` holds and the loop exits, or `¬b`, `C`, and
the loop again. -/
theorem exitLoopRefines_iff_cases :
    ExitLoopRefines L A b C ↔
      ∀ s u s', A s u → (b u → s' = u → L s s') ∧ (¬ b u → seq C L u s' → L s s') := by
  constructor
  · intro h s u s' hA
    exact ⟨fun hb hs => h s s' ⟨u, hA, Or.inl ⟨hb, hs⟩⟩, fun hb hCL => h s s' ⟨u, hA, Or.inr ⟨hb, hCL⟩⟩⟩
  · rintro h s s' ⟨u, hA, (⟨hb, hs⟩ | ⟨hb, hCL⟩)⟩
    · exact (h s u s' hA).1 hb hs
    · exact (h s u s' hA).2 hb hCL

/-- An exit at the top of the body is a while-loop: `L ⇐ do exit when b. C od` iff
`L ⇐ while ¬b do C od`. -/
theorem exitLoopRefines_ok_iff : ExitLoopRefines L ok b C ↔ WhileRefines L (fun s => ¬ b s) C := by
  rw [ExitLoopRefines, WhileRefines, ok_seq, cond_not]

/-- The parts of an exit-loop may be refined in place (Refinement by Steps). -/
theorem ExitLoopRefines.mono {A' C' : Spec σ} (h : ExitLoopRefines L A' b C') (hA : Refines A' A) (hC : Refines C' C) :
    ExitLoopRefines L A b C :=
  refines_trans _ _ _ h
    (refines_seq_mono hA (refines_cond_mono b (refines_refl _) (refines_seq_mono hC (refines_refl _))))

/-- Unrolling once more: `L ⇐ A. if b then ok else C. A. if b then ok else C. L`. -/
theorem ExitLoopRefines.unroll (h : ExitLoopRefines L A b C) :
    Refines L (seq A (cond b ok (seq C (seq A (cond b ok (seq C L)))))) :=
  refines_trans _ _ _ h
    (refines_seq_mono (refines_refl _) (refines_cond_mono b (refines_refl _) (refines_seq_mono (refines_refl _) h)))

/-! ### Deep exits -/

/-- `P ⇐ do A. do B. exit 2 when c. D od. E od`: "the refinement structure
corresponding to this loop is `P ⇐ A. Q`, `Q ⇐ B. if c then ok else D. Q` for some
appropriately defined `Q`". `E` is "stranded in a dead area" and does not occur. -/
def DeepExitRefines (P Q A B : Spec σ) (c : σ → Prop) (D : Spec σ) : Prop :=
  Refines P (seq A Q) ∧ Refines Q (seq B (cond c ok (seq D Q)))

/-- `exit 2` is the naming of the inner loop: the inner structure is itself an exit-loop. -/
theorem deepExitRefines_iff (P Q A B : Spec σ) (c : σ → Prop) (D : Spec σ) :
    DeepExitRefines P Q A B c D ↔ Refines P (seq A Q) ∧ ExitLoopRefines Q B c D := Iff.rfl

/-- The outer specification unrolled through the inner loop once. -/
theorem DeepExitRefines.unroll {P Q A B : Spec σ} {c : σ → Prop} {D : Spec σ} (h : DeepExitRefines P Q A B c D) :
    Refines P (seq A (seq B (cond c ok (seq D Q)))) :=
  refines_trans _ _ _ h.1 (refines_seq_mono (refines_refl _) h.2)

/-- `P ⇐ do A. exit 1 when b. C. do D. exit 2 when e. F. exit 1 when g. H od. I od`:
"the refinement structure corresponding to this loop is `P ⇐ A. if b then ok else C. Q`,
`Q ⇐ D. if e then ok else F. if g then I. P else H. Q` for some appropriately defined `Q`". -/
def DeepShallowRefines (P Q A : Spec σ) (b : σ → Prop) (C D : Spec σ) (e : σ → Prop) (F : Spec σ)
    (g : σ → Prop) (H I : Spec σ) : Prop :=
  Refines P (seq A (cond b ok (seq C Q))) ∧
    Refines Q (seq D (cond e ok (seq F (cond g (seq I P) (seq H Q)))))

/-- The outer loop of the deep-and-shallow example is an exit-loop whose
continuation is the inner specification `Q`. -/
theorem DeepShallowRefines.outer {P Q A : Spec σ} {b : σ → Prop} {C D : Spec σ} {e : σ → Prop} {F : Spec σ}
    {g : σ → Prop} {H I : Spec σ} (h : DeepShallowRefines P Q A b C D e F g H I) :
    Refines P (seq A (cond b ok (seq C Q))) := h.1

/-! ### Exits by a binary flag

"A binary variable can be introduced for the purpose of recording whether the
goal has been reached, and tested at each iteration of each level of loop to
decide whether to continue or exit." -/

/-- The while-loop with the flag `done`: if `done` holds do nothing, otherwise
establish `L` on the nonlocal variables and set `done`. -/
def flagLoop (L : Spec σ) : Spec (σ × Prop) := fun st st' =>
  (st.2 → st' = st) ∧ (¬ st.2 → L st.1 st'.1 ∧ st'.2)

/-- `done:= ⊤`. -/
def setDone : Spec (σ × Prop) := fun st st' => st' = (st.1, True)

/-- The translation of `L ⇐ do A. exit when b. C od` into
`L ⇐ new done := ⊥· while ¬done do A. if b then done:= ⊤ else C od`: the loop body
refines the flagged loop specification by the while-loop rule. -/
theorem ExitLoopRefines.flag (h : ExitLoopRefines L A b C) :
    WhileRefines (flagLoop L) (fun st => ¬ st.2)
      (seq (liftNonlocal A) (cond (fun st => b st.1) setDone (liftNonlocal C))) := by
  rintro ⟨s, d⟩ ⟨s', d'⟩ (⟨hd, ⟨u, v⟩, ⟨⟨w, x⟩, ⟨hA, hx⟩, hcond⟩, hW⟩ | ⟨hd, hok⟩)
  · simp only at hd hA hx
    refine ⟨fun hd' => absurd hd' hd, fun _ => ?_⟩
    rcases hcond with ⟨hb, huv⟩ | ⟨hb, hC, hv⟩
    · simp only [setDone, Prod.mk.injEq] at huv
      obtain ⟨rfl, rfl⟩ := huv
      obtain ⟨hst, -⟩ := hW
      have := hst trivial
      simp only [Prod.mk.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨h s s' ⟨s', hA, Or.inl ⟨hb, rfl⟩⟩, trivial⟩
    · simp only at hb hC hv
      subst hx hv
      obtain ⟨-, hL⟩ := hW
      obtain ⟨hL, hd'⟩ := hL (by simpa using hd)
      simp only at hL hd'
      exact ⟨h s s' ⟨w, hA, Or.inr ⟨hb, u, hC, hL⟩⟩, hd'⟩
  · simp only [not_not] at hd
    simp only [Spec.ok] at hok
    exact ⟨fun _ => hok, fun hd' => absurd hd hd'⟩

/-- Declaring the flag false and running the flagged loop is exactly `L`. -/
theorem newVarInit_flagLoop : newVarInit (fun _ => False) (flagLoop L) = L :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨_, _, h⟩ => (h not_false).1, fun h => ⟨True, fun hf => absurd hf id, fun _ => ⟨h, trivial⟩⟩⟩

/-! ### An example -/

namespace ExitLoopExample

/-- `x′ = x ↑ n ⇐ do exit when x ≥ n. x:= x+1 od`, on a state with one natural
variable `x`. -/
theorem count_up (n : ℕ) :
    ExitLoopRefines (fun x x' : ℕ => x' = max x n) ok (fun x => n ≤ x) (fun x x' => x' = x + 1) := by
  rw [ExitLoopRefines, ok_seq]
  rintro x x' (⟨hb, rfl⟩ | ⟨hb, u, rfl, hL⟩)
  · exact (max_eq_left hb).symm
  · rw [hL]
    omega

end ExitLoopExample

end Spec

end LaPToP.ProgramTheory
