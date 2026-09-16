import LaPToP.Interaction.Merge
import Mathlib.Data.List.Range

/-!
# Merge: what the implementation satisfies

This module makes precise, and proves, what is true of the book's `timemerge`
implementation (aPToP §9.1.4, Exercise 521(a)):

    timemerge ⇐ if √c then c?. e! c else ok. if √d then d?. e! d else ok. t:= t+1. timemerge

which the book asserts "using the same reasoning" as for Exercise 516(a) and
without proof. `LaPToP.Interaction.Merge` shows the step-wise refinement
fails (an iteration may read two inputs). Here the merge requirement itself
— "the output must be all and only the messages read from the inputs, and it
must preserve the order in which they were read on each channel" — is
formalized as an invariant `Inv`: over any run, the messages output on `e`
form an *interleaving* of the messages read from `c` and from `d`, and the
cursors do not decrease. `Inv` is preserved by a `merge` step, by a
`timemerge` step and by an iteration of the implementation, hence holds of
any number of iterations of each (`stepsInv_*`). Also proved: the
implementation outputs a message only after it has arrived (the transit-time
check), `implBody_c_arrived`, `implBody_d_arrived`.

What remains unproved is the book's literal fixed-point refinement with the
first-available criterion; the node records this.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

/-- The segment `f i; f (i+1); …; f (j–1)` of an infinite string. -/
def seg (f : ℕ → ℤ) (i j : ℕ) : List ℤ := (List.range (j - i)).map fun k => f (i + k)

theorem seg_self (f : ℕ → ℤ) (i : ℕ) : seg f i i = [] := by simp [seg]

theorem seg_cons (f : ℕ → ℤ) {i j : ℕ} (h : i < j) : seg f i j = f i :: seg f (i + 1) j := by
  unfold seg
  rw [show j - i = (j - (i + 1)) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp]
  congr 1
  omega

/-- `Interleave xs ys zs`: `zs` is an interleaving of `xs` and `ys`, each in order —
"all and only the messages read from the inputs, ... the order in which they
were read on each channel". -/
inductive Interleave : List ℤ → List ℤ → List ℤ → Prop where
  /-- Nothing read, nothing output. -/
  | nil : Interleave [] [] []
  /-- The next output is the next message of the first input. -/
  | left {x : ℤ} {xs ys zs : List ℤ} : Interleave xs ys zs → Interleave (x :: xs) ys (x :: zs)
  /-- The next output is the next message of the second input. -/
  | right {y : ℤ} {xs ys zs : List ℤ} : Interleave xs ys zs → Interleave xs (y :: ys) (y :: zs)

namespace Merge

variable (c d e : Scripts ℤ)

/-- The invariant of a run from `s` to `s′`: cursors do not decrease, and the outputs
`e (we;..we′)` interleave the inputs `c (rc;..rc′)` and `d (rd;..rd′)`. -/
def Inv (s s' : MS) : Prop :=
  s.rc ≤ s'.rc ∧ s.rd ≤ s'.rd ∧ s.we ≤ s'.we ∧
    Interleave (seg c.M s.rc s'.rc) (seg d.M s.rd s'.rd) (seg e.M s.we s'.we)

theorem Inv.refl (s : MS) : Inv c d e s s := ⟨le_rfl, le_rfl, le_rfl, by simp only [seg_self]; exact Interleave.nil⟩

/-- An atomic `c?. e! c`: `c` read, the message output. -/
def ReadC (s u : MS) : Prop := u.rc = s.rc + 1 ∧ u.rd = s.rd ∧ u.we = s.we + 1 ∧ e.M s.we = c.M s.rc

/-- An atomic `d?. e! d`. -/
def ReadD (s u : MS) : Prop := u.rd = s.rd + 1 ∧ u.rc = s.rc ∧ u.we = s.we + 1 ∧ e.M s.we = d.M s.rd

/-- A transition not touching the cursors (`ok`, a wait, `t:= t+1`). -/
def Idle (s u : MS) : Prop := u.rc = s.rc ∧ u.rd = s.rd ∧ u.we = s.we

theorem Inv.readC {s u s' : MS} (h : ReadC c e s u) (hu : Inv c d e u s') : Inv c d e s s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a1, a2, a3, hI⟩ := hu
  rw [h1] at a1 hI
  rw [h2] at a2 hI
  rw [h3] at a3 hI
  refine ⟨by omega, a2, by omega, ?_⟩
  rw [seg_cons c.M (by omega), seg_cons e.M (by omega), h4]
  exact Interleave.left hI

theorem Inv.readD {s u s' : MS} (h : ReadD d e s u) (hu : Inv c d e u s') : Inv c d e s s' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨a1, a2, a3, hI⟩ := hu
  rw [h1] at a2 hI
  rw [h2] at a1 hI
  rw [h3] at a3 hI
  refine ⟨a1, by omega, by omega, ?_⟩
  rw [seg_cons d.M (by omega), seg_cons e.M (by omega), h4]
  exact Interleave.right hI

theorem Inv.idle {s u s' : MS} (h : Idle s u) (hu : Inv c d e u s') : Inv c d e s s' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨a1, a2, a3, hI⟩ := hu
  rw [h1] at a1 hI
  rw [h2] at a2 hI
  rw [h3] at a3 hI
  exact ⟨a1, a2, a3, hI⟩

/-- The atomic transitions of the bodies. -/
theorem readC_of_seq {s u : MS} (h : seq inputC (outputE e (lastC c)) s u) : ReadC c e s u := by
  obtain ⟨_, rfl, ⟨hM, -⟩, rfl⟩ := h
  simp only [lastC, Nat.add_sub_cancel] at hM
  exact ⟨rfl, rfl, rfl, hM⟩

theorem readD_of_seq {s u : MS} (h : seq inputD (outputE e (lastD d)) s u) : ReadD d e s u := by
  obtain ⟨_, rfl, ⟨hM, -⟩, rfl⟩ := h
  simp only [lastD, Nat.add_sub_cancel] at hM
  exact ⟨rfl, rfl, rfl, hM⟩

theorem readC_of_wait {s u : MS} (h : seq (waitC c) (seq inputC (outputE e (lastC c))) s u) : ReadC c e s u := by
  obtain ⟨_, rfl, _, rfl, ⟨hM, -⟩, rfl⟩ := h
  simp only [lastC, Nat.add_sub_cancel] at hM
  exact ⟨rfl, rfl, rfl, hM⟩

theorem readD_of_wait {s u : MS} (h : seq (waitD d) (seq inputD (outputE e (lastD d))) s u) : ReadD d e s u := by
  obtain ⟨_, rfl, _, rfl, ⟨hM, -⟩, rfl⟩ := h
  simp only [lastD, Nat.add_sub_cancel] at hM
  exact ⟨rfl, rfl, rfl, hM⟩

theorem idle_of_ok {s u : MS} (h : ok s u) : Idle s u := by
  rw [Spec.ok] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

theorem idle_of_tick {s u : MS} (h : tick s u) : Idle s u := by
  rw [tick, stepF] at h
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-- A `merge` step preserves the invariant. -/
theorem mergeBody_inv {M : Spec MS} (hM : ∀ u s', M u s' → Inv c d e u s') {s s' : MS}
    (h : mergeBody c d e M s s') : Inv c d e s s' := by
  obtain ⟨u, hu, hM'⟩ := h
  rcases hu with hu | hu
  · exact Inv.readC c d e (readC_of_seq c e hu) (hM u s' hM')
  · exact Inv.readD c d e (readD_of_seq d e hu) (hM u s' hM')

/-- A `timemerge` step preserves the invariant. -/
theorem timemergeBody_inv {M : Spec MS} (hM : ∀ u s', M u s' → Inv c d e u s') {s s' : MS}
    (h : timemergeBody c d e M s s') : Inv c d e s s' := by
  obtain ⟨u, hu, w, hw, hM'⟩ := h
  have hw' := Inv.idle c d e (idle_of_tick hw) (hM w s' hM')
  rcases hu with ⟨-, hu⟩ | ⟨-, hu⟩
  · exact Inv.readC c d e (readC_of_wait c e hu) hw'
  · exact Inv.readD c d e (readD_of_wait d e hu) hw'

/-- An iteration of the implementation preserves the invariant: it reads zero, one
or two messages and outputs exactly those, in order. -/
theorem implBody_inv {M : Spec MS} (hM : ∀ u s', M u s' → Inv c d e u s') {s s' : MS}
    (h : implBody c d e M s s') : Inv c d e s s' := by
  obtain ⟨u, hu, v, hv, w, hw, hM'⟩ := h
  have hw' := Inv.idle c d e (idle_of_tick hw) (hM w s' hM')
  have hv' : Inv c d e u s' := by
    rcases hv with ⟨-, hv⟩ | ⟨-, hv⟩
    · exact Inv.readD c d e (readD_of_seq d e hv) hw'
    · exact Inv.idle c d e (idle_of_ok hv) hw'
  rcases hu with ⟨-, hu⟩ | ⟨-, hu⟩
  · exact Inv.readC c d e (readC_of_seq c e hu) hv'
  · exact Inv.idle c d e (idle_of_ok hu) hv'

/-- `n` iterations of a body, ending with `ok`. -/
def steps (B : Spec MS → Spec MS) : ℕ → Spec MS
  | 0 => ok
  | n + 1 => B (steps B n)

theorem stepsInv {B : Spec MS → Spec MS}
    (hB : ∀ M : Spec MS, (∀ u s', M u s' → Inv c d e u s') → ∀ s s', B M s s' → Inv c d e s s') (n : ℕ) :
    ∀ s s', steps B n s s' → Inv c d e s s' := by
  induction n with
  | zero => intro s s' h; rw [steps, Spec.ok] at h; subst h; exact Inv.refl c d e _
  | succ n ih => intro s s' h; exact hB _ ih s s' h

/-- Any number of `merge` steps outputs an interleaving of the messages read. -/
theorem stepsInv_merge (n : ℕ) (s s' : MS) (h : steps (mergeBody c d e) n s s') : Inv c d e s s' :=
  stepsInv c d e (fun _ hM _ _ h => mergeBody_inv c d e hM h) n s s' h

/-- Any number of `timemerge` steps outputs an interleaving of the messages read. -/
theorem stepsInv_timemerge (n : ℕ) (s s' : MS) (h : steps (timemergeBody c d e) n s s') : Inv c d e s s' :=
  stepsInv c d e (fun _ hM _ _ h => timemergeBody_inv c d e hM h) n s s' h

/-- Any number of iterations of the book's implementation outputs an interleaving of
the messages read: the implementation meets the merge requirement. -/
theorem stepsInv_impl (n : ℕ) (s s' : MS) (h : steps (implBody c d e) n s s') : Inv c d e s s' :=
  stepsInv c d e (fun _ hM _ _ h => implBody_inv c d e hM h) n s s' h

/-- The implementation outputs a message from `c` only after it has arrived: the
output time is at least `Tc rc + 1`. -/
theorem implBody_c_arrived {M : Spec MS} {s s' : MS} (h : implBody c d e M s s') (hc : checkC c s) :
    c.T s.rc + 1 ≤ e.T s.we := by
  obtain ⟨u, hu, -⟩ := h
  rcases hu with ⟨-, _, rfl, ⟨-, hT⟩, -⟩ | ⟨hc', -⟩
  · simp only at hT
    rw [hT]
    exact hc
  · exact absurd hc hc'

/-- Likewise for `d` (the output index depends on whether `c` was read first). -/
theorem implBody_d_arrived {M : Spec MS} {s s' : MS} (h : implBody c d e M s s') (hd : checkD d s) :
    (checkC c s → d.T s.rd + 1 ≤ e.T (s.we + 1)) ∧ (¬ checkC c s → d.T s.rd + 1 ≤ e.T s.we) := by
  obtain ⟨u, hu, v, hv, -⟩ := h
  rcases hu with ⟨hc, _, rfl, ⟨-, -⟩, rfl⟩ | ⟨hc, rfl⟩
  · refine ⟨fun _ => ?_, fun hc' => absurd hc hc'⟩
    rcases hv with ⟨-, _, rfl, ⟨-, hT⟩, -⟩ | ⟨hd', -⟩
    · simp only at hT
      rw [hT]
      exact hd
    · exact absurd hd hd'
  · refine ⟨fun hc' => absurd hc' hc, fun _ => ?_⟩
    rcases hv with ⟨-, _, rfl, ⟨-, hT⟩, -⟩ | ⟨hd', -⟩
    · simp only at hT
      rw [hT]
      exact hd
    · exact absurd hd hd'

end Merge

end LaPToP.Interaction
