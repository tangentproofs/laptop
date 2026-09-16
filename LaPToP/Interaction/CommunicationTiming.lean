import LaPToP.Interaction.Communication
import LaPToP.RecursiveDefinition.Nat

/-!
# Communication timing and recursive communication

This module formalizes Subsections 9.1.2 (Communication Timing) and 9.1.3
(Recursive Communication) of Eric Hehner's *A Practical Theory of
Programming* (aPToP).

"To be independent of these implementation details, we can use the transit
time measure, in which we suppose that the acts of input and output take no
time, and that communication transit takes 1 time unit. The message to be
read next on channel `c` is `Mc rc`. This message was or is or will be sent at
time `Tc rc`. Its arrival time, according to the transit time measure, is
`Tc rc + 1`. So input becomes `t:= t↑(Tc rc + 1). c?` ... And the input check
`√c` becomes `√c = Tc rc + 1 ≤ t`." Exercise 516(a): "Let `W` be “wait for input
on channel `c` and then read it”. Formally, `W = t:= t↑(T r + 1). c?`. Prove
`W ⇐ if √c then c? else t:= t+1. W` where time is an extended natural."

"Define `dbl` by the fixed-point construction (including recursive time but
ignoring input waits) `dbl = c?. d! 2×c. t:= t+1. dbl`. Regarding `dbl` as the
unknown, this equation has several solutions. The weakest is
`∀n: nat· Md wd+n = 2 × Mc rc+n ∧ Td wd+n = t+n`. ... The strongest solution is
`⊥`. ... we can say this: it refines the weakest solution ... and it is refined
by the right side of the fixed-point construction. ... If we begin recursive
construction with `dbl0 = ⊤` we find `dbl1 = Md wd = 2 × Mc rc ∧ Td wd = t`,
`dbl2 = Md wd = 2 × Mc rc ∧ Td wd = t ∧ Md wd+1 = 2 × Mc rc+1 ∧ Td wd+1 = t+1`
and so on. The result of the construction `dbl∞ = ∀n: nat· Md wd+n = 2 × Mc rc+n
∧ Td wd+n = t+n` is the weakest solution of the `dbl` fixed-point construction."

## The model

Transit-time input and the check are defined on the one-channel state of
`LaPToP.Interaction.Communication`, and Exercise 516(a) is proved by the two
cases of the book's calculation. For `dbl`, on the two-channel state: the
weakest solution is shown to be a fixed point of the construction, to be
refined by every fixed point (so "it refines the weakest solution" holds for
every solution `dbl`, and in particular the recursive program may be used to
solve problems), `⊥` is a fixed point, and the construction sequence
`dbl0 = ⊤`, `dbl(n+1) = c?. d! 2×c. t:= t+1. dbln` is computed in closed form
with `dbl∞` its intersection. The book's "strongest implementable solution"
has `rc′ = wd′ = t′ = ∞`; cursors are naturals in this development, so that
solution is not stated.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec LaPToP.RecursiveDefinition

universe u

/-! ### Communication timing (aPToP §9.1.2) -/

namespace Channel

variable {α : Type u}

/-- `t:= e`. -/
def assignT (e : CS → ℕ∞) : Spec CS := fun s s' => s' = { s with t := e s }

/-- `t:= t+1`. -/
def tick : Spec CS := assignT fun s => s.t + 1

theorem assignT_seq (e : CS → ℕ∞) (P : Spec CS) : seq (assignT e) P = fun s s' => P { s with t := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Input in the transit time measure: `t:= t↑(T r + 1). c?` — "if the input has
already arrived, `T r + 1 ≤ t`, and no time is spent waiting for input;
otherwise execution of `c?` is delayed until the input arrives". This is also
Exercise 516(a)'s `W`, "wait for input on channel `c` and then read it". -/
def inputT (sc : Scripts α) : Spec CS := seq (assignT fun s => max s.t (sc.T s.r + 1)) input

/-- `√c = T r + 1 ≤ t` in the transit time measure. -/
def checkT (sc : Scripts α) (s : CS) : Prop := sc.T s.r + 1 ≤ s.t

theorem inputT_eq (sc : Scripts α) :
    inputT sc = fun s s' => s' = { s with t := max s.t (sc.T s.r + 1), r := s.r + 1 } := by
  rw [inputT, assignT_seq]
  rfl

/-- Exercise 516(a): `W ⇐ if √c then c? else t:= t+1. W`. "If `T r + 1 ≤ t`, then
`t = t↑(T r + 1)`. If `T r + 1 > t` then `(t+1)↑(T r + 1) = T r + 1 = t↑(T r + 1)`." -/
theorem inputT_refines (sc : Scripts α) : Refines (inputT sc) (cond (checkT sc) input (seq tick (inputT sc))) := by
  rw [inputT_eq]
  rintro s s' (⟨hc, rfl⟩ | ⟨hc, h⟩)
  · simp only [checkT] at hc
    show ({ s with r := s.r + 1 } : CS) = { s with t := max s.t (sc.T s.r + 1), r := s.r + 1 }
    rw [max_eq_left hc]
  · rw [tick, assignT_seq] at h
    simp only [checkT, not_le] at hc h
    rw [h, max_eq_right (Order.add_one_le_of_lt hc), max_eq_right (le_of_lt hc)]

end Channel

/-! ### Recursive communication (aPToP §9.1.3) -/

namespace TwoChannels

/-- `t:= t+1` on the two-channel state. -/
def tick : Spec CS2 := fun s s' => s' = { s with t := s.t + 1 }

theorem tick_seq (P : Spec CS2) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (c d : Scripts ℤ)

/-- The right side of the fixed-point construction `dbl = c?. d! 2×c. t:= t+1. dbl`,
as a function of the unknown `dbl`. -/
def dblBody (D : Spec CS2) : Spec CS2 :=
  seq inputC (seq (outputD (fun s c => 2 * lastReadC c s) c d) (seq tick D))

/-- The weakest solution, `dbl∞ = ∀n: nat· Md wd+n = 2 × Mc rc+n ∧ Td wd+n = t+n`. -/
def dblW : Spec CS2 := fun s _ => ∀ n : ℕ, d.M (s.wd + n) = 2 * c.M (s.rc + n) ∧ d.T (s.wd + n) = s.t + n

/-- The construction sequence: `dbl0 = ⊤`, `dbl(n+1) = c?. d! 2×c. t:= t+1. dbln`. -/
def dblSeq : ℕ → Spec CS2
  | 0 => top
  | n + 1 => dblBody c d (dblSeq n)

/-- One unrolling of the construction, in closed form. -/
theorem dblBody_apply (D : Spec CS2) (s s' : CS2) :
    dblBody c d D s s' ↔
      d.M s.wd = 2 * c.M s.rc ∧ d.T s.wd = s.t ∧ D { s with t := s.t + 1, rc := s.rc + 1, wd := s.wd + 1 } s' := by
  simp only [dblBody, inputC_seq, outputD_seq, tick_seq, lastReadC, Nat.add_sub_cancel]

/-- `dbl∞` is a solution: `dbl∞ = c?. d! 2×c. t:= t+1. dbl∞`. -/
theorem dblW_fixedPoint : IsFixedPoint (dblBody c d) (dblW c d) := by
  refine Spec.ext fun s s' => ?_
  rw [dblBody_apply]
  simp only [dblW]
  constructor
  · rintro ⟨hM, hT, h⟩ n
    cases n with
    | zero => simpa using ⟨hM, hT⟩
    | succ n =>
      obtain ⟨h1, h2⟩ := h n
      rw [show s.wd + (n + 1) = s.wd + 1 + n by omega, show s.rc + (n + 1) = s.rc + 1 + n by omega, h1, h2]
      refine ⟨rfl, ?_⟩
      push_cast
      ring
  · intro h
    obtain ⟨h0M, h0T⟩ := h 0
    simp only [Nat.cast_zero, add_zero] at h0M h0T
    refine ⟨h0M, h0T, fun n => ?_⟩
    obtain ⟨h1, h2⟩ := h (n + 1)
    show d.M (s.wd + 1 + n) = 2 * c.M (s.rc + 1 + n) ∧ d.T (s.wd + 1 + n) = s.t + 1 + n
    rw [show s.wd + 1 + n = s.wd + (n + 1) by omega, show s.rc + 1 + n = s.rc + (n + 1) by omega, h1, h2]
    refine ⟨rfl, ?_⟩
    push_cast
    ring

/-- Every solution refines the weakest one: `dbl∞ ⇐ dbl` for any fixed point `dbl`. -/
theorem fixedPoint_refines_dblW {D : Spec CS2} (hD : IsFixedPoint (dblBody c d) D) : Refines (dblW c d) D := by
  intro s s' h n
  induction n generalizing s with
  | zero =>
    rw [← hD, dblBody_apply] at h
    obtain ⟨hM, hT, -⟩ := h
    simpa using ⟨hM, hT⟩
  | succ n ih =>
    rw [← hD, dblBody_apply] at h
    obtain ⟨-, -, h⟩ := h
    obtain ⟨h1, h2⟩ := ih _ h
    rw [show s.wd + (n + 1) = s.wd + 1 + n by omega, show s.rc + (n + 1) = s.rc + 1 + n by omega, h1, h2]
    refine ⟨rfl, ?_⟩
    push_cast
    ring

/-- "The strongest solution is `⊥`." -/
theorem bot_fixedPoint : IsFixedPoint (dblBody c d) bot :=
  Spec.ext fun s s' => by
    rw [dblBody_apply]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => h.elim⟩

/-- The construction sequence in closed form: `dbln = ∀k: 0,..n· Md wd+k = 2 × Mc rc+k ∧
Td wd+k = t+k`, so `dbl1 = Md wd = 2 × Mc rc ∧ Td wd = t` and
`dbl2 = dbl1 ∧ Md wd+1 = 2 × Mc rc+1 ∧ Td wd+1 = t+1`. -/
theorem dblSeq_eq (n : ℕ) :
    dblSeq c d n = fun s _ => ∀ k, k < n → d.M (s.wd + k) = 2 * c.M (s.rc + k) ∧ d.T (s.wd + k) = s.t + k := by
  induction n with
  | zero =>
    refine Spec.ext fun s s' => ?_
    simp [dblSeq, top]
  | succ n ih =>
    refine Spec.ext fun s s' => ?_
    rw [dblSeq, dblBody_apply, ih]
    simp only
    constructor
    · rintro ⟨hM, hT, h⟩ k hk
      cases k with
      | zero => simpa using ⟨hM, hT⟩
      | succ k =>
        obtain ⟨h1, h2⟩ := h k (by omega)
        rw [show s.wd + (k + 1) = s.wd + 1 + k by omega, show s.rc + (k + 1) = s.rc + 1 + k by omega, h1, h2]
        refine ⟨rfl, ?_⟩
        push_cast
        ring
    · intro h
      obtain ⟨h0M, h0T⟩ := h 0 (by omega)
      simp only [Nat.cast_zero, add_zero] at h0M h0T
      refine ⟨h0M, h0T, fun k hk => ?_⟩
      obtain ⟨h1, h2⟩ := h (k + 1) (by omega)
      show d.M (s.wd + 1 + k) = 2 * c.M (s.rc + 1 + k) ∧ d.T (s.wd + 1 + k) = s.t + 1 + k
      rw [show s.wd + 1 + k = s.wd + (k + 1) by omega, show s.rc + 1 + k = s.rc + (k + 1) by omega, h1, h2]
      refine ⟨rfl, ?_⟩
      push_cast
      ring

/-- "The result of the construction `dbl∞`" is the intersection of the sequence. -/
theorem dblW_iff_forall (s s' : CS2) : dblW c d s s' ↔ ∀ n, dblSeq c d n s s' := by
  simp only [dblSeq_eq, dblW]
  exact ⟨fun h n k _ => h k, fun h k => h (k + 1) k (Nat.lt_succ_self k)⟩

end TwoChannels

end LaPToP.Interaction
