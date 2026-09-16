import LaPToP.Interaction.InteractiveVariables

/-!
# Space as an interactive variable

This module formalizes Subsection 9.0.1 (Space) of Eric Hehner's *A
Practical Theory of Programming* (aPToP), Exercise 497.

"We make the space variable `s` into an interactive variable in order to look
at the space occupied during the course of a computation. ... Suppose `alloc`
allocates 1 unit of memory space and takes time 1 to do so. Then the
following computation slowly allocates memory.
`GrowSlow ⇐ if t=2×x then alloc || x:= t else t:= t+1. GrowSlow`. If the
time is equal to `2×x`, then one space is allocated, and concurrently `x`
becomes the time stamp of the allocation; otherwise the clock ticks. The
process is repeated forever. Prove that if the space is initially less than
the logarithm of the time, and `x` is suitably initialized, then at all times
the space is less than the logarithm of the time. It is not clear what
initialization is suitable for `x`, so leaving that aside for a moment, we
define `GrowSlow` to be the desired specification.
`GrowSlow = s < log t ⇒ (∀t″· t″ ≥ t ⇒ s″ < log t″)` where `s` is an interactive
variable, so `s` is really `s t` and `s″` is really `s t″`. ... we can take
`alloc` to be `s:= s+1`. There is no need for `x` to be interactive, so let's
make it a boundary variable. ... The body of the loop can be written as a
disjunction. `if t=2×x then s:= s+1 || x:= t else t:= t+1 = t=2×x ∧ s′=s+1 ∧ x′=t
∧ t′=t+1 ∨ t⧧2×x ∧ s′=s ∧ x′=x ∧ t′=t+1`. ... The next step should be discharge.
We need `s < log t ∧ t=2×x ⇒ s+1 < log(t+1) = 2^s < t = 2×x ⇒ 2^(s+1) < t+1 = … =
2^s < t = 2×x ⇒ 2^s ≤ x`. This is the missing initialization of `x`. So we go
back and redefine `GrowSlow`. `GrowSlow = s < log t ∧ x≥2^s ⇒ (∀t″· t″ ≥ t ⇒ s″ <
log t″)`. Now we redo the proof."

## The model

Time is a natural number here (the book uses extended naturals "to make the
proof easier"; at `t = ∞` the statements degenerate). `x` is a boundary
variable and `s` an interactive variable, a function of time, as in
`LaPToP.Interaction.InteractiveVariables`; a specification is a function of
`s`. `s < log t` is rendered as `2^s < t`, the book's own rewriting in the
discharge step (no other use of `log` is needed). The loop body is the
book's disjunction, with `s′ = s+1` read as `s (t+1) = s t + 1` ("remove
sequential composition, remembering that `s` is interactive"), and the
recursive call is the specification (Section 6.1). Proved: the discharge
calculation and its consequence — with the antecedent `s < log t ∧ t = 2×x`,
`s+1 < log(t+1)` is equivalent to `x ≥ 2^s`, "the missing initialization";
the first specification is *not* refined by its body (a counterexample);
the redefined `GrowSlow` is, by the book's two cases.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace Exercise497

/-- A specification in the time `t`, the boundary variable `x` and the interactive
space variable `s`. -/
abbrev GSpec := (ℕ → ℕ) → Spec (ℕ × ℕ)

/-- The first attempt: `GrowSlow = s < log t ⇒ (∀t″· t″ ≥ t ⇒ s″ < log t″)`. -/
def GrowSlow₀ : GSpec := fun s st _ => 2 ^ s st.1 < st.1 → ∀ t'', st.1 ≤ t'' → 2 ^ s t'' < t''

/-- The redefined specification, `GrowSlow = s < log t ∧ x≥2^s ⇒ (∀t″· t″ ≥ t ⇒ s″ < log t″)`. -/
def GrowSlow : GSpec := fun s st _ =>
  2 ^ s st.1 < st.1 ∧ 2 ^ s st.1 ≤ st.2 → ∀ t'', st.1 ≤ t'' → 2 ^ s t'' < t''

/-- The loop body as the book's disjunction: `t=2×x ∧ s′=s+1 ∧ x′=t ∧ t′=t+1 ∨ t⧧2×x ∧ s′=s
∧ x′=x ∧ t′=t+1`, with `s′` the value of the interactive `s` at time `t+1`. -/
def step (s : ℕ → ℕ) : Spec (ℕ × ℕ) := fun st u =>
  (st.1 = 2 * st.2 ∧ s (st.1 + 1) = s st.1 + 1 ∧ u = (st.1 + 1, st.1)) ∨
  (st.1 ≠ 2 * st.2 ∧ s (st.1 + 1) = s st.1 ∧ u = (st.1 + 1, st.2))

/-- `if t=2×x then s:= s+1 || x:= t else t:= t+1. G`, with the recursive call `G` as a specification. -/
def body (G : GSpec) : GSpec := fun s => seq (step s) (G s)

/-- The discharge calculation: under `s < log t ∧ t=2×x`, `s+1 < log(t+1)` is exactly
`x ≥ 2^s` — "this is the missing initialization of `x`". -/
theorem discharge_iff (s t x : ℕ) (_h1 : 2 ^ s < t) (h2 : t = 2 * x) : 2 ^ (s + 1) < t + 1 ↔ 2 ^ s ≤ x := by
  rw [pow_succ]
  omega

/-- The first specification is not refined by its body: from `t = 6`, `x = 3`, `s t = 2`
(`s < log t`, but `x < 2^s`) the allocation step reaches `t = 7`, `s = 3`, where the
recursive call's antecedent `2^3 < 7` fails, so the body allows `s″ ≥ log t″`. -/
theorem growSlow₀_not_refines : ∃ s : ℕ → ℕ, ¬ Refines (GrowSlow₀ s) (body GrowSlow₀ s) := by
  refine ⟨fun t => if t = 6 then 2 else 3, fun h => ?_⟩
  have := h (6, 3) (7, 6) ⟨(7, 6), Or.inl ⟨rfl, by simp, rfl⟩, fun hant => absurd hant (by simp)⟩ (by simp) 7 (by omega)
  simp at this

/-- `GrowSlow ⇐ if t=2×x then s:= s+1 || x:= t else t:= t+1. GrowSlow`, by the book's two
cases: "discharge, as calculated earlier ... when `t″=t`, then `s″=s` and since
`s < log t`, the domain of `t″` can be increased". -/
theorem growSlow_refines (s : ℕ → ℕ) : Refines (GrowSlow s) (body GrowSlow s) := by
  rintro ⟨t, x⟩ st' ⟨u, hu, hG⟩ ⟨hlog, hx⟩ t'' ht''
  simp only at hlog hx ht''
  rcases Nat.eq_or_lt_of_le ht'' with rfl | hlt
  · exact hlog
  rcases hu with ⟨htx, hs, rfl⟩ | ⟨htx, hs, rfl⟩ <;> simp only at htx hs
  · -- first case: `t=2×x`, one space allocated
    refine hG ⟨?_, ?_⟩ t'' hlt <;> simp only <;> rw [hs, pow_succ] <;> omega
  · -- second case: the clock ticks
    refine hG ⟨?_, ?_⟩ t'' hlt <;> simp only <;> rw [hs]
    · omega
    · exact hx

end Exercise497

end LaPToP.Interaction
