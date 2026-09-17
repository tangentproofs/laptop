import LaPToP.ProgramTheory.Probabilistic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Int.Interval

/-!
# Random number generators

This module formalizes Subsection 5.7.0 (Random Number Generators) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), pp. 87–89.

"If `n: nat+1`, we use the notation `rand n` for a generator that produces
natural numbers uniformly distributed over the range `0,..n`. So `rand n` has
value `r` with probability `(r: 0,..n) / n`. Functional notation for a random
number generator is inconsistent. Since `x=x` is a law, we should be able to
simplify `rand n = rand n` to `⊤`, but we cannot because the two occurrences of
`rand n` might generate different numbers. ... To restore consistency, we
replace each use of `rand` with a fresh variable before we do anything else.
We can replace `rand n` with integer variable `r` whose value has probability
`(r: 0,..n) / n`. ... For example, in one state variable `x`,
`x:= rand 2. x:= x + rand 3 = Σr: 0,..2· Σs: 0,..3· (x:= r)/2. (x:= x + s)/3 = ...
= (x′=0)/6 + (x′=1)/3 + (x′=2)/3 + (x′=3)/6`. ... Whenever `rand` occurs in the
context of a simple equation, such as `r = rand n`, we don't need to introduce a
variable for it ... `x:= rand 2. x:= x + rand 3 = (x′: 0,..2)/2. (x′: x+(0,..3))/3
= ... as before. And `if rand 2 then A else B` can be replaced by
`if 1/2 then A else B`. ... `rand 8 < 3` has binary value `b` with distribution
`Σr: 0,..8· (b = (r<3)) / 8 = (b=⊤) × 3/8 + (b=⊥) × 5/8 = 5/8 – b/4`. ...
Exercise 351 asks: If you repeatedly throw a pair of six-sided dice, how long
does it take until the dice are equal? Using `u` and `v` for the dice and `t` for
recursive time, the program is
`u′=v′ ⇐ u:= (rand 6) + 1. v:= (rand 6) + 1. if u=v then ok else t:= t+1. u′=v′`.
Each iteration, with probability `5/6` we keep going, and with probability `1/6`
we stop. So we offer the hypothesis that (for finite `t`) the execution time has
the distribution `(t′≥t) × (5/6)^(t′–t) × 1/6`. ... which is the distribution we
hypothesized, and that completes the proof. The average value of `t′` is
`(t′≥t) × (5/6)^(t′–t) × 1/6. t = t+5`, so on average it takes `5` additional
throws of the dice (after the first) to get an equal pair."

## The model

`x:= e (rand n)` is the book's replacement by a fresh variable `r` summed over
`0,..n` (`randAssign`); `rand n` by itself is the uniform distribution `urand`.
Both computations of `x:= rand 2. x:= x + rand 3` are formalized: the
fresh-variable double sum, and the sequential composition of the two
"deceptive equations". For the dice, the book's calculation sums out the dice
`u′′, v′′` and then reads the result as a distribution of `t′` alone (the final
values of `u`, `v` are dropped). This is formalized in two layers: the dice
layer, where a throw of two dice has `36` equiprobable outcomes and the
probability of equal dice is `1/6`; and the time layer on the (finite, `ℕ`)
recursive-time variable, where the loop body is
`if 1/6 then ok else t:= t+1. H` and the hypothesis `tdist` is proved to be its
fixed point, a distribution, with average `t+5`. The blackjack Exercise 344 is
formalized in `LaPToP.ProgramTheory.Blackjack`.
-/

namespace LaPToP.ProgramTheory

namespace Probabilistic

open scoped Classical
open Finset

universe u

variable {σ : Type u}

/-! ### Deterministic steps on any state -/

/-- A deterministic step `s′ = f s` as a probabilistic specification. -/
noncomputable def pdet (f : σ → σ) : PSpec σ := fun s s' => ind (s' = f s)

/-- Substitution Law for a deterministic step. -/
theorem pdet_pseq (f : σ → σ) (P : PSpec σ) : pseq (pdet f) P = fun s s' => P (f s) s' := by
  funext s s'
  simp only [pseq, pdet, ind]
  simp

/-- `ok` on any state. -/
theorem pdet_id_eq_ofSpec_ok : pdet (id : σ → σ) = ofSpec Spec.ok := rfl

/-! ### `rand n` (aPToP p. 87) -/

/-- `rand n` "has value `r` with probability `(r: 0,..n) / n`". -/
noncomputable def urand (n : ℤ) (r : ℤ) : ℝ := ind (0 ≤ r ∧ r < n) / n

/-- `x:= e (rand n)`: "replace `rand n` with integer variable `r`", summed over `0,..n`. -/
noncomputable def randAssign (n : ℤ) (e : ℤ → ℤ → ℤ) : PSpec ℤ :=
  fun x x' => (∑ r ∈ Finset.Ico 0 n, ind (x' = e x r)) / n

/-- `urand n` is a distribution for `n: nat+1`. -/
theorem hasSum_urand {n : ℤ} (hn : 0 < n) : HasSum (urand n) 1 := by
  have h : ∀ r ∉ Finset.Ico 0 n, urand n r = 0 := fun r hr => by
    rw [Finset.mem_Ico] at hr
    simp [urand, ind, hr]
  have this : ∀ r ∈ Finset.Ico 0 n, urand n r = 1 / n := fun r hr => by
    rw [Finset.mem_Ico] at hr
    simp [urand, ind, hr]
  have hsum : ∑ r ∈ Finset.Ico 0 n, urand n r = 1 := by
    rw [Finset.sum_congr rfl this, Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn.le
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [hcast]
    field_simp
  exact hsum ▸ hasSum_sum_of_ne_finset_zero h

theorem prob_urand (n : ℤ) (hn : 0 < n) (r : ℤ) : Prob (urand n r) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold urand ind Prob
  split_ifs
  · constructor
    · positivity
    · rw [div_le_one hn']; exact h1
  · simp

/-- `x:= rand n` is "the deceptive equation replaced with `(x′: 0,..n) / n`". -/
theorem randAssign_id (n : ℤ) : randAssign n (fun _ r => r) = fun _ x' => urand n x' := by
  funext x x'
  simp only [randAssign, urand, ind]
  congr 1
  by_cases h : 0 ≤ x' ∧ x' < n
  · rw [if_pos h]
    exact (Finset.sum_eq_single_of_mem x' (Finset.mem_Ico.2 h) fun r _ hr => if_neg (Ne.symm hr)).trans (if_pos rfl)
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun r hr => if_neg fun heq => h ?_
    subst heq
    exact Finset.mem_Ico.1 hr

/-! ### `x:= rand 2. x:= x + rand 3` (aPToP p. 88) -/

theorem Ico_zero_two : Finset.Ico (0 : ℤ) 2 = {0, 1} := by ext; simp; omega
theorem Ico_zero_three : Finset.Ico (0 : ℤ) 3 = {0, 1, 2} := by ext; simp; omega

/-- The result: "`x′` is `0` with probability `1/6`, `1` with probability `1/3`, `2` with
probability `1/3`, `3` with probability `1/6`, and any other value with probability `0`". -/
noncomputable def sumDist : PSpec ℤ := fun _ x' => ind (x' = 0) / 6 + ind (x' = 1) / 3 + ind (x' = 2) / 3 + ind (x' = 3) / 6

/-- The fresh-variable form `(Σr: 0,..2· Σs: 0,..3· (x′ = r+s)) / 6`. -/
noncomputable def freshForm : PSpec ℤ := fun _ x' => (∑ r ∈ Finset.Ico 0 2, ∑ s ∈ Finset.Ico 0 3, ind (x' = r + s)) / 6

/-- `(Σr: 0,..2· Σs: 0,..3· (x′ = r+s)) / 6 = (x′=0)/6 + (x′=1)/3 + (x′=2)/3 + (x′=3)/6`. -/
theorem freshForm_eq : freshForm = sumDist := by
  funext x x'
  simp only [freshForm, sumDist, Ico_zero_two, Ico_zero_three]
  rw [Finset.sum_pair (by norm_num)]
  simp only [Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
    Finset.sum_insert (by decide : (1 : ℤ) ∉ ({2} : Finset ℤ)), Finset.sum_singleton]
  norm_num [ind]
  split_ifs <;> (try omega) <;> norm_num

/-- The two-`rand` program: `x:= rand 2. x:= x + rand 3`. -/
noncomputable def twoRand : PSpec ℤ := pseq (randAssign 2 fun _ r => r) (randAssign 3 fun x s => x + s)

theorem support_randAssign_two (x : ℤ) : (Function.support (randAssign 2 (fun _ r => r) x)).Finite := by
  apply (Set.toFinite ({0, 1} : Finset ℤ)).subset
  intro x' hx'
  rw [Function.mem_support] at hx'
  by_contra h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  exact hx' (by simp [randAssign, Ico_zero_two, ind, h.1, h.2])

/-- "`x:= rand 2. x:= x + rand 3 = (x′: 0,..2)/2. (x′: x+(0,..3))/3 = ... = (x′=0)/6 + (x′=1)/3 +
(x′=2)/3 + (x′=3)/6` as before." -/
theorem twoRand_eq : twoRand = sumDist := by
  funext x x'
  have hfin := support_randAssign_two x
  rw [twoRand, pseq_eq_sum hfin]
  have hF : hfin.toFinset ⊆ {0, 1} := by
    intro x'' hx''
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hx''
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact hx'' (by simp [randAssign, Ico_zero_two, ind, h.1, h.2])
  rw [Finset.sum_subset hF fun x'' _ hx'' => by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx''; simp [hx'']]
  rw [Finset.sum_pair (by norm_num)]
  simp only [randAssign, sumDist, Ico_zero_two, Ico_zero_three]
  simp only [Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1} : Finset ℤ)),
    Finset.sum_insert (by decide : (0 : ℤ) ∉ ({1, 2} : Finset ℤ)),
    Finset.sum_insert (by decide : (1 : ℤ) ∉ ({2} : Finset ℤ)), Finset.sum_singleton]
  norm_num [ind]
  split_ifs <;> (try omega) <;> norm_num

/-- "`if rand 2 then A else B` can be replaced by `if 1/2 then A else B`": the probability that
`rand 2` is `1` (`⊤`) is `1/2`. -/
theorem pcond_rand_two (A B : PSpec ℤ) :
    pcond (fun _ => ∑ r ∈ Finset.Ico (0 : ℤ) 2, ind (r = 1) / 2) A B = pcond (fun _ => 1 / 2) A B := by
  simp [Ico_zero_two, ind]

/-! ### `rand 8 < 3` (aPToP p. 88) -/

/-- "`rand 8 < 3` has binary value `b` with distribution `Σr: 0,..8· (b = (r<3)) / 8`". -/
noncomputable def randLt (b : Prop) : ℝ := ∑ r ∈ Finset.Ico (0 : ℤ) 8, ind (b ↔ r < 3) / 8

theorem Ico_zero_eight : Finset.Ico (0 : ℤ) 8 = {0, 1, 2, 3, 4, 5, 6, 7} := by ext; simp; omega

/-- `= (b=⊤) × 3/8 + (b=⊥) × 5/8`: "`b` is `⊤` with probability `3/8`, and `⊥` with probability `5/8`". -/
theorem randLt_eq (b : Prop) : randLt b = ind b * (3 / 8) + ind (¬ b) * (5 / 8) := by
  by_cases hb : b <;> simp [randLt, Ico_zero_eight, ind, hb, Finset.sum_insert] <;> norm_num

/-- `= 5/8 – b/4`. -/
theorem randLt_eq' (b : Prop) : randLt b = 5 / 8 - ind b / 4 := by
  rw [randLt_eq, ind_not]; ring

/-! ### Dice (Exercise 351, aPToP p. 89) -/

/-- The dice layer: `u:= (rand 6) + 1. v:= (rand 6) + 1` has `36` equiprobable outcomes in
`1,..7 × 1,..7`; the probability that `u=v` is `1/6`. -/
theorem prob_dice_eq :
    (∑ p ∈ Finset.Ico (1 : ℤ) 7 ×ˢ Finset.Ico (1 : ℤ) 7, ind (p.1 = p.2)) / 36 = 1 / 6 := by
  have : Finset.Ico (1 : ℤ) 7 = {1, 2, 3, 4, 5, 6} := by ext; simp; omega
  rw [this]
  simp [ind, Finset.sum_product, Finset.sum_insert]
  norm_num

/-- ... and the probability that `u⧧v` is `5/6`. -/
theorem prob_dice_ne :
    (∑ p ∈ Finset.Ico (1 : ℤ) 7 ×ˢ Finset.Ico (1 : ℤ) 7, ind (p.1 ≠ p.2)) / 36 = 5 / 6 := by
  have : Finset.Ico (1 : ℤ) 7 = {1, 2, 3, 4, 5, 6} := by ext; simp; omega
  rw [this]
  simp [ind, Finset.sum_product, Finset.sum_insert]
  norm_num

/-- The time layer: the loop body with the dice summed out,
`if 1/6 then ok else t:= t+1. H`, on the recursive-time variable `t`. -/
noncomputable def diceBody (H : PSpec ℕ) : PSpec ℕ := pcond (fun _ => 1 / 6) (pdet id) (pseq (pdet (· + 1)) H)

/-- The hypothesis: "(for finite `t`) the execution time has the distribution
`(t′≥t) × (5/6)^(t′–t) × 1/6`". -/
noncomputable def tdist : PSpec ℕ := fun t t' => ind (t ≤ t') * (5 / 6 : ℝ) ^ (t' - t) / 6

/-- The book's last three lines: `(t′=t)/6 + (t′≥t+1) × (5/6)^(t′–t) / 6 = (t′≥t) × (5/6)^(t′–t) × 1/6`,
i.e. `tdist` is a fixed point of the loop body — "which is the distribution we hypothesized, and
that completes the proof". -/
theorem diceBody_tdist : diceBody tdist = tdist := by
  funext t t'
  simp only [diceBody, pcond, pdet_pseq, pdet, tdist, id, ind]
  rcases lt_trichotomy t' t with h | rfl | h
  · have h1 : ¬ t ≤ t' := by omega
    have h2 : ¬ t + 1 ≤ t' := by omega
    have h3 : t' ≠ t := by omega
    simp [h1, h2, h3]
  · simp
  · have h1 : t ≤ t' := h.le
    have h2 : t + 1 ≤ t' := h
    have h3 : t' ≠ t := by omega
    have h4 : t' - t = (t' - (t + 1)) + 1 := by omega
    simp only [h1, h2, h3, if_true, if_false]
    rw [h4, pow_succ]
    ring

/-- The shifted terms of `tdist t`: `tdist t (n + t) = (5/6)^n / 6`. -/
theorem tdist_add (t n : ℕ) : tdist t (n + t) = (5 / 6 : ℝ) ^ n / 6 := by
  simp [tdist, ind]

/-- `tdist` is a distribution of `t′`. -/
theorem isDistribution_tdist : IsDistribution tdist := fun t => by
  refine ⟨fun t' => ?_, ?_⟩
  · unfold tdist ind Prob
    split_ifs
    · constructor
      · positivity
      · have : (5 / 6 : ℝ) ^ (t' - t) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    · simp
  · have hg : HasSum (fun n : ℕ => (5 / 6 : ℝ) ^ n / 6) 1 := by
      have key := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num)).mul_left (1 / 6)
      have e : (fun i : ℕ => 1 / 6 * (5 / 6 : ℝ) ^ i) = fun n => (5 / 6 : ℝ) ^ n / 6 := by funext n; ring
      rw [e, show (1 / 6 * (1 - 5 / 6)⁻¹ : ℝ) = 1 by norm_num] at key
      exact key
    rw [← hasSum_nat_add_iff' t]
    have e : (fun n => tdist t (n + t)) = fun n => (5 / 6 : ℝ) ^ n / 6 := funext (tdist_add t)
    have z : ∑ i ∈ Finset.range t, tdist t i = 0 := Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      simp [tdist, ind]; omega
    rw [e, z, sub_zero]
    exact hg

/-- "The average value of `t′` is `(t′≥t) × (5/6)^(t′–t) × 1/6. t = t+5`, so on average it
takes `5` additional throws of the dice (after the first) to get an equal pair." -/
theorem avg_tdist (t : ℕ) : avg tdist (fun t' => (t' : ℝ)) t = t + 5 := by
  have h1 : HasSum (fun n : ℕ => (n : ℝ) * (5 / 6) ^ n) 30 := by
    have key := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 5 / 6) (by rw [Real.norm_eq_abs]; norm_num)
    rw [show (5 / 6 / (1 - 5 / 6) ^ 2 : ℝ) = 30 by norm_num] at key
    exact key
  have h2 : HasSum (fun n : ℕ => (5 / 6 : ℝ) ^ n) 6 := by
    have key := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num)
    rw [show ((1 - 5 / 6)⁻¹ : ℝ) = 6 by norm_num] at key
    exact key
  have h3 : HasSum (fun n : ℕ => (5 / 6 : ℝ) ^ n / 6 * ((n : ℝ) + t)) (t + 5) := by
    have key := (h1.mul_left (1 / 6)).add (h2.mul_left ((t : ℝ) / 6))
    have e : (fun n : ℕ => 1 / 6 * ((n : ℝ) * (5 / 6) ^ n) + (t : ℝ) / 6 * (5 / 6) ^ n) =
        fun n : ℕ => (5 / 6 : ℝ) ^ n / 6 * ((n : ℝ) + t) := by funext n; ring
    rw [e, show (1 / 6 * 30 + (t : ℝ) / 6 * 6 : ℝ) = t + 5 by ring] at key
    exact key
  have h4 : HasSum (fun t' : ℕ => tdist t t' * (t' : ℝ)) (t + 5) := by
    rw [← hasSum_nat_add_iff' t]
    have e : (fun n => tdist t (n + t) * ((n + t : ℕ) : ℝ)) = fun n : ℕ => (5 / 6 : ℝ) ^ n / 6 * ((n : ℝ) + t) := by
      funext n; rw [tdist_add]; push_cast; ring
    have z : ∑ i ∈ Finset.range t, tdist t i * (i : ℝ) = 0 := Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      simp [tdist, ind]; omega
    rw [e, z, sub_zero]
    exact h3
  exact h4.tsum_eq

end Probabilistic

end LaPToP.ProgramTheory
