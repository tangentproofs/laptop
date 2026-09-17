import LaPToP.ProgramTheory.RandomNumbers
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Information

This module formalizes Subsection 5.7.1 (Information) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), p. 90.

"There is a close connection between information and probability. If a binary
expression has probability `p` of being true, and you evaluate it, and it turns
out to be true, then the amount of information in bits that you have just
learned is `info p`, defined as `info p = – log p` where `log` is the binary
(base `2`) logarithm. For example, `even (rand 8)` has probability `1/2` of being
true. If we evaluate it and find that it is true, we have just learned
`info (1/2) = – log (1/2) = log 2 = 1` bit of information ... If we test
`rand 8 = 5`, which has probability `1/8` of being true, and we find that it is
true, we learn `info (1/8) = – log (1/8) = log 8 = 3` bits, which is the entire
random number in binary. If we find that `rand 8 = 5` is false, we learn
`info (7/8) = – log (7/8) = log 8 – log 7 = 3 – 2.80736 = 0.19264` approximately
bits ... Suppose we test `rand 8 < 8`. Since it is certain to be true, there is
really no point in making this test; we learn `info 1 = – log 1 = –0 = 0`. In
`if b then P else Q`, suppose `b` has probability `p` of being true. When it is
true, we learn `info p` bits, and this happens with probability `p`. When it is
false, we learn `info (1–p)` bits, and this happens with probability `(1–p)`.
The average amount of information gained, called the entropy, is
`entro p = p × info p + (1–p) × info (1–p)`. For examples, `entro (1/2) = 1`, and
`entro (1/8) = entro (7/8) = 0.54356` approximately. Since `entro p` is at its
maximum when `p=1/2`, we learn most on average, and make the most efficient
use of the test, if its probability is near `1/2`."

## The model

`info` is `-Real.logb 2`, and `entro` is Mathlib's `Real.binEntropy` (natural
logarithm) divided by `log 2`; the maximum at `1/2` is
`Real.binEntropy_le_log_two`/`Real.binEntropy_eq_log_two`. The approximate
values are formalized as bounds: `0.19 < info (7/8) < 0.2` and
`0.54 < entro (1/8) < 0.55`. The probabilities of the three tests on `rand 8`
are computed from `urand`. The remarks on binary search and fast
exponentiation are not formalized.
-/

namespace LaPToP.ProgramTheory

namespace Probabilistic

open scoped Classical
open Finset Real

/-- `info p = – log p`, "where `log` is the binary (base 2) logarithm". -/
noncomputable def info (p : ℝ) : ℝ := -Real.logb 2 p

/-- `entro p = p × info p + (1–p) × info (1–p)`, "the average amount of information gained". -/
noncomputable def entro (p : ℝ) : ℝ := p * info p + (1 - p) * info (1 - p)

/-! ### The three tests on `rand 8` (aPToP p. 90) -/

/-- "`even (rand 8)` has probability `1/2` of being true." -/
theorem prob_even_rand_eight : ∑ r ∈ Finset.Ico (0 : ℤ) 8, ind (Even r) / 8 = 1 / 2 := by
  simp [Ico_zero_eight, ind, Finset.sum_insert, Int.even_iff]
  norm_num

/-- "`rand 8 = 5`, which has probability `1/8` of being true". -/
theorem prob_rand_eight_eq_five : ∑ r ∈ Finset.Ico (0 : ℤ) 8, ind (r = 5) / 8 = 1 / 8 := by
  simp [Ico_zero_eight, ind, Finset.sum_insert]

/-- "`rand 8 < 8` ... is certain to be true." -/
theorem prob_rand_eight_lt_eight : ∑ r ∈ Finset.Ico (0 : ℤ) 8, ind (r < 8) / 8 = 1 := by
  simp [Ico_zero_eight, ind, Finset.sum_insert]
  norm_num

/-! ### Values of `info` -/

/-- `info (1/2) = – log (1/2) = log 2 = 1`. -/
theorem info_half : info (1 / 2) = 1 := by
  rw [info, one_div, Real.logb_inv, neg_neg, Real.logb_self_eq_one (by norm_num)]

/-- `info (1/8) = – log (1/8) = log 8 = 3`. -/
theorem info_eighth : info (1 / 8) = 3 := by
  rw [info, one_div, Real.logb_inv, neg_neg, show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

/-- `info 1 = – log 1 = –0 = 0`. -/
theorem info_one : info 1 = 0 := by simp [info]

/-- `info (7/8) = log 8 – log 7`. -/
theorem info_seven_eighths : info (7 / 8) = Real.logb 2 8 - Real.logb 2 7 := by
  rw [info, Real.logb_div (by norm_num) (by norm_num)]; ring

/-- `info (7/8) = 0.19264` approximately: `0.19 < info (7/8) < 0.2`. -/
theorem info_seven_eighths_bounds : 0.19 < info (7 / 8) ∧ info (7 / 8) < 0.2 := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hinfo : info (7 / 8) = Real.logb 2 (8 / 7) := by
    rw [info, ← Real.logb_inv]; norm_num
  rw [hinfo]
  constructor
  · -- `2^19 < (8/7)^100`, so `19 < 100 × log (8/7)`
    have h : Real.logb 2 ((2 : ℝ) ^ (19 : ℕ)) < Real.logb 2 ((8 / 7 : ℝ) ^ (100 : ℕ)) :=
      (Real.logb_lt_logb_iff h2 (by positivity) (by positivity)).2 (by norm_num)
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one h2] at h
    norm_num at h ⊢
    linarith
  · -- `(8/7)^5 < 2`, so `5 × log (8/7) < 1`
    have h : Real.logb 2 ((8 / 7 : ℝ) ^ (5 : ℕ)) < Real.logb 2 2 :=
      (Real.logb_lt_logb_iff h2 (by positivity) (by norm_num)).2 (by norm_num)
    rw [Real.logb_pow, Real.logb_self_eq_one h2] at h
    norm_num at h ⊢
    linarith

/-! ### Entropy -/

/-- `entro` is the binary entropy in bits: Mathlib's `Real.binEntropy` (in nats) divided by `log 2`. -/
theorem entro_eq_binEntropy_div (p : ℝ) : entro p = Real.binEntropy p / Real.log 2 := by
  simp only [entro, info, Real.binEntropy, Real.logb, Real.log_inv]
  ring

/-- `entro (1/2) = 1`. -/
theorem entro_half : entro (1 / 2) = 1 := by
  rw [entro_eq_binEntropy_div, one_div, Real.binEntropy_two_inv, div_self (Real.log_pos (by norm_num)).ne']

/-- `entro p = entro (1–p)`, so `entro (1/8) = entro (7/8)`. -/
theorem entro_symm (p : ℝ) : entro p = entro (1 - p) := by
  simp only [entro, sub_sub_cancel]; ring

theorem entro_eighth_eq : entro (1 / 8) = entro (7 / 8) := by rw [entro_symm]; norm_num

/-- `entro (1/8) = 0.54356` approximately: `0.54 < entro (1/8) < 0.55`. -/
theorem entro_eighth_bounds : 0.54 < entro (1 / 8) ∧ entro (1 / 8) < 0.55 := by
  have h : entro (1 / 8) = 1 / 8 * 3 + 7 / 8 * info (7 / 8) := by
    rw [entro, info_eighth]; norm_num
  obtain ⟨h1, h2⟩ := info_seven_eighths_bounds
  rw [h]
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- "`entro p` is at its maximum when `p=1/2`": `entro p ≤ 1` for every `p`. -/
theorem entro_le_one (p : ℝ) : entro p ≤ 1 := by
  rw [entro_eq_binEntropy_div, div_le_one (Real.log_pos (by norm_num))]
  exact Real.binEntropy_le_log_two

/-- ... and the maximum `1` is attained exactly at `p = 1/2`. -/
theorem entro_eq_one_iff (p : ℝ) : entro p = 1 ↔ p = 1 / 2 := by
  rw [entro_eq_binEntropy_div, div_eq_one_iff_eq (Real.log_pos (by norm_num)).ne', Real.binEntropy_eq_log_two,
    one_div]

end Probabilistic

end LaPToP.ProgramTheory
