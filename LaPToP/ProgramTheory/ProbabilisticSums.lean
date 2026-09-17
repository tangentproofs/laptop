import LaPToP.ProgramTheory.Probabilistic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Data.Nat.Choose.Cast

/-!
# Probabilistic programming: infinite sums

This module completes two claims of Section 5.7 (Probabilistic Programming)
of Eric Hehner's *A Practical Theory of Programming* (aPToP) that
`LaPToP.ProgramTheory.Probabilistic` left open.

"If `P` and `Q` are distributions of the final state, then `P.Q` is a
distribution of the final state." — proved there only for `P` with finitely
many possible final states; here in general (`isDistribution_pseq'`), by the
interchange of a nonnegative double sum.

"The average value of `n²` as `n` varies over `nat+1` according to distribution
`2–n` is `2–n. n² = Σn′: nat+1· 2–n′ × n′² = 6`." — `avg_geomDist_sq`, from
Mathlib's sums `Σn· C(n+k, k) rⁿ = 1/(1–r)^(k+1)` for `k = 1, 2`.
-/

namespace LaPToP.ProgramTheory

namespace Probabilistic

open scoped Classical

universe u

variable {σ : Type u}

/-! ### `P.Q` is a distribution, in general -/

/-- The terms `P s s′′ × Q s′′ s′` of `P.Q`, as a function of the pair `(s′′, s′)`. -/
private def terms (P Q : PSpec σ) (s : σ) : σ × σ → ℝ := fun p => P s p.1 * Q p.1 p.2

private theorem terms_nonneg {P Q : PSpec σ} (hP : IsDistribution P) (hQ : IsDistribution Q) (s : σ) :
    0 ≤ terms P Q s := fun p => mul_nonneg ((hP s).1 p.1).1 ((hQ p.1).1 p.2).1

/-- The inner sums: `Σs′· P s s′′ × Q s′′ s′ = P s s′′`. -/
private theorem tsum_terms_right {P Q : PSpec σ} (hQ : IsDistribution Q) (s s'' : σ) :
    ∑' s', terms P Q s (s'', s') = P s s'' := by
  have := ((hQ s'').2.mul_left (P s s'')).tsum_eq
  simpa [terms] using this

/-- The double sum `Σs′′, s′· P s s′′ × Q s′′ s′` converges. -/
private theorem summable_terms {P Q : PSpec σ} (hP : IsDistribution P) (hQ : IsDistribution Q) (s : σ) :
    Summable (terms P Q s) := by
  rw [summable_prod_of_nonneg (terms_nonneg hP hQ s)]
  refine ⟨fun s'' => ((hQ s'').2.mul_left (P s s'')).summable, ?_⟩
  simp only [tsum_terms_right hQ s]
  exact (hP s).2.summable

/-- "If `P` and `Q` are distributions of the final state, then `P.Q` is a distribution of the
final state" — in general, by interchanging the nonnegative double sum. -/
theorem isDistribution_pseq' {P Q : PSpec σ} (hP : IsDistribution P) (hQ : IsDistribution Q) :
    IsDistribution (pseq P Q) := fun s => by
  have hsum := summable_terms hP hQ s
  -- the fibers with the final state fixed
  have hfib : ∀ s', Summable fun s'' => terms P Q s (s'', s') := fun s' => by
    have := hsum.prod_symm.prod_factor s'
    simpa [Prod.swap] using this
  have hpseq : ∀ s', pseq P Q s s' = ∑' s'', terms P Q s (s'', s') := fun s' => rfl
  refine ⟨fun s' => ⟨?_, ?_⟩, ?_⟩
  · rw [hpseq]
    exact tsum_nonneg fun s'' => terms_nonneg hP hQ s (s'', s')
  · rw [hpseq]
    calc ∑' s'', terms P Q s (s'', s') ≤ ∑' s'', P s s'' :=
          (hfib s').tsum_le_tsum (fun s'' => by
            simpa [terms] using mul_le_mul_of_nonneg_left ((hQ s'').1 s').2 ((hP s).1 s'').1)
            (hP s).2.summable
      _ = 1 := (hP s).2.tsum_eq
  · -- the outer sums over `s′` are summable, and their total is `Σs′′· P s s′′ = 1`
    have houter : Summable fun s' => ∑' s'', terms P Q s (s'', s') := by
      have h := (summable_prod_of_nonneg (f := fun p : σ × σ => terms P Q s p.swap)
        (fun p => terms_nonneg hP hQ s p.swap)).1 hsum.prod_symm
      simpa [Prod.swap] using h.2
    have hcomm : ∑' s', ∑' s'', terms P Q s (s'', s') = ∑' s'', ∑' s', terms P Q s (s'', s') :=
      Summable.tsum_comm (f := fun s'' s' => terms P Q s (s'', s')) hsum
    have htot : ∑' s'', ∑' s', terms P Q s (s'', s') = 1 := by
      simp only [tsum_terms_right hQ s]
      exact (hP s).2.tsum_eq
    have h := houter.hasSum
    rw [hcomm, htot] at h
    exact h

/-! ### The average of `n²` under `2⁻ⁿ` -/

/-- The distribution `2–n` of `n: nat+1`, as a probabilistic specification (of the final state,
independent of the initial state) on `ℕ`, with value `0` at `0`. -/
noncomputable def geomDist : PSpec ℕ := fun _ n' => ind (1 ≤ n') * (1 / 2 : ℝ) ^ n'

theorem geomDist_succ (m n : ℕ) : geomDist m (n + 1) = (1 / 2 : ℝ) ^ (n + 1) := by
  simp [geomDist, ind]

/-- `2–n` is a distribution of `n: nat+1`. -/
theorem isDistribution_geomDist : IsDistribution geomDist := fun m => by
  refine ⟨fun n' => ?_, ?_⟩
  · unfold geomDist ind Prob
    split_ifs
    · exact ⟨by positivity, by rw [one_mul]; exact pow_le_one₀ (by norm_num) (by norm_num)⟩
    · simp
  · rw [← hasSum_nat_add_iff' 1]
    have e : (fun n => geomDist m (n + 1)) = fun n => (1 / 2 : ℝ) ^ (n + 1) := funext (geomDist_succ m)
    have z : ∑ i ∈ Finset.range 1, geomDist m i = 0 := by simp [geomDist, ind]
    rw [e, z, sub_zero]
    exact geometric_distribution.2

/-- `Σn· (n+1)² (1/2)^(n+1) = 6`, from `Σn· C(n+2,2) rⁿ = 1/(1–r)³` and `Σn· (n+1) rⁿ = 1/(1–r)²` with
`(n+1)² = 2·C(n+2,2) – (n+1)`. -/
theorem hasSum_sq_geometric : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) ^ 2) 6 := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2 hr
  have h1 := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr
  have key := ((h2.mul_left 2).sub h1).mul_left (1 / 2)
  have e : (fun n : ℕ => 1 / 2 * (2 * (((n + 2).choose 2 : ℕ) * (1 / 2 : ℝ) ^ n) - ((n + 1).choose 1 : ℕ) * (1 / 2 : ℝ) ^ n))
      = fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ((n : ℝ) + 1) ^ 2 := by
    funext n
    rw [Nat.cast_choose_two, Nat.choose_one_right]
    push_cast
    ring
  rw [e, show (1 / 2 * (2 * (1 / (1 - 1 / 2 : ℝ) ^ (2 + 1)) - 1 / (1 - 1 / 2) ^ (1 + 1)) : ℝ) = 6 by norm_num] at key
  exact key

/-- "The average value of `n²` as `n` varies over `nat+1` according to distribution `2–n` is
`2–n. n² = Σn′: nat+1· 2–n′ × n′² = 6`." -/
theorem avg_geomDist_sq (n : ℕ) : avg geomDist (fun n' => ((n' : ℕ) : ℝ) ^ 2) n = 6 := by
  unfold avg
  have h : HasSum (fun n' : ℕ => geomDist n n' * ((n' : ℕ) : ℝ) ^ 2) 6 := by
    rw [← hasSum_nat_add_iff' 1]
    have e : (fun k => geomDist n (k + 1) * ((k + 1 : ℕ) : ℝ) ^ 2) =
        fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) * ((k : ℝ) + 1) ^ 2 := by
      funext k
      simp [geomDist, ind]
    have z : ∑ i ∈ Finset.range 1, geomDist n i * ((i : ℕ) : ℝ) ^ 2 = 0 := by simp [geomDist, ind]
    rw [e, z, sub_zero]
    exact hasSum_sq_geometric
  exact h.tsum_eq

end Probabilistic

end LaPToP.ProgramTheory
