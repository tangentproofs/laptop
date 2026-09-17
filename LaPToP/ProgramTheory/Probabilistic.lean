import LaPToP.ProgramTheory.Programs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Probabilistic programming

This module formalizes Section 5.7 (Probabilistic Programming) of Eric
Hehner's *A Practical Theory of Programming* (aPToP), pp. 85–87.

"Probability Theory has been developed using the arbitrary convention that a
probability is a real number between 0 and 1 inclusive `prob = §r: real· 0≤r≤1`
... Accordingly, for this section only, we add the axioms `⊤=1`, `⊥=0`. With
these axioms, binary operators can be expressed arithmetically: `¬x = 1–x`,
`x∧y = x×y`, and `x∨y = x – x×y + y`. A distribution is an expression whose
value (for all assignments of values to its variables) is a probability, and
whose sum (over all assignments of values to its variables) is `1`. ... if
`n: nat+1`, then `2–n` is a distribution ... The specification `n′ = n+1` is not a
distribution of `n` and `n′` because there are infinitely many pairs of values
that give `n′ = n+1` the value `⊤` or `1`, and so `Σn, n′· n′ = n+1 = ∞`. But for any
fixed value of `n`, there is a single value of `n′` that gives `n′ = n+1` the value
`⊤` or `1`, and so `Σn′· n′ = n+1 = 1`. ... We generalize our programming notations
to allow probabilistic operands as follows. `ok = (x′=x) × (y′=y) × ...`,
`x:= e = (x′=e) × (y′=y) × ...`, `if b then P else Q = b × P + (1–b) × Q`,
`P. Q = Σx′′, y′′, ...· (for x′, y′, ... substitute x′′, y′′, ... in P) × (for x, y,
... substitute x′′, y′′, ... in Q)`. Since `⊥=0` and `⊤=1`, the definitions of `ok`
and assignment have not changed; they have just been expressed arithmetically.
... If `b` is a probability of the initial state, and `P` and `Q` are
distributions of the final state, then `if b then P else Q` is a distribution
of the final state. If `P` and `Q` are distributions of the final state, then
`P.Q` is a distribution of the final state. ... Let `P` be any distribution of
final states, and let `e` be any number expression over initial states. After
execution of `P`, the average value of `e` is `(P. e)`. ... Let `P` be any
distribution of final states, and let `b` be any binary expression over initial
states. After execution of `P`, the probability that `b` is true is `(P. b)`.
Probability is just the average value of a binary expression."

## The model

A probabilistic specification is `PSpec σ := σ → σ → ℝ`. The "axioms" `⊤=1`,
`⊥=0` are the indicator `ind : Prop → ℝ`, and a binary specification is
embedded by `ofSpec`. Sums over the (integer) state space are `tsum` (`∑'`).
"Distribution of the final state" is `IsDistribution`: for every initial
state, the values are probabilities summing to `1`. The closure of
distributions under `P. Q` is proved for `P` with finitely many possible final
states (the case of all the examples; the general case needs an interchange of
infinite sums and is not proved here). "The definitions have not changed" is
proved for `ok`, assignment and `if`, and for `P. Q` with an assignment as `P`
(the Substitution Law); the state is the book's "one variable `x`", an integer.
The average of `n²` under `2⁻ⁿ` (`= 6`) is not proved.
-/

namespace LaPToP.ProgramTheory

namespace Probabilistic

open Spec
open scoped Classical

universe u

/-- `prob = §r: real· 0≤r≤1`. -/
def Prob (r : ℝ) : Prop := 0 ≤ r ∧ r ≤ 1

/-- The axioms `⊤=1`, `⊥=0` as an indicator. -/
noncomputable def ind (p : Prop) : ℝ := if p then 1 else 0

theorem ind_true {p : Prop} (h : p) : ind p = 1 := if_pos h
theorem ind_false {p : Prop} (h : ¬ p) : ind p = 0 := if_neg h
theorem prob_ind (p : Prop) : Prob (ind p) := by unfold ind Prob; split_ifs <;> norm_num

/-- `¬x = 1–x`. -/
theorem ind_not (p : Prop) : ind (¬ p) = 1 - ind p := by unfold ind; split_ifs <;> simp_all
/-- `x∧y = x×y`. -/
theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by unfold ind; split_ifs <;> simp_all
/-- `x∨y = x – x×y + y`. -/
theorem ind_or (p q : Prop) : ind (p ∨ q) = ind p - ind p * ind q + ind q := by
  unfold ind; split_ifs <;> simp_all

/-- A probabilistic specification: a real-valued expression of the initial and final states. -/
abbrev PSpec (σ : Type u) := σ → σ → ℝ

variable {σ : Type u}

/-- A binary specification read arithmetically (`⊤=1`, `⊥=0`). -/
noncomputable def ofSpec (S : Spec σ) : PSpec σ := fun s s' => ind (S s s')

/-- "A distribution of the final state": for each initial state, probabilities summing to `1`. -/
def IsDistribution (P : PSpec σ) : Prop := ∀ s, (∀ s', Prob (P s s')) ∧ HasSum (P s) 1

/-- `if b then P else Q = b × P + (1–b) × Q`. -/
noncomputable def pcond (b : σ → ℝ) (P Q : PSpec σ) : PSpec σ := fun s s' => b s * P s s' + (1 - b s) * Q s s'

/-- `P. Q = Σx′′· (P with x′′ for x′) × (Q with x′′ for x)`. -/
noncomputable def pseq (P Q : PSpec σ) : PSpec σ := fun s s' => ∑' s'', P s s'' * Q s'' s'

/-- The average value of `e` after `P`: `Σx′· P × e x′`. -/
noncomputable def avg (P : PSpec σ) (e : σ → ℝ) (s : σ) : ℝ := ∑' s', P s s' * e s'

/-- "The average value of `e` is `(P. e)`": `avg` is `P. e` with `e` read over the initial state
of the second operand (and independent of the final state). -/
theorem pseq_const_eq_avg (P : PSpec σ) (e : σ → ℝ) (s s' : σ) : pseq P (fun s'' _ => e s'') s s' = avg P e s := rfl

/-! ### Deterministic specifications are one-point distributions -/

/-- `ok` is a distribution (of the final state). -/
theorem isDistribution_ofSpec_ok : IsDistribution (ofSpec (ok : Spec σ)) := fun s =>
  ⟨fun _ => prob_ind _, hasSum_ite_eq s (1 : ℝ)⟩

/-- Any deterministic specification `s′ = f s` is a one-point distribution: "for any fixed value
of `n`, `n′ = n+1` is a one-point distribution of `n′`". -/
theorem isDistribution_ofSpec_det (f : σ → σ) : IsDistribution (ofSpec fun s s' => s' = f s) := fun s =>
  ⟨fun _ => prob_ind _, hasSum_ite_eq (f s) (1 : ℝ)⟩

/-- `Σn′· n′ = n+1 = 1`. -/
theorem tsum_succ_eq_one (n : ℤ) : ∑' n' : ℤ, ind (n' = n + 1) = 1 := by
  unfold ind
  convert tsum_ite_eq (n + 1) (fun _ => (1 : ℝ)) using 1
  congr
  funext n'
  congr

/-- "`Σn, n′· n′ = n+1 = ∞`": the specification is not a distribution of `n` and `n′` — summed
over both variables it is not even summable. -/
theorem not_summable_succ : ¬ Summable fun p : ℤ × ℤ => ind (p.2 = p.1 + 1) := by
  intro h
  have h1 := h.tendsto_cofinite_zero
  have h2 : ∀ᶠ p : ℤ × ℤ in Filter.cofinite, ind (p.2 = p.1 + 1) < 1 :=
    h1.eventually (gt_mem_nhds one_pos)
  rw [Filter.eventually_cofinite] at h2
  have hsub : Set.range (fun n : ℤ => (n, n + 1)) ⊆ {p : ℤ × ℤ | ¬ ind (p.2 = p.1 + 1) < 1} := by
    rintro p ⟨n, rfl⟩
    simp [ind]
  exact Set.infinite_range_of_injective (fun a b h => (Prod.mk.inj h).1) (h2.subset hsub)

/-- `2⁻ⁿ` for `n: nat+1` is a distribution: `(∀n: nat+1· 2–n: prob) ∧ (Σn: nat+1· 2–n)=1`. -/
theorem geometric_distribution :
    (∀ n : ℕ, Prob ((1 / 2 : ℝ) ^ (n + 1))) ∧ HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
  refine ⟨fun n => ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩, ?_⟩
  have := hasSum_geometric_two.mul_left (1 / 2)
  simpa [pow_succ, mul_comm] using this

/-! ### The generalized programming notations -/

/-- "If `b` is a probability of the initial state, and `P` and `Q` are distributions of the final
state, then `if b then P else Q` is a distribution of the final state." -/
theorem isDistribution_pcond {b : σ → ℝ} (hb : ∀ s, Prob (b s)) {P Q : PSpec σ}
    (hP : IsDistribution P) (hQ : IsDistribution Q) : IsDistribution (pcond b P Q) := fun s => by
  obtain ⟨hb0, hb1⟩ := hb s
  refine ⟨fun s' => ?_, ?_⟩
  · obtain ⟨hP0, hP1⟩ := (hP s).1 s'
    obtain ⟨hQ0, hQ1⟩ := (hQ s).1 s'
    constructor
    · unfold pcond; nlinarith
    · unfold pcond; nlinarith
  · have := ((hP s).2.mul_left (b s)).add ((hQ s).2.mul_left (1 - b s))
    rw [mul_one, mul_one, add_sub_cancel] at this
    exact this

/-- `P. Q` for `P` with finitely many possible final states is a finite sum. -/
theorem pseq_eq_sum {P Q : PSpec σ} {s : σ} (hfin : (Function.support (P s)).Finite) (s' : σ) :
    pseq P Q s s' = ∑ s'' ∈ hfin.toFinset, P s s'' * Q s'' s' := by
  unfold pseq
  refine tsum_eq_sum fun b hb => ?_
  rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hb
  simp [hb]

/-- "If `P` and `Q` are distributions of the final state, then `P.Q` is a distribution of the
final state" — proved for `P` with finitely many possible final states. -/
theorem isDistribution_pseq {P Q : PSpec σ} (hP : IsDistribution P)
    (hfin : ∀ s, (Function.support (P s)).Finite) (hQ : IsDistribution Q) :
    IsDistribution (pseq P Q) := fun s => by
  have hsum : ∑ s'' ∈ (hfin s).toFinset, P s s'' = 1 :=
    (hasSum_sum_of_ne_finset_zero fun b hb => by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hb; exact hb).unique (hP s).2
  refine ⟨fun s' => ?_, ?_⟩
  · rw [pseq_eq_sum (hfin s)]
    constructor
    · exact Finset.sum_nonneg fun s'' _ => mul_nonneg ((hP s).1 s'').1 ((hQ s'').1 s').1
    · calc ∑ s'' ∈ (hfin s).toFinset, P s s'' * Q s'' s'
          ≤ ∑ s'' ∈ (hfin s).toFinset, P s s'' * 1 :=
            Finset.sum_le_sum fun s'' _ => mul_le_mul_of_nonneg_left ((hQ s'').1 s').2 ((hP s).1 s'').1
        _ = 1 := by simpa using hsum
  · have h : HasSum (fun s' => ∑ s'' ∈ (hfin s).toFinset, P s s'' * Q s'' s')
        (∑ s'' ∈ (hfin s).toFinset, P s s'' * 1) :=
      hasSum_sum fun s'' _ => (hQ s'').2.mul_left (P s s'')
    simp only [mul_one, hsum] at h
    convert h using 1
    funext s'
    exact pseq_eq_sum (hfin s) s'

/-! ### One variable `x` (aPToP p. 86): the definitions have not changed -/

/-- `ok` in one integer variable. -/
noncomputable def pok : PSpec ℤ := fun x x' => ind (x' = x)

/-- `x:= e = (x′=e)`. -/
noncomputable def passign (e : ℤ → ℤ) : PSpec ℤ := fun x x' => ind (x' = e x)

/-- `x:= e` as a binary specification. -/
def assignX (e : ℤ → ℤ) : Spec ℤ := fun x x' => x' = e x

/-- "Since `⊥=0` and `⊤=1`, the definitions of `ok` ... have not changed". -/
theorem ofSpec_ok : ofSpec (ok : Spec ℤ) = pok := rfl

/-- "... and assignment have not changed". -/
theorem ofSpec_assign (e : ℤ → ℤ) : ofSpec (assignX e) = passign e := rfl

/-- "If `b`, `P`, and `Q` are binary, the definitions of `if b then P else Q` ... have not changed." -/
theorem ofSpec_cond (b : σ → Prop) (S R : Spec σ) :
    ofSpec (Spec.cond b S R) = pcond (fun s => ind (b s)) (ofSpec S) (ofSpec R) := by
  funext s s'
  simp only [ofSpec, pcond, ind]
  by_cases hb : b s <;> simp [Spec.cond, hb]

/-- The Substitution Law for probabilistic specifications: `x:= e. P = (for x substitute e in P)`. -/
theorem passign_pseq (e : ℤ → ℤ) (P : PSpec ℤ) : pseq (passign e) P = fun x x' => P (e x) x' := by
  funext x x'
  simp only [pseq, passign, ind]
  simp

/-- "... and `P.Q` have not changed", for an assignment followed by any binary specification. -/
theorem ofSpec_assign_seq (e : ℤ → ℤ) (R : Spec ℤ) : ofSpec (seq (assignX e) R) = pseq (passign e) (ofSpec R) := by
  rw [passign_pseq]
  funext x x'
  simp only [ofSpec, seq, assignX, ind]
  congr 1
  exact propext ⟨fun ⟨_, h, hR⟩ => h ▸ hR, fun hR => ⟨_, rfl, hR⟩⟩

/-- `x:= e` is a distribution. -/
theorem isDistribution_passign (e : ℤ → ℤ) : IsDistribution (passign e) := isDistribution_ofSpec_det e

/-- `x:= e` has one possible final state. -/
theorem support_passign (e : ℤ → ℤ) (x : ℤ) : (Function.support (passign e x)).Finite := by
  apply (Set.finite_singleton (e x)).subset
  intro x' hx'
  rw [Function.mem_support] at hx'
  by_contra h
  exact hx' (ind_false h)

/-! ### The examples (aPToP p. 86–87) -/

/-- `if 1/3 then x:= 0 else x:= 1`. -/
noncomputable def ex₁ : PSpec ℤ := pcond (fun _ => 1 / 3) (passign fun _ => 0) (passign fun _ => 1)

/-- `if 1/3 then x:= 0 else x:= 1 = 1/3 × (x′=0) + (1 – 1/3) × (x′=1)`. -/
theorem ex₁_eq (x x' : ℤ) : ex₁ x x' = 1 / 3 * ind (x' = 0) + (1 - 1 / 3) * ind (x' = 1) := rfl

/-- "the probability that `x` has final value `0`" is `1/3`. -/
theorem ex₁_zero (x : ℤ) : ex₁ x 0 = 1 / 3 := by simp [ex₁_eq, ind]
/-- "... final value `1`" is `2/3`. -/
theorem ex₁_one (x : ℤ) : ex₁ x 1 = 2 / 3 := by simp [ex₁_eq, ind]; norm_num
/-- "... final value `2`" is `0`. -/
theorem ex₁_two (x : ℤ) : ex₁ x 2 = 0 := by simp [ex₁_eq, ind]

theorem isDistribution_ex₁ : IsDistribution ex₁ :=
  isDistribution_pcond (fun _ => by norm_num [Prob]) (isDistribution_passign _) (isDistribution_passign _)

theorem support_ex₁ (x : ℤ) : (Function.support (ex₁ x)).Finite := by
  apply (Set.toFinite ({0, 1} : Finset ℤ)).subset
  intro x' hx'
  rw [Function.mem_support] at hx'
  by_contra h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  exact hx' (by simp [ex₁_eq, ind, h.1, h.2])

/-- `if x=0 then if 1/2 then x:= x+2 else x:= x+3 else if 1/4 then x:= x+4 else x:= x+5`. -/
noncomputable def ex₂body : PSpec ℤ :=
  pcond (fun x => ind (x = 0))
    (pcond (fun _ => 1 / 2) (passign fun x => x + 2) (passign fun x => x + 3))
    (pcond (fun _ => 1 / 4) (passign fun x => x + 4) (passign fun x => x + 5))

/-- The "slightly more elaborate example": `ex₁. ex₂body`. -/
noncomputable def ex₂ : PSpec ℤ := pseq ex₁ ex₂body

/-- `... = (x′=2)/6 + (x′=3)/6 + (x′=5)/6 + (x′=6)/2`. -/
theorem ex₂_eq (x x' : ℤ) :
    ex₂ x x' = ind (x' = 2) / 6 + ind (x' = 3) / 6 + ind (x' = 5) / 6 + ind (x' = 6) / 2 := by
  have hfin := support_ex₁ x
  rw [ex₂, pseq_eq_sum hfin]
  have hF : hfin.toFinset ⊆ {0, 1} := by
    intro x'' hx''
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hx''
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact hx'' (by simp [ex₁_eq, ind, h.1, h.2])
  rw [Finset.sum_subset hF fun x'' _ hx'' => by
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx''; simp [hx'']]
  rw [Finset.sum_pair (by norm_num)]
  simp only [ex₁_zero, ex₁_one, ex₂body, pcond, passign, ind, zero_add]
  norm_num
  split_ifs <;> (try omega) <;> norm_num

theorem isDistribution_ex₂ : IsDistribution ex₂ :=
  isDistribution_pseq isDistribution_ex₁ support_ex₁
    (isDistribution_pcond (fun _ => prob_ind _)
      (isDistribution_pcond (fun _ => by norm_num [Prob]) (isDistribution_passign _) (isDistribution_passign _))
      (isDistribution_pcond (fun _ => by norm_num [Prob]) (isDistribution_passign _) (isDistribution_passign _)))

/-- The possible final values of the example are `2, 3, 5, 6`. -/
theorem support_ex₂ (x : ℤ) : Function.support (ex₂ x) ⊆ ({2, 3, 5, 6} : Finset ℤ) := by
  intro x' hx'
  rw [Function.mem_support] at hx'
  by_contra h
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  exact hx' (by simp [ex₂_eq, ind, h.1, h.2.1, h.2.2.1, h.2.2.2])

/-- An average after the example is a finite sum over its possible final values. -/
theorem avg_ex₂_eq (e : ℤ → ℝ) (x : ℤ) : avg ex₂ e x = ∑ x' ∈ ({2, 3, 5, 6} : Finset ℤ), ex₂ x x' * e x' := by
  unfold avg
  refine tsum_eq_sum fun b hb => ?_
  have : ex₂ x b = 0 := by
    by_contra h
    exact hb (by simpa using support_ex₂ x (Function.mem_support.2 h))
  simp [this]

/-- "After execution of the previous example, the average value of `x` is ... `4 + 2/3`." -/
theorem avg_ex₂_x (x : ℤ) : avg ex₂ (fun x' => (x' : ℝ)) x = 4 + 2 / 3 := by
  rw [avg_ex₂_eq]
  simp [Finset.sum_insert, ex₂_eq, ind]
  norm_num

/-- "the probability that `x` is greater than `3` is ... `2/3`" — "Probability is just the average
value of a binary expression". -/
theorem prob_ex₂_gt_three (x : ℤ) : avg ex₂ (fun x' => ind (x' > 3)) x = 2 / 3 := by
  rw [avg_ex₂_eq]
  simp [Finset.sum_insert, ex₂_eq, ind]
  norm_num

end Probabilistic

end LaPToP.ProgramTheory
