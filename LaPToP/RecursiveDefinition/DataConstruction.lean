import LaPToP.RecursiveDefinition.Nat

/-!
# Recursive data construction

This module formalizes Section 6.0.2 (Recursive Data Construction) of Eric
Hehner's *A Practical Theory of Programming* (aPToP).

## The model

"Recursive construction is a procedure for constructing solutions from
constructors. It usually works, but not always." Its steps: (0) construct the
sequence `name₀ = null`, `nameₙ₊₁ = (expression involving nameₙ)`; (1) find an
expression for `nameₙ` not involving `name`; (2) form `name∞` by replacing `n`
with `∞`; (3) test that `name∞` is a solution; (4) for the smallest solution,
test `B = (expression involving B) ⇒ name∞ : B`.

The general part of the procedure is stated for an arbitrary *monotone*
constructor `C` on bunches (`chain C n`, the `nameₙ`): the sequence is
increasing, its union is included in every fixed point (step 4 is automatic),
and if the union passes the test of step 3 it is the least fixed point. The
honest caveat is the book's own: "the bunch `name∞` is usually a solution, but
not always" — when the test fails the procedure yields nothing, and the
property ("continuity") that would guarantee success is left to other books.

The book's illustration is `pow` with constructor `B ↦ 1, 2×B`: `pow₀ = null`,
`pow₁ = 1`, `pow₂ = 1, 2`, `pow₃ = 1, 2, 4`, the guess `powₙ = 2^(0,..n)`,
`pow∞ = 2^nat`, and the two tests — so `pow = 2^nat`. Finally the axiom
`bad = §n: nat· ¬ n: bad` is shown inconsistent (no bunch satisfies it), and
its construction sequence alternates `null, nat, null, …`, so "we cannot say
what `bad∞` is".
-/

namespace LaPToP.RecursiveDefinition

open LaPToP.BasicTheories

universe u

/-! ### The procedure for a monotone constructor (aPToP §6.0.2) -/

section Procedure

variable {α : Type u} (C : Bunch α → Bunch α)

/-- Step 0: `name₀ = null`, `nameₙ₊₁ = (expression involving nameₙ)`. -/
def chain : ℕ → Bunch α
  | 0 => Bunch.null
  | n + 1 => C (chain n)

/-- "`nameₙ` represents our knowledge of `name` after `n` uses of its constructor." -/
theorem chain_succ (n : ℕ) : chain C (n + 1) = C (chain C n) := rfl

/-- Step 2, read honestly: `name∞` is the union of all the `nameₙ`. -/
def limit : Bunch α := ⋃ n, chain C n

variable (hC : Monotone C)
include hC

/-- For a monotone constructor the sequence is increasing. -/
theorem chain_mono : Monotone (chain C) := by
  refine monotone_nat_of_le_succ fun n => ?_
  induction n with
  | zero => exact Set.empty_subset _
  | succ n ih => exact hC ih

/-- Every `nameₙ` is included in every pre-fixed point `C B ⊆ B`. -/
theorem chain_subset_of_prefixed {B : Bunch α} (hB : C B ⊆ B) (n : ℕ) : chain C n ⊆ B := by
  induction n with
  | zero => exact Set.empty_subset _
  | succ n ih => exact (hC ih).trans hB

/-- Step 4 is automatic: the limit is included in every fixed point. -/
theorem limit_subset_of_fixedPoint {B : Bunch α} (hB : IsFixedPoint C B) : limit C ⊆ B :=
  Set.iUnion_subset (chain_subset_of_prefixed C hC hB.le)

/-- Step 3 decides: if the limit is a fixed point, it is the least fixed point. -/
theorem isLeastFixedPoint_of_test (h : IsFixedPoint C (limit C)) : IsLeastFixedPoint C (limit C) :=
  ⟨h, fun _ hB => limit_subset_of_fixedPoint C hC hB⟩

/-- One inclusion of the test always holds for a monotone constructor: the
limit is a *post*-fixed point, `limit ⊆ C limit`. -/
theorem limit_subset_apply : limit C ⊆ C (limit C) := by
  refine Set.iUnion_subset fun n => ?_
  cases n with
  | zero => exact Set.empty_subset _
  | succ n => exact hC (Set.subset_iUnion (chain C) n)

end Procedure

/-! ### The illustration `pow` (aPToP §6.0.2) -/

/-- The `pow` constructor `B ↦ 1, 2×B`; "`2×B`" is the bunch of doubles of
elements of `B` (`×` distributes over bunch union). -/
def powConstructor (B : Bunch ℤ) : Bunch ℤ := Bunch.elem 1 ∪ (fun n => 2 * n) '' B

/-- The pow constructor is monotone. -/
theorem powConstructor_mono : Monotone powConstructor := fun _ _ h =>
  Set.union_subset_union_right _ (Set.image_mono h)

/-- `powₙ`, the construction sequence of `pow`. -/
def powN : ℕ → Bunch ℤ := chain powConstructor

/-- `pow₀ = null`. -/
theorem powN_zero : powN 0 = Bunch.null := rfl

/-- `pow₁ = 1`. -/
theorem powN_one : powN 1 = Bunch.elem 1 := by
  simp [powN, chain, powConstructor]

/-- `pow₂ = 1, 2`. -/
theorem powN_two : powN 2 = Bunch.elem 1 ∪ Bunch.elem 2 := by
  simp [powN, chain, powConstructor, Bunch.elem]

/-- `pow₃ = 1, 2, 4`. -/
theorem powN_three : powN 3 = Bunch.elem 1 ∪ Bunch.elem 2 ∪ Bunch.elem 4 := by
  simp [powN, chain, powConstructor, Bunch.elem, Set.image_insert_eq]

/-- Step 1, the guess `powₙ = 2^(0,..n)`: "we could prove this by nat
induction, but it is not really necessary" — here it is anyway. -/
theorem powN_eq (n : ℕ) : powN n = (fun k : ℕ => (2 : ℤ) ^ k) '' {k | k < n} := by
  induction n with
  | zero =>
    ext m; simp [powN, chain]
  | succ n ih =>
    rw [powN, chain_succ, ← powN, ih]
    ext m
    simp only [powConstructor, Set.mem_union, Bunch.elem, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_ofPred_eq]
    constructor
    · rintro (rfl | ⟨_, ⟨k, hk, rfl⟩, rfl⟩)
      · exact ⟨0, Nat.succ_pos n, by simp⟩
      · exact ⟨k + 1, by omega, by rw [pow_succ]; ring⟩
    · rintro ⟨k, hk, rfl⟩
      cases k with
      | zero => exact Or.inl (by simp)
      | succ k => exact Or.inr ⟨2 ^ k, ⟨k, by omega, rfl⟩, by rw [pow_succ]; ring⟩

/-- Step 2: `pow∞ = 2^(0,..∞) = 2^nat`. -/
def powInf : Bunch ℤ := (fun k : ℕ => (2 : ℤ) ^ k) '' Set.univ

/-- `pow∞` is the limit of the `powₙ` ("replacing `n` with `∞`"). -/
theorem powInf_eq_limit : powInf = limit powConstructor := by
  ext m
  simp only [powInf, limit, Set.mem_iUnion, Set.mem_image, Set.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by rw [← powN, powN_eq]; exact ⟨k, show k < k + 1 by omega, rfl⟩⟩
  · rintro ⟨n, hn⟩
    rw [← powN, powN_eq] at hn
    obtain ⟨k, -, rfl⟩ := hn
    exact ⟨k, rfl⟩

/-- Step 3, the test: `2^nat = 1, 2×2^nat`, "⇐ `nat = 0, nat+1`, nat fixed-point construction". -/
theorem powConstructor_powInf : powConstructor powInf = powInf := by
  ext m
  simp only [powConstructor, powInf, Set.mem_union, Bunch.elem, Set.mem_singleton_iff, Set.mem_image,
    Set.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨_, ⟨k, rfl⟩, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨k + 1, by rw [pow_succ]; ring⟩
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact Or.inl (by simp)
    | succ k => exact Or.inr ⟨2 ^ k, ⟨k, rfl⟩, by rw [pow_succ]; ring⟩

/-- Step 4, the test for leastness: `2^nat: B ⇐ B = 1, 2×B`, "using the
predicate form of nat induction". -/
theorem powInf_subset_of_fixedPoint {B : Bunch ℤ} (hB : powConstructor B = B) : powInf ⊆ B := by
  rintro m ⟨k, -, rfl⟩
  induction k with
  | zero => exact hB.le (Or.inl (by simp [Bunch.elem]))
  | succ k ih =>
    exact hB.le (Or.inr ⟨2 ^ k, ih, by show (2 : ℤ) * 2 ^ k = 2 ^ (k + 1); rw [pow_succ]; ring⟩)

/-- "Since `2^nat` is the least fixed-point of the pow constructor, we conclude
`pow = 2^nat`." -/
theorem powInf_isLeastFixedPoint : IsLeastFixedPoint powConstructor powInf :=
  ⟨powConstructor_powInf, fun _ hB => powInf_subset_of_fixedPoint hB⟩

/-- Any `pow` satisfying the fixed-point construction and induction axioms is `2^nat`. -/
theorem pow_eq_powInf {pow : Bunch ℤ} (hpow : IsLeastFixedPoint powConstructor pow) : pow = powInf :=
  hpow.unique powInf_isLeastFixedPoint

/-- The same conclusion by the general procedure: the limit passes the test. -/
theorem limit_powConstructor_isLeastFixedPoint : IsLeastFixedPoint powConstructor (limit powConstructor) :=
  isLeastFixedPoint_of_test powConstructor powConstructor_mono
    (powInf_eq_limit ▸ powConstructor_powInf)

/-! ### An inconsistent axiom (aPToP §6.0.2)

"Suppose we make `bad = §n: nat· ¬ n: bad` an axiom. Thus `bad` is defined as
the bunch of all naturals that are not in `bad`. ... `0: bad = ¬ 0: bad` is a
theorem [and] also an antitheorem. To avoid the inconsistency, we must
withdraw this axiom." -/

/-- The `bad` constructor `B ↦ §n: nat· ¬ n: B`. -/
def badConstructor (B : Bunch ℤ) : Bunch ℤ := {n | n ∈ Bunch.nat ∧ n ∉ B}

/-- `0: bad = ¬ 0: bad` for any `bad` satisfying the axiom. -/
theorem zero_mem_iff_not_mem {B : Bunch ℤ} (hB : badConstructor B = B) : 0 ∈ B ↔ 0 ∉ B := by
  conv_lhs => rw [← hB]
  simp [badConstructor, mem_nat]

/-- The axiom is inconsistent: no bunch satisfies `bad = §n: nat· ¬ n: bad`. -/
theorem not_exists_bad : ¬ ∃ B : Bunch ℤ, badConstructor B = B := fun ⟨_B, hB⟩ =>
  iff_not_self (zero_mem_iff_not_mem hB)

/-- The `bad` constructor is antitone, not monotone — the procedure's
hypothesis fails. -/
theorem badConstructor_antitone : Antitone badConstructor := fun _ _ h _n ⟨hn, hB⟩ => ⟨hn, fun hm => hB (h hm)⟩

/-- `badₙ`, the construction sequence of `bad`. -/
def badN : ℕ → Bunch ℤ := chain badConstructor

/-- `bad₀ = null`. -/
theorem badN_zero : badN 0 = Bunch.null := rfl

/-- `bad₁ = nat`. -/
theorem badN_one : badN 1 = Bunch.nat := by
  ext n; simp [badN, chain, badConstructor]

/-- `bad₂ = null`. -/
theorem badN_two : badN 2 = Bunch.null := by
  ext n; simp [badN, chain, badConstructor]

/-- "And so on, alternating between `null` and `nat`": `badₙ₊₂ = badₙ`. -/
theorem badN_add_two (n : ℕ) : badN (n + 2) = badN n := by
  induction n with
  | zero => exact badN_two
  | succ n ih =>
    show badConstructor (badN (n + 2)) = badConstructor (badN n)
    rw [ih]

/-- "We cannot say what `bad∞` is": the sequence has no limit in the sense of
the procedure — `bad₁ ⊄ bad₂`. -/
theorem badN_not_mono : ¬ Monotone badN := fun h => by
  have := h (show 1 ≤ 2 by norm_num) (show (0 : ℤ) ∈ badN 1 from badN_one ▸ mem_nat.2 le_rfl)
  rw [badN_two] at this
  exact Set.notMem_empty _ this

end LaPToP.RecursiveDefinition
