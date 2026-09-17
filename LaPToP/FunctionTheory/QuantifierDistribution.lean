import LaPToP.FunctionTheory.Quantifiers
import LaPToP.FunctionTheory.Limits
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.Data.EReal.Inv

/-!
# Distributive laws of the numeric quantifiers

This module formalizes the Distributive laws of the Quantifiers table of the
Reference chapter (Section 11.3.8) of Eric Hehner's *A Practical Theory of
Programming* (aPToP), p. 242, and its Extreme laws for the reals.

"Distributive — if `D⧧null` and `v` does not appear in `n`:
`n↑(⇑v: D· m) = (⇑v: D· n↑m)`, `n↓(⇓v: D· m) = (⇓v: D· n↓m)`,
`n↑(⇓v: D· m) = (⇓v: D· n↑m)`, `n↓(⇑v: D· m) = (⇑v: D· n↓m)`,
`n + (⇑v: D· m) = (⇑v: D· n+m)`, `n + (⇓v: D· m) = (⇓v: D· n+m)`,
`n – (⇑v: D· m) = (⇓v: D· n–m)`, `n – (⇓v: D· m) = (⇑v: D· n–m)`,
`(⇑v: D· m) – n = (⇑v: D· m–n)`, `(⇓v: D· m) – n = (⇓v: D· m–n)`,
`n≥0 ⇒ n×(⇑v: D· m) = (⇑v: D· n×m)`, `n≥0 ⇒ n×(⇓v: D· m) = (⇓v: D· n×m)`,
`n≤0 ⇒ n×(⇑v: D· m) = (⇓v: D· n×m)`, `n≤0 ⇒ n×(⇓v: D· m) = (⇑v: D· n×m)`,
`n×(Σv: D· m) = (Σv: D· n×m)`, `(Πv: D· m)^n = (Πv: D· m^n)`."
"Extreme: `(⇓n: int· n) = (⇓n: real· n) = –∞`, `(⇑n: int· n) = (⇑n: real· n) = ∞`."

## The model

`⇑`, `⇓` are `Fn.sup`, `Fn.inf` of Section 3.1 (suprema and infima in the
extended reals `Number = EReal`); `↑`, `↓` are `⊔`, `⊓`. The lattice laws hold
in the complete linear order (`n↑` and `n↓` with `⇑`, `⇓`); the arithmetic laws
are proved by the monotonicity and continuity of `n + ·`, `n – ·`, `· – n`,
`n × ·` on the extended reals, for a *finite* `n` — the book's `n` ranges over
its numbers, but `∞ + (⇑v: D· m)` with `⇑v: D· m = –∞` is `∞ + –∞`, which the
book's number theory leaves undetermined, so finiteness of `n` is the honest
side condition. `D⧧null` is needed only where the book needs it: for `n↑⇑`,
`n↓⇓` and `n×` with `n = 0`, and it is assumed throughout for uniformity in
the `×` laws. `n×Σ` is proved for finite `D` and `0 ≤ n < ∞` (the distributivity
of `×` over `+` in the extended reals needs a nonnegative finite factor), and
`(Π)^n` for finite `D` and natural `n`.
-/

namespace LaPToP.FunctionTheory

open LaPToP.BasicTheories Filter Topology

namespace Fn

universe u

variable {α : Type u} (D : Bunch α) (m : α → Number)

/-- `⇑v: D· m` as a supremum over `D`. -/
theorem sup_lam_eq_iSup : sup (lam D m) = ⨆ v : D, m v := by
  rw [sup, values_lam, sSup_image']

/-- `⇓v: D· m` as an infimum over `D`. -/
theorem inf_lam_eq_iInf : inf (lam D m) = ⨅ v : D, m v := by
  rw [inf, values_lam, sInf_image']

/-! ### `↑` and `↓` -/

section Lattice

variable (n : Number)

/-- `n↑(⇑v: D· m) = (⇑v: D· n↑m)`, for `D⧧null`. -/
theorem sup_sup_distrib (hD : D.Nonempty) : n ⊔ sup (lam D m) = sup (lam D fun v => n ⊔ m v) := by
  have := hD.to_subtype
  rw [sup_lam_eq_iSup, sup_lam_eq_iSup]
  exact sup_iSup

/-- `n↓(⇓v: D· m) = (⇓v: D· n↓m)`, for `D⧧null`. -/
theorem inf_inf_distrib (hD : D.Nonempty) : n ⊓ inf (lam D m) = inf (lam D fun v => n ⊓ m v) := by
  have := hD.to_subtype
  rw [inf_lam_eq_iInf, inf_lam_eq_iInf]
  exact inf_iInf

/-- `n↑(⇓v: D· m) = (⇓v: D· n↑m)`. -/
theorem sup_inf_distrib : n ⊔ inf (lam D m) = inf (lam D fun v => n ⊔ m v) := by
  rw [inf_lam_eq_iInf, inf_lam_eq_iInf]
  exact sup_iInf_eq _ _

/-- `n↓(⇑v: D· m) = (⇑v: D· n↓m)`. -/
theorem inf_sup_distrib : n ⊓ sup (lam D m) = sup (lam D fun v => n ⊓ m v) := by
  rw [sup_lam_eq_iSup, sup_lam_eq_iSup]
  exact inf_iSup_eq _ _

end Lattice

/-! ### Arithmetic: monotone and antitone continuous operations -/

section Arithmetic

variable (n : ℝ)

/-- A monotone operation, continuous on the extended reals, distributes over `⇑` (for `D⧧null`). -/
theorem monotone_sup (g : Number → Number) (hg : Monotone g) (hc : ∀ x, ContinuousAt g x) (hD : D.Nonempty) :
    g (sup (lam D m)) = sup (lam D fun v => g (m v)) := by
  rw [sup, sup, values_lam, values_lam, hg.map_csSup_of_continuousAt (hc _) (hD.image m) (OrderTop.bddAbove _),
    Set.image_image]

/-- A monotone continuous operation distributes over `⇓` (for `D⧧null`). -/
theorem monotone_inf (g : Number → Number) (hg : Monotone g) (hc : ∀ x, ContinuousAt g x) (hD : D.Nonempty) :
    g (inf (lam D m)) = inf (lam D fun v => g (m v)) := by
  rw [inf, inf, values_lam, values_lam, hg.map_csInf_of_continuousAt (hc _) (hD.image m) (OrderBot.bddBelow _),
    Set.image_image]

/-- An antitone continuous operation turns `⇑` into `⇓` (for `D⧧null`). -/
theorem antitone_sup (g : Number → Number) (hg : Antitone g) (hc : ∀ x, ContinuousAt g x) (hD : D.Nonempty) :
    g (sup (lam D m)) = inf (lam D fun v => g (m v)) := by
  rw [sup, inf, values_lam, values_lam, hg.map_csSup_of_continuousAt (hc _) (hD.image m) (OrderTop.bddAbove _),
    Set.image_image]

/-- An antitone continuous operation turns `⇓` into `⇑` (for `D⧧null`). -/
theorem antitone_inf (g : Number → Number) (hg : Antitone g) (hc : ∀ x, ContinuousAt g x) (hD : D.Nonempty) :
    g (inf (lam D m)) = sup (lam D fun v => g (m v)) := by
  rw [sup, inf, values_lam, values_lam, hg.map_csInf_of_continuousAt (hc _) (hD.image m) (OrderBot.bddBelow _),
    Set.image_image]

theorem continuousAt_add_left (x : Number) : ContinuousAt (fun y : Number => (n : Number) + y) x :=
  (EReal.continuousAt_add (p := ((n : Number), x)) (Or.inl (EReal.coe_ne_top n)) (Or.inl (EReal.coe_ne_bot n))).comp
    (continuousAt_const.prodMk continuousAt_id)

theorem continuousAt_sub_left (x : Number) : ContinuousAt (fun y : Number => (n : Number) - y) x := by
  simp only [sub_eq_add_neg]
  exact (EReal.continuousAt_add (p := ((n : Number), -x)) (Or.inl (EReal.coe_ne_top n)) (Or.inl (EReal.coe_ne_bot n))).comp
    (f := fun y : Number => ((n : Number), -y)) (continuousAt_const.prodMk continuous_neg.continuousAt)

theorem continuousAt_sub_right (x : Number) : ContinuousAt (fun y : Number => y - (n : Number)) x := by
  simp only [sub_eq_add_neg]
  exact (EReal.continuousAt_add (p := (x, -(n : Number))) (Or.inr (by simp)) (Or.inr (by simp))).comp
    (f := fun y : Number => (y, -(n : Number))) (continuousAt_id.prodMk continuousAt_const)

theorem continuousAt_mul_left (hn : n ≠ 0) (x : Number) : ContinuousAt (fun y : Number => (n : Number) * y) x :=
  have h0 : (n : Number) ≠ 0 := by simpa using hn
  (EReal.continuousAt_mul (p := ((n : Number), x)) (Or.inl h0) (Or.inl h0)
    (Or.inl (EReal.coe_ne_bot n)) (Or.inl (EReal.coe_ne_top n))).comp (continuousAt_const.prodMk continuousAt_id)

/-- `n + (⇑v: D· m) = (⇑v: D· n+m)`, for finite `n` and `D⧧null`. -/
theorem add_sup (hD : D.Nonempty) : (n : Number) + sup (lam D m) = sup (lam D fun v => n + m v) :=
  monotone_sup D m _ (fun _ _ h => add_le_add le_rfl h) (continuousAt_add_left n) hD

/-- `n + (⇓v: D· m) = (⇓v: D· n+m)`, for finite `n` and `D⧧null`. -/
theorem add_inf (hD : D.Nonempty) : (n : Number) + inf (lam D m) = inf (lam D fun v => n + m v) :=
  monotone_inf D m _ (fun _ _ h => add_le_add le_rfl h) (continuousAt_add_left n) hD

/-- `n – (⇑v: D· m) = (⇓v: D· n–m)`, for finite `n` and `D⧧null`. -/
theorem sub_sup (hD : D.Nonempty) : (n : Number) - sup (lam D m) = inf (lam D fun v => n - m v) :=
  antitone_sup D m _ (fun a b h => by
    show (n : Number) - b ≤ n - a
    simp only [sub_eq_add_neg]; exact add_le_add le_rfl (EReal.neg_le_neg_iff.2 h)) (continuousAt_sub_left n) hD

/-- `n – (⇓v: D· m) = (⇑v: D· n–m)`, for finite `n` and `D⧧null`. -/
theorem sub_inf (hD : D.Nonempty) : (n : Number) - inf (lam D m) = sup (lam D fun v => n - m v) :=
  antitone_inf D m _ (fun a b h => by
    show (n : Number) - b ≤ n - a
    simp only [sub_eq_add_neg]; exact add_le_add le_rfl (EReal.neg_le_neg_iff.2 h)) (continuousAt_sub_left n) hD

/-- `(⇑v: D· m) – n = (⇑v: D· m–n)`, for finite `n` and `D⧧null`. -/
theorem sup_sub (hD : D.Nonempty) : sup (lam D m) - (n : Number) = sup (lam D fun v => m v - n) :=
  monotone_sup D m _ (fun a b h => by
    show a - (n : Number) ≤ b - n
    simp only [sub_eq_add_neg]; exact add_le_add h le_rfl) (continuousAt_sub_right n) hD

/-- `(⇓v: D· m) – n = (⇓v: D· m–n)`, for finite `n` and `D⧧null`. -/
theorem inf_sub (hD : D.Nonempty) : inf (lam D m) - (n : Number) = inf (lam D fun v => m v - n) :=
  monotone_inf D m _ (fun a b h => by
    show a - (n : Number) ≤ b - n
    simp only [sub_eq_add_neg]; exact add_le_add h le_rfl) (continuousAt_sub_right n) hD

/-- `n≥0 ⇒ n×(⇑v: D· m) = (⇑v: D· n×m)`, for finite `n` and `D⧧null`. -/
theorem mul_sup_of_nonneg (hn : 0 ≤ n) (hD : D.Nonempty) :
    (n : Number) * sup (lam D m) = sup (lam D fun v => n * m v) := by
  rcases hn.eq_or_lt with rfl | hpos
  · simp only [EReal.coe_zero, zero_mul]
    rw [sup, values_lam]
    have : (fun _ : α => (0 : Number)) '' D = {0} := Set.Nonempty.image_const hD 0
    rw [this, sSup_singleton]
  · exact monotone_sup D m _ (fun a b h => mul_le_mul_of_nonneg_left h (by exact_mod_cast hpos.le))
      (continuousAt_mul_left n hpos.ne') hD

/-- `n≥0 ⇒ n×(⇓v: D· m) = (⇓v: D· n×m)`, for finite `n` and `D⧧null`. -/
theorem mul_inf_of_nonneg (hn : 0 ≤ n) (hD : D.Nonempty) :
    (n : Number) * inf (lam D m) = inf (lam D fun v => n * m v) := by
  rcases hn.eq_or_lt with rfl | hpos
  · simp only [EReal.coe_zero, zero_mul]
    rw [inf, values_lam]
    have : (fun _ : α => (0 : Number)) '' D = {0} := Set.Nonempty.image_const hD 0
    rw [this, sInf_singleton]
  · exact monotone_inf D m _ (fun a b h => mul_le_mul_of_nonneg_left h (by exact_mod_cast hpos.le))
      (continuousAt_mul_left n hpos.ne') hD

/-- `n≤0 ⇒ n×(⇑v: D· m) = (⇓v: D· n×m)`, for finite `n` and `D⧧null`. -/
theorem mul_sup_of_nonpos (hn : n ≤ 0) (hD : D.Nonempty) :
    (n : Number) * sup (lam D m) = inf (lam D fun v => n * m v) := by
  rcases hn.eq_or_lt with rfl | hneg
  · simp only [EReal.coe_zero, zero_mul]
    rw [inf, values_lam]
    have : (fun _ : α => (0 : Number)) '' D = {0} := Set.Nonempty.image_const hD 0
    rw [this, sInf_singleton]
  · exact antitone_sup D m _ (fun a b h => by
      show (n : Number) * b ≤ n * a
      rw [mul_comm, mul_comm (n : Number)]
      exact EReal.mul_le_mul_of_nonpos_right h (by exact_mod_cast hneg.le)) (continuousAt_mul_left n hneg.ne) hD

/-- `n≤0 ⇒ n×(⇓v: D· m) = (⇑v: D· n×m)`, for finite `n` and `D⧧null`. -/
theorem mul_inf_of_nonpos (hn : n ≤ 0) (hD : D.Nonempty) :
    (n : Number) * inf (lam D m) = sup (lam D fun v => n * m v) := by
  rcases hn.eq_or_lt with rfl | hneg
  · simp only [EReal.coe_zero, zero_mul]
    rw [sup, values_lam]
    have : (fun _ : α => (0 : Number)) '' D = {0} := Set.Nonempty.image_const hD 0
    rw [this, sSup_singleton]
  · exact antitone_inf D m _ (fun a b h => by
      show (n : Number) * b ≤ n * a
      rw [mul_comm, mul_comm (n : Number)]
      exact EReal.mul_le_mul_of_nonpos_right h (by exact_mod_cast hneg.le)) (continuousAt_mul_left n hneg.ne) hD

end Arithmetic

/-! ### `Σ` and `Π` -/

section SumProd

/-- Multiplication by a nonnegative finite number is additive on the extended reals. -/
noncomputable def mulLeftHom (n : ℝ) (hn : 0 ≤ n) : Number →+ Number where
  toFun := fun x => (n : Number) * x
  map_zero' := mul_zero _
  map_add' := fun x y => EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hn) (EReal.coe_ne_top n) x y

/-- `n×(Σv: D· m) = (Σv: D· n×m)`, for `0 ≤ n < ∞` and finite `D`. -/
theorem mul_sum (n : ℝ) (hn : 0 ≤ n) (hD : D.Finite) :
    (n : Number) * sum (lam D m) = sum (lam D fun v => n * m v) := by
  show (n : Number) * (∑ᶠ x ∈ D, m x) = ∑ᶠ x ∈ D, (n : Number) * m x
  rw [finsum_mem_eq_finite_toFinset_sum _ hD, finsum_mem_eq_finite_toFinset_sum _ hD]
  exact map_sum (mulLeftHom n hn) _ _

/-- `(Πv: D· m)^n = (Πv: D· m^n)`, for finite `D` and natural `n`. -/
theorem prod_pow (hD : D.Finite) (k : ℕ) : prod (lam D m) ^ k = prod (lam D fun v => m v ^ k) := by
  show (∏ᶠ x ∈ D, m x) ^ k = ∏ᶠ x ∈ D, m x ^ k
  rw [finprod_mem_eq_finite_toFinset_prod _ hD, finprod_mem_eq_finite_toFinset_prod _ hD]
  exact (Finset.prod_pow hD.toFinset k m).symm

end SumProd

/-! ### Extreme -/

/-- The bunch `real` of finite numbers. -/
def realBunch : Bunch Number := Set.range ((↑) : ℝ → Number)

/-- `(⇓n: real· n) = –∞`. -/
theorem inf_real : inf (lam realBunch id) = ⊥ := by
  rw [inf, values_lam, Set.image_id, sInf_eq_bot]
  intro b hb
  induction b using EReal.rec with
  | bot => exact absurd hb (lt_irrefl _)
  | coe r => exact ⟨r - 1, ⟨r - 1, rfl⟩, by exact_mod_cast (by linarith : r - 1 < r)⟩
  | top => exact ⟨0, ⟨0, rfl⟩, EReal.coe_lt_top 0⟩

/-- `(⇑n: real· n) = ∞`. -/
theorem sup_real : sup (lam realBunch id) = ⊤ := by
  rw [sup, values_lam, Set.image_id, sSup_eq_top]
  intro b hb
  induction b using EReal.rec with
  | bot => exact ⟨0, ⟨0, rfl⟩, EReal.bot_lt_coe 0⟩
  | coe r => exact ⟨r + 1, ⟨r + 1, rfl⟩, by exact_mod_cast (by linarith : r < r + 1)⟩
  | top => exact absurd hb (lt_irrefl _)

end Fn

end LaPToP.FunctionTheory
