import LaPToP.FunctionTheory.Functions
import LaPToP.BasicTheories.NumberLaws
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.CompleteLattice.Basic

/-!
# Quantifiers: `⇑ ⇓ Σ Π` and the laws of quantification

This module continues Section 3.1 (Quantifiers) of Eric Hehner's *A Practical
Theory of Programming* (aPToP) with the numeric quantifiers, and formalizes the
laws of the reference section "Quantifiers" (§11.3.8) for `∀ ∃ §` and `⇑ ⇓`.

## The model

For a numeric function `f : Fn α Number`, `⇑f` and `⇓f` are the least upper
bound and greatest lower bound of the *range* of `f` (`Fn.values f`), taken in
`Number = EReal`, a complete linear order. Thus `⇑` over `null` is `–∞` and `⇓`
over `null` is `∞`, exactly as the book's axioms say; Hehner's `↑`/`↓` are
`⊔`/`⊓` (`max`/`min`).

`Σf` and `Πf` are Mathlib's `finsum`/`finprod` over the domain. **These are
honest only for finite domains**: Mathlib's `∑ᶠ` is `0` (and `∏ᶠ` is `1`) when
the support is infinite, whereas the book's `Σn: nat+1· 1/2ⁿ = 1` is a
convergent series. The laws below that split a domain therefore carry
finiteness hypotheses, and no law here claims anything about infinite sums.

`∀p`, `∃p` are propositions and `§p` is a bunch, as in
`LaPToP.FunctionTheory.Functions`. Laws the book states for "any fixed domain"
are stated for `Fn.lam D _`; where the book's body is a nested quantification
(the Commutative and Semicommutative laws), it is written as iterated bounded
quantification, since `∀p` is a proposition and cannot be the `Binary` body of
another predicate. "`v` does not appear in `a`" means `a` is a constant.
-/

namespace LaPToP.FunctionTheory

open LaPToP.BasicTheories

universe u v

namespace Fn

variable {α : Type u} {β : Type v}

/-- The *range* of a function (aPToP §3.0): the elements obtained by applying
it to each element of its domain. -/
def values (f : Fn α β) : Bunch β := {y | ∃ x, ∃ h : x ∈ f.dom, f.apply x h = y}

/-- The range of `⟨v: D· b⟩` is the image of `D` under `b`. -/
theorem values_lam (D : Bunch α) (b : α → β) : (lam D b).values = b '' D := by
  ext y; simp [values, lam, apply]

/-- Unfolding `∀⟨v: D· b⟩`. -/
theorem all_lam (D : Bunch α) (b : α → Binary) : all (lam D b) ↔ ∀ x ∈ D, b x = true := Iff.rfl

/-- Unfolding `∃⟨v: D· b⟩`. -/
theorem ex_lam (D : Bunch α) (b : α → Binary) : ex (lam D b) ↔ ∃ x ∈ D, b x = true := by
  simp [ex, lam, apply]

/-- Unfolding `§⟨v: D· b⟩`. -/
theorem sols_lam (D : Bunch α) (b : α → Binary) : sols (lam D b) = {x | x ∈ D ∧ b x = true} := by
  ext x; simp [sols, lam, apply]

/-! ### The numeric quantifiers `⇑ ⇓ Σ Π` (aPToP §3.1) -/

/-- `⇑f`, the maximum (least upper bound) of the results of `f`. -/
noncomputable def sup (f : Fn α Number) : Number := sSup f.values

/-- `⇓f`, the minimum (greatest lower bound) of the results of `f`. -/
noncomputable def inf (f : Fn α Number) : Number := sInf f.values

/-- `Σf`, the sum of the results of `f` — for a finite domain (see the module
docstring). -/
noncomputable def sum (f : Fn α Number) : Number := ∑ᶠ (x) (h : x ∈ f.dom), f.body x h

/-- `Πf`, the product of the results of `f` — for a finite domain (see the
module docstring). -/
noncomputable def prod (f : Fn α Number) : Number := ∏ᶠ (x) (h : x ∈ f.dom), f.body x h

section NumericAxioms

variable (A B D : Bunch α) (n : α → Number) (b : α → Binary) (x : α)

/-- `⇑v: null· n = –∞`. -/
theorem sup_null : sup (lam Bunch.null n) = ⊥ := by simp [sup, values_lam]

/-- `⇓v: null· n = ∞`. -/
theorem inf_null : inf (lam Bunch.null n) = ⊤ := by simp [inf, values_lam]

/-- `⇑v: x· n = ⟨v: x· n⟩ x`. -/
theorem sup_elem : sup (lam (Bunch.elem x) n) = n x := by simp [sup, values_lam]

/-- `⇓v: x· n = ⟨v: x· n⟩ x`. -/
theorem inf_elem : inf (lam (Bunch.elem x) n) = n x := by simp [inf, values_lam]

/-- `⇑v: A, B· n = (⇑v: A· n) ↑ (⇑v: B· n)`. -/
theorem sup_union : sup (lam (A ∪ B) n) = sup (lam A n) ⊔ sup (lam B n) := by
  simp [sup, values_lam, Set.image_union, sSup_union]

/-- `⇓v: A, B· n = (⇓v: A· n) ↓ (⇓v: B· n)`. -/
theorem inf_union : inf (lam (A ∪ B) n) = inf (lam A n) ⊓ inf (lam B n) := by
  simp [inf, values_lam, Set.image_union, sInf_union]

/-- `↑` and `↓` are `max` and `min`. -/
theorem sup_eq_max (a b : Number) : a ⊔ b = max a b := rfl

/-- `⇑v: (§v: D· b)· n = ⇑v: D· if b then n else –∞`. -/
theorem sup_sols : sup (lam (sols (lam D b)) n) = sup (lam D fun v => if b v = true then n v else ⊥) := by
  simp only [sup, values_lam, sols_lam]
  apply le_antisymm
  · refine sSup_le_iff.2 ?_
    rintro y ⟨v, ⟨hv, hb⟩, rfl⟩
    exact le_sSup ⟨v, hv, by simp [hb]⟩
  · refine sSup_le_iff.2 ?_
    rintro y ⟨v, hv, rfl⟩
    by_cases hb : b v = true
    · simp only [hb, if_true]; exact le_sSup ⟨v, ⟨hv, hb⟩, rfl⟩
    · simp [hb]

/-- `⇓v: (§v: D· b)· n = ⇓v: D· if b then n else ∞`. -/
theorem inf_sols : inf (lam (sols (lam D b)) n) = inf (lam D fun v => if b v = true then n v else ⊤) := by
  simp only [inf, values_lam, sols_lam]
  apply le_antisymm
  · refine le_sInf_iff.2 ?_
    rintro y ⟨v, hv, rfl⟩
    by_cases hb : b v = true
    · simp only [hb, if_true]; exact sInf_le ⟨v, ⟨hv, hb⟩, rfl⟩
    · simp [hb]
  · refine le_sInf_iff.2 ?_
    rintro y ⟨v, ⟨hv, hb⟩, rfl⟩
    exact sInf_le ⟨v, hv, by simp [hb]⟩

/-- `Σv: null· n = 0`. -/
theorem sum_null : sum (lam Bunch.null n) = 0 := finsum_mem_empty

/-- `Σv: x· n = ⟨v: x· n⟩ x`. -/
theorem sum_elem : sum (lam (Bunch.elem x) n) = n x := finsum_mem_singleton

/-- `(Σv: A, B· n) + (Σv: A‘B· n) = (Σv: A· n) + (Σv: B· n)`, for finite `A`, `B`. -/
theorem sum_union_add_sum_inter (hA : A.Finite) (hB : B.Finite) :
    sum (lam (A ∪ B) n) + sum (lam (A ∩ B) n) = sum (lam A n) + sum (lam B n) :=
  finsum_mem_union_inter hA hB

/-- `Σv: (§v: D· b)· n = Σv: D· if b then n else 0`. -/
theorem sum_sols : sum (lam (sols (lam D b)) n) = sum (lam D fun v => if b v = true then n v else 0) := by
  show (∑ᶠ x ∈ sols (lam D b), n x) = ∑ᶠ x ∈ D, (if b x = true then n x else 0)
  rw [sols_lam,
    finsum_mem_inter_support_eq' (fun v => if b v = true then n v else 0) D {x | x ∈ D ∧ b x = true}]
  · exact (finsum_mem_congr rfl fun v (hv : v ∈ {x | x ∈ D ∧ b x = true}) => if_pos hv.2).symm
  · intro v hv
    have : b v = true := by
      by_contra h
      exact hv (by simp [h])
    simp [this]

/-- `Πv: null· n = 1`. -/
theorem prod_null : prod (lam Bunch.null n) = 1 := finprod_mem_empty

/-- `Πv: x· n = ⟨v: x· n⟩ x`. -/
theorem prod_elem : prod (lam (Bunch.elem x) n) = n x := finprod_mem_singleton

/-- `(Πv: A, B· n) × (Πv: A‘B· n) = (Πv: A· n) × (Πv: B· n)`, for finite `A`, `B`. -/
theorem prod_union_mul_prod_inter (hA : A.Finite) (hB : B.Finite) :
    prod (lam (A ∪ B) n) * prod (lam (A ∩ B) n) = prod (lam A n) * prod (lam B n) :=
  finprod_mem_union_inter hA hB

/-- `Πv: (§v: D· b)· n = Πv: D· if b then n else 1`. -/
theorem prod_sols : prod (lam (sols (lam D b)) n) = prod (lam D fun v => if b v = true then n v else 1) := by
  show (∏ᶠ x ∈ sols (lam D b), n x) = ∏ᶠ x ∈ D, (if b x = true then n x else 1)
  rw [sols_lam,
    finprod_mem_inter_mulSupport_eq' (fun v => if b v = true then n v else 1) D {x | x ∈ D ∧ b x = true}]
  · exact (finprod_mem_congr rfl fun v (hv : v ∈ {x | x ∈ D ∧ b x = true}) => if_pos hv.2).symm
  · intro v hv
    have : b v = true := by
      by_contra h
      exact hv (by simp [h])
    simp [this]

/-- `¢A = Σ(A→1)` (Cardinality), for finite `A`: both sides are the number of
elements of `A`. -/
theorem size_eq_sum_one (hA : A.Finite) :
    ∃ k : ℕ, Bunch.size A = k ∧ sum (lam A fun _ => (1 : Number)) = k := by
  refine ⟨hA.toFinset.card, hA.encard_eq_coe_toFinset_card, ?_⟩
  show (∑ᶠ x ∈ A, (1 : Number)) = _
  rw [finsum_mem_eq_finite_toFinset_sum _ hA]
  simp [Finset.sum_const]

end NumericAxioms

/-! ### Specialize and Generalize, Duality, Bounding, Extreme (aPToP §11.3.8) -/

section NumericLaws

variable (f : Fn α Number) (D : Bunch α) (m : α → Number) (n : Number) (x : α)

/-- `⇓f ≤ f x` for `x: ☐f` (Specialize). -/
theorem inf_le_apply (h : x ∈ f.domain) : inf f ≤ f.apply x h := sInf_le ⟨x, h, rfl⟩

/-- `f x ≤ ⇑f` for `x: ☐f` (Generalize). -/
theorem apply_le_sup (h : x ∈ f.domain) : f.apply x h ≤ sup f := le_sSup ⟨x, h, rfl⟩

/-- `–sSup S = sInf (–S)` in the extended reals. -/
theorem neg_sSup (S : Set Number) : -sSup S = sInf ((fun y => -y) '' S) := by
  apply le_antisymm
  · refine le_sInf_iff.2 ?_
    rintro y ⟨a, ha, rfl⟩
    exact EReal.neg_le_neg_iff.2 (le_sSup ha)
  · rw [EReal.le_neg]
    refine sSup_le_iff.2 fun a ha => ?_
    rw [EReal.le_neg]
    exact sInf_le ⟨a, ha, rfl⟩

/-- `–⇑v· n = ⇓v· –n` (Duality). -/
theorem neg_sup : -sup (lam D m) = inf (lam D fun v => -m v) := by
  simp only [sup, inf, values_lam, neg_sSup, Set.image_image]

/-- `–⇓v· n = ⇑v· –n` (Duality). -/
theorem neg_inf : -inf (lam D m) = sup (lam D fun v => -m v) := by
  rw [← _root_.neg_neg (sup _), neg_sup]
  simp only [_root_.neg_neg]

/-- `n ≥ (⇑v: D· m) = (∀v: D· n ≥ m)` (Bounding). -/
theorem sup_le_iff : sup (lam D m) ≤ n ↔ ∀ v ∈ D, m v ≤ n := by
  simp [sup, values_lam, sSup_le_iff]

/-- `n ≤ (⇓v: D· m) = (∀v: D· n ≤ m)` (Bounding). -/
theorem le_inf_iff : n ≤ inf (lam D m) ↔ ∀ v ∈ D, n ≤ m v := by
  simp [inf, values_lam, le_sInf_iff]

/-- `n > (⇓v: D· m) = (∃v: D· n > m)` (Bounding). -/
theorem inf_lt_iff : inf (lam D m) < n ↔ ∃ v ∈ D, m v < n := by
  simp [inf, values_lam, sInf_lt_iff]

/-- `n < (⇑v: D· m) = (∃v: D· n < m)` (Bounding). -/
theorem lt_sup_iff : n < sup (lam D m) ↔ ∃ v ∈ D, n < m v := by
  simp [sup, values_lam, lt_sSup_iff]

/-- `n > (⇑v: D· m) ⇒ (∀v: D· n > m)` (Bounding). -/
theorem forall_lt_of_sup_lt (h : sup (lam D m) < n) : ∀ v ∈ D, m v < n :=
  fun v hv => (le_sSup ⟨v, hv, rfl⟩ : m v ≤ sup (lam D m)).trans_lt h

/-- `n < (⇓v: D· m) ⇒ (∀v: D· n < m)` (Bounding). -/
theorem forall_lt_of_lt_inf (h : n < inf (lam D m)) : ∀ v ∈ D, n < m v :=
  fun v hv => h.trans_le (sInf_le ⟨v, hv, rfl⟩)

/-- `n ≥ (⇓v: D· m) ⇐ (∃v: D· n ≥ m)` (Bounding). -/
theorem inf_le_of_exists (h : ∃ v ∈ D, m v ≤ n) : inf (lam D m) ≤ n :=
  let ⟨v, hv, hm⟩ := h; (sInf_le ⟨v, hv, rfl⟩ : inf (lam D m) ≤ m v).trans hm

/-- `n ≤ (⇑v: D· m) ⇐ (∃v: D· n ≤ m)` (Bounding). -/
theorem le_sup_of_exists (h : ∃ v ∈ D, n ≤ m v) : n ≤ sup (lam D m) :=
  let ⟨v, hv, hm⟩ := h; hm.trans (le_sSup ⟨v, hv, rfl⟩)

/-- `(⇓n: int· n) = –∞` (Extreme): the integers are unbounded below. -/
theorem inf_int : inf (lam Bunch.int fun k : ℤ => ((k : ℝ) : Number)) = ⊥ := by
  rw [inf, values_lam, sInf_eq_bot]
  intro y hy
  induction y using EReal.rec with
  | bot => exact absurd hy (lt_irrefl _)
  | coe r => exact ⟨_, ⟨⌊r⌋ - 1, Set.mem_univ _, rfl⟩, by
      rw [EReal.coe_lt_coe_iff]; push_cast; linarith [Int.floor_le r]⟩
  | top => exact ⟨_, ⟨0, Set.mem_univ _, rfl⟩, by simp⟩

/-- `(⇑n: int· n) = ∞` (Extreme): the integers are unbounded above. -/
theorem sup_int : sup (lam Bunch.int fun k : ℤ => ((k : ℝ) : Number)) = ⊤ := by
  rw [sup, values_lam, sSup_eq_top]
  intro y hy
  induction y using EReal.rec with
  | bot => exact ⟨_, ⟨0, Set.mem_univ _, rfl⟩, by simp⟩
  | coe r => exact ⟨_, ⟨⌈r⌉ + 1, Set.mem_univ _, rfl⟩, by
      rw [EReal.coe_lt_coe_iff]; push_cast; linarith [Int.le_ceil r]⟩
  | top => exact absurd hy (lt_irrefl _)

/-- `n ≤ m = ∀k· k ≤ n ⇒ k ≤ m` (Connection). -/
theorem le_iff_forall_le_imp (n m : Number) : n ≤ m ↔ ∀ k : Number, k ≤ n → k ≤ m :=
  ⟨fun h _ hk => hk.trans h, fun h => h n le_rfl⟩

/-- `n ≤ m = ∀k· k < n ⇒ k < m` (Connection). -/
theorem le_iff_forall_lt_imp (n m : Number) : n ≤ m ↔ ∀ k : Number, k < n → k < m :=
  ⟨fun h _ hk => hk.trans_le h, fun h => le_of_not_gt fun hmn => lt_irrefl m (h m hmn)⟩

/-- `n ≤ m = ∀k· m ≤ k ⇒ n ≤ k` (Connection). -/
theorem le_iff_forall_le_imp' (n m : Number) : n ≤ m ↔ ∀ k : Number, m ≤ k → n ≤ k :=
  ⟨fun h _ hk => h.trans hk, fun h => h m le_rfl⟩

/-- `n ≤ m = ∀k· m < k ⇒ n < k` (Connection). -/
theorem le_iff_forall_lt_imp' (n m : Number) : n ≤ m ↔ ∀ k : Number, m < k → n < k :=
  ⟨fun h _ hk => h.trans_lt hk, fun h => le_of_not_gt fun hmn => lt_irrefl n (h n hmn)⟩

/-- `⇑r: f D· b = ⇑d: D· ⟨r: f D· b⟩ (f d)` (Change of Variable). -/
theorem sup_image (g : β → α) (E : Bunch β) : sup (lam (g '' E) m) = sup (lam E fun d => m (g d)) := by
  simp [sup, values_lam, Set.image_image]

/-- `⇓r: f D· b = ⇓d: D· ⟨r: f D· b⟩ (f d)` (Change of Variable). -/
theorem inf_image (g : β → α) (E : Bunch β) : inf (lam (g '' E) m) = inf (lam E fun d => m (g d)) := by
  simp [inf, values_lam, Set.image_image]

end NumericLaws

/-! ### Laws of `∀ ∃ §` (aPToP §11.3.8) -/

section LogicalLaws

variable (A B D E : Bunch α) (a : Binary) (b c p : α → Binary) (x : α)

/-- `∀v: (§v: D· b)· c = ∀v: D· b ⇒ c`. -/
theorem all_sols : all (lam (sols (lam D b)) c) ↔ all (lam D fun v => Binary.imp (b v) (c v)) := by
  simp only [all_lam, sols_lam, Set.mem_ofPred_eq, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  constructor
  · intro h v hv
    by_cases hb : b v = true
    · exact Or.inr (h v ⟨hv, hb⟩)
    · exact Or.inl (by simpa using hb)
  · rintro h v ⟨hv, hb⟩
    rcases h v hv with h' | h'
    · rw [hb] at h'; cases h'
    · exact h'

/-- `∃v: (§v: D· b)· c = ∃v: D· b ∧ c`. -/
theorem ex_sols : ex (lam (sols (lam D b)) c) ↔ ex (lam D fun v => b v && c v) := by
  simp only [ex_lam, sols_lam, Set.mem_ofPred_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨v, ⟨hv, hb⟩, hc⟩; exact ⟨v, hv, hb, hc⟩
  · rintro ⟨v, hv, hb, hc⟩; exact ⟨v, ⟨hv, hb⟩, hc⟩

/-- `§v: (§v: D· b)· c = §v: D· b ∧ c`. -/
theorem sols_sols : sols (lam (sols (lam D b)) c) = sols (lam D fun v => b v && c v) := by
  ext v; simp [sols_lam, and_assoc]

/-- `§v: A‘B· b = (§v: A· b) ‘ (§v: B· b)`. -/
theorem sols_inter : sols (lam (A ∩ B) b) = sols (lam A b) ∩ sols (lam B b) := by
  ext v; simp only [sols_lam, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto

/-- `A: B = ∀x: A· x: B` (Inclusion). -/
theorem subset_iff_all [DecidablePred (· ∈ B)] : A ⊆ B ↔ all (lam A fun v => decide (v ∈ B)) := by
  simp [all_lam, Set.subset_def]

/-- `A: B = ∀a: A· ∃b: B· a = b` (Bunch-Element Conversion). -/
theorem subset_iff_forall_exists : A ⊆ B ↔ ∀ a ∈ A, ∃ b ∈ B, a = b := by
  simp [Set.subset_def]

/-- `f A: g B = ∀a: A· ∃b: B· f a = g b` (Bunch-Element Conversion). -/
theorem image_subset_image_iff_forall_exists (f g : α → β) (A B : Bunch α) :
    f '' A ⊆ g '' B ↔ ∀ a ∈ A, ∃ b ∈ B, f a = g b := by
  simp only [Set.subset_def, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h a ha
    obtain ⟨b, hb, hfg⟩ := h a ha
    exact ⟨b, hb, hfg.symm⟩
  · intro h a ha
    obtain ⟨b, hb, hfg⟩ := h a ha
    exact ⟨b, hb, hfg.symm⟩

/-- `∀v· ⊤` (Identity). -/
theorem all_top : all (lam D fun _ => Binary.top) := fun _ _ => rfl

/-- `¬∃v· ⊥` (Identity). -/
theorem not_ex_bot : ¬ ex (lam D fun _ => Binary.bot) := by simp [ex_lam]

/-- `∀v: D· b = b` for `D ⧧ null` and `v` not in `b` (Idempotent). -/
theorem all_const (hD : D.Nonempty) : all (lam D fun _ => a) ↔ a = true :=
  ⟨fun h => let ⟨x, hx⟩ := hD; h x hx, fun h _ _ => h⟩

/-- `∃v: D· b = b` for `D ⧧ null` and `v` not in `b` (Idempotent). -/
theorem ex_const (hD : D.Nonempty) : ex (lam D fun _ => a) ↔ a = true := by
  rw [ex_lam]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => let ⟨x, hx⟩ := hD; ⟨x, hx, h⟩⟩

/-- `¬∀v· b = ∃v· ¬b` (Duality). -/
theorem not_all : ¬ all (lam D b) ↔ ex (lam D fun v => !b v) := by
  simp [all_lam, ex_lam]

/-- `¬∃v· b = ∀v· ¬b` (Duality). -/
theorem not_ex : ¬ ex (lam D b) ↔ all (lam D fun v => !b v) := by
  simp [all_lam, ex_lam]

/-- `a ∧ ∀v: D· b = ∀v: D· a ∧ b` for `D ⧧ null` (Distributive). -/
theorem and_all (hD : D.Nonempty) : a = true ∧ all (lam D b) ↔ all (lam D fun v => a && b v) := by
  simp only [all_lam, Bool.and_eq_true]
  obtain ⟨x, hx⟩ := hD
  exact ⟨fun ⟨ha, h⟩ v hv => ⟨ha, h v hv⟩, fun h => ⟨(h x hx).1, fun v hv => (h v hv).2⟩⟩

/-- `a ∧ ∃v: D· b = ∃v: D· a ∧ b` (Distributive; the book's proviso `D ⧧ null`
is not needed). -/
theorem and_ex : a = true ∧ ex (lam D b) ↔ ex (lam D fun v => a && b v) := by
  simp only [ex_lam, Bool.and_eq_true]
  constructor
  · rintro ⟨ha, v, hv, hb⟩; exact ⟨v, hv, ha, hb⟩
  · rintro ⟨v, hv, ha, hb⟩; exact ⟨ha, v, hv, hb⟩

/-- `a ∨ ∀v: D· b = ∀v: D· a ∨ b` (Distributive; the proviso is not needed). -/
theorem or_all : a = true ∨ all (lam D b) ↔ all (lam D fun v => a || b v) := by
  simp only [all_lam, Bool.or_eq_true]
  constructor
  · rintro (ha | h) v hv
    · exact Or.inl ha
    · exact Or.inr (h v hv)
  · intro h
    by_cases ha : a = true
    · exact Or.inl ha
    · exact Or.inr fun v hv => (h v hv).resolve_left ha

/-- `a ∨ ∃v: D· b = ∃v: D· a ∨ b` for `D ⧧ null` (Distributive). -/
theorem or_ex (hD : D.Nonempty) : a = true ∨ ex (lam D b) ↔ ex (lam D fun v => a || b v) := by
  simp only [ex_lam, Bool.or_eq_true]
  obtain ⟨x, hx⟩ := hD
  constructor
  · rintro (ha | ⟨v, hv, hb⟩)
    · exact ⟨x, hx, Or.inl ha⟩
    · exact ⟨v, hv, Or.inr hb⟩
  · rintro ⟨v, hv, ha | hb⟩
    · exact Or.inl ha
    · exact Or.inr ⟨v, hv, hb⟩

/-- `a ⇒ ∀v: D· b = ∀v: D· a ⇒ b` (Distributive; the proviso is not needed). -/
theorem imp_all : (a = true → all (lam D b)) ↔ all (lam D fun v => Binary.imp a (b v)) := by
  simp only [all_lam, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · intro h v hv
    by_cases ha : a = true
    · exact Or.inr (h ha v hv)
    · exact Or.inl (by simpa using ha)
  · intro h ha v hv
    rcases h v hv with h' | h'
    · rw [ha] at h'; cases h'
    · exact h'

/-- `a ⇒ ∃v: D· b = ∃v: D· a ⇒ b` for `D ⧧ null` (Distributive). -/
theorem imp_ex (hD : D.Nonempty) : (a = true → ex (lam D b)) ↔ ex (lam D fun v => Binary.imp a (b v)) := by
  simp only [ex_lam, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  obtain ⟨x, hx⟩ := hD
  constructor
  · intro h
    by_cases ha : a = true
    · obtain ⟨v, hv, hb⟩ := h ha; exact ⟨v, hv, Or.inr hb⟩
    · exact ⟨x, hx, Or.inl (by simpa using ha)⟩
  · rintro ⟨v, hv, ha | hb⟩ ha'
    · rw [ha'] at ha; cases ha
    · exact ⟨v, hv, hb⟩

/-- `a ⇐ ∃v: D· b = ∀v: D· a ⇐ b` (Antidistributive; the proviso is not needed). -/
theorem ex_imp : (ex (lam D b) → a = true) ↔ all (lam D fun v => Binary.rimp a (b v)) := by
  simp only [ex_lam, all_lam, Binary.rimp, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  constructor
  · intro h v hv
    by_cases hb : b v = true
    · exact Or.inr (h ⟨v, hv, hb⟩)
    · exact Or.inl (by simpa using hb)
  · rintro h ⟨v, hv, hb⟩
    rcases h v hv with h' | h'
    · rw [hb] at h'; cases h'
    · exact h'

/-- `a ⇐ ∀v: D· b = ∃v: D· a ⇐ b` for `D ⧧ null` (Antidistributive). -/
theorem all_imp (hD : D.Nonempty) : (all (lam D b) → a = true) ↔ ex (lam D fun v => Binary.rimp a (b v)) := by
  simp only [ex_lam, all_lam, Binary.rimp, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  obtain ⟨x, hx⟩ := hD
  constructor
  · intro h
    by_cases hall : ∀ v ∈ D, b v = true
    · exact ⟨x, hx, Or.inr (h hall)⟩
    · push Not at hall
      obtain ⟨v, hv, hb⟩ := hall
      exact ⟨v, hv, Or.inl (by simpa using hb)⟩
  · rintro ⟨v, hv, hb | ha⟩ hall
    · rw [hall v hv] at hb; cases hb
    · exact ha

/-- `⟨v: D· b⟩ x ∧ ∃v: D· b = ⟨v: D· b⟩ x` for `x: D` (Absorption). -/
theorem apply_and_ex (hx : x ∈ D) : b x = true ∧ ex (lam D b) ↔ b x = true :=
  ⟨And.left, fun h => ⟨h, (ex_lam D b).2 ⟨x, hx, h⟩⟩⟩

/-- `⟨v: D· b⟩ x ∨ ∀v: D· b = ⟨v: D· b⟩ x` for `x: D` (Absorption). -/
theorem apply_or_all (hx : x ∈ D) : b x = true ∨ all (lam D b) ↔ b x = true :=
  ⟨fun h => h.elim id fun h' => h' x hx, Or.inl⟩

/-- `⟨v: D· b⟩ x ∧ ∀v: D· b = ∀v: D· b` for `x: D` (Absorption). -/
theorem apply_and_all (hx : x ∈ D) : b x = true ∧ all (lam D b) ↔ all (lam D b) :=
  ⟨And.right, fun h => ⟨h x hx, h⟩⟩

/-- `⟨v: D· b⟩ x ∨ ∃v: D· b = ∃v: D· b` for `x: D` (Absorption). -/
theorem apply_or_ex (hx : x ∈ D) : b x = true ∨ ex (lam D b) ↔ ex (lam D b) :=
  ⟨fun h => h.elim (fun h' => (ex_lam D b).2 ⟨x, hx, h'⟩) id, Or.inr⟩

/-- `∀v· a ∧ b = (∀v· a) ∧ (∀v· b)` (Splitting). -/
theorem all_and : all (lam D fun v => b v && c v) ↔ all (lam D b) ∧ all (lam D c) := by
  simp only [all_lam, Bool.and_eq_true]
  exact ⟨fun h => ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩,
    fun h v hv => ⟨h.1 v hv, h.2 v hv⟩⟩

/-- `∃v· a ∧ b ⇒ (∃v· a) ∧ (∃v· b)` (Splitting). -/
theorem ex_and : ex (lam D fun v => b v && c v) → ex (lam D b) ∧ ex (lam D c) := by
  simp only [ex_lam, Bool.and_eq_true]
  rintro ⟨v, hv, hb, hc⟩
  exact ⟨⟨v, hv, hb⟩, ⟨v, hv, hc⟩⟩

/-- `∀v· a ∨ b ⇐ (∀v· a) ∨ (∀v· b)` (Splitting). -/
theorem all_or : all (lam D b) ∨ all (lam D c) → all (lam D fun v => b v || c v) := by
  simp only [all_lam, Bool.or_eq_true]
  rintro (h | h) v hv
  · exact Or.inl (h v hv)
  · exact Or.inr (h v hv)

/-- `∃v· a ∨ b = (∃v· a) ∨ (∃v· b)` (Splitting). -/
theorem ex_or : ex (lam D fun v => b v || c v) ↔ ex (lam D b) ∨ ex (lam D c) := by
  simp only [ex_lam, Bool.or_eq_true]
  constructor
  · rintro ⟨v, hv, hb | hc⟩
    · exact Or.inl ⟨v, hv, hb⟩
    · exact Or.inr ⟨v, hv, hc⟩
  · rintro (⟨v, hv, hb⟩ | ⟨v, hv, hc⟩)
    · exact ⟨v, hv, Or.inl hb⟩
    · exact ⟨v, hv, Or.inr hc⟩

/-- `∀v· a ⇒ b ⇒ (∀v· a) ⇒ (∀v· b)` (Splitting). -/
theorem all_imp_all : all (lam D fun v => Binary.imp (b v) (c v)) → all (lam D b) → all (lam D c) := by
  simp only [all_lam, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  intro h hb v hv
  rcases h v hv with h' | h'
  · rw [hb v hv] at h'; cases h'
  · exact h'

/-- `∀v· a ⇒ b ⇒ (∃v· a) ⇒ (∃v· b)` (Splitting). -/
theorem all_imp_ex : all (lam D fun v => Binary.imp (b v) (c v)) → ex (lam D b) → ex (lam D c) := by
  simp only [all_lam, ex_lam, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  rintro h ⟨v, hv, hb⟩
  rcases h v hv with h' | h'
  · rw [hb] at h'; cases h'
  · exact ⟨v, hv, h'⟩

/-- `∀v· a = b ⇒ (∀v· a) = (∀v· b)` (Splitting). -/
theorem all_beq_all : all (lam D fun v => b v == c v) → (all (lam D b) ↔ all (lam D c)) := by
  simp only [all_lam, beq_iff_eq]
  intro h
  exact ⟨fun hb v hv => (h v hv).symm.trans (hb v hv), fun hc v hv => (h v hv).trans (hc v hv)⟩

/-- `∀v· a = b ⇒ (∃v· a) = (∃v· b)` (Splitting). -/
theorem all_beq_ex : all (lam D fun v => b v == c v) → (ex (lam D b) ↔ ex (lam D c)) := by
  simp only [all_lam, ex_lam, beq_iff_eq]
  intro h
  exact ⟨fun ⟨v, hv, hb⟩ => ⟨v, hv, (h v hv).symm.trans hb⟩,
    fun ⟨v, hv, hc⟩ => ⟨v, hv, (h v hv).trans hc⟩⟩

/-- `∀v· ∀w· b = ∀w· ∀v· b` (Commutative), as iterated bounded quantification. -/
theorem forall_forall_comm (q : α → α → Prop) :
    (∀ v ∈ D, ∀ w ∈ E, q v w) ↔ ∀ w ∈ E, ∀ v ∈ D, q v w :=
  ⟨fun h w hw v hv => h v hv w hw, fun h v hv w hw => h w hw v hv⟩

/-- `∃v· ∃w· b = ∃w· ∃v· b` (Commutative), as iterated bounded quantification. -/
theorem exists_exists_comm (q : α → α → Prop) :
    (∃ v ∈ D, ∃ w ∈ E, q v w) ↔ ∃ w ∈ E, ∃ v ∈ D, q v w :=
  ⟨fun ⟨v, hv, w, hw, h⟩ => ⟨w, hw, v, hv, h⟩, fun ⟨w, hw, v, hv, h⟩ => ⟨v, hv, w, hw, h⟩⟩

/-- `∃v· ∀w· b ⇒ ∀w· ∃v· b` (Semicommutative). -/
theorem exists_forall_imp (q : α → α → Prop) :
    (∃ v ∈ D, ∀ w ∈ E, q v w) → ∀ w ∈ E, ∃ v ∈ D, q v w :=
  fun ⟨v, hv, h⟩ w hw => ⟨v, hv, h w hw⟩

/-- `∀x· ∃y· p x y = ∃f· ∀x· p x (f x)` (Semicommutative): a choice function
for `x: D` into `E`. -/
theorem forall_exists_iff_exists_fun [Nonempty β] (E : Bunch β) (q : α → β → Prop) :
    (∀ x ∈ D, ∃ y ∈ E, q x y) ↔ ∃ f : α → β, ∀ x ∈ D, f x ∈ E ∧ q x (f x) := by
  constructor
  · intro h
    classical
    refine ⟨fun x => if hx : x ∈ D then Classical.choose (h x hx) else Classical.arbitrary β,
      fun x hx => ?_⟩
    simp only [dif_pos hx]
    exact Classical.choose_spec (h x hx)
  · rintro ⟨f, hf⟩ x hx
    exact ⟨f x, (hf x hx).1, (hf x hx).2⟩

/-- `§v: D· ⊤ = D` (Solution). -/
theorem sols_top : sols (lam D fun _ => Binary.top) = D := by
  ext v; simp [sols_lam]

/-- `§v: D· ⊥ = null` (Solution). -/
theorem sols_bot : sols (lam D fun _ => Binary.bot) = Bunch.null := by
  ext v; simp [sols_lam]

/-- `(§v· b): (§v· c) = ∀v· b ⇒ c` (Solution). -/
theorem sols_subset_sols : sols (lam D b) ⊆ sols (lam D c) ↔ all (lam D fun v => Binary.imp (b v) (c v)) := by
  simp only [sols_lam, all_lam, Set.subset_def, Set.mem_ofPred_eq, Binary.imp, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, and_imp]
  constructor
  · intro h v hv
    by_cases hb : b v = true
    · exact Or.inr (h v hv hb).2
    · exact Or.inl (by simpa using hb)
  · intro h v hv hb
    refine ⟨hv, ?_⟩
    rcases h v hv with h' | h'
    · rw [hb] at h'; cases h'
    · exact h'

/-- `(§v· b), (§v· c) = §v· b ∨ c` (Solution). -/
theorem sols_union_sols : sols (lam D b) ∪ sols (lam D c) = sols (lam D fun v => b v || c v) := by
  ext v; simp only [sols_lam, Set.mem_union, Set.mem_ofPred_eq, Bool.or_eq_true]; tauto

/-- `(§v· b) ‘ (§v· c) = §v· b ∧ c` (Solution). -/
theorem sols_inter_sols : sols (lam D b) ∩ sols (lam D c) = sols (lam D fun v => b v && c v) := by
  ext v; simp only [sols_lam, Set.mem_inter_iff, Set.mem_ofPred_eq, Bool.and_eq_true]; tauto

/-- `∀f = ((§f) = (☐f))` (Solution). -/
theorem all_iff_sols_eq_domain (q : Pred α) : all q ↔ q.sols = q.domain := by
  constructor
  · intro h
    exact Set.Subset.antisymm (sols_subset_domain q) fun x hx => ⟨hx, h x hx⟩
  · intro h x hx
    obtain ⟨_, hq⟩ : x ∈ q.sols := h ▸ hx
    exact hq

/-- `∃f = ((§f) ⧧ null)` (Solution). -/
theorem ex_iff_sols_ne_null (q : Pred α) : ex q ↔ q.sols ≠ Bunch.null := by
  rw [← Set.nonempty_iff_ne_empty]
  exact ⟨fun ⟨x, h, hq⟩ => ⟨x, h, hq⟩, fun ⟨x, h, hq⟩ => ⟨x, h, hq⟩⟩

/-- `A: B ⇒ (∀v: A· b) ⇐ (∀v: B· b)` (Domain Change). -/
theorem all_of_subset (h : A ⊆ B) : all (lam B b) → all (lam A b) :=
  fun hB v hv => hB v (h hv)

/-- `A: B ⇒ (∃v: A· b) ⇒ (∃v: B· b)` (Domain Change). -/
theorem ex_of_subset (h : A ⊆ B) : ex (lam A b) → ex (lam B b) := by
  simp only [ex_lam]
  rintro ⟨v, hv, hb⟩
  exact ⟨v, h hv, hb⟩

/-- `∀v: A· v: B ⇒ p = ∀v: A‘B· p` (Domain Change). -/
theorem all_mem_imp [DecidablePred (· ∈ B)] :
    all (lam A fun v => Binary.imp (decide (v ∈ B)) (p v)) ↔ all (lam (A ∩ B) p) := by
  simp only [all_lam, Binary.imp, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, Set.mem_inter_iff, and_imp]
  constructor
  · intro h v hvA hvB
    exact (h v hvA).resolve_left (not_not.2 hvB)
  · intro h v hvA
    by_cases hvB : v ∈ B
    · exact Or.inr (h v hvA hvB)
    · exact Or.inl hvB

/-- `∃v: A· v: B ∧ p = ∃v: A‘B· p` (Domain Change). -/
theorem ex_mem_and [DecidablePred (· ∈ B)] :
    ex (lam A fun v => decide (v ∈ B) && p v) ↔ ex (lam (A ∩ B) p) := by
  simp only [ex_lam, Bool.and_eq_true, decide_eq_true_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hvA, hvB, hp⟩; exact ⟨v, ⟨hvA, hvB⟩, hp⟩
  · rintro ⟨v, ⟨hvA, hvB⟩, hp⟩; exact ⟨v, hvA, hvB, hp⟩

/-- `∀r: f D· b = ∀d: D· ⟨r: f D· b⟩ (f d)` (Change of Variable). -/
theorem all_image (g : β → α) (E : Bunch β) : all (lam (g '' E) b) ↔ all (lam E fun d => b (g d)) := by
  simp [all_lam]

/-- `∃r: f D· b = ∃d: D· ⟨r: f D· b⟩ (f d)` (Change of Variable). -/
theorem ex_image (g : β → α) (E : Bunch β) : ex (lam (g '' E) b) ↔ ex (lam E fun d => b (g d)) := by
  simp [ex_lam]

end LogicalLaws

end Fn

end LaPToP.FunctionTheory
