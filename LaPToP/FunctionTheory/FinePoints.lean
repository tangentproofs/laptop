import LaPToP.FunctionTheory.Quantifiers
import LaPToP.DataStructures.Lists
import Mathlib.Algebra.BigOperators.Fin

/-!
# Function Fine Points and List as Function

This module formalizes Sections 3.2 (Function Fine Points, including 3.2.0
Function Inclusion and Equality) and 3.3 (List as Function) of Eric Hehner's
*A Practical Theory of Programming* (aPToP).

## The model

* A function applied to a *bunch* of arguments distributes over bunch union:
  `f A` is the bunch of results `f x` for `x : A` (`Fn.applyBunch`, meaningful
  for `A : ☐f`). A *bunch of functions* applied to an argument likewise
  (`Fn.applyFns`).
* A function "in which the body is a bunch" is `Fn α (Bunch β)`. It is *total*
  when every result is nonempty, *deterministic* when every result has at most
  one element, *partial* and *nondeterministic* otherwise. An ordinary
  function is viewed as a deterministic one by `Fn.toBunch` (results are
  elementary bunches).
* The Function Inclusion Law defines `f : g` for bunch-valued functions
  (`Fn.Incl`); `A→B` is `⟨n: A· B⟩` (`Fn.arrowB`), and, in the book's other
  reading, "the bunch of all functions whose domain includes `A` and whose
  result is included in `B`" (`Fn.arrowSet`).
* A list `L` is viewed as the function `⟨n: ☐L· L n⟩` (`HList.toFn`); the
  book's coincidences between list and function notions are proved for it.

One honesty note: the book's Arrow law `A→B : C→D = A::C ∧ B:D` fails when
`C = null` and `B` is not included in `D` (the left side is then vacuously
true, since `f : null→D` for every `f`); we prove the corrected form with the
proviso `C ⧧ null` on the second conjunct.
-/

namespace LaPToP.FunctionTheory

open LaPToP.BasicTheories LaPToP.DataStructures
open scoped Pointwise

universe u v w

namespace Fn

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Functions applied to bunches (aPToP §3.2) -/

/-- `f A`, a function applied to a bunch of arguments `A : ☐f`: the bunch of
results `f x` for `x : A`. -/
def applyBunch (f : Fn α β) (A : Bunch α) : Bunch β :=
  {y | ∃ x, ∃ h : x ∈ f.dom, x ∈ A ∧ f.apply x h = y}

/-- `F x`, a bunch of functions applied to an argument: the bunch of results. -/
def applyFns (F : Bunch (Fn α β)) (x : α) : Bunch β :=
  {y | ∃ f ∈ F, ∃ h : x ∈ f.dom, f.apply x h = y}

section Distribution

variable (f : Fn α β) (A B : Bunch α) (x : α)

/-- `f null = null`. -/
theorem applyBunch_null : f.applyBunch Bunch.null = Bunch.null := by
  ext y; simp [applyBunch]

/-- `f (A, B) = f A, f B`. -/
theorem applyBunch_union : f.applyBunch (A ∪ B) = f.applyBunch A ∪ f.applyBunch B := by
  ext y; simp only [applyBunch, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨x, h, hx | hx, rfl⟩
    · exact Or.inl ⟨x, h, hx, rfl⟩
    · exact Or.inr ⟨x, h, hx, rfl⟩
  · rintro (⟨x, h, hx, rfl⟩ | ⟨x, h, hx, rfl⟩)
    · exact ⟨x, h, Or.inl hx, rfl⟩
    · exact ⟨x, h, Or.inr hx, rfl⟩

/-- `f x = f x`: applied to an elementary bunch, `f` gives the elementary
result (the Application Axiom in bunch form). -/
theorem applyBunch_elem (h : x ∈ f.domain) : f.applyBunch (Bunch.elem x) = Bunch.elem (f.apply x h) := by
  ext y; simp only [applyBunch, Set.mem_ofPred_eq, Bunch.elem, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x', h', rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨x, h, rfl, rfl⟩

/-- "The range of function `f` is `f (☐f)`." -/
theorem values_eq_applyBunch_domain : f.values = f.applyBunch f.domain := by
  ext y; simp only [values, applyBunch, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, h, rfl⟩; exact ⟨x, h, h, rfl⟩
  · rintro ⟨x, h, -, rfl⟩; exact ⟨x, h, rfl⟩

/-- `f (§g) = §y: f (☐g)· ∃x: ☐g· f x = y ∧ g x`, for a predicate `g` with
`☐g : ☐f` (the solution quantifier written as set-builder notation). -/
theorem applyBunch_sols (g : Pred α) (hg : g.domain ⊆ f.domain) :
    f.applyBunch g.sols =
      {y | y ∈ f.applyBunch g.domain ∧ ∃ x, ∃ h : x ∈ g.domain, f.apply x (hg h) = y ∧ g.apply x h = true} := by
  ext y; simp only [applyBunch, Set.mem_ofPred_eq, mem_sols]
  constructor
  · rintro ⟨x, h, ⟨hx, hgx⟩, rfl⟩; exact ⟨⟨x, h, hx, rfl⟩, x, hx, rfl, hgx⟩
  · rintro ⟨-, x, hx, rfl, hgx⟩; exact ⟨x, hg hx, ⟨hx, hgx⟩, rfl⟩

/-- `(f, g) x = f x, g x`: a union of functions applied to an argument gives
the union of the results. -/
theorem applyFns_union (F G : Bunch (Fn α β)) : applyFns (F ∪ G) x = applyFns F x ∪ applyFns G x := by
  ext y; simp only [applyFns, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨f, hf | hf, h, rfl⟩
    · exact Or.inl ⟨f, hf, h, rfl⟩
    · exact Or.inr ⟨f, hf, h, rfl⟩
  · rintro (⟨f, hf, h, rfl⟩ | ⟨f, hf, h, rfl⟩)
    · exact ⟨f, Or.inl hf, h, rfl⟩
    · exact ⟨f, Or.inr hf, h, rfl⟩

/-- An elementary bunch of functions applied to an argument gives the
elementary result. -/
theorem applyFns_elem (h : x ∈ f.domain) : applyFns (Bunch.elem f) x = Bunch.elem (f.apply x h) := by
  ext y; simp only [applyFns, Bunch.elem, Set.mem_singleton_iff]
  constructor
  · rintro ⟨f', rfl, h', rfl⟩; rfl
  · rintro rfl; exact ⟨f, rfl, h, rfl⟩

/-- The book's example: `double = ⟨n: nat· n+n⟩` applied to `2, 3` gives `4, 6`. -/
def double : Fn ℤ ℤ := lam Bunch.nat fun n => n + n

/-- `double (2, 3) = 4, 6`. -/
theorem double_two_three : double.applyBunch (Bunch.elem 2 ∪ Bunch.elem 3) = Bunch.elem 4 ∪ Bunch.elem 6 := by
  ext y
  simp only [applyBunch, double, lam, apply, Bunch.nat, Bunch.elem, Set.mem_ofPred_eq,
    Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, -, rfl | rfl, rfl⟩ <;> norm_num
  · rintro (rfl | rfl)
    · exact ⟨2, by norm_num, Or.inl rfl, by norm_num⟩
    · exact ⟨3, by norm_num, Or.inr rfl, by norm_num⟩

/-- `f (if b then x else y) = if b then f x else f y` (Reference §11.3.7), for `x`, `y` in the domain. -/
theorem apply_ite (b : Prop) [Decidable b] (y : α) (hx : x ∈ f.domain) (hy : y ∈ f.domain)
    (h : (if b then x else y) ∈ f.domain) :
    f.apply (if b then x else y) h = if b then f.apply x hx else f.apply y hy := by
  split_ifs <;> rfl

/-- `(if b then f else g) x = if b then f x else g x` (Reference §11.3.7), for `x` in both domains. -/
theorem ite_apply (g : Fn α β) (b : Prop) [Decidable b] (hf : x ∈ f.domain) (hg : x ∈ g.domain)
    (h : x ∈ (if b then f else g).domain) :
    (if b then f else g).apply x h = if b then f.apply x hf else g.apply x hg := by
  split_ifs <;> rfl

end Distribution

/-! ### Partial, total, deterministic, nondeterministic (aPToP §3.2) -/

/-- `n : nat` for `0 ≤ n`. -/
theorem mem_nat_of_nonneg {n : ℤ} (h : 0 ≤ n) : n ∈ Bunch.nat := h

/-- A bunch-valued function is *total* when it always produces at least one result. -/
def Total (f : Fn α (Bunch β)) : Prop := ∀ x (h : x ∈ f.dom), (f.apply x h).Nonempty

/-- A bunch-valued function is *partial* when it sometimes produces no result. -/
def Partial (f : Fn α (Bunch β)) : Prop := ¬ Total f

/-- A bunch-valued function is *deterministic* when it always produces at most one result. -/
def Deterministic (f : Fn α (Bunch β)) : Prop := ∀ x (h : x ∈ f.dom), (f.apply x h).Subsingleton

/-- A bunch-valued function is *nondeterministic* when it sometimes produces more than one result. -/
def Nondeterministic (f : Fn α (Bunch β)) : Prop := ¬ Deterministic f

/-- An ordinary function viewed as a bunch-valued one: each result is an
elementary bunch. -/
def toBunch (f : Fn α β) : Fn α (Bunch β) := ⟨f.dom, fun x h => Bunch.elem (f.apply x h)⟩

/-- An ordinary function is total. -/
theorem total_toBunch (f : Fn α β) : Total f.toBunch := fun x h => ⟨f.apply x h, rfl⟩

/-- An ordinary function is deterministic. -/
theorem deterministic_toBunch (f : Fn α β) : Deterministic f.toBunch :=
  fun _ _ => Set.subsingleton_singleton

/-- `⟨n: nat· n, n+1⟩`, mapping each natural number to two natural numbers. -/
def pair : Fn ℤ (Bunch ℤ) := lam Bunch.nat fun n => Bunch.elem n ∪ Bunch.elem (n + 1)

/-- `⟨n: nat· n, n+1⟩ 3 = 3, 4`. -/
theorem pair_three : pair.apply 3 (mem_nat_of_nonneg (by norm_num)) = Bunch.elem 3 ∪ Bunch.elem 4 := rfl

/-- `⟨n: nat· n, n+1⟩` is total. -/
theorem total_pair : Total pair := fun n _ => ⟨n, Or.inl rfl⟩

/-- `⟨n: nat· n, n+1⟩` is nondeterministic. -/
theorem nondeterministic_pair : Nondeterministic pair := fun h =>
  absurd (h 0 (mem_nat_of_nonneg le_rfl) (Or.inl rfl) (Or.inr rfl)) (by decide)

/-- `⟨n: nat· 0,..n⟩`, "both partial and nondeterministic". -/
def below : Fn ℤ (Bunch ℤ) := lam Bunch.nat fun n => Bunch.interval 0 n

/-- `⟨n: nat· 0,..n⟩` is partial: at `0` it produces no result. -/
theorem partial_below : Partial below := fun h => by
  obtain ⟨y, hy⟩ := h 0 (mem_nat_of_nonneg le_rfl)
  simp [below, lam, apply, Bunch.interval] at hy

/-- `⟨n: nat· 0,..n⟩` is nondeterministic: at `2` it produces `0` and `1`. -/
theorem nondeterministic_below : Nondeterministic below := fun h =>
  absurd (h 2 (mem_nat_of_nonneg (by norm_num)) (by simp [below, lam, apply, Bunch.interval])
    (by simp [below, lam, apply, Bunch.interval])) (by decide : (0 : ℤ) ≠ 1)

/-! ### Function Inclusion and Equality (aPToP §3.2.0) -/

/-- `f: g`, the Function Inclusion Law: `☐f :: ☐g ∧ ∀x: ☐g· f x : g x`. -/
def Incl (f g : Fn α (Bunch β)) : Prop :=
  g.dom ⊆ f.dom ∧ ∀ x (hg : x ∈ g.dom) (hf : x ∈ f.dom), f.apply x hf ⊆ g.apply x hg

/-- `A→B` as a function: `⟨n: A· B⟩`, the nondeterministic function whose
result, for each element of `A`, is the bunch `B`. -/
def arrowB (A : Bunch α) (B : Bunch β) : Fn α (Bunch β) := lam A fun _ => B

/-- `A→B` as a bunch of functions: "the bunch of all functions whose domain
includes `A` and whose result is included in `B`". -/
def arrowSet (A : Bunch α) (B : Bunch β) : Bunch (Fn α β) :=
  {g | A ⊆ g.dom ∧ ∀ x, x ∈ A → ∀ (hg : x ∈ g.dom), g.apply x hg ∈ B}

section Inclusion

variable (f g : Fn α (Bunch β)) (A C : Bunch α) (B D : Bunch β)

/-- `f = g = ☐f = ☐g ∧ ∀x: ☐f· f x = g x` (function equality). -/
theorem eq_iff (f g : Fn α β) :
    f = g ↔ f.domain = g.domain ∧ ∀ x (hf : x ∈ f.domain) (hg : x ∈ g.domain), f.apply x hf = g.apply x hg :=
  ⟨fun h => by subst h; exact ⟨rfl, fun _ _ _ => rfl⟩, fun ⟨hd, hb⟩ => Fn.ext hd hb⟩

/-- Function inclusion both ways round is function equality. -/
theorem incl_antisymm (h₁ : Incl f g) (h₂ : Incl g f) : f = g :=
  Fn.ext (Set.Subset.antisymm h₂.1 h₁.1) fun x hf hg =>
    Set.Subset.antisymm (h₁.2 x hg hf) (h₂.2 x hf hg)

/-- `f: f` (reflexivity of function inclusion). -/
theorem incl_refl : Incl f f := ⟨le_rfl, fun _ _ _ => le_rfl⟩

/-- `f: A→B = ☐f :: A ∧ f A : B`: the results of `f` on `A` are included in `B`. -/
theorem incl_arrowB : Incl f (arrowB A B) ↔ A ⊆ f.dom ∧ ∀ x, x ∈ A → ∀ (hf : x ∈ f.dom), f.apply x hf ⊆ B :=
  Iff.rfl

/-- `g: A→B` for an ordinary function `g`: `☐g :: A ∧ g A : B`. -/
theorem mem_arrowSet_iff (g : Fn α β) : g ∈ arrowSet A B ↔ A ⊆ g.dom ∧ g.applyBunch A ⊆ B := by
  simp only [arrowSet, Set.mem_ofPred_eq, applyBunch, Set.subset_def]
  constructor
  · rintro ⟨hA, h⟩
    exact ⟨hA, fun y ⟨x, hg, hx, hy⟩ => hy ▸ h x hx hg⟩
  · rintro ⟨hA, h⟩
    exact ⟨hA, fun x hx hg => h _ ⟨x, hg, hx, rfl⟩⟩

/-- The two readings of `A→B` agree: `g: A→B` as inclusion of `g` in the
function `A→B` is membership of `g` in the bunch `A→B`. -/
theorem incl_toBunch_arrowB_iff (g : Fn α β) : Incl g.toBunch (arrowB A B) ↔ g ∈ arrowSet A B :=
  and_congr Iff.rfl (forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    Set.singleton_subset_iff)

/-- `f: null→A` (Arrow). -/
theorem incl_arrowB_null : Incl f (arrowB Bunch.null B) :=
  ⟨Set.empty_subset _, fun x hx => absurd hx (Set.notMem_empty x)⟩

/-- `A→B : C→D = A::C ∧ B:D` (Arrow), corrected: the second conjunct is needed
only when `C ⧧ null` (for `C = null` the inclusion holds vacuously). -/
theorem arrowB_incl_arrowB : Incl (arrowB A B) (arrowB C D) ↔ C ⊆ A ∧ (C.Nonempty → B ⊆ D) := by
  simp only [Incl, arrowB, lam, apply]
  constructor
  · rintro ⟨hCA, h⟩
    exact ⟨hCA, fun ⟨x, hx⟩ => h x hx (hCA hx)⟩
  · rintro ⟨hCA, h⟩
    exact ⟨hCA, fun x hx _ => h ⟨x, hx⟩⟩

/-- `(A, B)→(C‘D) : A→C` (Arrow). -/
theorem arrowB_union_inter_incl : Incl (arrowB (A ∪ C) (B ∩ D)) (arrowB A B) :=
  ⟨Set.subset_union_left, fun _ _ _ => Set.inter_subset_left⟩

/-- `A→C : (A‘B)→(C, D)` (Arrow). -/
theorem arrowB_incl_inter_union : Incl (arrowB A B) (arrowB (A ∩ C) (B ∪ D)) :=
  ⟨Set.inter_subset_left, fun _ _ _ => Set.subset_union_left⟩

open Classical in
/-- `(A, B)→C = A→C | B→C` (Arrow). -/
theorem arrowB_union_eq_orElse : arrowB (A ∪ C) B = orElse (arrowB A B) (arrowB C B) :=
  Fn.ext rfl fun x _ _ => by
    show B = if _ : x ∈ A then B else B
    split <;> rfl

/-- `suc = ⟨n: nat· n+1⟩`, the successor function on the natural numbers. -/
def suc : Fn ℤ ℤ := lam Bunch.nat fun n => n + 1

/-- `suc 3 = 4`. -/
theorem suc_three : suc.apply 3 (mem_nat_of_nonneg (by norm_num)) = 4 := rfl

/-- `suc: nat→nat`, the book's worked proof by the Function Inclusion Law. -/
theorem suc_incl : suc ∈ arrowSet Bunch.nat Bunch.nat := by
  rw [mem_arrowSet_iff]
  refine ⟨le_rfl, ?_⟩
  rintro y ⟨n, hn, -, rfl⟩
  simp only [Bunch.nat, Set.mem_ofPred_eq, suc, lam, apply] at hn ⊢
  omega

/-- `even: int→bin`. -/
theorem even_incl : even ∈ arrowSet Bunch.int Bunch.bin :=
  (mem_arrowSet_iff _ _ _).2 ⟨le_rfl, fun _ _ => Set.mem_univ _⟩

/-- `odd: int→bin`. -/
theorem odd_incl : odd ∈ arrowSet Bunch.int Bunch.bin :=
  (mem_arrowSet_iff _ _ _).2 ⟨le_rfl, fun _ _ => Set.mem_univ _⟩

/-- `divides: (nat+1)→int→bin`. -/
theorem divides_incl : divides ∈ arrowSet (Bunch.nat + Bunch.elem 1) (arrowSet Bunch.int Bunch.bin) := by
  rw [mem_arrowSet_iff]
  refine ⟨le_rfl, ?_⟩
  rintro g ⟨n, hn, -, rfl⟩
  exact (mem_arrowSet_iff _ _ _).2 ⟨le_rfl, fun _ _ => Set.mem_univ _⟩

end Inclusion

end Fn

end LaPToP.FunctionTheory

/-! ### List as Function (aPToP §3.3)

"A list `L` has much in common with the function `⟨n: ☐L· L n⟩`." -/

namespace LaPToP.DataStructures.HList

open LaPToP.BasicTheories LaPToP.FunctionTheory

universe u v

variable {α : Type u} [Inhabited α]

/-- `⟨n: ☐L· L n⟩`, a list viewed as a function on its domain. -/
def toFn (L : HList α) : Fn ℕ α := Fn.lam L.domain fun n => L.at n

variable (L M : HList α) (m : ℕ)

/-- `L m = ⟨n: ☐L· L n⟩ m`: list indexing is function application. -/
theorem toFn_apply (h : m ∈ L.domain) : L.toFn.apply m h = L.at m := rfl

/-- `☐L = ☐⟨n: ☐L· L n⟩`: list domain is function domain. -/
theorem toFn_domain : L.toFn.domain = L.domain := rfl

/-- `#L = #⟨n: ☐L· L n⟩`: list size is function size. -/
theorem toFn_size : L.toFn.size = L.length := by
  simp only [Fn.size, toFn, Fn.lam, domain, length, Str.len, Bunch.size, ← Finset.coe_range,
    Set.encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- `L M m = ⟨n: ☐L· L n⟩ ⟨n: ☐M· M n⟩ m`: list composition is function
composition, for `m` an index of `M` whose item is an index of `L`. -/
theorem toFn_comp (N : HList ℕ) (hm : m ∈ N.domain) (hL : N.at m ∈ L.domain) :
    (L.comp N).toFn.apply m (by show m < (N.contents.map _).length; rw [List.length_map]; exact hm) =
      L.toFn.apply (N.toFn.apply m hm) hL :=
  comp_at L N hm

/-- `L {A} = {L A}` (Reference §11.3.6): a list applied to a bunch of indices gives the bunch of the
items at those indices (in the domain); packaging both sides is the book's law. -/
theorem toFn_applyBunch (A : Bunch ℕ) : L.toFn.applyBunch A = L.at '' (A ∩ L.domain) := by
  ext y
  simp only [Fn.applyBunch, toFn, Fn.lam, Fn.apply, Set.mem_ofPred_eq, Set.mem_image, Set.mem_inter_iff]
  constructor
  · rintro ⟨n, hn, hA, rfl⟩; exact ⟨n, ⟨hA, hn⟩, rfl⟩
  · rintro ⟨n, ⟨hA, hn⟩, rfl⟩; exact ⟨n, hn, hA, rfl⟩

/-- `L [S] = [L S]` (Reference §11.3.6): a list applied to a list of indices. -/
theorem comp_pack (T : Str ℕ) : L.comp (Str.pack T) = Str.pack (Str.sub L.contents T) := rfl

/-- `L = M = ⟨n: ☐L· L n⟩ = ⟨n: ☐M· M n⟩`: list equality is function equality. -/
theorem toFn_inj : L.toFn = M.toFn ↔ L = M := by
  constructor
  · intro h
    obtain ⟨hd, hb⟩ := (Fn.eq_iff _ _).1 h
    have hlen : L.contents.length = M.contents.length := Set.Iio_inj.1 hd
    apply HList.ext
    apply List.ext_getElem hlen
    intro n hL hM
    have h' := hb n hL hM
    simp only [toFn, Fn.lam, Fn.apply, «at», Str.at, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hL, List.getElem?_eq_getElem hM, Option.getD_some] at h'
    exact h'
  · rintro rfl; rfl

/-- `ΣL = Σn: ☐L· L n`: the sum of the items of a list of numbers. -/
theorem sum_toFn (L : HList Number) : Fn.sum L.toFn = L.contents.sum := by
  show (∑ᶠ n ∈ L.domain, L.at n) = L.contents.sum
  rw [domain, ← Finset.coe_range, finsum_mem_coe_finset, Finset.sum_range, ← Fin.sum_univ_getElem]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [«at», Str.at, List.getD_eq_getElem?_getD]

/-- A function composed with a list: `f L` applies `f` to each item. -/
def map {β : Type v} (f : α → β) (L : HList α) : HList β := ⟨L.contents.map f⟩

/-- `suc [3; 5; 2] = [4; 6; 3]`. -/
theorem suc_map_example : map (· + 1) (Str.pack [3, 5, 2] : HList ℤ) = Str.pack [4, 6, 3] := by decide

/-- `–[3; 5; 2] = [–3; –5; –2]`. -/
theorem neg_map_example : map Neg.neg (Str.pack [3, 5, 2] : HList ℤ) = Str.pack [-3, -5, -2] := by decide

/-- `n→i | L = (n→i | L)`: a selective union of an arrow and a list is the
modified list, for `n` an index of `L`. -/
theorem orElse_arrow_toFn (n : ℕ) (i : α) (hn : n ∈ L.domain) :
    Fn.orElse (Fn.arrow n i) L.toFn = (modify n i L).toFn := by
  refine Fn.ext ?_ fun x hx hx' => ?_
  · show Bunch.elem n ∪ L.domain = (modify n i L).domain
    simp only [modify, domain, Str.update, List.length_set]
    exact Set.union_eq_right.2 (Set.singleton_subset_iff.2 hn)
  · simp only [Fn.orElse, Fn.arrow, Fn.lam, toFn, modify, «at», Str.update, Str.at,
      List.getD_eq_getElem?_getD]
    split
    · rename_i hxn
      simp only [Bunch.elem, Set.mem_singleton_iff] at hxn
      subst hxn
      rw [List.getElem?_set_self hn, Option.getD_some]
    · rename_i hxn
      simp only [Bunch.elem, Set.mem_singleton_iff] at hxn
      rw [List.getElem?_set_ne (Ne.symm hxn)]

/-- `1→21 | [10; 11; 12] = [10; 21; 12]`, the book's example. -/
theorem orElse_arrow_example :
    Fn.orElse (Fn.arrow 1 21) (Str.pack [10, 11, 12] : HList ℤ).toFn = (Str.pack [10, 21, 12] : HList ℤ).toFn := by
  rw [orElse_arrow_toFn (Str.pack [10, 11, 12] : HList ℤ) 1 21 (show (1 : ℕ) < 3 by decide)]
  rfl

end LaPToP.DataStructures.HList
