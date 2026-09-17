import LaPToP.FunctionTheory.FinePoints
import LaPToP.DataStructures.Lists

/-!
# Functions as data: higher-order functions and function composition

This module formalizes Sections 3.2.1 (Higher-Order Functions) and 3.2.2
(Function Composition) of Eric Hehner's *A Practical Theory of Programming*
(aPToP), and records that functions are ordinary data: items of bunches, sets
and lists.

## The model

"A higher-order function is a function whose parameter is function-valued, and
whose argument must therefore be a function": a `Fn (Fn α β) γ`. The book's
example is `check = ⟨f: (0,..10)→int· ∀n: 0,..10· even (f n)⟩`, whose domain
`(0,..10)→int` is the bunch of functions whose domain includes `0,..10` and
whose results on it are integers (`Fn.arrowSet`); `check suc = ⊥`.

"Let `f` and `g` be functions such that `g` is not in the domain of `f`. Then
`f g` is the composition of `f` and `g`, defined by the Function Composition
Axioms `☐(f g) = §x: ☐g· g x: ☐f` and `(f g) x = f (g x)`." `Fn.comp f g` has
that domain and body (the proviso is automatic: in the typed model a function
is never an element of another function's domain of a different type). The
book's examples `even suc` and the composition of an operator with a function
(`–suc`, `¬even = odd`) are checked, and "like application, composition
distributes over bunch union".

Since `Fn α β` is a type, functions are elements in the sense of Section 2:
bunches of functions (`Bunch (Fn α β)`, already used by `Fn.applyFns` and
`Fn.arrowSet`), sets of functions (`HSet`) and lists of functions (`HList`)
are all available — "functions are ordinary data".
-/

namespace LaPToP.FunctionTheory

open LaPToP.BasicTheories LaPToP.DataStructures

universe u v w

namespace Fn

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ### Function composition (aPToP §3.2.2) -/

/-- `f g`, the composition of `f` and `g`: domain `§x: ☐g· g x: ☐f`, body `f (g x)`.
(The domain is stated as a conjunction so that the body can use the
membership proofs.) -/
def comp (f : Fn β γ) (g : Fn α β) : Fn α γ where
  dom := {x | x ∈ g.dom ∧ ∀ h : x ∈ g.dom, g.apply x h ∈ f.dom}
  body x hx := f.apply (g.apply x hx.1) (hx.2 hx.1)

/-- `☐(f g) = §x: ☐g· g x: ☐f` (Function Composition Axiom). -/
theorem comp_domain (f : Fn β γ) (g : Fn α β) :
    (f.comp g).domain = {x | ∃ h : x ∈ g.domain, g.apply x h ∈ f.domain} := by
  ext x
  simp only [comp, domain, Set.mem_ofPred_eq]
  exact ⟨fun ⟨h, hf⟩ => ⟨h, hf h⟩, fun ⟨h, hf⟩ => ⟨h, fun _ => hf⟩⟩

/-- `(f g) x = f (g x)` (Function Composition Axiom). -/
theorem comp_apply (f : Fn β γ) (g : Fn α β) (x : α) (hx : x ∈ (f.comp g).domain) :
    (f.comp g).apply x hx = f.apply (g.apply x hx.1) (hx.2 hx.1) := rfl

/-- `f | f = f` (Selective Union). -/
theorem orElse_self (f : Fn α β) : orElse f f = f := by
  classical
  refine Fn.ext (Set.union_self _) fun x hf hg => ?_
  change (f.orElse f).apply x hf = f.apply x hg
  rw [apply_orElse, dif_pos hg]

/-- `f | (g | h) = (f | g) | h` (Selective Union). -/
theorem orElse_assoc (f g h : Fn α β) : orElse f (orElse g h) = orElse (orElse f g) h := by
  classical
  refine Fn.ext (Set.union_assoc _ _ _).symm fun x h₁ h₂ => ?_
  change (f.orElse (g.orElse h)).apply x h₁ = ((f.orElse g).orElse h).apply x h₂
  simp only [apply_orElse]
  by_cases hf : x ∈ f.domain <;> by_cases hg : x ∈ g.domain <;> simp [hf, hg, domain_orElse]

/-- `(g | h) f = g f | h f` (Selective Union distributes over composition). -/
theorem orElse_comp (g h : Fn β γ) (f : Fn α β) : (orElse g h).comp f = orElse (g.comp f) (h.comp f) := by
  classical
  refine Fn.ext ?_ fun x h₁ h₂ => ?_
  · ext x
    simp only [comp, orElse, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨hf, hd⟩
      rcases hd hf with hg | hh
      · exact Or.inl ⟨hf, fun _ => hg⟩
      · exact Or.inr ⟨hf, fun _ => hh⟩
    · rintro (⟨hf, hg⟩ | ⟨hf, hh⟩)
      · exact ⟨hf, fun _ => Or.inl (hg hf)⟩
      · exact ⟨hf, fun _ => Or.inr (hh hf)⟩
  · by_cases hg : x ∈ (g.comp f).dom
    · have hgd : f.body x h₁.1 ∈ g.dom := hg.2 hg.1
      show (if hg' : f.body x h₁.1 ∈ g.dom then g.body _ hg' else _) =
        if hg' : x ∈ (g.comp f).dom then (g.comp f).body x hg' else _
      rw [dif_pos hgd, dif_pos hg]
      rfl
    · have hgd : f.body x h₁.1 ∉ g.dom := fun hgd => hg ⟨h₁.1, fun _ => hgd⟩
      show (if hg' : f.body x h₁.1 ∈ g.dom then _ else h.body _ _) =
        if hg' : x ∈ (g.comp f).dom then _ else (h.comp f).body x (h₂.resolve_left hg')
      rw [dif_neg hgd, dif_neg hg]
      rfl

/-- An operator composed with a function: `h f` for an operator `h`, applied to
each result (`–suc`, `¬even`). -/
def map (h : β → γ) (f : Fn α β) : Fn α γ := ⟨f.dom, fun x hx => h (f.apply x hx)⟩

/-- `☐(h f) = ☐f`. -/
theorem map_domain (h : β → γ) (f : Fn α β) : (map h f).domain = f.domain := rfl

/-- `(h f) x = h (f x)`. -/
theorem map_apply (h : β → γ) (f : Fn α β) (x : α) (hx : x ∈ f.domain) : (map h f).apply x hx = h (f.apply x hx) := rfl

/-- The range of `h f` is the image of the range of `f`. -/
theorem values_map (h : β → γ) (f : Fn α β) : (map h f).values = h '' f.values := by
  ext y
  simp only [values, map, apply, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨f.apply x hx, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

/-- "Like application, composition distributes over bunch union": a function
composed with a bunch of functions is the bunch of compositions. -/
def compFns (f : Fn β γ) (G : Bunch (Fn α β)) : Bunch (Fn α γ) := (f.comp ·) '' G

/-- `f (g, h) = f g, f h`. -/
theorem compFns_union (f : Fn β γ) (G H : Bunch (Fn α β)) : compFns f (G ∪ H) = compFns f G ∪ compFns f H :=
  Set.image_union _ G H

/-- A bunch of functions composed with a function. -/
def fnsComp (F : Bunch (Fn β γ)) (g : Fn α β) : Bunch (Fn α γ) := (·.comp g) '' F

/-- `(f, g) h = f h, g h`. -/
theorem fnsComp_union (F G : Bunch (Fn β γ)) (h : Fn α β) : fnsComp (F ∪ G) h = fnsComp F h ∪ fnsComp G h :=
  Set.image_union _ F G

/-! ### The book's examples (aPToP §3.2.2) -/

/-- `☐(even suc) = §x: ☐suc· suc x: ☐even = §x: nat· x+1: int = nat`. -/
theorem domain_even_comp_suc : (even.comp suc).domain = Bunch.nat := by
  ext x
  simp only [comp, domain, even, suc, lam, apply, Bunch.int, Set.mem_ofPred_eq, Set.mem_univ, imp_true_iff,
    and_true]

/-- `(even suc) 3 = even (suc 3) = even 4 = ⊤`. -/
theorem even_comp_suc_three :
    (even.comp suc).apply 3 ⟨mem_nat_of_nonneg (by norm_num), fun _ => Set.mem_univ _⟩ = Binary.top := by
  decide

/-- `(–suc) 3 = –(suc 3) = –4`. -/
theorem neg_suc_three : (map Neg.neg suc).apply 3 (mem_nat_of_nonneg (by norm_num)) = -4 := rfl

/-- `¬even = odd`: composing `¬` with `even` gives `odd`. -/
theorem not_comp_even : map (fun b => !b) even = odd := rfl

/-- "We can write the Duality Laws this way": `¬∀f = ∃¬f`. -/
theorem not_all_iff_ex_not (p : Pred α) : ¬ all p ↔ ex (map (fun b => !b) p) := by
  simp only [all, ex, map, apply, not_forall, Bool.not_eq_true']
  exact ⟨fun ⟨x, h, hx⟩ => ⟨x, h, by simpa using hx⟩, fun ⟨x, h, hx⟩ => ⟨x, h, by simpa using hx⟩⟩

/-- `¬∃f = ∀¬f`. -/
theorem not_ex_iff_all_not (p : Pred α) : ¬ ex p ↔ all (map (fun b => !b) p) := by
  simp only [all, ex, map, apply, not_exists, Bool.not_eq_true']
  exact ⟨fun h x hx => by simpa using h x hx, fun h x hx => by simpa using h x hx⟩

/-- `–⇑f = ⇓–f`. -/
theorem neg_sup_eq_inf_neg (f : Fn α Number) : -sup f = inf (map (fun n => -n) f) := by
  rw [sup, inf, values_map, neg_sSup]

/-- `–⇓f = ⇑–f`. -/
theorem neg_inf_eq_sup_neg (f : Fn α Number) : -inf f = sup (map (fun n => -n) f) := by
  have h := neg_sup_eq_inf_neg (map (fun n : Number => -n) f)
  have hmm : map (fun n : Number => -n) (map (fun n : Number => -n) f) = f := by
    obtain ⟨D, b⟩ := f
    simp [map, apply]
  rw [hmm] at h
  rw [← h, neg_neg]

/-! ### Higher-order functions (aPToP §3.2.1) -/

/-- `check = ⟨f: (0,..10)→int· ∀n: 0,..10· even (f n)⟩`: "a higher-order function
is a function whose parameter is function-valued". Its domain `(0,..10)→int`
is the bunch of functions whose domain includes `0,..10` with integer results
there; the body tests the ten values for evenness. -/
def check : Fn (Fn ℤ ℤ) Binary where
  dom := arrowSet (Bunch.interval 0 10) Bunch.int
  body f hf := decide (∀ k : Fin 10, Even (f.apply k (hf.1 ⟨by omega, by omega⟩)))

/-- `suc: nat→nat: (0,..10)→int`, so `suc` is in the domain of `check`. -/
theorem suc_mem_check_domain : suc ∈ check.domain :=
  ⟨fun _x hx => mem_nat_of_nonneg hx.1, fun _ _ _ => Set.mem_univ _⟩

/-- "We can apply `check` to `suc` and the result is `⊥`": `suc 0 = 1` is odd. -/
theorem check_suc : check.apply suc suc_mem_check_domain = Binary.bot := by
  simp only [check, apply, Binary.bot, decide_eq_false_iff_not, not_forall]
  exact ⟨0, by simp [suc, lam]⟩

/-! ### Functions as data (aPToP §3, "functions are ordinary data") -/

/-- A list of functions, e.g. `[suc; double]`, and its pointwise application to
an argument in all their domains. -/
def applyList [Inhabited β] (L : HList (Fn α β)) (x : α) (h : ∀ f ∈ L.contents, x ∈ f.domain) : List β :=
  L.contents.attach.map fun ⟨f, hf⟩ => f.apply x (h f hf)

/-- `[suc; double] 3 = 4; 6`: applying a list of functions to an argument. -/
theorem applyList_example :
    applyList (Str.pack [suc, double]) 3
      (by
        intro f hf
        simp only [Str.pack, List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> exact mem_nat_of_nonneg (by norm_num)) = [4, 6] := rfl

end Fn

end LaPToP.FunctionTheory
