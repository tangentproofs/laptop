import LaPToP.BasicTheories.Numbers
import LaPToP.BasicTheories.Binary

/-!
# Function Theory: functions, selective union, predicates, quantifiers

This module formalizes Sections 3.0 (Functions) and 3.1 (Quantifiers, for
`∀`, `∃` and `§`) of Eric Hehner's *A Practical Theory of Programming* (aPToP).

## The model

Hehner's function `⟨v: D· b⟩` ("map `v` in `D` to `b`") carries its domain `D`,
a bunch, and its body `b` is only meaningful for `v: D`. A *function from `α`
to `β`* is therefore modelled as a structure `Fn α β` with a domain
`dom : Bunch α` and a body defined only on the domain,
`body : (x : α) → x ∈ dom → β`. Because the body is defined only on the
domain, Lean's equality of `Fn` values *is* Hehner's function equality: same
domain, same values on it (`Fn.ext`).

| aPToP           | here                                    |
| --------------- | --------------------------------------- |
| `⟨v: D· b⟩`     | `Fn.lam D (fun v => b)`                 |
| `☐f`            | `Fn.domain f` (`= f.dom`)               |
| `#f`            | `Fn.size f`                             |
| `f x` (`x: ☐f`) | `Fn.apply f x h` with `h : x ∈ f.dom`   |
| `f \| g`        | `Fn.orElse f g`                         |
| `x→y`           | `Fn.arrow x y`                          |
| predicate       | `Pred α := Fn α Binary`                 |
| `∀p`, `∃p`      | `Fn.all p`, `Fn.ex p` (propositions)    |
| `§p`            | `Fn.sols p` (a bunch)                   |

Application requires a proof that the argument is in the domain: this is the
book's local axiom `v: D` inside the body, made explicit. The Application
Axiom "substitute `x` for `v` in `b`" is β-reduction, so it holds by `rfl`.

The book's `∀p` and `∃p` are binary values. Over an infinite domain they are
not computable, so they are modelled as propositions (`Prop`) rather than as
`Bool`; the axioms then read as equivalences.
-/

namespace LaPToP.FunctionTheory

open LaPToP.BasicTheories
open scoped Pointwise

universe u v

/-- A Hehner *function* (aPToP §3.0): a domain (a bunch) together with a body
defined on that domain. `⟨v: D· b⟩` is `Fn.lam D (fun v => b)`. -/
structure Fn (α : Type u) (β : Type v) where
  /-- `☐f`, the domain of the function. -/
  dom : Bunch α
  /-- The body, defined for elements of the domain only. -/
  body : (x : α) → x ∈ dom → β

namespace Fn

variable {α : Type u} {β : Type v}

/-- Two functions are equal when they have the same domain and agree on it:
Hehner's function equality. -/
theorem ext {f g : Fn α β} (hd : f.dom = g.dom)
    (hb : ∀ x (hf : x ∈ f.dom) (hg : x ∈ g.dom), f.body x hf = g.body x hg) : f = g := by
  obtain ⟨D, b⟩ := f
  obtain ⟨D', b'⟩ := g
  cases hd
  congr
  funext x h
  exact hb x h h

/-- `⟨v: D· b⟩`, the function with domain `D` and body `b`, for a body that does
not need the local axiom `v: D`. -/
def lam (D : Bunch α) (b : α → β) : Fn α β := ⟨D, fun x _ => b x⟩

/-- `☐f`, the domain of `f`. -/
abbrev domain (f : Fn α β) : Bunch α := f.dom

/-- `#f = ¢☐f`, the size of a function: the size of its domain. -/
noncomputable def size (f : Fn α β) : ℕ∞ := Bunch.size f.dom

/-- `f x`, "`f` applied to `x`", for `x` in the domain of `f`. -/
abbrev apply (f : Fn α β) (x : α) (h : x ∈ f.dom) : β := f.body x h

/-- `x→y`, "`x` maps to `y`": the function `⟨v: x· y⟩` with an unused variable. -/
def arrow (x : α) (y : β) : Fn α β := lam (Bunch.elem x) fun _ => y

/-! ### Axioms (aPToP §3.0) -/

section Axioms

variable (D : Bunch α) (b : α → β) (f : Fn α β) (x : α)

/-- `☐⟨v: D· b⟩ = D` (Domain Axiom). -/
theorem domain_lam : (lam D b).domain = D := rfl

/-- `#f = ¢☐f` (size of a function). -/
theorem size_eq : f.size = Bunch.size f.domain := rfl

/-- `x: D ⇒ ⟨v: D· b⟩ x = (substitute x for v in b)` (Application Axiom). -/
theorem apply_lam (h : x ∈ D) : (lam D b).apply x h = b x := rfl

/-- `f = ⟨w: ☐f· f w⟩` (Axiom of Extension). -/
theorem extension : f = ⟨f.domain, fun w hw => f.apply w hw⟩ := rfl

/-- `⟨v: D· b⟩ = ⟨w: D· ⟨v: D· b⟩ w⟩` (Renaming Axiom), an instance of Extension. -/
theorem renaming_axiom : lam D b = ⟨D, fun w hw => (lam D b).apply w hw⟩ := rfl

/-- `(x→y) x = y`. -/
theorem apply_arrow (y : β) : (arrow x y).apply x rfl = y := rfl

/-- `☐(x→y) = x`. -/
theorem domain_arrow (y : β) : (arrow x y).domain = Bunch.elem x := rfl

end Axioms

/-! ### Selective union (aPToP §3.0)

`f | g`, "`f` otherwise `g`", behaves like `f` on the domain of `f` and
otherwise like `g`. -/

open Classical in
/-- `f | g`, the selective union of `f` and `g`. -/
noncomputable def orElse (f g : Fn α β) : Fn α β :=
  ⟨f.dom ∪ g.dom, fun x hx =>
    if h : x ∈ f.dom then f.body x h else g.body x (hx.resolve_left h)⟩

section SelectiveUnion

variable (f g : Fn α β) (x : α)

/-- `☐(f | g) = ☐f, ☐g`. -/
theorem domain_orElse : (orElse f g).domain = f.domain ∪ g.domain := rfl

open Classical in
/-- `(f | g) x = if x: ☐f then f x else g x`. -/
theorem apply_orElse (hx : x ∈ (orElse f g).domain) :
    (orElse f g).apply x hx =
      if h : x ∈ f.domain then f.apply x h else g.apply x (hx.resolve_left h) := rfl

/-- `(f | g) x = f x` for `x: ☐f`. -/
theorem apply_orElse_left (h : x ∈ f.domain) :
    (orElse f g).apply x (Or.inl h) = f.apply x h := dif_pos h

/-- `(f | g) x = g x` for `x: ☐g` with `¬ x: ☐f`. -/
theorem apply_orElse_right (h : x ∉ f.domain) (hg : x ∈ g.domain) :
    (orElse f g).apply x (Or.inr hg) = g.apply x hg := dif_neg h

end SelectiveUnion

end Fn

/-! ### Predicates and relations (aPToP §3.0)

"A predicate is a function whose body is a binary expression. ... A relation
is a function whose body is a predicate." -/

/-- A *predicate*: a function with a binary body. -/
abbrev Pred (α : Type u) := Fn α Binary

/-- `even = ⟨i: int· i/2: int⟩`: `i/2` is an integer, i.e. `2` divides `i`. -/
def even : Pred ℤ := Fn.lam Bunch.int fun i => decide (2 ∣ i)

/-- `odd = ⟨i: int· ¬ i/2: int⟩`. -/
def odd : Pred ℤ := Fn.lam Bunch.int fun i => !decide (2 ∣ i)

/-- `divides = ⟨n: nat+1· ⟨i: int· i/n: int⟩⟩`, a relation: a function whose
body is a predicate. -/
def divides : Fn ℤ (Pred ℤ) :=
  Fn.lam (Bunch.nat + Bunch.elem 1) fun n => Fn.lam Bunch.int fun i => decide (n ∣ i)

/-- `2 : nat+1`. -/
theorem two_mem_nat_add_one : (2 : ℤ) ∈ Bunch.nat + Bunch.elem 1 :=
  ⟨1, by simp [Bunch.nat], 1, rfl, by simp⟩

/-- `divides 2 = even`. -/
theorem divides_two : divides.apply 2 two_mem_nat_add_one = even := rfl

/-- `divides 2 3 = ⊥`. -/
theorem divides_two_three :
    (divides.apply 2 two_mem_nat_add_one).apply 3 (Set.mem_univ 3) = Binary.bot := by
  decide

/-- `odd = ⟨i: int· ¬ even i⟩`: the two examples are complementary. -/
theorem odd_apply (i : ℤ) (h : i ∈ Bunch.int) : odd.apply i h = !even.apply i h := rfl

/-! ### Quantifiers `∀`, `∃`, `§` (aPToP §3.1)

"If `p` is a predicate, then universal quantification `∀p` is the binary
result of applying `p` to all its domain elements and conjoining all the
results. Similarly, existential quantification `∃p` is the binary result of
applying `p` to all its domain elements and disjoining all the results."
The solution quantifier `§p`, "those", "gives the bunch of solutions of a
predicate". -/

namespace Fn

variable {α : Type u}

/-- `∀p`: `p` holds of every element of its domain. -/
def all (p : Pred α) : Prop := ∀ x (h : x ∈ p.dom), p.apply x h = true

/-- `∃p`: `p` holds of some element of its domain. -/
def ex (p : Pred α) : Prop := ∃ x, ∃ h : x ∈ p.dom, p.apply x h = true

/-- `§p`, the bunch of solutions of `p`: the domain elements of which `p` holds. -/
def sols (p : Pred α) : Bunch α := {x | ∃ h : x ∈ p.dom, p.apply x h = true}

section QuantifierAxioms

variable (A B : Bunch α) (b : α → Binary) (x : α)

/-- `∀v: null· b = ⊤`. -/
theorem all_null : all (lam Bunch.null b) := fun x h => absurd h (Set.notMem_empty x)

/-- `∀v: x· b = ⟨v: x· b⟩ x`. -/
theorem all_elem : all (lam (Bunch.elem x) b) ↔ b x = true := by
  simp [all, lam, apply]

/-- `∀v: A, B· b = (∀v: A· b) ∧ (∀v: B· b)`. -/
theorem all_union : all (lam (A ∪ B) b) ↔ all (lam A b) ∧ all (lam B b) := by
  simp only [all, lam, apply, Set.mem_union]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

/-- `∃v: null· b = ⊥`. -/
theorem not_ex_null : ¬ ex (lam Bunch.null b) := fun ⟨x, h, _⟩ => Set.notMem_empty x h

/-- `∃v: x· b = ⟨v: x· b⟩ x`. -/
theorem ex_elem : ex (lam (Bunch.elem x) b) ↔ b x = true := by
  simp [ex, lam, apply]

/-- `∃v: A, B· b = (∃v: A· b) ∨ (∃v: B· b)`. -/
theorem ex_union : ex (lam (A ∪ B) b) ↔ ex (lam A b) ∨ ex (lam B b) := by
  simp only [ex, lam, apply, Set.mem_union]
  constructor
  · rintro ⟨x, hx | hx, hb⟩
    · exact Or.inl ⟨x, hx, hb⟩
    · exact Or.inr ⟨x, hx, hb⟩
  · rintro (⟨x, hx, hb⟩ | ⟨x, hx, hb⟩)
    · exact ⟨x, Or.inl hx, hb⟩
    · exact ⟨x, Or.inr hx, hb⟩

/-- `§v: null· b = null`. -/
theorem sols_null : sols (lam Bunch.null b) = Bunch.null := by
  ext x; simp [sols, lam]

/-- `§v: x· b = if ⟨v: x· b⟩ x then x else null`. -/
theorem sols_elem : sols (lam (Bunch.elem x) b) = if b x = true then Bunch.elem x else Bunch.null := by
  ext y
  by_cases hb : b x = true
  · simp [sols, lam, apply, hb]
    rintro rfl; exact hb
  · simp [sols, lam, apply, hb]
    rintro rfl; simpa using hb

/-- `§v: A, B· b = (§v: A· b), (§v: B· b)`. -/
theorem sols_union : sols (lam (A ∪ B) b) = sols (lam A b) ∪ sols (lam B b) := by
  ext y; simp [sols, lam, apply, or_and_right]

/-- Solutions lie in the domain: `§p : ☐p`. -/
theorem sols_subset_domain (p : Pred α) : p.sols ⊆ p.domain := fun _ ⟨h, _⟩ => h

/-- `x: §p = x: ☐p ∧ p x`. -/
theorem mem_sols (p : Pred α) : x ∈ p.sols ↔ ∃ h : x ∈ p.domain, p.apply x h = true := Iff.rfl

end QuantifierAxioms

/-! ### Specialization, Generalization, One-Point (aPToP §3.1) -/

section QuantifierLaws

variable (p : Pred α) (D : Bunch α) (b : α → Binary) (x : α)

/-- `∀p ⇒ p x` for `x: ☐p` (Specialization). -/
theorem all_apply (hp : all p) (h : x ∈ p.domain) : p.apply x h = true := hp x h

/-- `p x ⇒ ∃p` for `x: ☐p` (Generalization). -/
theorem ex_of_apply (h : x ∈ p.domain) (hx : p.apply x h = true) : ex p := ⟨x, h, hx⟩

/-- `∀p ⇒ ∃p` when the domain is nonempty (Specialization then Generalization). -/
theorem ex_of_all (hp : all p) (h : x ∈ p.domain) : ex p := ex_of_apply p x h (hp x h)

/-- `∀v: D· v=x ⇒ b = ⟨v: D· b⟩ x` for `x: D` (One-Point Law). -/
theorem all_eq_imp [DecidableEq α] (hx : x ∈ D) :
    all (lam D fun v => Binary.imp (decide (v = x)) (b v)) ↔ b x = true := by
  simp only [all, lam, apply, Binary.imp]
  constructor
  · intro h; simpa using h x hx
  · intro h v _
    by_cases hv : v = x
    · subst hv; simp [h]
    · simp [hv]

/-- `∃v: D· v=x ∧ b = ⟨v: D· b⟩ x` for `x: D` (One-Point Law). -/
theorem ex_eq_and [DecidableEq α] (hx : x ∈ D) :
    ex (lam D fun v => decide (v = x) && b v) ↔ b x = true := by
  simp only [ex, lam, apply]
  constructor
  · rintro ⟨v, _, hv⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1 ▸ hv.2
  · intro h; exact ⟨x, hx, by simp [h]⟩

end QuantifierLaws

end Fn

end LaPToP.FunctionTheory
