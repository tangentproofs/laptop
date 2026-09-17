import LaPToP.ProgramTheory.Programs
import LaPToP.FunctionTheory.FinePoints
import LaPToP.BasicTheories.Numbers
import Mathlib.Data.Set.Card

/-!
# Functional programming

This module formalizes Section 5.8 (Functional Programming) and Subsection
5.8.0 (Function Refinement) of Eric Hehner's *A Practical Theory of
Programming* (aPToP).

"This section presents an alternative: a program is a function from its
input to its output. More generally, a specification is a function from
possible inputs to desired outputs, and programs (as always) are implemented
specifications. We take away `ok`, assignment, and sequential composition
from our programming notations, and we add functions. To illustrate, we look
once again at the list summation problem (Exercise 174). This time, the
specification is `⟨L: [*rat]· ΣL⟩`. ... We introduce variable `n` to indicate
how much of the list has been summed; initially `n` is `0`.
`ΣL = ⟨n: 0,..#L+1· Σ L [n;..#L]⟩ 0` ... `0,..#L+1 = ☐L, #L`. We divide the
function into a selective union ... `⟨n: ☐L· Σ L [n;..#L]⟩ = ⟨n: ☐L· L n + Σ L
[n+1;..#L]⟩`, `⟨n: #L· Σ L [n;..#L]⟩ = ⟨n: #L· 0⟩`. The one remaining problem is
solved by recursion. `Σ L [n+1;..#L] = ⟨n: 0,..#L+1· Σ L [n;..#L]⟩ (n+1)`. In
place of the selective union we could have used `if then else`; they are
related by the law `⟨v: A· x⟩ | ⟨v: B· y⟩ = ⟨v: A, B· if v: A then x else y⟩`.
When we are interested in the execution time rather than the result, we
replace the result of each function with its time according to some measure."

"In functional programming, a nondeterministic specification is a bunch
consisting of more than one element. ... Functional specification `S` is
unsatisfiable for domain element `x`: `¢S x < 1`; satisfiable: `¢S x ≥ 1`;
deterministic: `¢S x ≤ 1`; nondeterministic: `¢S x > 1`; ... implementable:
`∀x· ∃y· y: S x`. Implementability can be restated as `∀x· S x ⧧ null`. ...
`⟨L: [*int]· ⟨x: int· §n: ☐L· L n = x⟩⟩` ... if `x` does not occur in `L`, we are
left without any possible result, so this specification is unimplementable.
... `⟨L: [*int]· ⟨x: int· if x: L (☐L) then §n: ☐L· L n = x else #L,..∞⟩⟩` This
specification is implementable, and often nondeterministic. ... Functional
specification `P` (the problem) is refined by functional specification `S`
(the solution) if and only if `S: P`. ... “`P` is refined by `S`” is written
`P:: S`."

## The model

Lists are the integer lists `HList ℤ` of the list-summation example, with
integer indices and the interval `x,..y` of Section 2.0; a function is `Fn`
(Section 3.0) and functional refinement `P:: S` is the function inclusion
`S: P` of Section 3.2.0. The book's rationals are integers here. `#L,..∞` is
the bunch of integers `≥ #L`. In the second linear-search refinement the
book has `i: nat`; for its timing refinement the domain must be `0,..#L+1`
("we could have been more precise about the domain of `i`"), which is used
and recorded. The bunch sum `1 + B` is the image of `B` under `1 + ·`.
-/

namespace LaPToP.ProgramTheory

namespace Functional

open LaPToP.BasicTheories LaPToP.DataStructures LaPToP.FunctionTheory Fn ListSummation
open Classical

/-! ### List summation as a function (aPToP §5.8) -/

/-- `☐L`, the domain of a list: `0,..#L`. -/
def dom (L : HList ℤ) : Bunch ℤ := Bunch.interval 0 (len L)

variable (L : HList ℤ)

/-- `⟨n: 0,..#L+1· Σ L [n;..#L]⟩`. -/
def sumFn : Fn ℤ ℤ := lam (Bunch.interval 0 (len L + 1)) fun n => sumFrom L n

theorem zero_mem_sumFn_dom : (0 : ℤ) ∈ (sumFn L).dom := by
  simp only [sumFn, lam, Bunch.interval, Set.mem_Ico, le_refl, true_and, len]
  omega

/-- `ΣL = ⟨n: 0,..#L+1· Σ L [n;..#L]⟩ 0`. -/
theorem sum_eq : L.contents.sum = (sumFn L).apply 0 (zero_mem_sumFn_dom L) := (sumFrom_zero L).symm

/-- `0,..#L+1 = ☐L, #L`: "the domain is really composed of two parts". -/
theorem domain_split : Bunch.interval 0 (len L + 1) = dom L ∪ Bunch.elem (len L) := by
  ext n
  simp only [Bunch.interval, dom, Bunch.elem, Set.mem_Ico, Set.mem_union, Set.mem_singleton_iff, len]
  omega

/-- The law relating selective union and `if`: `⟨v: A· x⟩ | ⟨v: B· y⟩ = ⟨v: A, B· if v: A then x else y⟩`. -/
theorem orElse_lam_lam {α β : Type} (A B : Bunch α) (x y : α → β) :
    orElse (lam A x) (lam B y) = lam (A ∪ B) fun v => if v ∈ A then x v else y v := by
  refine Fn.ext rfl fun v _ _ => ?_
  show (if h : v ∈ A then x v else y v) = if v ∈ A then x v else y v
  split_ifs <;> rfl

/-- `⟨n: 0,..#L+1· Σ L [n;..#L]⟩ = ⟨n: ☐L· Σ L [n;..#L]⟩ | ⟨n: #L· Σ L [n;..#L]⟩`. -/
theorem sumFn_orElse :
    sumFn L = orElse (lam (dom L) fun n => sumFrom L n) (lam (Bunch.elem (len L)) fun n => sumFrom L n) := by
  rw [orElse_lam_lam, sumFn, domain_split]
  refine Fn.ext rfl fun n _ _ => ?_
  simp only [lam]
  split_ifs <;> rfl

/-- `⟨n: ☐L· Σ L [n;..#L]⟩ = ⟨n: ☐L· L n + Σ L [n+1;..#L]⟩`. -/
theorem left_part : (lam (dom L) fun n => sumFrom L n) = lam (dom L) fun n => L.at n.toNat + sumFrom L (n + 1) := by
  refine Fn.ext rfl fun n hn _ => ?_
  simp only [lam, dom, Bunch.interval, Set.mem_Ico] at hn
  exact sumFrom_succ L hn.1 hn.2

/-- `⟨n: #L· Σ L [n;..#L]⟩ = ⟨n: #L· 0⟩`. -/
theorem right_part : (lam (Bunch.elem (len L)) fun n => sumFrom L n) = lam (Bunch.elem (len L)) fun _ => 0 := by
  refine Fn.ext rfl fun n hn _ => ?_
  simp only [lam, Bunch.elem, Set.mem_singleton_iff] at hn
  subst hn
  exact sumFrom_len L

/-- "The one remaining problem is solved by recursion": `Σ L [n+1;..#L] = ⟨n: 0,..#L+1· Σ L [n;..#L]⟩ (n+1)`. -/
theorem recursion (n : ℤ) (h : n + 1 ∈ (sumFn L).dom) : sumFrom L (n + 1) = (sumFn L).apply (n + 1) h := rfl

/-! ### Execution time as a function -/

/-- Charging `1` for each addition: `⟨n: 0,..#L+1· #L–n⟩`. -/
def timeFn : Fn ℤ ℤ := lam (Bunch.interval 0 (len L + 1)) fun n => len L - n

/-- `#L = ⟨n: 0,..#L+1· #L–n⟩ 0`. -/
theorem len_eq : len L = (timeFn L).apply 0 (zero_mem_sumFn_dom L) := by simp [timeFn, lam, apply]

/-- `⟨n: 0,..#L+1· #L–n⟩ = ⟨n: ☐L· #L–n⟩ | ⟨n: #L· #L–n⟩`. -/
theorem timeFn_orElse :
    timeFn L = orElse (lam (dom L) fun n => len L - n) (lam (Bunch.elem (len L)) fun n => len L - n) := by
  rw [orElse_lam_lam, timeFn, domain_split]
  refine Fn.ext rfl fun n _ _ => ?_
  simp only [lam]
  split_ifs <;> rfl

/-- "The left side of the selective union became a function with one addition in it,
so our timing function must become a function with a charge of `1` in it":
`⟨n: ☐L· #L–n⟩ = ⟨n: ☐L· 1 + #L–n–1⟩`. -/
theorem time_left : (lam (dom L) fun n => len L - n) = lam (dom L) fun n => 1 + (len L - n - 1) := by
  refine Fn.ext rfl fun n _ _ => ?_
  simp only [lam]
  ring

/-- "The right side ... became a function with a constant result; according to our
measure, its time must be `0`": `⟨n: #L· #L–n⟩ = ⟨n: #L· 0⟩`. -/
theorem time_right : (lam (Bunch.elem (len L)) fun n => len L - n) = lam (Bunch.elem (len L)) fun _ => 0 := by
  refine Fn.ext rfl fun n hn _ => ?_
  simp only [lam, Bunch.elem, Set.mem_singleton_iff] at hn
  simp [lam, hn]

/-- `#L–n–1 = ⟨n: 0,..#L+1· #L–n⟩ (n+1)`, the time of the recursive call (addition measure). -/
theorem time_recursion (n : ℤ) (h : n + 1 ∈ (timeFn L).dom) : len L - n - 1 = (timeFn L).apply (n + 1) h := by
  simp only [timeFn, lam, apply]; ring

/-- In the recursive time measure, "we charge nothing for any operation except
recursive call, and we charge `1` for that": `#L–n = 1 + ⟨n: 0,..#L+1· #L–n⟩ (n+1)`. -/
theorem time_recursive_measure (n : ℤ) (h : n + 1 ∈ (timeFn L).dom) : len L - n = 1 + (timeFn L).apply (n + 1) h := by
  simp only [timeFn, lam, apply]; ring

/-! ### Function refinement (aPToP §5.8.0) -/

section FunctionalSpec

variable {α β : Type}

/-- A functional specification is a function whose results are bunches. -/
abbrev FSpec (α β : Type) := Fn α (Bunch β)

/-- "Functional specification `S` is unsatisfiable for domain element `x`: `¢S x < 1`." -/
def Unsat (S : FSpec α β) (x : α) (hx : x ∈ S.dom) : Prop := Bunch.size (S.apply x hx) < 1
/-- "satisfiable ...: `¢S x ≥ 1`". -/
def Sat (S : FSpec α β) (x : α) (hx : x ∈ S.dom) : Prop := 1 ≤ Bunch.size (S.apply x hx)
/-- "deterministic ...: `¢S x ≤ 1`". -/
def Det (S : FSpec α β) (x : α) (hx : x ∈ S.dom) : Prop := Bunch.size (S.apply x hx) ≤ 1
/-- "nondeterministic ...: `¢S x > 1`". -/
def Nondet (S : FSpec α β) (x : α) (hx : x ∈ S.dom) : Prop := 1 < Bunch.size (S.apply x hx)

/-- "Functional specification `S` is satisfiable for domain element `x`: `∃y· y: S x`." -/
theorem sat_iff (S : FSpec α β) (x : α) (hx : x ∈ S.dom) : Sat S x hx ↔ ∃ y, y ∈ S.apply x hx := by
  simp only [Sat, Bunch.size, Set.one_le_encard_iff_nonempty, Set.Nonempty]

/-- "Functional specification `S` is implementable: `∀x· ∃y· y: S x`." -/
def Implementable (S : FSpec α β) : Prop := ∀ x (hx : x ∈ S.dom), ∃ y, y ∈ S.apply x hx

/-- "Implementability can be restated as `∀x· S x ⧧ null`." -/
theorem implementable_iff_ne_null (S : FSpec α β) : Implementable S ↔ ∀ x (hx : x ∈ S.dom), S.apply x hx ≠ Bunch.null := by
  simp only [Implementable, Bunch.null, ← Set.nonempty_iff_ne_empty, Set.Nonempty]

/-- "`P` is refined by `S`", `P:: S`, is the function inclusion `S: P`. -/
def Refines (P S : FSpec α β) : Prop := Incl S P

end FunctionalSpec

/-! ### The search specification -/

/-- `x: L (☐L)`: `x` occurs in the list. -/
def occursIn (x : ℤ) : Prop := ∃ n, n ∈ dom L ∧ L.at n.toNat = x

/-- `⟨x: int· §n: ☐L· L n = x⟩`, the first attempt (for a fixed list `L`). -/
def search₀ : FSpec ℤ ℤ := lam Set.univ fun x => {n | n ∈ dom L ∧ L.at n.toNat = x}

/-- "If `x` does not occur in `L`, we are left without any possible result, so this
specification is unimplementable": for the empty list, no `x` has a result. -/
theorem not_implementable_search₀ : ¬ Implementable (search₀ (Str.pack [])) := by
  intro h
  obtain ⟨n, hn, -⟩ := h 0 trivial
  simp [dom, Bunch.interval, len, Str.pack] at hn

/-- `#L,..∞`: the integers from `#L` on ("any natural that is not an index of `L`"). -/
def beyond : Bunch ℤ := Set.Ici (len L)

/-- `⟨x: int· if x: L (☐L) then §n: ☐L· L n = x else #L,..∞⟩`. -/
noncomputable def search : FSpec ℤ ℤ :=
  lam Set.univ fun x => if occursIn L x then {n | n ∈ dom L ∧ L.at n.toNat = x} else beyond L

/-- "This specification is implementable." -/
theorem implementable_search : Implementable (search L) := by
  intro x _
  simp only [search, lam, apply]
  by_cases h : occursIn L x
  · rw [if_pos h]
    obtain ⟨n, hn, hx⟩ := h
    exact ⟨n, hn, hx⟩
  · rw [if_neg h]
    exact ⟨len L, Set.self_mem_Ici⟩

/-! ### The linear-search refinement -/

/-- `x: L (i,..#L)`. -/
def occursFrom (x i : ℤ) : Prop := ∃ n, i ≤ n ∧ n < len L ∧ L.at n.toNat = x

/-- The body `if x: L (i,..#L) then §n: i,..#L· L n = x else #L,..∞`. -/
noncomputable def sfBody (x i : ℤ) : Bunch ℤ :=
  if occursFrom L x i then {n | i ≤ n ∧ n < len L ∧ L.at n.toNat = x} else beyond L

/-- `⟨i: nat· if x: L (i,..#L) then §n: i,..#L· L n = x else #L,..∞⟩`. -/
noncomputable def searchFrom (x : ℤ) : FSpec ℤ ℤ := lam (Set.Ici 0) (sfBody L x)

/-- The first refinement: `if x: L (☐L) then §n: ☐L· L n = x else #L,..∞ :: ⟨i: nat· …⟩ 0`
— "the two sides of this refinement are equal". -/
theorem search_apply_eq (x : ℤ) : (search L).apply x trivial = (searchFrom L x).apply 0 Set.self_mem_Ici := by
  simp only [search, searchFrom, sfBody, lam, apply, occursIn, occursFrom, dom, Bunch.interval, Set.mem_Ico, and_assoc]
  congr

/-- The second refinement: `if x: L (i,..#L) then … else #L,..∞ :: if i = #L then #L else if
x = L i then i else ⟨i: nat· …⟩ (i+1)`, i.e. the step of the linear search. -/
theorem search_step_refines (x : ℤ) :
    Refines (searchFrom L x)
      (lam (Set.Ici 0) fun i => if i = len L then Bunch.elem (len L) else if x = L.at i.toNat then Bunch.elem i else sfBody L x (i + 1)) := by
  classical
  refine ⟨subset_rfl, fun i hi _ => ?_⟩
  simp only [searchFrom, lam, apply, sfBody, beyond]
  have hi0 : (0 : ℤ) ≤ i := hi
  by_cases hlen : i = len L
  · rw [if_pos hlen]
    have hno : ¬ occursFrom L x i := by rintro ⟨n, h1, h2, -⟩; omega
    rw [if_neg hno]
    intro n hn
    rw [Bunch.elem, Set.mem_singleton_iff] at hn
    subst hn
    exact Set.self_mem_Ici
  rw [if_neg hlen]
  by_cases hx : x = L.at i.toNat
  · rw [if_pos hx]
    intro n hn
    rw [Bunch.elem, Set.mem_singleton_iff] at hn
    subst hn
    by_cases hlt : n < len L
    · have hocc : occursFrom L x n := ⟨n, le_rfl, hlt, hx.symm⟩
      rw [if_pos hocc]
      exact ⟨le_rfl, hlt, hx.symm⟩
    · have hno : ¬ occursFrom L x n := by rintro ⟨m, h1, h2, -⟩; omega
      rw [if_neg hno]
      exact not_lt.mp hlt
  · rw [if_neg hx]
    have hiff : occursFrom L x (i + 1) ↔ occursFrom L x i := by
      constructor
      · rintro ⟨n, h1, h2, h3⟩; exact ⟨n, by omega, h2, h3⟩
      · rintro ⟨n, h1, h2, h3⟩
        rcases eq_or_lt_of_le h1 with rfl | h1'
        · exact absurd h3.symm hx
        · exact ⟨n, by omega, h2, h3⟩
    by_cases hocc : occursFrom L x i
    · rw [if_pos hocc, if_pos (hiff.mpr hocc)]
      rintro n ⟨h1, h2, h3⟩
      exact ⟨by omega, h2, h3⟩
    · rw [if_neg hocc, if_neg (fun h => hocc (hiff.mp h))]

/-! ### Timing of the search, recursive measure -/

/-- `0,..#L–i+1`, the time bound at index `i`. -/
def timeBound (i : ℤ) : Bunch ℤ := Bunch.interval 0 (len L - i + 1)

/-- `1 + B`, the bunch `B` with `1` added to each element. -/
def onePlus (B : Bunch ℤ) : Bunch ℤ := (fun t => 1 + t) '' B

/-- `0,..#L+1 :: ⟨i· 0,..#L–i+1⟩ 0`. -/
theorem time_top : Bunch.interval 0 (len L + 1) = timeBound L 0 := by simp [timeBound]

/-- `0,..#L–i+1 :: if i = #L then 0 else if x = L i then 0 else 1 + ⟨i· 0,..#L–i+1⟩ (i+1)`,
for `i` in the domain `0,..#L+1`. -/
theorem time_step (x : ℤ) :
    Refines (lam (Bunch.interval 0 (len L + 1)) (timeBound L))
      (lam (Bunch.interval 0 (len L + 1)) fun i =>
        if i = len L then Bunch.elem 0 else if x = L.at i.toNat then Bunch.elem 0 else onePlus (timeBound L (i + 1))) := by
  classical
  refine ⟨subset_rfl, fun i hi _ => ?_⟩
  simp only [lam, apply, timeBound, Bunch.interval, Set.mem_Ico] at hi ⊢
  have h0 : (0 : ℤ) ∈ Set.Ico 0 (len L - i + 1) := by simp only [Set.mem_Ico]; omega
  split_ifs
  · intro n hn; rw [Bunch.elem, Set.mem_singleton_iff] at hn; subst hn; exact h0
  · intro n hn; rw [Bunch.elem, Set.mem_singleton_iff] at hn; subst hn; exact h0
  · rintro n ⟨t, ht, rfl⟩
    simp only [Set.mem_Ico] at ht ⊢
    omega

end Functional

end LaPToP.ProgramTheory
