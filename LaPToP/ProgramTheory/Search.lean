import LaPToP.ProgramTheory.Time
import LaPToP.Concurrency.ListConcurrency

/-!
# Linear search and binary search

This module formalizes Subsections 4.2.4 (Linear Search, Exercise 186) and
4.2.5 (Binary Search, Exercise 187) of Eric Hehner's *A Practical Theory of
Programming* (aPToP).

"Exercise 186: Write a program to find the first occurrence of a given item in
a given list. The execution time must be linear in the length of the list. Let
the list be `L` and the value we are looking for be `x` (these are not state
variables). Our program will assign natural variable `h` (for “here”) the
index of the first occurrence of `x` in `L` if `x` is there. ... it will be
convenient to indicate that `x` is not in `L` by assigning `h` the length of
`L`. The specification is `¬ x: L (0,..h′) ∧ (L h′ = x ∨ h′=#L) ∧ t′ ≤ t+#L`."

"Exercise 187: Write a program to find a given item in a given nonempty
sorted list. The execution time must be logarithmic in the length of the list.
... let's indicate whether `x` is present in `L` by assigning binary variable
`p` the value `⊤` if it is and `⊥` if not. Ignoring time for the moment, the
problem is `x: L (☐L) = p′ ⇒ L h′ = x`. ... let specification `R` describe the
search within the segment `h,..j`. `R = (x: L (h,..j) = p′ ⇒ L h′ = x)`."

## The model

A list is a function `L : ℕ → ℤ` with length `n` (`#L`); `x` is a constant;
`¬ x: L (a,..b)` is `∀k· a ≤ k < b ⇒ L k ≠ x`. The recursive calls are the
specifications being refined (Section 6.1). For linear search the three
refinements, their timing versions, the combined version ("it is not really
necessary to take such small steps"), the nonempty variant and the sentinel
variant are proved.

For binary search the book's `R = (x: L (h,..j) = p′ ⇒ L h′ = x)` is read
with Hehner's continuing operators, as its proof of the `j–h = 1` case
confirms ("`x = L h = L h = x ⇒ L h = x` ... Symmetry and Base and Reflexive
Laws `= ⊤`"): `p′` is whether `x` occurs in `L (h,..j)`, and if it does then
`L h′ = x`. The four correctness refinements are proved from the sortedness
of `L` ("If `h<i` and `L i ≤ x` and `L` is sorted, then `x: L (i,..j) = x:
L (h,..j)`"), and the three timing refinements with `ceil (log …)` as
`Nat.clog 2`, using the halving lemma of `LaPToP.Concurrency.ListConcurrency`.
-/

namespace LaPToP.ProgramTheory

namespace LinearSearch

open Spec

/-- The state: the index `h` and the time. -/
structure LS where
  /-- `h`, "here". -/
  h : ℕ
  /-- The time. -/
  t : ℕ∞

/-- `h:= e`. -/
def assignH (e : LS → ℕ) : Spec LS := fun s s' => s' = { s with h := e s }
/-- `t:= t+1`. -/
def tick : Spec LS := fun s s' => s' = { s with t := s.t + 1 }

theorem assignH_seq (e : LS → ℕ) (P : Spec LS) : seq (assignH e) P = fun s s' => P { s with h := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem tick_seq (P : Spec LS) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (L : ℕ → ℤ) (n : ℕ) (x : ℤ)

/-- `¬ x: L (a,..b)`: `x` does not occur in the segment. -/
def notIn (a b : ℕ) : Prop := ∀ k, a ≤ k → k < b → L k ≠ x

/-- `¬ x: L (0,..h′) ∧ (L h′ = x ∨ h′=#L)`, the problem without time. -/
def P : Spec LS := fun _ s' => notIn L x 0 s'.h ∧ (L s'.h = x ∨ s'.h = n)

/-- `h≤#L ⇒ ¬ x: L (h,..h′) ∧ (L h′ = x ∨ h′=#L)`, "a linear search starting at index `h`". -/
def Q : Spec LS := fun s s' => s.h ≤ n → notIn L x s.h s'.h ∧ (L s'.h = x ∨ s'.h = n)

/-- `h<#L ⇒ ¬ x: L (h,..h′) ∧ (L h′ = x ∨ h′=#L)`. -/
def Q' : Spec LS := fun s s' => s.h < n → notIn L x s.h s'.h ∧ (L s'.h = x ∨ s'.h = n)

/-- `¬ x: L (0,..h′) ∧ (L h′ = x ∨ h′=#L) ⇐ h:= 0. h≤#L ⇒ …`. -/
theorem refine₁ : Refines (P L n x) (seq (assignH fun _ => 0) (Q L n x)) := by
  intro s s' h
  rw [assignH_seq] at h
  exact h (Nat.zero_le n)

/-- `h≤#L ⇒ … ⇐ if h=#L then ok else h<#L ⇒ …`: "we have to test `h=#L` first". -/
theorem refine₂ : Refines (Q L n x) (cond (fun s => s.h = n) ok (Q' L n x)) := by
  rintro s s' (⟨hn, rfl⟩ | ⟨hn, h⟩) hle
  · exact ⟨fun k h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _), Or.inr hn⟩
  · exact h (lt_of_le_of_ne hle hn)

/-- `h<#L ⇒ … ⇐ if L h = x then ok else h:= h+1. h≤#L ⇒ …`. -/
theorem refine₃ : Refines (Q' L n x) (cond (fun s => L s.h = x) ok (seq (assignH fun s => s.h + 1) (Q L n x))) := by
  rintro s s' (⟨hx, rfl⟩ | ⟨hx, h⟩) hlt
  · exact ⟨fun k h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _), Or.inl hx⟩
  · rw [assignH_seq] at h
    obtain ⟨hni, hor⟩ := h (by simp only; omega)
    refine ⟨fun k h1 h2 => ?_, hor⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact hx
    · exact hni k (by simp only; omega) h2

/-! ### Timing -/

/-- `t′ ≤ t+#L`. -/
def T : Spec LS := fun s s' => s'.t ≤ s.t + n
/-- `h≤#L ⇒ t′ ≤ t+#L–h`. -/
def TQ : Spec LS := fun s s' => s.h ≤ n → s'.t ≤ s.t + ((n - s.h : ℕ) : ℕ∞)
/-- `h<#L ⇒ t′ ≤ t+#L–h`. -/
def TQ' : Spec LS := fun s s' => s.h < n → s'.t ≤ s.t + ((n - s.h : ℕ) : ℕ∞)

theorem time₁ : Refines (T n) (seq (assignH fun _ => 0) (TQ n)) := by
  intro s s' h
  rw [assignH_seq] at h
  simpa [TQ, T] using h (Nat.zero_le n)

theorem time₂ : Refines (TQ n) (cond (fun s => s.h = n) ok (TQ' n)) := by
  rintro s s' (⟨-, rfl⟩ | ⟨hn, h⟩) hle
  · exact le_self_add
  · exact h (lt_of_le_of_ne hle hn)

theorem time₃ : Refines (TQ' n) (cond (fun s => L s.h = x) ok (seq (assignH fun s => s.h + 1) (seq tick (TQ n)))) := by
  rintro s s' (⟨-, rfl⟩ | ⟨-, h⟩) hlt
  · exact le_self_add
  · rw [assignH_seq, tick_seq] at h
    have h' := h (by simp only; omega)
    simp only at h'
    refine le_trans h' (le_of_eq ?_)
    rw [add_assoc, ← Nat.cast_one, ← Nat.cast_add]
    congr 2
    omega

/-! ### The combined version -/

/-- `¬ x: L (0,..h′) ∧ (L h′ = x ∨ h′=#L) ∧ t′ ≤ t+#L`. -/
def PT : Spec LS := fun s s' => P L n x s s' ∧ T n s s'

/-- `h≤#L ⇒ ¬ x: L (h,..h′) ∧ (L h′ = x ∨ h′=#L) ∧ t′ ≤ t+#L–h`. -/
def QT : Spec LS := fun s s' => Q L n x s s' ∧ TQ n s s'

/-- "It is not really necessary to take such small steps": the combined first line
`… ⇐ h:= 0. h≤#L ⇒ …`; by Refinement by Parts, the same structure serves the conjunction. -/
theorem combined₁ : Refines (PT L n x) (seq (assignH fun _ => 0) (QT L n x)) := by
  intro s s' h
  rw [assignH_seq] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨refine₁ L n x s s' (by rw [assignH_seq]; exact h1), time₁ n s s' (by rw [assignH_seq]; exact h2)⟩

/-- The combined loop: `… ⇐ if h = #L then ok else if L h = x then ok else h:= h+1. t:= t+1. …`. -/
theorem combined₂ :
    Refines (QT L n x)
      (cond (fun s => s.h = n) ok
        (cond (fun s => L s.h = x) ok (seq (assignH fun s => s.h + 1) (seq tick (QT L n x))))) := by
  rintro s s' h
  refine ⟨refine₂ L n x s s' ?_, time₂ n s s' ?_⟩
  · rcases h with ⟨hn, hok⟩ | ⟨hn, (⟨hx, hok⟩ | ⟨hx, hseq⟩)⟩
    · exact Or.inl ⟨hn, hok⟩
    · exact Or.inr ⟨hn, refine₃ L n x s s' (Or.inl ⟨hx, hok⟩)⟩
    · refine Or.inr ⟨hn, refine₃ L n x s s' (Or.inr ⟨hx, ?_⟩)⟩
      rw [assignH_seq, tick_seq] at hseq
      rw [assignH_seq]
      exact hseq.1
  · rcases h with ⟨hn, hok⟩ | ⟨hn, (⟨hx, hok⟩ | ⟨hx, hseq⟩)⟩
    · exact Or.inl ⟨hn, hok⟩
    · exact Or.inr ⟨hn, time₃ L n x s s' (Or.inl ⟨hx, hok⟩)⟩
    · refine Or.inr ⟨hn, time₃ L n x s s' (Or.inr ⟨hx, ?_⟩)⟩
      rw [assignH_seq, tick_seq] at hseq
      rw [assignH_seq, tick_seq]
      exact hseq.2

/-- "Suppose we learn that the given list `L` is known to be nonempty": the first line
becomes `… ⇐ h:= 0. h<#L ⇒ …`. -/
theorem nonempty_variant (hn : 0 < n) : Refines (P L n x) (seq (assignH fun _ => 0) (Q' L n x)) := by
  intro s s' h
  rw [assignH_seq] at h
  exact h hn

/-! ### The sentinel -/

/-- The state for the sentinel version: the list is a variable, with its length. -/
structure SS where
  /-- The list variable `L`. -/
  L : ℕ → ℤ
  /-- Its length `#L`. -/
  n : ℕ
  /-- The index `h`. -/
  h : ℕ

/-- `L:= L;;[x]`. -/
def appendX : Spec SS := fun s s' => s' = { s with L := Function.update s.L s.n x, n := s.n + 1 }
/-- `h:= e` on the sentinel state. -/
def assignHs (e : SS → ℕ) : Spec SS := fun s s' => s' = { s with h := e s }

/-- `Q = L (#L–1) = x ∧ h<#L ⇒ L′=L ∧ ¬ x: L (h,..h′) ∧ L h′ = x`. -/
def Qs : Spec SS := fun s s' =>
  s.L (s.n - 1) = x ∧ s.h < s.n → s'.L = s.L ∧ s'.n = s.n ∧ notIn s.L x s.h s'.h ∧ s.L s'.h = x

/-- `Q ⇐ if L h = x then ok else h:= h+1. Q`: "we can skip the test `h=#L` each iteration". -/
theorem sentinel_loop : Refines (Qs x) (cond (fun s => s.L s.h = x) ok (seq (assignHs fun s => s.h + 1) (Qs x))) := by
  rintro s s' (⟨hx, rfl⟩ | ⟨hx, u, rfl, h⟩) ⟨hsent, hlt⟩
  · exact ⟨rfl, rfl, fun k h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _), hx⟩
  · have hne : s.h ≠ s.n - 1 := fun heq => hx (show s.L s.h = x by rw [heq]; exact hsent)
    obtain ⟨hL, hn, hni, hx'⟩ := h ⟨hsent, by simp only; omega⟩
    refine ⟨hL, hn, fun k h1 h2 => ?_, hx'⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact hx
    · exact hni k (by simp only; omega) h2

/-- The problem on the sentinel state (about the initial list). -/
def Ps : Spec SS := fun s s' => notIn s.L x 0 s'.h ∧ (s.L s'.h = x ∨ s'.h = s.n)

/-- `¬ x: L (0,..h′) ∧ (L h′ = x ∨ h′=#L) ⇐ L:= L;;[x]. h:= 0. Q`: "the search is sure to find `x`". -/
theorem sentinel_top : Refines (Ps x) (seq (appendX x) (seq (assignHs fun _ => 0) (Qs x))) := by
  rintro s s' ⟨_, rfl, _, rfl, h⟩
  simp only [Qs, Nat.add_sub_cancel, Function.update_self] at h
  obtain ⟨-, -, hni, hx'⟩ := h ⟨trivial, Nat.succ_pos _⟩
  have hle : s'.h ≤ s.n := by
    by_contra hgt
    exact hni s.n (Nat.zero_le _) (by omega) (Function.update_self ..)
  refine ⟨fun k h1 h2 => ?_, ?_⟩
  · have := hni k h1 h2
    rwa [Function.update_of_ne (by omega)] at this
  · rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · exact Or.inr heq
    · left
      rwa [Function.update_of_ne (by omega)] at hx'

end LinearSearch

/-! ### Binary search (aPToP §4.2.5) -/

namespace BinarySearch

open Spec

/-- The state: `h`, `i`, `j`, the binary `p`, and the time. -/
structure BS where
  /-- Left end of the segment. -/
  h : ℕ
  /-- The midpoint. -/
  i : ℕ
  /-- Right end of the segment. -/
  j : ℕ
  /-- Whether `x` is present. -/
  p : Prop
  /-- The time. -/
  t : ℕ∞

def assignH (e : BS → ℕ) : Spec BS := fun s s' => s' = { s with h := e s }
def assignI (e : BS → ℕ) : Spec BS := fun s s' => s' = { s with i := e s }
def assignJ (e : BS → ℕ) : Spec BS := fun s s' => s' = { s with j := e s }
def assignP (e : BS → Prop) : Spec BS := fun s s' => s' = { s with p := e s }
def tick : Spec BS := fun s s' => s' = { s with t := s.t + 1 }

theorem assignH_seq (e : BS → ℕ) (P : Spec BS) : seq (assignH e) P = fun s s' => P { s with h := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignI_seq (e : BS → ℕ) (P : Spec BS) : seq (assignI e) P = fun s s' => P { s with i := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignJ_seq (e : BS → ℕ) (P : Spec BS) : seq (assignJ e) P = fun s s' => P { s with j := e s } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem tick_seq (P : Spec BS) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (L : ℕ → ℤ) (n : ℕ) (x : ℤ)

/-- `x: L (a,..b)`: `x` occurs in the segment. -/
def occurs (a b : ℕ) : Prop := ∃ k, a ≤ k ∧ k < b ∧ L k = x

/-- `L` is sorted on `0,..n`. -/
def Sorted : Prop := ∀ a b, a ≤ b → b < n → L a ≤ L b

/-- The problem: `x: L (☐L) = p′ ⇒ L h′ = x` — `p′` says whether `x` is in `L`, and if
so `L h′ = x`. -/
def Prob : Spec BS := fun _ s' => (occurs L x 0 n ↔ s'.p) ∧ (s'.p → L s'.h = x)

/-- `R = (x: L (h,..j) = p′ ⇒ L h′ = x)`, the search within the segment `h,..j`. -/
def R : Spec BS := fun s s' => (occurs L x s.h s.j ↔ s'.p) ∧ (s'.p → L s'.h = x)

/-- `h<j ⇒ R`. -/
def U : Spec BS := fun s s' => s.h < s.j → R L x s s'
/-- `j–h ≥ 2 ⇒ R`. -/
def V : Spec BS := fun s s' => 2 ≤ s.j - s.h → R L x s s'
/-- `j–h ≥ 2 ⇒ h′=h<i′<j′=j`. -/
def Mid : Spec BS := fun s s' => 2 ≤ s.j - s.h → s'.h = s.h ∧ s.h < s'.i ∧ s'.i < s'.j ∧ s'.j = s.j ∧ s'.p = s.p ∧ s'.t = s.t

/-- `(x: L (☐L) = p′ ⇒ L h′ = x) ⇐ h:= 0. j:= #L. h<j ⇒ R`, "we are given that `L` is nonempty". -/
theorem refine₁ (hn : 0 < n) : Refines (Prob L n x) (seq (assignH fun _ => 0) (seq (assignJ fun _ => n) (U L x))) := by
  intro s s' h
  rw [assignH_seq, assignJ_seq] at h
  exact h hn

/-- `h<j ⇒ R ⇐ if j–h = 1 then p:= L h = x else j–h ≥ 2 ⇒ R`; the first case is
"`x = L h = L h = x ⇒ L h = x`, Symmetry and Base and Reflexive Laws". -/
theorem refine₂ : Refines (U L x) (cond (fun s => s.j - s.h = 1) (assignP fun s => L s.h = x) (V L x)) := by
  rintro s s' (⟨h1, rfl⟩ | ⟨h1, h⟩) hlt
  · refine ⟨?_, fun hp => hp⟩
    constructor
    · rintro ⟨k, hk1, hk2, hk⟩
      have : k = s.h := by omega
      subst this; exact hk
    · intro hp; exact ⟨s.h, le_rfl, by omega, hp⟩
  · exact h (by omega)

/-- "If `h<i` and `L i ≤ x` and `L` is sorted, then `x: L (i,..j) = x: L (h,..j)`." -/
theorem occurs_right (hs : Sorted L n) {h i j : ℕ} (hhi : h ≤ i) (hij : i < j) (hjn : j ≤ n) (hLi : L i ≤ x) :
    occurs L x i j ↔ occurs L x h j := by
  constructor
  · rintro ⟨k, hk1, hk2, hk⟩; exact ⟨k, le_trans hhi hk1, hk2, hk⟩
  · rintro ⟨k, hk1, hk2, hk⟩
    rcases Nat.lt_or_ge k i with hki | hki
    · exact ⟨i, le_rfl, hij, le_antisymm hLi (hk ▸ hs k i (le_of_lt hki) (by omega))⟩
    · exact ⟨k, hki, hk2, hk⟩

/-- Likewise, if `L i > x` then `x: L (h,..i) = x: L (h,..j)`. -/
theorem occurs_left (hs : Sorted L n) {h i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) (hLi : x < L i) :
    occurs L x h i ↔ occurs L x h j := by
  constructor
  · rintro ⟨k, hk1, hk2, hk⟩; exact ⟨k, hk1, lt_of_lt_of_le hk2 hij, hk⟩
  · rintro ⟨k, hk1, hk2, hk⟩
    rcases Nat.lt_or_ge k i with hki | hki
    · exact ⟨k, hk1, hki, hk⟩
    · exact absurd (hs i k hki (by omega)) (not_le.mpr (hk ▸ hLi))

/-- `j–h ≥ 2 ⇒ R ⇐ (j–h ≥ 2 ⇒ h′=h<i′<j′=j). if L i ≤ x then h:= i else j:= i. h<j ⇒ R`,
for a sorted list with `j ≤ #L`. -/
theorem refine₃ (hs : Sorted L n) :
    Refines (fun s s' => s.j ≤ n → V L x s s')
      (seq (Mid) (seq (cond (fun s => L s.i ≤ x) (assignH fun s => s.i) (assignJ fun s => s.i)) (U L x))) := by
  rintro s s' ⟨u, hu, v, hv, hU⟩ hjn h2
  obtain ⟨huh, hhi, hij, huj, -, -⟩ := hu h2
  rcases hv with ⟨hLi, rfl⟩ | ⟨hLi, rfl⟩
  · obtain ⟨hocc, hp⟩ := hU (by simp only; omega)
    simp only at hocc
    refine ⟨?_, hp⟩
    rw [← hocc, huj, occurs_right L n x hs (le_of_lt (huh ▸ hhi)) (huj ▸ hij) (huj ▸ hjn) hLi, huh]
  · obtain ⟨hocc, hp⟩ := hU (by simp only; omega)
    simp only at hocc
    refine ⟨?_, hp⟩
    rw [← hocc, huh, occurs_left L n x hs (le_of_lt hij) (huj ▸ hjn) (not_le.mp hLi)]
    rw [huj]

/-- `j–h ≥ 2 ⇒ h′=h<i′<j′=j ⇐ i:= div (h+j) 2`. -/
theorem refine₄ : Refines Mid (assignI fun s => (s.h + s.j) / 2) := by
  rintro s _ rfl h2
  refine ⟨rfl, by simp only; omega, by simp only; omega, rfl, rfl, rfl⟩

/-! ### Timing: `ceil (log …)` as `Nat.clog 2` -/

open LaPToP.Concurrency.ListConc in
/-- `T = t′ ≤ t + ceil (log (#L))`. -/
def T : Spec BS := fun s s' => s'.t ≤ s.t + (Nat.clog 2 n : ℕ∞)
/-- `U = h<j ⇒ t′ ≤ t + ceil (log (j–h))`. -/
def TU : Spec BS := fun s s' => s.h < s.j → s'.t ≤ s.t + (Nat.clog 2 (s.j - s.h) : ℕ∞)
/-- `V = j–h≥2 ⇒ t′ ≤ t + ceil (log (j–h))`. -/
def TV : Spec BS := fun s s' => 2 ≤ s.j - s.h → s'.t ≤ s.t + (Nat.clog 2 (s.j - s.h) : ℕ∞)

theorem time₁ (hn : 0 < n) : Refines (T n) (seq (assignH fun _ => 0) (seq (assignJ fun _ => n) TU)) := by
  intro s s' h
  rw [assignH_seq, assignJ_seq] at h
  simpa [TU, T] using h hn

theorem time₂ : Refines TU (cond (fun s => s.j - s.h = 1) (assignP fun s => L s.h = x) TV) := by
  rintro s s' (⟨h1, rfl⟩ | ⟨h1, h⟩) hlt
  · exact le_self_add
  · exact h (by omega)

/-- `V ⇐ i:= div (h+j) 2. if L i ≤ x then h:= i else j:= i. t:= t+1. U`: halving gives
`1 + ceil (log (half)) ≤ ceil (log (j–h))`. -/
theorem time₃ :
    Refines TV (seq (assignI fun s => (s.h + s.j) / 2)
      (seq (cond (fun s => L s.i ≤ x) (assignH fun s => s.i) (assignJ fun s => s.i)) (seq tick TU))) := by
  rintro s s' h h2
  rw [assignI_seq] at h
  obtain ⟨u, hu, h⟩ := h
  rw [tick_seq] at h
  have hsplit := LaPToP.Concurrency.ListConc.clog_two_split h2
  rcases hu with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · -- `h:= i`: the new segment is `i,..j`, of length `j – ⌊(h+j)/2⌋ = ⌈(j–h)/2⌉`
    have h' := h (by simp only; omega)
    simp only at h'
    refine le_trans h' ?_
    rw [add_assoc, add_comm (1 : ℕ∞), ← Nat.cast_one, ← Nat.cast_add]
    gcongr
    rw [hsplit, show s.j - (s.h + s.j) / 2 = (s.j - s.h) - (s.j - s.h) / 2 by omega]
    omega
  · -- `j:= i`: the new segment is `h,..i`, of length `⌊(j–h)/2⌋`
    have h' := h (by simp only; omega)
    simp only at h'
    refine le_trans h' ?_
    rw [add_assoc, add_comm (1 : ℕ∞), ← Nat.cast_one, ← Nat.cast_add]
    gcongr
    rw [hsplit, show (s.h + s.j) / 2 - s.h = (s.j - s.h) / 2 by omega]
    omega

end BinarySearch

end LaPToP.ProgramTheory
