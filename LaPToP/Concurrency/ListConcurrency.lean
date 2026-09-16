import LaPToP.Concurrency.Composition
import Mathlib.Data.Nat.Log
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# List concurrency: the maximum of a list in logarithmic time

This module formalizes Section 8.0.1 (List Concurrency) of Eric Hehner's
*A Practical Theory of Programming* (aPToP) and its example, Exercise 172.

## The model

"We have defined concurrent composition by partitioning the variables. For
finer-grained concurrency, we can extend this same idea to the individual
items within list variables. ... For concurrent composition, we must specify
the final values of only the items and variables in one side of the
partition."

The state is a list variable `L`, modelled as an indexed sequence `ℕ → ℤ`,
together with the time `t`. Segment concurrency `parSeg i m j P Q` composes a
process `P` owning the items `i,..m` with a process `Q` owning `m,..j`: both
start from the same state, the final list takes `P`'s values on `P`'s segment
and `Q`'s on `Q`'s, items outside `i,..j` are unchanged, and the time is the
maximum of the two finishing times — the list-item form of `P||Q` with time.

The segment maximum `⇑ L[i;..j]` is a `WithBot ℤ`-valued supremum over the
indexes, so that it is `–∞` on an empty segment as in the book's `⇑ null = –∞`.
The recursive time `ceil (log (j–i))` is `Nat.clog 2 (j - i)`.

Exercise 172: `findmax = ⟨i, j· i<j ⇒ L′ i = ⇑ L [i;..j] ∧ t′ = t + ceil (log (j–i))⟩`
and the refinement
`findmax i j ⇐ if j–i = 1 then ok else t:= t+1. (findmax i m || findmax m j). L i:= L i ↑ L m`
with `m = div (i+j) 2` are formalized; the refinement is proved outright (as
in Section 6.1, the recursive calls are specifications, not yet programs), and
the exact timing `ceil (log (j–i))` follows from
`clog 2 n = 1 + max (clog 2 ⌊n/2⌋) (clog 2 ⌈n/2⌉)` for `n ≥ 2`.
-/

namespace LaPToP.Concurrency

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

/-- A state with a time variable and a list variable `L`, as an indexed sequence. -/
structure LS where
  /-- The time variable. -/
  t : ℕ∞
  /-- The list variable `L`. -/
  L : ℕ → ℤ

namespace ListConc

/-- `L i:= e`: "`L′i = e ∧ (∀j· j⧧i ⇒ L′j = L j)`" and other variables unchanged. -/
def assignItem (i : ℕ) (e : LS → ℤ) : Spec LS := fun s s' => s' = { s with L := Function.update s.L i (e s) }

/-- `t:= t+1`. -/
def tick : Spec LS := fun s s' => s' = { s with t := s.t + 1 }

/-- Substitution Law for `t:= t+1`. -/
theorem tick_seq (P : Spec LS) : seq tick P = fun s s' => P { s with t := s.t + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- Segment concurrency with time: `P` owns the items `i,..m`, `Q` owns `m,..j`;
the final list takes each process's values on its segment, items outside
`i,..j` are unchanged, and `t′ = tP ↑ tQ`. -/
def parSeg (i m j : ℕ) (P Q : Spec LS) : Spec LS := fun s s' =>
  ∃ sP sQ : LS, P s sP ∧ Q s sQ ∧
    (∀ k, i ≤ k → k < m → s'.L k = sP.L k) ∧ (∀ k, m ≤ k → k < j → s'.L k = sQ.L k) ∧
    (∀ k, ¬ (i ≤ k ∧ k < j) → s'.L k = s.L k) ∧ s'.t = max sP.t sQ.t

/-- `⇑ L [i;..j]`, the maximum of the segment `i,..j` of `L`, in `xint`: `–∞` on an
empty segment. -/
def segSup (L : ℕ → ℤ) (i j : ℕ) : WithBot ℤ := (Finset.Ico i j).sup fun k => (L k : WithBot ℤ)

/-- `⇑ L [i;..i+1] = L i`. -/
theorem segSup_singleton (L : ℕ → ℤ) (i : ℕ) : segSup L i (i + 1) = L i := by
  simp [segSup, Nat.Ico_succ_singleton]

/-- `⇑ L [i;..j] = ⇑ L [i;..m] ↑ ⇑ L [m;..j]` for `i ≤ m ≤ j`. -/
theorem segSup_split (L : ℕ → ℤ) {i m j : ℕ} (him : i ≤ m) (hmj : m ≤ j) :
    segSup L i j = max (segSup L i m) (segSup L m j) := by
  simp only [segSup]
  rw [← Finset.Ico_union_Ico_eq_Ico him hmj, Finset.sup_union]

/-- The segment maximum depends only on the items in the segment. -/
theorem segSup_congr {L L' : ℕ → ℤ} {i j : ℕ} (h : ∀ k, i ≤ k → k < j → L' k = L k) : segSup L' i j = segSup L i j := by
  simp only [segSup]
  exact Finset.sup_congr rfl fun k hk => by rw [h k (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2]

/-- `ceil (log n) = 1 + ceil (log ⌊n/2⌋) ↑ ceil (log ⌈n/2⌉)` for `n ≥ 2`: the
recursive time of halving. -/
theorem clog_two_split {n : ℕ} (hn : 2 ≤ n) :
    Nat.clog 2 n = 1 + max (Nat.clog 2 (n / 2)) (Nat.clog 2 (n - n / 2)) := by
  have h1 : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    have := Nat.clog_of_two_le (b := 2) (by norm_num) hn
    simpa using this
  have h2 : n - n / 2 = (n + 1) / 2 := by omega
  have h3 : Nat.clog 2 (n / 2) ≤ Nat.clog 2 ((n + 1) / 2) := Nat.clog_mono_right 2 (by omega)
  rw [h1, h2, max_eq_right h3, add_comm]

/-- Casting a maximum of naturals into `xnat`. -/
theorem coe_max_enat (a b : ℕ) : ((max a b : ℕ) : ℕ∞) = max (a : ℕ∞) (b : ℕ∞) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

/-- `(a + b) ↑ (a + c) = a + (b ↑ c)` in `xnat`. -/
theorem max_add_add_left_enat (a b c : ℕ∞) : max (a + b) (a + c) = a + max b c := by
  rcases le_total b c with h | h
  · rw [max_eq_right h, max_eq_right (add_le_add_right h a)]
  · rw [max_eq_left h, max_eq_left (add_le_add_right h a)]

/-! ### Exercise 172 -/

/-- `findmax = ⟨i, j· i<j ⇒ L′ i = ⇑ L [i;..j] ∧ t′ = t + ceil (log (j–i))⟩`: "at the
end, item `i` of list `L` will be the maximum of the original items of the
segment `i,..j`". -/
def findmax (i j : ℕ) : Spec LS := fun s s' =>
  i < j → (s'.L i : WithBot ℤ) = segSup s.L i j ∧ s'.t = s.t + (Nat.clog 2 (j - i) : ℕ∞)

/-- `findmax 0 (#L)` is the book's specification `L′ 0 = ⇑L ∧ t′ = t + ceil (log (#L))`. -/
theorem findmax_zero (n : ℕ) (hn : 0 < n) (s s' : LS) :
    findmax 0 n s s' ↔ (s'.L 0 : WithBot ℤ) = segSup s.L 0 n ∧ s'.t = s.t + (Nat.clog 2 n : ℕ∞) := by
  simp [findmax, hn]

/-- The midpoint `div (i+j) 2`. -/
def mid (i j : ℕ) : ℕ := (i + j) / 2

/-- The book's refinement:
`findmax i j ⇐ if j–i = 1 then ok else t:= t+1. (findmax i m || findmax m j). L i:= L i ↑ L m`
with `m = div (i+j) 2`. "If `j–i = 1` the segment contains one item ... In the
other case ... we divide the segment into two halves, placing the maximum of
each half at the beginning of the half. In the concurrent composition, the two
processes change disjoint segments of the list. We finish by placing the
maximum of the two maximums at the start of the whole segment. The recursive
execution time is `ceil (log (j–i))`." -/
theorem findmax_refines (i j : ℕ) :
    Refines (findmax i j)
      (cond (fun _ => j - i = 1) ok
        (seq tick (seq (parSeg i (mid i j) j (findmax i (mid i j)) (findmax (mid i j) j))
          (assignItem i fun s => max (s.L i) (s.L (mid i j)))))) := by
  rintro s s' (⟨h1, hok⟩ | ⟨h1, h⟩) hij
  · -- one item: `ok`
    simp only [Spec.ok] at hok
    subst hok
    have hj : j = i + 1 := by omega
    subst hj
    simp [segSup_singleton]
  · -- more than one item
    have hn : 2 ≤ j - i := by omega
    have him : i < mid i j := by simp only [mid]; omega
    have hmj : mid i j < j := by simp only [mid]; omega
    rw [tick_seq] at h
    obtain ⟨s₂, ⟨sP, sQ, hP, hQ, hPseg, hQseg, -, ht₂⟩, hs'⟩ := h
    obtain ⟨hPi, hPt⟩ := hP him
    obtain ⟨hQm, hQt⟩ := hQ hmj
    simp only at hPi hPt hQm hQt
    simp only [assignItem] at hs'
    subst hs'
    refine ⟨?_, ?_⟩
    · -- `L′ i = ⇑ L [i;..j]`
      simp only [Function.update_self, WithBot.coe_max]
      rw [hPseg i le_rfl him, hQseg (mid i j) le_rfl hmj, hPi, hQm,
        segSup_split s.L him.le hmj.le]
    · -- `t′ = t + ceil (log (j–i))`
      simp only
      rw [ht₂, hPt, hQt, clog_two_split hn]
      have hm1 : mid i j - i = (j - i) / 2 := by simp only [mid]; omega
      have hm2 : j - mid i j = (j - i) - (j - i) / 2 := by simp only [mid]; omega
      rw [hm1, hm2, Nat.cast_add, Nat.cast_one, coe_max_enat, add_assoc, add_assoc, max_add_add_left_enat,
        max_add_add_left_enat]

end ListConc

end LaPToP.Concurrency
