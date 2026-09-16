import LaPToP.Concurrency.ListConcurrency
import LaPToP.Concurrency.Transformation
import LaPToP.ProgramTheory.ForLoop
import Mathlib.Logic.Equiv.Basic

/-!
# Insertion sort

This module formalizes Section 8.1.1 (Insertion Sort) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), Exercise 209.

"Let the list be `L`, and define `sort = ⟨n· ∀i, j: 0,..n· i≤j ⇒ L i ≤ L j⟩` so
that `sort n` says that `L` is sorted up to index `n`. The specification is
`(L′ is a permutation of L) ∧ sort′ (#L) ∧ t′ ≤ t + (#L)²`. We leave the first
conjunct informal, and ensure that it is satisfied by using
`swap i j = L i:= L j || L j:= L i` to make changes to `L`. We ignore the last
conjunct; program transformation will give a linear time solution. The second
conjunct is equal to `sort 0 ⇒ sort′ (#L)` since `sort 0` is a theorem.

    sort 0 ⇒ sort′ (#L) ⇐ for n:= 0;..#L do sort n ⇒ sort′ (n+1)
    sort n ⇒ sort′ (n+1) ⇐ if n=0 then ok
                            else if L (n–1) ≤ L n then ok
                            else swap (n–1) n. sort (n–1) ⇒ sort′ n"

## The model

The state is `LS` of `LaPToP.Concurrency.ListConcurrency` (`L : ℕ → ℤ`, and
the time `t`, which — as in the book — is ignored here: `swap` leaves it
unchanged and no timing is claimed). The length `#L` is a parameter `len`.

`swap i j` is the simultaneous update `L′ = L ∘ (i ↔ j)`; `swap_iff` gives the
item-level reading of `L i:= L j || L j:= L i` (each side reads the initial
values, other items unchanged).

*Deviation, recorded honestly.* The book leaves "`L′` is a permutation of `L`"
informal, but the refinement of `sort n ⇒ sort′ (n+1)` is not provable from the
sortedness conjunct alone: the recursive call `sort (n–1) ⇒ sort′ n` must be
known to leave item `n` in place and to only permute items `0,..n`. So the
specification `sortStep n` carries the conjunct `IsPermBelow (n+1) L L′` —
`L′ = L ∘ σ` for a permutation `σ` fixing every index `≥ n+1` — which makes the
book's first conjunct formal and is exactly what `swap` establishes. The
quadratic time bound is ignored as in the book, and the "linear-time parallel
sort" is a picture; what is proved is that `swap`s on disjoint items commute
and that a `swap` does not disturb a comparison on other items.
-/

namespace LaPToP.Concurrency

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace ISort

/-- `sort n`: "`L` is sorted up to index `n`", `∀i, j: 0,..n· i≤j ⇒ L i ≤ L j`. -/
def sorted (L : ℕ → ℤ) (n : ℕ) : Prop := ∀ i j, i ≤ j → j < n → L i ≤ L j

/-- "`sort 0` is a theorem". -/
theorem sorted_zero (L : ℕ → ℤ) : sorted L 0 := fun _ _ _ h => absurd h (Nat.not_lt_zero _)

/-- `sort 1` is also a theorem. -/
theorem sorted_one (L : ℕ → ℤ) : sorted L 1 := fun i j hij hj => by
  have : i = j := le_antisymm hij (by omega)
  exact this ▸ le_rfl

/-- `L′` is a permutation of `L` that moves only items below `n`: `L′ = L ∘ σ`
for a permutation `σ` fixing every index `≥ n`. -/
def IsPermBelow (n : ℕ) (L L' : ℕ → ℤ) : Prop :=
  ∃ σ : Equiv.Perm ℕ, (∀ k, n ≤ k → σ k = k) ∧ ∀ k, L' k = L (σ k)

theorem IsPermBelow.refl (n : ℕ) (L : ℕ → ℤ) : IsPermBelow n L L :=
  ⟨Equiv.refl ℕ, fun _ _ => rfl, fun _ => rfl⟩

theorem IsPermBelow.mono {n m : ℕ} (hnm : n ≤ m) {L L' : ℕ → ℤ} (h : IsPermBelow n L L') :
    IsPermBelow m L L' :=
  let ⟨σ, hfix, hL⟩ := h
  ⟨σ, fun k hk => hfix k (le_trans hnm hk), hL⟩

theorem IsPermBelow.trans {n : ℕ} {L L' L'' : ℕ → ℤ} (h₁ : IsPermBelow n L L') (h₂ : IsPermBelow n L' L'') :
    IsPermBelow n L L'' :=
  let ⟨σ, hσ, hL'⟩ := h₁
  let ⟨τ, hτ, hL''⟩ := h₂
  ⟨τ.trans σ, fun k hk => by simp only [Equiv.trans_apply, hτ k hk, hσ k hk],
   fun k => by rw [hL'', hL', Equiv.trans_apply]⟩

/-- Items at or above `n` are unchanged. -/
theorem IsPermBelow.eq_of_le {n : ℕ} {L L' : ℕ → ℤ} (h : IsPermBelow n L L') {k : ℕ} (hk : n ≤ k) :
    L' k = L k :=
  let ⟨_, hfix, hL⟩ := h
  by rw [hL, hfix k hk]

/-- A permutation fixing every index `≥ n` maps indices `< n` to indices `< n`. -/
theorem IsPermBelow.apply_lt {n : ℕ} {σ : Equiv.Perm ℕ} (hfix : ∀ k, n ≤ k → σ k = k) {k : ℕ} (hk : k < n) :
    σ k < n := by
  by_contra hge
  have h1 : σ (σ k) = σ k := hfix _ (not_lt.mp hge)
  have : σ k = k := σ.injective h1
  omega

/-- An upper bound on the items below `n` is preserved by a permutation of them. -/
theorem IsPermBelow.le_of_forall_le {n : ℕ} {L L' : ℕ → ℤ} (h : IsPermBelow n L L') {c : ℤ}
    (hc : ∀ k, k < n → L k ≤ c) : ∀ k, k < n → L' k ≤ c :=
  let ⟨_, hfix, hL⟩ := h
  fun k hk => by rw [hL]; exact hc _ (IsPermBelow.apply_lt hfix hk)

/-- `swap i j = L i:= L j || L j:= L i`, as the simultaneous update `L ∘ (i ↔ j)`. -/
def swap (i j : ℕ) : Spec LS := fun s s' => s' = { s with L := s.L ∘ Equiv.swap i j }

/-- The item-level reading of `L i:= L j || L j:= L i`: each side reads the
initial values, and all other items (and the time) are unchanged. -/
theorem swap_iff (i j : ℕ) (s s' : LS) :
    swap i j s s' ↔
      s'.L i = s.L j ∧ s'.L j = s.L i ∧ (∀ k, k ≠ i → k ≠ j → s'.L k = s.L k) ∧ s'.t = s.t := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_, fun k hki hkj => ?_, rfl⟩ <;> simp [Equiv.swap_apply_of_ne_of_ne, *]
  · rintro ⟨hi, hj, hk, ht⟩
    cases s
    cases s'
    simp only at hi hj hk ht
    subst ht
    simp only [swap]
    congr 1
    funext k
    by_cases hki : k = i
    · subst hki; simp [hi]
    by_cases hkj : k = j
    · subst hkj; simp [hj]
    simp [hk k hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]

/-- `swap` establishes the permutation conjunct. -/
theorem swap_isPermBelow {i j n : ℕ} (hi : i < n) (hj : j < n) {s s' : LS} (h : swap i j s s') :
    IsPermBelow n s.L s'.L := by
  subst h
  exact ⟨Equiv.swap i j, fun k hk => Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), fun _ => rfl⟩

/-- `sort n ⇒ sort′ (n+1)`, together with the permutation conjunct (see the module
docstring for why it must be carried). -/
def sortStep (n : ℕ) : Spec LS := fun s s' =>
  IsPermBelow (n + 1) s.L s'.L ∧ (sorted s.L n → sorted s'.L (n + 1))

/-- `sort n ⇒ sort′ (n+1) ⇐ if n=0 then ok else if L (n–1) ≤ L n then ok else
swap (n–1) n. sort (n–1) ⇒ sort′ n`. "If we consider `sort n ⇒ sort′ (n+1)` to
be a procedure with parameter `n` we are finished; the final specification
`sort (n–1) ⇒ sort′ n` calls the same procedure with argument `n–1`" — the
recursive call is taken as a specification (Section 6.1). -/
theorem sortStep_refines (n : ℕ) :
    Refines (sortStep n)
      (cond (fun _ => n = 0) ok
        (cond (fun s => s.L (n - 1) ≤ s.L n) ok
          (seq (swap (n - 1) n) (sortStep (n - 1))))) := by
  rintro s s' (⟨hn, rfl⟩ | ⟨hn, (⟨hle, rfl⟩ | ⟨hlt, u, hswap, hperm, hsort⟩)⟩)
  · subst hn
    exact ⟨IsPermBelow.refl _ _, fun _ => sorted_one _⟩
  · refine ⟨IsPermBelow.refl _ _, fun hs i j hij hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hs i j hij hj
    rcases Nat.lt_or_ge i j with hi | hi
    · exact le_trans (hs i (j - 1) (by omega) (by omega)) hle
    · have : i = j := le_antisymm hij hi
      exact this ▸ le_rfl
  · have hlt' : s.L n < s.L (n - 1) := not_le.mp hlt
    have hn1 : n - 1 + 1 = n := by omega
    -- the swap, item by item
    have hu := (swap_iff _ _ _ _).mp hswap
    obtain ⟨hu1, hu2, hu3, -⟩ := hu
    have hperm₁ : IsPermBelow (n + 1) s.L u.L := swap_isPermBelow (by omega) (by omega) hswap
    rw [hn1] at hperm hsort
    refine ⟨hperm₁.trans (hperm.mono (by omega)), fun hs => ?_⟩
    -- item n now holds the maximum of the old items 0,..n
    have hmax : ∀ k, k < n → u.L k ≤ u.L n := by
      intro k hk
      rw [hu2]
      by_cases hk1 : k = n - 1
      · subst hk1; rw [hu1]; exact le_of_lt hlt'
      · rw [hu3 k hk1 (by omega)]
        exact hs k (n - 1) (by omega) (by omega)
    -- the swap leaves items 0,..n–1 sorted
    have hus : sorted u.L (n - 1) := fun i j hij hj => by
      rw [hu3 i (by omega) (by omega), hu3 j (by omega) (by omega)]
      exact hs i j hij (by omega)
    have hs' : sorted s'.L n := hsort hus
    have hn' : s'.L n = u.L n := hperm.eq_of_le le_rfl
    intro i j hij hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact hs' i j hij hj
    rcases Nat.lt_or_ge i j with hi | hi
    · rw [hn']
      exact hperm.le_of_forall_le hmax i hi
    · have : i = j := le_antisymm hij hi
      exact this ▸ le_rfl

/-- The for-loop invariant `sort n ⇒ sort′ (#L)` (with the permutation conjunct
for the whole list). -/
def sortLoop (len n : ℕ) : Spec LS := fun s s' =>
  IsPermBelow len s.L s'.L ∧ (sorted s.L n → sorted s'.L len)

/-- `sort 0 ⇒ sort′ (#L) ⇐ for n:= 0;..#L do sort n ⇒ sort′ (n+1)`, as the
for-loop obligations of Section 5.2.3. -/
theorem sortLoop_forRefines (len : ℕ) : ForRefines (sortLoop len) 0 len sortStep := by
  refine ⟨fun i _ hi s s' ⟨u, ⟨hperm₁, hsort₁⟩, hperm₂, hsort₂⟩ => ?_, fun s s' h => ?_⟩
  · exact ⟨(hperm₁.mono (by omega)).trans hperm₂, fun hs => hsort₂ (hsort₁ hs)⟩
  · rw [Spec.ok] at h
    subst h
    exact ⟨IsPermBelow.refl _ _, id⟩

/-- The specification of Exercise 209 without its time conjunct:
`(L′ is a permutation of L) ∧ sort′ (#L)`; it is `sort 0 ⇒ sort′ (#L)` "since
`sort 0` is a theorem". -/
theorem sortLoop_zero (len : ℕ) :
    sortLoop len 0 = fun s s' => IsPermBelow len s.L s'.L ∧ sorted s'.L len :=
  Spec.ext fun s _ => by
    simp only [sortLoop, sorted_zero, true_implies]

/-! ### Opportunities for concurrency (aPToP §8.1.1)

"Let `C n` stand for the comparison `L (n–1) ≤ L n` and let `S n` stand for
`swap (n–1) n`. ... If `i` and `j` differ by more than `1`, then `S i` and `S j`
can be executed concurrently. Under the same condition, `S i` can be executed
and `C j` can be evaluated concurrently." What is proved: swaps on four distinct
items commute (so by Section 8.1 either order, hence a concurrent execution,
gives the same result), and a swap leaves a comparison on other items
unchanged. The linear-time execution pattern is not formalized. -/

/-- `swap`s on disjoint pairs of items commute. -/
theorem swap_swap_comm {i j k l : ℕ} (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    seq (swap i j) (swap k l) = seq (swap k l) (swap i j) := by
  refine Spec.ext fun s s' => ?_
  simp only [seq, swap, exists_eq_left]
  have : (s.L ∘ Equiv.swap i j) ∘ Equiv.swap k l = (s.L ∘ Equiv.swap k l) ∘ Equiv.swap i j := by
    funext x
    simp only [Function.comp, Equiv.swap_apply_def]
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [this]

/-- `S i` and `S j` commute when `i` and `j` differ by more than `1`. -/
theorem S_comm {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (h : 1 < i - j ∨ 1 < j - i) :
    seq (swap (i - 1) i) (swap (j - 1) j) = seq (swap (j - 1) j) (swap (i - 1) i) :=
  swap_swap_comm (by omega) (by omega) (by omega) (by omega)

/-- A swap of items `i`, `j` does not change a comparison `L k ≤ L l` on other items. -/
theorem swap_preserves_cmp {i j k l : ℕ} (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j)
    {s s' : LS} (h : swap i j s s') : (s'.L k ≤ s'.L l ↔ s.L k ≤ s.L l) := by
  obtain ⟨-, -, hk, -⟩ := (swap_iff _ _ _ _).mp h
  rw [hk k hki hkj, hk l hli hlj]

/-- `S i` does not disturb `C j` when `i` and `j` differ by more than `1`. -/
theorem S_preserves_C {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (h : 1 < i - j ∨ 1 < j - i)
    {s s' : LS} (hs : swap (i - 1) i s s') : (s'.L (j - 1) ≤ s'.L j ↔ s.L (j - 1) ≤ s.L j) :=
  swap_preserves_cmp (by omega) (by omega) (by omega) (by omega) hs

end ISort

end LaPToP.Concurrency
