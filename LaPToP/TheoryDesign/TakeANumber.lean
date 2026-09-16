import LaPToP.TheoryDesign.DataTransformation
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Set.Basic

/-!
# Take a number

This module formalizes Section 7.2.1 (Take a Number) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), Exercise 462.

"Maintain a list of natural numbers standing for those that are “in use”. The
three operations are: make the list empty (for initialization); assign to
variable `n` a number that is not in use, and add this number to the list (now
it is in use); given a number `n` that is in use, remove it from the list. The
user's variable is `n: nat`. ... We therefore use a set variable `s ⊆ {nat}`
as our implementer's variable. The three operations are

    start = s′={null} ∧ n′=n
    take  = ¬ n′∈s ∧ s′ = s∪{n′}
    give  = n∈s ⇒ ¬ n′∈s′ ∧ s′∪{n} = s ∧ n′=n

Here is a data transformation that replaces set `s` with natural `m` according
to the transformer `s ⊆ {0,..m}`. Instead of maintaining the exact set of
numbers that are in use, we will maintain a possibly larger set. We will still
never give out a number that is in use."

## The model

User's variable `ℕ` (`n`), old implementer's variable `Set ℕ` (`s`), new
implementer's variable `ℕ` (`m`); `{0,..m}` is `Set.Iio m`. The transformer
does not mention `n`, so `Spec.transform` applies. The book computes the three
transformed specifications after "several omitted steps"; the omitted steps
are filled in here, as equalities:

* `start` transforms to `n′=n`, refined by `ok`;
* `take` transforms to `m ≤ n′ < m′`, refined by `n:= m. m:= m+1`;
* `give` transforms to `n<m ⇒ (n+1=m ⇒ n≤m′) ∧ (n+1<m ⇒ m≤m′) ∧ n′=n`.

*Deviation, recorded honestly.* For `give` the book states the result
`(n+1 = m ⇒ n ≤ m′) ∧ (n+1 < m ⇒ m ≤ m′) ∧ n′=n` without the guard `n<m`.
When `m ≤ n`, no imagined set `s ⊆ {0,..m}` contains `n`, so `give`'s
antecedent is false and the transformed specification is `⊤`; the book's
expression strengthens it to `n′=n`. The book's line is therefore a
refinement of the transformed specification rather than an equality, and
both are refined by `ok`, so the book's conclusion stands. The two-machine
transformers `s ⊆ {0,..i↑j}` and the even/odd split are treated as
refinements: the general lemma `transform_take` covers `s ⊆ {0,..f new}` for
any `f`, and for the even/odd transformer the program
`(n:= i. i:= i+2) ∨ (n:= j. j:= j+2)` is shown to refine the transformed
`take` under the typing `i: 2×nat`, `j: 2×nat+1` (stated as hypotheses
`Even i`, `Odd j`).
-/

namespace LaPToP.TheoryDesign

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

namespace TakeANumber

open Spec

/-- `start = s′={null} ∧ n′=n`. -/
def start : Spec (ℕ × Set ℕ) := fun s s' => s'.2 = ∅ ∧ s'.1 = s.1

/-- `take = ¬ n′∈s ∧ s′ = s∪{n′}`. -/
def take : Spec (ℕ × Set ℕ) := fun s s' => s'.1 ∉ s.2 ∧ s'.2 = s.2 ∪ {s'.1}

/-- `give = n∈s ⇒ ¬ n′∈s′ ∧ s′∪{n} = s ∧ n′=n`. -/
def give : Spec (ℕ × Set ℕ) := fun s s' => s.1 ∈ s.2 → s'.1 ∉ s'.2 ∧ s'.2 ∪ {s.1} = s.2 ∧ s'.1 = s.1

/-- The transformer `s ⊆ {0,..f new}`; the book's single machine is `f = id`
(`s ⊆ {0,..m}`), the two-machine attempt is `f (i, j) = i↑j`. -/
def Dbelow {N : Type} (f : N → ℕ) (s : Set ℕ) (n : N) : Prop := s ⊆ Set.Iio (f n)

/-- `∀new· ∃old· D`: the empty set is below anything. -/
theorem isTransformer_Dbelow {N : Type} (f : N → ℕ) : IsTransformer (Dbelow f) :=
  fun _ => ⟨∅, Set.empty_subset _⟩

/-- `s ⊆ {0,..m}`. -/
abbrev D : Set ℕ → ℕ → Prop := Dbelow id

/-- `start` transforms to `n′=n`: "one-point and identity". For any `f`. -/
theorem transform_start {N : Type} (f : N → ℕ) :
    transform (Dbelow f) start = fun s s' : ℕ × N => s'.1 = s.1 := by
  refine Spec.ext fun s s' => ?_
  simp only [transform, Dbelow, start]
  constructor
  · intro h
    obtain ⟨_, -, -, hn⟩ := h ∅ (Set.empty_subset _)
    exact hn
  · intro hn _ _
    exact ⟨∅, Set.empty_subset _, rfl, hn⟩

/-- `take` transforms to `f new ≤ n′ < f new′` — the book's `m ≤ n′ < m′` for the
single machine and `i↑j ≤ n′ < i′↑j′` for two machines ("several omitted steps"
filled in). -/
theorem transform_take {N : Type} (f : N → ℕ) :
    transform (Dbelow f) take = fun s s' : ℕ × N => f s.2 ≤ s'.1 ∧ s'.1 < f s'.2 := by
  refine Spec.ext fun s s' => ?_
  simp only [transform, Dbelow, take]
  constructor
  · intro h
    obtain ⟨o', ho', hnot, rfl⟩ := h (Set.Iio (f s.2)) subset_rfl
    refine ⟨not_lt.mp hnot, ?_⟩
    exact ho' (Set.mem_union_right _ rfl)
  · rintro ⟨hle, hlt⟩ o ho
    refine ⟨o ∪ {s'.1}, ?_, fun hmem => ?_, rfl⟩
    · intro k hk
      rcases hk with hk | hk
      · exact lt_of_lt_of_le (ho hk) (le_of_lt (lt_of_le_of_lt hle hlt))
      · exact Set.mem_singleton_iff.mp hk ▸ hlt
    · exact absurd (ho hmem) (not_lt.mpr hle)

/-- The exact transformed `give`: `n<m ⇒ (n+1=m ⇒ n≤m′) ∧ (n+1<m ⇒ m≤m′) ∧ n′=n`. -/
theorem transform_give :
    transform D give = fun s s' : ℕ × ℕ =>
      s.1 < s.2 → (s.1 + 1 = s.2 → s.1 ≤ s'.2) ∧ (s.1 + 1 < s.2 → s.2 ≤ s'.2) ∧ s'.1 = s.1 := by
  refine Spec.ext fun ⟨n, m⟩ ⟨n', m'⟩ => ?_
  simp only [transform, D, Dbelow, give, id]
  constructor
  · intro h hnm
    -- the imagined set `{0,..m}`, which contains `n`
    obtain ⟨o', ho', himp⟩ := h (Set.Iio m) subset_rfl
    obtain ⟨-, hunion, -⟩ := himp hnm
    -- the imagined set `{n}`
    obtain ⟨_, -, himp'⟩ := h {n} (fun k hk => Set.mem_singleton_iff.mp hk ▸ hnm)
    obtain ⟨-, -, heq⟩ := himp' rfl
    refine ⟨fun h1 => ?_, fun h1 => ?_, heq⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hpos
      · exact Nat.zero_le _
      have hmem : n - 1 ∈ o' ∪ {n} := hunion ▸ (show n - 1 < m by omega)
      rcases hmem with hmem | hmem
      · have := ho' hmem
        simp only [Set.mem_Iio] at this
        omega
      · exact absurd (Set.mem_singleton_iff.mp hmem) (by omega)
    · have hmem : m - 1 ∈ o' ∪ {n} := hunion ▸ (show m - 1 < m by omega)
      rcases hmem with hmem | hmem
      · have := ho' hmem
        simp only [Set.mem_Iio] at this
        omega
      · exact absurd (Set.mem_singleton_iff.mp hmem) (by omega)
  · intro h o ho
    by_cases hn : n ∈ o
    · have hnm : n < m := ho hn
      obtain ⟨h1, h2, heq⟩ := h hnm
      refine ⟨o \ {n}, fun k hk => ?_, fun _ => ⟨?_, ?_, heq⟩⟩
      · obtain ⟨hko, hkn⟩ := hk
        have hkm : k < m := ho hko
        have hkn' : k ≠ n := hkn
        show k < m'
        omega
      · rw [heq]
        exact fun hk => hk.2 rfl
      · exact Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hn)
    · exact ⟨∅, Set.empty_subset _, fun hn' => absurd hn' hn⟩

/-- The book's stated result for `give`, `(n+1 = m ⇒ n ≤ m′) ∧ (n+1 < m ⇒ m ≤ m′) ∧ n′=n`. -/
def giveBook : Spec (ℕ × ℕ) := fun s s' =>
  (s.1 + 1 = s.2 → s.1 ≤ s'.2) ∧ (s.1 + 1 < s.2 → s.2 ≤ s'.2) ∧ s'.1 = s.1

/-- The book's line refines the transformed `give` (it is the transformed `give`
strengthened by `n′=n` in the case `m ≤ n`, where no imagined set contains `n`). -/
theorem transform_give_refines_book : Refines (transform D give) giveBook := by
  rw [transform_give]
  intro _ _ h _
  exact h

/-- The book's line is not equal to the transformed `give`: with `n = m = 0` the
transformed specification allows `n′ = 1`, the book's line does not. -/
theorem transform_give_ne_book : transform D give ≠ giveBook := by
  rw [transform_give]
  intro h
  have := congrFun (congrFun h (0, 0)) (1, 0)
  simp [giveBook] at this

/-- `n′=n ⇐ ok`: "the transformed specification is just `n′=n`, which is most
efficiently refined as `ok`". -/
theorem start_refines : Refines (transform D start) ok := by
  rw [transform_start]
  rintro _ _ rfl
  rfl

/-- `n:= m. m:= m+1` on the transformed state `(n, m)`. -/
def takeProg : Spec (ℕ × ℕ) := fun s s' => s' = (s.2, s.2 + 1)

/-- `m ≤ n′ < m′ ⇐ n:= m. m:= m+1`. -/
theorem take_refines : Refines (transform D take) takeProg := by
  rw [transform_take]
  rintro s _ rfl
  exact ⟨le_rfl, Nat.lt_succ_self _⟩

/-- The transformed `give` is refined by `ok`. -/
theorem give_refines : Refines (transform D give) ok :=
  fun _ _ h => transform_give_refines_book _ _ (by
    subst h
    exact ⟨fun _ => Nat.le_of_lt_succ (by omega), fun _ => le_rfl, rfl⟩)

/-! ### Two machines (aPToP §7.2.1) -/

/-- The transformer `s ⊆ {0,..i↑j}` for two “take a number” machines. -/
abbrev D₂ : Set ℕ → ℕ × ℕ → Prop := Dbelow fun ij => max ij.1 ij.2

/-- `n:= i↑j. if i≥j then i:= i+1 else j:= j+1`. -/
def takeProg₂ : Spec (ℕ × (ℕ × ℕ)) := fun s s' =>
  s'.1 = max s.2.1 s.2.2 ∧
    ((s.2.2 ≤ s.2.1 ∧ s'.2 = (s.2.1 + 1, s.2.2)) ∨ (¬ s.2.2 ≤ s.2.1 ∧ s'.2 = (s.2.1, s.2.2 + 1)))

/-- `i↑j ≤ n′ < i′↑j′ ⇐ n:= i↑j. if i≥j then i:= i+1 else j:= j+1`. "From the program
on the last line we see that this data transformation does not provide the
independent operation of two machines as we were hoping." -/
theorem take_refines₂ : Refines (transform D₂ take) takeProg₂ := by
  rw [transform_take]
  rintro ⟨n, i, j⟩ ⟨n', i', j'⟩ ⟨hn, (⟨hij, hs⟩ | ⟨hij, hs⟩)⟩ <;>
    simp only [Prod.mk.injEq] at hn hs hij ⊢ <;> obtain ⟨rfl, rfl⟩ := hs <;> subst hn <;>
    constructor <;> simp only [max_def] <;> split_ifs <;> omega

/-- The even/odd transformer `∀k: ~s· even k ∧ k<i ∨ odd k ∧ k<j`, with new
variables `i: 2×nat` and `j: 2×nat+1`. -/
def Deo (s : Set ℕ) (ij : ℕ × ℕ) : Prop := ∀ k ∈ s, (Even k ∧ k < ij.1) ∨ (Odd k ∧ k < ij.2)

theorem isTransformer_Deo : IsTransformer Deo := fun _ => ⟨∅, fun _ h => absurd h (Set.notMem_empty _)⟩

/-- `(n:= i. i:= i+2) ∨ (n:= j. j:= j+2)`. -/
def takeProgEO : Spec (ℕ × (ℕ × ℕ)) :=
  Spec.or (fun s s' => s' = (s.2.1, (s.2.1 + 2, s.2.2))) (fun s s' => s' = (s.2.2, (s.2.1, s.2.2 + 2)))

/-- Under the typing `i: 2×nat`, `j: 2×nat+1`, the program `(n:= i. i:= i+2) ∨
(n:= j. j:= j+2)` refines the transformed `take`: "we can take a number from
either machine without disturbing the other". -/
theorem take_refinesEO {s s' : ℕ × (ℕ × ℕ)} (hi : Even s.2.1) (hj : Odd s.2.2) (h : takeProgEO s s') :
    transform Deo take s s' := by
  obtain ⟨n, i, j⟩ := s
  simp only [takeProgEO, Spec.or] at h hi hj
  intro o ho
  simp only [Deo] at ho
  rcases h with rfl | rfl
  · refine ⟨o ∪ {i}, ?_, fun hmem => ?_, rfl⟩
    · simp only [Deo]
      rintro k (hk | hk)
      · rcases ho k hk with ⟨he, hlt⟩ | ⟨hodd, hlt⟩
        · exact Or.inl ⟨he, by omega⟩
        · exact Or.inr ⟨hodd, hlt⟩
      · rw [Set.mem_singleton_iff.mp hk]
        exact Or.inl ⟨hi, by omega⟩
    · change i ∈ o at hmem
      rcases ho _ hmem with ⟨_, hlt⟩ | ⟨hodd, _⟩
      · omega
      · exact Nat.not_even_iff_odd.mpr hodd hi
  · refine ⟨o ∪ {j}, ?_, fun hmem => ?_, rfl⟩
    · simp only [Deo]
      rintro k (hk | hk)
      · rcases ho k hk with ⟨he, hlt⟩ | ⟨hodd, hlt⟩
        · exact Or.inl ⟨he, hlt⟩
        · exact Or.inr ⟨hodd, by omega⟩
      · rw [Set.mem_singleton_iff.mp hk]
        exact Or.inr ⟨hj, by omega⟩
    · change j ∈ o at hmem
      rcases ho _ hmem with ⟨he, _⟩ | ⟨_, hlt⟩
      · exact Nat.not_even_iff_odd.mpr hj he
      · omega

end TakeANumber

end LaPToP.TheoryDesign
