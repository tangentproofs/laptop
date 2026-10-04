import LaPToP.Exercises.Basic
import LaPToP.BasicTheories.Numbers
import LaPToP.DataStructures.Strings
import Mathlib.Tactic

/-!
# Exercises — Basic Data Structures (aPToP §10.2)

Bunches are sets (`LaPToP.BasicTheories.Bunch`), with the arithmetic operators
applied pointwise; strings are lists. Exercises that ask to design notation or
axioms, or to explain (45, 46, 52, 53, 57, 59, 63, 66, 67, 68), and the
simplifications whose meaning rests on the book's untyped bunches of strings and
lists (62, 64), have no formal statement here; they are listed in `MISSING.md`
§5.
-/

namespace LaPToP.Exercises.Ch2

open LaPToP.BasicTheories
open LaPToP.DataStructures
open scoped Pointwise

/-! ### Exercise 41: simplify -/

/-- **Exercise 41(a)**: `(1, 7–3) + 4 – (2, 6, 8) = –3, –1, 0, 2, 3, 6`. -/
theorem exercise_41_a :
    (({1, 7 - 3} : Bunch ℤ) + {4} - {2, 6, 8}) = {-3, -1, 0, 2, 3, 6} := by
  ext x
  simp only [Set.mem_sub, Set.mem_add, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, ⟨a, ha, b, rfl, rfl⟩, c, hc, rfl⟩
    rcases ha with rfl | rfl <;> rcases hc with rfl | rfl | rfl <;> norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨5, ⟨1, .inl rfl, 4, rfl, rfl⟩, 8, .inr (.inr rfl), by norm_num⟩
    · exact ⟨5, ⟨1, .inl rfl, 4, rfl, rfl⟩, 6, .inr (.inl rfl), by norm_num⟩
    · exact ⟨8, ⟨4, .inr (by norm_num), 4, rfl, by norm_num⟩, 8, .inr (.inr rfl), by norm_num⟩
    · exact ⟨8, ⟨4, .inr (by norm_num), 4, rfl, by norm_num⟩, 6, .inr (.inl rfl), by norm_num⟩
    · exact ⟨5, ⟨1, .inl rfl, 4, rfl, rfl⟩, 2, .inl rfl, by norm_num⟩
    · exact ⟨8, ⟨4, .inr (by norm_num), 4, rfl, by norm_num⟩, 2, .inl rfl, by norm_num⟩

/-- **Exercise 41(b)–(d)**: `nat×nat = nat`, `nat–nat = int`,
`(nat+1)×(nat+1) = nat+1`. -/
theorem exercise_41_bcd :
    Bunch.nat * Bunch.nat = Bunch.nat ∧ Bunch.nat - Bunch.nat = Bunch.int ∧
      (Bunch.nat + {1}) * (Bunch.nat + {1}) = Bunch.nat + {1} := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [Set.mem_mul, Bunch.nat, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact mul_nonneg ha hb
    · intro hx; exact ⟨x, hx, 1, by norm_num, by ring⟩
  · ext x
    simp only [Set.mem_sub, Bunch.nat, Bunch.int, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨max x 0, le_max_right _ _, max (-x) 0, le_max_right _ _, by omega⟩
  · ext x
    simp only [Set.mem_mul, Set.mem_add, Bunch.nat, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, _, ⟨b, hb, _, rfl, rfl⟩, rfl⟩
      exact ⟨(a + 1) * (b + 1) - 1, by nlinarith, 1, rfl, by ring⟩
    · rintro ⟨a, ha, _, rfl, rfl⟩
      exact ⟨a + 1, ⟨a, ha, 1, rfl, rfl⟩, 1, ⟨0, le_rfl, 1, rfl, by ring⟩, by ring⟩

/-! ### Exercises 42–44 -/

/-- **Exercise 42**: `¬ 7: null`. -/
theorem exercise_42 : (7 : ℤ) ∉ (Bunch.null : Bunch ℤ) := Set.notMem_empty 7

/-- **Exercise 43**: no harm in a bunch `all` with `A: all` for every `A`: the
bunch of everything (of a type) is one. -/
theorem exercise_43 (α : Type*) : ∃ all : Bunch α, ∀ A : Bunch α, A ⊆ all :=
  ⟨Set.univ, fun A => Set.subset_univ A⟩

/-- **Exercise 44**: `¬ x: A ⇐ ¢(A‘x) = 0`. -/
theorem exercise_44 {α : Type*} (x : α) (A : Bunch α)
    (h : Bunch.size (A ∩ Bunch.elem x) = 0) : x ∉ A := by
  intro hx
  have : A ∩ Bunch.elem x = Bunch.elem x := Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hx)
  rw [this, Bunch.size_elem] at h
  exact one_ne_zero h

/-! ### Exercise 47: how many times `n` is a factor of `m` -/

/-- The two axioms of `⊗`, for a function `f n m = n⊗m`. -/
def Factor (f : ℕ → ℕ → ℕ∞) : Prop :=
  (∀ n m, (∃ k, m = n * k) ∨ f n m = 0) ∧ ∀ n m, n ≠ 0 → f n (m * n) = f n m + 1

theorem eq_top_of_eq_succ {x : ℕ∞} (h : x = x + 1) : x = ⊤ := by
  induction x using ENat.recTopCoe with
  | top => rfl
  | coe n => exact absurd (by exact_mod_cast h : n = n + 1) (by omega)

/-- **Exercise 47(a)**: the chart of `(0,..3)⊗(0,..3)`: `0⊗1 = 0⊗2 = 0`,
`1⊗m = ∞`, `2⊗0 = ∞`, `2⊗1 = 0`, `2⊗2 = 1`; the axioms leave `0⊗0` open. -/
theorem exercise_47_a {f : ℕ → ℕ → ℕ∞} (h : Factor f) :
    f 0 1 = 0 ∧ f 0 2 = 0 ∧ f 1 0 = ⊤ ∧ f 1 1 = ⊤ ∧ f 1 2 = ⊤ ∧ f 2 0 = ⊤ ∧ f 2 1 = 0 ∧
      f 2 2 = 1 := by
  obtain ⟨h₁, h₂⟩ := h
  have z : ∀ n m, ¬ (∃ k, m = n * k) → f n m = 0 := fun n m hn => (h₁ n m).resolve_left hn
  have one : ∀ m, f 1 m = ⊤ := fun m => eq_top_of_eq_succ (by simpa using h₂ 1 m one_ne_zero)
  have f21 : f 2 1 = 0 := z 2 1 (by rintro ⟨k, hk⟩; omega)
  refine ⟨z 0 1 (by simp), z 0 2 (by simp), one 0, one 1, one 2,
    eq_top_of_eq_succ (by simpa using h₂ 2 0 two_ne_zero), f21, ?_⟩
  have := h₂ 2 1 two_ne_zero
  rw [f21] at this; simpa using this

/-- **Exercise 47(b)**: without the antecedent `n ⧧ 0`, the axioms are
inconsistent. -/
theorem exercise_47_b (f : ℕ → ℕ → ℕ∞) :
    ¬ ((∀ n m, (∃ k, m = n * k) ∨ f n m = 0) ∧ ∀ n m, f n (m * n) = f n m + 1) := by
  rintro ⟨h₁, h₂⟩
  have f01 : f 0 1 = 0 := (h₁ 0 1).resolve_left (by simp)
  have a := h₂ 0 1
  have b := eq_top_of_eq_succ (by simpa using h₂ 0 0)
  simp only [f01, zero_add, Nat.one_mul] at a
  rw [b] at a
  exact absurd a (by decide)

/-! ### Exercises 48–51 -/

/-- **Exercise 48**: a bunch of binary values with `A = ¬A` is `null` or
`⊤, ⊥`. -/
theorem exercise_48 (A : Bunch Bool) : A = (! ·) '' A ↔ A = ∅ ∨ A = Set.univ := by
  constructor
  · intro h
    by_cases ht : true ∈ A
    · right
      have hf : false ∈ A := by rw [h]; exact ⟨true, ht, rfl⟩
      ext b; cases b <;> simp [ht, hf]
    · left
      have hf : false ∉ A := by
        rw [h]; rintro ⟨b, hb, hb'⟩
        have : b = true := by simpa using hb'
        exact ht (this ▸ hb)
      ext b; cases b <;> simp [ht, hf]
  · rintro (rfl | rfl)
    · simp
    · ext b; simp only [Set.image_univ, Set.mem_univ, Set.mem_range, true_iff]
      exact ⟨!b, by simp⟩

/-- `n` is a factor of `m`: `m: n×nat`. -/
def Factor' (n m : ℕ) : Prop := ∃ k, m = n * k

/-- **Exercise 49**: (a) everything is a factor of `0`; (b) `0` is a factor of
`0` only; (c) only `1` is a factor of `1`; (d) `1` is a factor of everything. -/
theorem exercise_49 :
    (∀ n, Factor' n 0) ∧ (∀ m, Factor' 0 m ↔ m = 0) ∧ (∀ n, Factor' n 1 ↔ n = 1) ∧
      ∀ m, Factor' 1 m := by
  refine ⟨fun n => ⟨0, by simp⟩, fun m => ⟨fun ⟨k, hk⟩ => by simpa using hk, fun h => ⟨0, by simp [h]⟩⟩,
    fun n => ⟨fun ⟨k, hk⟩ => Nat.eq_one_of_mul_eq_one_right hk.symm, fun h => ⟨1, by simp [h]⟩⟩,
    fun m => ⟨m, by simp⟩⟩

/-- **Exercise 50**: the composite numbers are `(nat+2)×(nat+2)`. -/
theorem exercise_50 (m : ℕ) : (∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ m = a * b) ↔ 2 ≤ m ∧ ¬ m.Prime := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    refine ⟨by nlinarith, fun hp => ?_⟩
    rcases Nat.prime_mul_iff.mp hp with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  · rintro ⟨h2, hp⟩
    obtain ⟨a, ham, ha2, halt⟩ := Nat.exists_dvd_of_not_prime2 h2 hp
    obtain ⟨b, rfl⟩ := ham
    refine ⟨a, b, ha2, ?_, rfl⟩
    by_contra hb
    interval_cases b <;> simp_all

/-- `B = 1, 3, 5`. -/
def B : Finset ℤ := {1, 3, 5}

/-- **Exercise 51**: `¢(B+B) = 5`, `¢(B×2) = 3`, `¢(B×B) = 6`, `¢(B²) = 3`. -/
theorem exercise_51 :
    (B + B).card = 5 ∧ (B * {2}).card = 3 ∧ (B * B).card = 6 ∧ (B.image (· ^ 2)).card = 3 := by
  decide

/-! ### Exercises 54–56 -/

/-- **Exercise 54**: `¢𝒫B > ¢B` is neither a theorem nor an antitheorem: it holds
for `B = null`, and not for `B = nat`, where both are `∞`. -/
theorem exercise_54 :
    (Bunch.size (Bunch.power (Bunch.null : Bunch ℕ)) > Bunch.size (Bunch.null : Bunch ℕ)) ∧
      ¬ (Bunch.size (Bunch.power (Set.univ : Bunch ℕ)) > Bunch.size (Set.univ : Bunch ℕ)) := by
  constructor
  · rw [Bunch.size_null]
    have : (Bunch.pack (∅ : Bunch ℕ)) ∈ Bunch.power (Bunch.null : Bunch ℕ) := by
      simp [Bunch.power, Bunch.pack]
    exact Set.encard_pos.mpr ⟨_, this⟩
  · have hu : Bunch.size (Set.univ : Bunch ℕ) = ⊤ := Set.infinite_univ.encard_eq
    rw [hu]; exact not_top_lt

/-- **Exercise 55**: `$S = ¢~S`, and `A∈S = A: ~S` for an element `A`. -/
theorem exercise_55 {α : Type*} (S : HSet α) (A : α) :
    S.card = Bunch.size S.contents ∧ (A ∈ S ↔ A ∈ S.contents) := ⟨rfl, Iff.rfl⟩

/-- **Exercise 56(a)–(b)**: `¢null = 0` and `¢nil = 1` (`nil` is one string). -/
theorem exercise_56 {α : Type*} :
    Bunch.size (Bunch.null : Bunch α) = 0 ∧ Bunch.size (Bunch.elem (Str.nil : Str α)) = 1 :=
  ⟨Bunch.size_null, Bunch.size_elem _⟩

/-! ### Exercise 58: the prefix order -/

/-- `S` is an initial segment of `T`. -/
def Pre {α : Type*} (S T : Str α) : Prop := ∃ U, S ++ U = T

/-- **Exercise 58**: the prefix order is given by the axioms `nil ≤ S` and
`(i;S) ≤ (j;T) = i=j ∧ S ≤ T` (and nothing longer before `nil`), and it is a
partial order. -/
theorem exercise_58 {α : Type*} :
    (∀ S : Str α, Pre [] S) ∧ (∀ (i : α) S, ¬ Pre (i :: S) []) ∧
    (∀ (i j : α) S T, Pre (i :: S) (j :: T) ↔ i = j ∧ Pre S T) ∧
    (∀ S : Str α, Pre S S) ∧ (∀ S T : Str α, Pre S T → Pre T S → S = T) ∧
    ∀ S T U : Str α, Pre S T → Pre T U → Pre S U := by
  refine ⟨fun S => ⟨S, rfl⟩, fun i S ⟨U, h⟩ => by simp at h, fun i j S T => ?_,
    fun S => ⟨[], by simp⟩, fun S T ⟨U, hU⟩ ⟨V, hV⟩ => ?_, fun S T U ⟨V, hV⟩ ⟨W, hW⟩ => ?_⟩
  · constructor
    · rintro ⟨U, h⟩; simp only [List.cons_append, List.cons.injEq] at h; exact ⟨h.1, U, h.2⟩
    · rintro ⟨rfl, U, rfl⟩; exact ⟨U, rfl⟩
  · subst hU
    have : (S ++ U ++ V).length = S.length := by rw [hV]
    simp only [List.length_append] at this
    have hU : U = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [hU]
  · exact ⟨V ++ W, by rw [← hW, ← hV, List.append_assoc]⟩

/-! ### Exercise 60: strings added item by item -/

/-- **Exercise 60**: `f = 0; 1; f + f[1;..∞]` is the Fibonacci sequence. -/
theorem exercise_60 (f : ℕ → ℕ) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (h : ∀ n, f (n + 2) = f n + f (n + 1)) : f = Nat.fib := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [h0]
    | 1 => simp [h1]
    | n + 2 => rw [h, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega)]

/-! ### Exercise 61: string replacement -/

/-- `S` with its part from `n` to `m` replaced by `T`. -/
def replace {α : Type*} (S : Str α) (n m : ℕ) (T : Str α) : Str α := S.take n ++ T ++ S.drop m

/-- **Exercise 61**: with `n = m` it inserts, with `T = nil` it deletes, at the
end it appends, at the start it prepends. -/
theorem exercise_61 {α : Type*} (S T : Str α) (n m : ℕ) :
    replace S n n T = S.take n ++ T ++ S.drop n ∧ replace S n m [] = S.take n ++ S.drop m ∧
      replace S S.length S.length T = S ++ T ∧ replace S 0 0 T = T ++ S := by
  simp [replace]

/-! ### Exercise 65: lists -/

/-- **Exercise 65**, for `i` and `L i` indexes of `L`: (a) `i→Li | L = L`;
(b) `(Li→i | L) i = L i`; (c) `L[0;..i] ;; [x] ;; L[i+1;..#L] = i→x | L`. -/
theorem exercise_65 (L : List ℕ) (i x : ℕ) (hi : i < L.length) (hLi : L[i] < L.length) :
    L.set i L[i] = L ∧ (L.set L[i] i)[i]'(by simpa using hi) = L[i] ∧
      L.take i ++ [x] ++ L.drop (i + 1) = L.set i x := by
  refine ⟨List.set_getElem_self hi, ?_, ?_⟩
  · rw [List.getElem_set]
    split_ifs with h
    · exact h.symm ▸ rfl
    · rfl
  · rw [List.set_eq_take_append_cons_drop, if_pos hi, List.append_assoc]; rfl

end LaPToP.Exercises.Ch2
