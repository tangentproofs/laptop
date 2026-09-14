import LaPToP.ProgramTheory.WhileLoop
import Mathlib.Tactic.Ring

/-!
# The for-loop

This module formalizes Section 5.2.3 (For-Loop) of Eric Hehner's *A Practical
Theory of Programming* (aPToP): the for-loop as an indexed refinement
notation, the invariant rule, and the book's examples — binary exponentiation
(Exercise 179), loop timing, and adding 1 to each item of a list
(Exercise 326).

## The model

"As with the previous loop constructs, we will not define the for-loop as a
specification, but instead show how it is used in refinement. The for-loop is
indexed, and it refines a specification that is also indexed (a predicate).
Specification `F i` describes the computation from index `i` to the end. ...
To prove `F m ⇐ for i:= m;..n do P od` prove `F i ⇐ i: m,..n ∧ (P. F(i+1))` and
`F n ⇐ ok`."

`Spec.ForRefines F m n P` is *defined* as those two proof obligations. The
index `i` "is not a state variable (so it cannot be assigned within `P`)": it
is a parameter of the body `P i` and of the indexed specification `F i`, and
the bounds `m`, `n` are natural numbers fixed before the loop. Although the
book gives the for-loop no meaning as a specification, the rule has an honest
consequence: `F m` is refined by the `n – m`-fold unrolling
`P m. P (m+1). … . P (n–1). ok` (`Spec.ForRefines.unroll`).

For Exercise 326 the loop bound is `#L`, the length of the list in the
initial state; since the body preserves the length, the indexed
specifications carry the antecedent `#L = N` for a constant `N`, which is the
book's implicit use of the initial value of `#L`.
-/

namespace LaPToP.ProgramTheory

open LaPToP.BasicTheories LaPToP.DataStructures

universe u

namespace Spec

variable {σ : Type u}

/-- `F m ⇐ for i:= m;..n do P od`: "prove `F i ⇐ i: m,..n ∧ (P. F(i+1))` and
`F n ⇐ ok`". -/
def ForRefines (F : ℕ → Spec σ) (m n : ℕ) (P : ℕ → Spec σ) : Prop :=
  (∀ i, m ≤ i → i < n → Refines (F i) (seq (P i) (F (i + 1)))) ∧ Refines (F n) ok

variable {F : ℕ → Spec σ} {m n : ℕ} {P : ℕ → Spec σ}

/-- The iteration obligation: `F i ⇐ i: m,..n ∧ (P. F(i+1))`. -/
theorem ForRefines.step (h : ForRefines F m n P) {i : ℕ} (hm : m ≤ i) (hn : i < n) :
    Refines (F i) (seq (P i) (F (i + 1))) := h.1 i hm hn

/-- The exit obligation: `F n ⇐ ok`. -/
theorem ForRefines.exit (h : ForRefines F m n P) : Refines (F n) ok := h.2

/-- A for-loop with no iterations: `F m ⇐ for i:= m;..m do P od` iff `F m ⇐ ok`. -/
theorem forRefines_self : ForRefines F m m P ↔ Refines (F m) ok :=
  ⟨fun h => h.2, fun h => ⟨fun _ h₁ h₂ => absurd (h₁.trans_lt h₂) (lt_irrefl _), h⟩⟩

/-- `P m. P (m+1). … . P (m+k–1). W`: `k` iterations of the body from index `m`,
followed by `W`. -/
def iterSeq (P : ℕ → Spec σ) (m : ℕ) : ℕ → Spec σ → Spec σ
  | 0, W => W
  | k + 1, W => seq (P m) (iterSeq (fun i => P (i + 1)) m k W)

/-- Unrolling is monotonic in the continuation. -/
theorem iterSeq_mono (P : ℕ → Spec σ) (m k : ℕ) {W W' : Spec σ} (h : Refines W W') :
    Refines (iterSeq P m k W) (iterSeq P m k W') := by
  induction k generalizing P with
  | zero => exact h
  | succ k ih => exact refines_seq_mono (refines_refl _) (ih _)

/-- The for-loop rule has the expected consequence: `F m` is refined by the
`n – m`-fold unrolling `P m. P (m+1). … . P (n–1). ok`. -/
theorem ForRefines.unroll (h : ForRefines F m n P) (hmn : m ≤ n) :
    Refines (F m) (iterSeq P m (n - m) ok) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
  rw [Nat.add_sub_cancel_left]
  induction k generalizing F m P with
  | zero => exact h.2
  | succ k ih =>
    refine refines_trans _ _ _ (h.step le_rfl (by omega)) (refines_seq_mono (refines_refl _) ?_)
    have h' : ForRefines (fun i => F (i + 1)) m (m + k) fun i => P (i + 1) :=
      ⟨fun i hi hik => h.step (by omega) (by omega), by
        show Refines (F (m + k + 1)) ok
        exact h.2⟩
    exact ih h' (by omega)

/-- The invariant for-loop rule: "sometimes the indexed specification for the
for-loop has the form `A m ⇒ A′ n`, where `A i` is a binary expression in
unprimed variables called an invariant. ... `A m ⇒ A′ n ⇐ for i:= m;..n do
i: m,..n ∧ A i ⇒ A′(i+1) od`", and "there is nothing to prove". -/
theorem forRefines_invariant (A : ℕ → σ → Prop) (m n : ℕ) :
    ForRefines (fun i s s' => A i s → A n s') m n fun i s s' => (m ≤ i ∧ i < n ∧ A i s) → A (i + 1) s' :=
  ⟨fun _i hm hn _ _ ⟨_, hP, hF⟩ hA => hF (hP ⟨hm, hn, hA⟩), fun _ _ hok hA => hok ▸ hA⟩

end Spec

/-! ### Exercise 179: binary exponentiation (aPToP §5.2.3) -/

namespace BinaryExponentiation

open Spec

/-- A state with one natural variable `x`. -/
structure XS where
  /-- The natural variable `x`. -/
  x : ℕ

/-- `x:= e`. -/
def assignX (e : XS → ℕ) : Spec XS := fun st st' => st' = { st with x := e st }

/-- Substitution Law for `x:= e`. -/
theorem assignX_seq (e : XS → ℕ) (P : Spec XS) : seq (assignX e) P = fun st st' => P { st with x := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (n : ℕ)

/-- `F i = (x′ = x × 2^(n–i))`: "the final product is the product so far times
the remaining factors". -/
def F (i : ℕ) : Spec XS := fun st st' => st'.x = st.x * 2 ^ (n - i)

/-- `F i ⇐ i: 0,..n ∧ (x:= 2×x. F(i+1))` and `F n ⇐ ok`:
`F 0 ⇐ for i:= 0;..n do x:= 2×x od`. -/
theorem forRefines_F : ForRefines (F n) 0 n fun _ => assignX fun st => 2 * st.x := by
  refine ⟨fun i _ hi st st' h => ?_, fun st st' hok => ?_⟩
  · rw [assignX_seq] at h
    simp only [F] at h ⊢
    rw [h, show n - i = n - (i + 1) + 1 by omega, pow_succ]
    ring
  · simp only [Spec.ok] at hok
    simp [F, hok]

/-- `x′ = 2^n ⇐ x:= 1. F 0`. -/
theorem refine_pow : Refines (fun _ st' : XS => st'.x = 2 ^ n) (seq (assignX fun _ => 1) (F n 0)) := by
  intro st st' h
  rw [assignX_seq] at h
  simpa [F] using h

/-- `x′ = 2^n ⇐ x:= 1. for i:= 0;..n do x:= 2×x od`, with the loop unrolled. -/
theorem refine_pow_unrolled :
    Refines (fun _ st' : XS => st'.x = 2 ^ n)
      (seq (assignX fun _ => 1) (iterSeq (fun _ => assignX fun st => 2 * st.x) 0 n ok)) :=
  steps_seq (refine_pow n) (refines_refl _)
    (by simpa using (forRefines_F n).unroll (Nat.zero_le n))

end BinaryExponentiation

/-! ### Loop timing (aPToP §5.2.3) -/

namespace ForLoopTiming

open Spec

/-- A state with only a time variable. -/
structure TS where
  /-- The time variable. -/
  t : ℕ∞

/-- `t:= t + c`, a body taking time `c`. -/
def addT (c : ℕ) : Spec TS := fun st st' => st' = { st with t := st.t + c }

/-- Substitution Law for `t:= t + c`. -/
theorem addT_seq (c : ℕ) (P : Spec TS) : seq (addT c) P = fun st st' => P { st with t := st.t + c } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (f : ℕ → ℕ) (m n : ℕ)

/-- `F i = (t′ = t + Σj: i,..n· f j)`. -/
def F (i : ℕ) : Spec TS := fun st st' => st'.t = st.t + ((∑ j ∈ Finset.Ico i n, f j : ℕ) : ℕ∞)

/-- `t′ = t + Σi: m,..n· f i ⇐ for i:= m;..n do t′ = t + f i od`: the obligations
`F i ⇐ i: m,..n ∧ (t′ = t + f i. F(i+1))` and `F n ⇐ ok`, "all of which are easy". -/
theorem forRefines_F : ForRefines (F f n) m n fun i => addT (f i) := by
  refine ⟨fun i _ hi st st' h => ?_, fun st st' hok => ?_⟩
  · rw [addT_seq] at h
    simp only [F] at h ⊢
    rw [h, Finset.sum_eq_sum_Ico_succ_bot hi, Nat.cast_add, add_assoc]
  · simp only [Spec.ok] at hok
    simp [F, hok]

/-- `t′ = t + Σi: m,..n· f i ⇐ F m` (they are equal). -/
theorem refine_time : Refines (fun st st' : TS => st'.t = st.t + ((∑ i ∈ Finset.Ico m n, f i : ℕ) : ℕ∞)) (F f n m) :=
  refines_refl _

/-- "When the body takes constant time `c`, this simplifies to
`t′ = t + (n–m)×c ⇐ for i:= m;..n do t′ = t+c od`." -/
theorem forRefines_const (c : ℕ) :
    ForRefines (fun i st st' => st'.t = st.t + (((n - i) * c : ℕ) : ℕ∞)) m n fun _ => addT c := by
  have h := forRefines_F (fun _ => c) m n
  have hF : F (fun _ => c) n = fun i st st' => st'.t = st.t + (((n - i) * c : ℕ) : ℕ∞) := by
    funext i st st'
    simp [F, Finset.sum_const, Nat.card_Ico]
  rwa [hF] at h

end ForLoopTiming

/-! ### Exercise 326: add 1 to each item of a list (aPToP §5.2.3) -/

namespace AddOneToEach

open Spec

/-- A state with one list variable `L`. -/
structure LS where
  /-- The list variable. -/
  L : HList ℤ

/-- `L:= e`. -/
def assignL (e : LS → HList ℤ) : Spec LS := fun st st' => st' = { st with L := e st }

/-- Substitution Law for `L:= e`. -/
theorem assignL_seq (e : LS → HList ℤ) (P : Spec LS) : seq (assignL e) P = fun st st' => P { st with L := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

variable (N : ℕ)

/-- `S = (#L′ = #L ∧ ∀n: ☐L· L′ n = L n + 1)`, for a list of length `N`. -/
def S : Spec LS := fun st st' =>
  st.L.contents.length = N →
    st'.L.contents.length = N ∧ ∀ j, j < N → st'.L.at j = st.L.at j + 1

/-- `F i = (#L′ = #L ∧ (∀n: 0,..i· L′ n = L n) ∧ (∀n: i,..#L· L′ n = L n + 1))`:
"adding 1 to each item from index `i` to (not including) `#L`". -/
def F (i : ℕ) : Spec LS := fun st st' =>
  st.L.contents.length = N →
    st'.L.contents.length = N ∧ (∀ j, j < i → st'.L.at j = st.L.at j) ∧
      ∀ j, i ≤ j → j < N → st'.L.at j = st.L.at j + 1

/-- `S = F 0`: `S ⇐ F 0`. -/
theorem refine_S : Refines (S N) (F N 0) := fun _ _ h hN =>
  let ⟨hl, _, h1⟩ := h hN; ⟨hl, fun j hj => h1 j (Nat.zero_le j) hj⟩

/-- `F i ⇐ i: 0,..#L ∧ (L:= i→L i+1 | L. F(i+1))` and `F(#L) ⇐ ok`:
`F 0 ⇐ for i:= 0;..#L do L:= i→L i+1 | L od`. -/
theorem forRefines_F :
    ForRefines (F N) 0 N fun i => assignL fun st => HList.modify i (st.L.at i + 1) st.L := by
  refine ⟨fun i _ hi st st' h hN => ?_, fun st st' hok hN => ?_⟩
  · rw [assignL_seq] at h
    simp only [F] at h
    obtain ⟨hl, hlow, hhigh⟩ := h (by simpa [HList.length_contents_modify] using hN)
    have hiN : i < st.L.contents.length := hN ▸ hi
    refine ⟨hl, fun j hj => ?_, fun j hij hjN => ?_⟩
    · rw [hlow j (by omega), HList.at_modify_ne _ _ (by omega)]
    · rcases Nat.eq_or_lt_of_le hij with heq | hlt
      · rw [← heq, hlow i (by omega), HList.at_modify_self _ _ hiN]
      · rw [hhigh j hlt hjN, HList.at_modify_ne _ _ (by omega)]
  · simp only [Spec.ok] at hok
    subst hok
    exact ⟨hN, fun _ _ => rfl, fun j hj hjN => absurd (hj.trans_lt hjN) (lt_irrefl _)⟩

end AddOneToEach

end LaPToP.ProgramTheory
