import LaPToP.ProgramTheory.Time
import Mathlib.Tactic.Ring

/-!
# Space

This module formalizes Section 4.3 (Space) and Subsection 4.3.0 (Maximum
Space) of Eric Hehner's *A Practical Theory of Programming* (aPToP), on the
Towers of Hanoi (Exercise 293).

"Our solution is `MovePile “A” “B” “C”` where we refine `MovePile` as follows.
`MovePile from to using ⇐ if n=0 then ok else n:= n–1. MovePile from using to.
MoveDisk from to. MovePile using to from. n:= n+1` ... Our concern is just the
time and space requirements, so we will ignore the disk positions and the
parameters `from`, `to`, and `using`. All we can prove at the moment is that
if `MoveDisk` satisfies `n′=n`, so does `MovePile`. To measure time, we add a
time variable `t`, and use it to count disk moves. We suppose that
`MoveDisk` takes time `1` ... so we replace it by `t:= t+1`. We now prove that
the execution time is `2^n – 1` by replacing `MovePile` with the specification
`t:= t + 2^n – 1`. ... To talk about the memory space used by a computation,
we just add a space variable `s`. Like the time variable `t`, `s` is not part
of the implementation, but only used in specifying and calculating space
requirements. ... To allow for the possibility that execution endlessly
consumes space, we take the domain of space to be the natural numbers
extended with `∞`. Wherever space is being increased, we insert
`s:= s+(the increase)` ... In our example, the recursive calls are not the
last action in the refinement; they require that a return address be pushed
onto a stack at the start of the call, and popped off at the end. Considering
only space, ignoring time and disk movements, we can prove `s′=s ⇐ if n=0 then
ok else n:= n–1. s:= s+1. s′=s. s:= s–1. ok. s:= s+1. s′=s. s:= s–1. n:= n+1`
which says that the space occupied is the same at the end as at the start."

"Let `m` be the maximum space occupied before the start of execution ..., and
`m′` be the maximum space occupied by the end of execution. Implementability
requires `m′≥m`. Wherever space is being increased, we insert `m:= m↑s` to
keep `m` current. In our example, we want to prove that the maximum space
occupied is `n`. However, in a larger context, it may happen that the
starting space `s` is not `0`, so we specify `m′ = s+n`. At the start, `s≤m`,
since `m` is the maximum value of `s`. We assume `m ≤ s+n` so that `m` does not
start larger than the maximum we are trying to prove. The refinement becomes
`s ≤ m ≤ s+n ⇒ (m:= s+n) ⇐ if n=0 then ok else n:= n–1. s:= s+1. m:= m↑s.
s ≤ m ≤ s+n ⇒ (m:= s+n). s:= s–1. ok. s:= s+1. m:= m↑s. s ≤ m ≤ s+n ⇒ (m:= s+n).
s:= s–1. n:= n+1`."

## The model

The state has the number of disks `n : ℕ`, the time `t`, the space `s` and the
maximum space `m`, the last three in `xnat`; disk positions and the tower
parameters are ignored, as the book does. The recursive calls are the
specifications being refined (Section 6.1), `MoveDisk` is `t:= t+1` (or `ok`
when only space is considered). All three refinements are proved by the
book's two cases, the last one via the book's simplified "long line"
`m ≤ s+1+n ⇒ (m:= s+1+n)`.
-/

namespace LaPToP.ProgramTheory

namespace Hanoi

open Spec

/-- The state: the number of disks, the time, the space, and the maximum space. -/
structure HS where
  /-- The number of disks `n`. -/
  n : ℕ
  /-- The time. -/
  t : ℕ∞
  /-- The space occupied. -/
  s : ℕ∞
  /-- The maximum space occupied so far. -/
  m : ℕ∞

/-- `n:= e`. -/
def assignN (e : HS → ℕ) : Spec HS := fun st st' => st' = { st with n := e st }
/-- `t:= t+1`, one disk move. -/
def tick : Spec HS := fun st st' => st' = { st with t := st.t + 1 }
/-- `s:= e`. -/
def assignS (e : HS → ℕ∞) : Spec HS := fun st st' => st' = { st with s := e st }
/-- `m:= e`. -/
def assignM (e : HS → ℕ∞) : Spec HS := fun st st' => st' = { st with m := e st }

theorem assignN_seq (e : HS → ℕ) (P : Spec HS) : seq (assignN e) P = fun st st' => P { st with n := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem tick_seq (P : Spec HS) : seq tick P = fun st st' => P { st with t := st.t + 1 } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignS_seq (e : HS → ℕ∞) (P : Spec HS) : seq (assignS e) P = fun st st' => P { st with s := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignM_seq (e : HS → ℕ∞) (P : Spec HS) : seq (assignM e) P = fun st st' => P { st with m := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `s + 1 – 1 = s` in `xnat`. -/
theorem enat_add_one_sub_one (s : ℕ∞) : s + 1 - 1 = s := by
  induction s using ENat.recTopCoe with
  | top => rfl
  | coe n => norm_cast

/-! ### `n′=n` and the time `2^n – 1` -/

/-- The shape of `MovePile`: `if n=0 then ok else n:= n–1. Pile. Disk. Pile. n:= n+1`, with
the recursive calls `Pile` and the disk move `Disk` as specifications. -/
def movePile (Pile Disk : Spec HS) : Spec HS :=
  cond (fun st => st.n = 0) ok
    (seq (assignN fun st => st.n - 1) (seq Pile (seq Disk (seq Pile (assignN fun st => st.n + 1)))))

/-- "If `MoveDisk` satisfies `n′=n`, so does `MovePile`." -/
theorem movePile_n {Disk : Spec HS} (hD : ∀ st st', Disk st st' → st'.n = st.n) :
    Refines (fun st st' => st'.n = st.n) (movePile (fun st st' => st'.n = st.n) Disk) := by
  rintro st st' (⟨-, rfl⟩ | ⟨hn, h⟩)
  · rfl
  · rw [assignN_seq] at h
    obtain ⟨a, ha, b, hb, c, hc, hd⟩ := h
    simp only at ha
    rw [assignN] at hd
    subst hd
    simp only
    rw [hc, hD a b hb, ha]
    omega

/-- `t:= t + 2^n – 1`. -/
def T : Spec HS := fun st st' => st' = { st with t := st.t + ((2 ^ st.n - 1 : ℕ) : ℕ∞) }

/-- `2^(k+1) – 1 = (2^k – 1) + 1 + (2^k – 1)`. -/
theorem two_pow_succ_sub_one (k : ℕ) : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + 1 + (2 ^ k - 1) := by
  have := Nat.one_le_two_pow (n := k)
  rw [pow_succ]
  omega

/-- `t:= t + 2^n – 1 ⇐ if n=0 then ok else n:= n–1. t:= t + 2^n – 1. t:= t+1. t:= t + 2^n – 1. n:= n+1`,
"by cases": the execution time of the Towers of Hanoi is `2^n – 1`. -/
theorem time_refines : Refines T (movePile T tick) := by
  rintro st st' (⟨hn, hok⟩ | ⟨hn, h⟩)
  · rw [Spec.ok] at hok
    subst st'
    obtain ⟨n, t, s, m⟩ := st
    simp only at hn
    subst hn
    simp [T]
  · rw [assignN_seq] at h
    simp only [seq, exists_eq_left, tick, T, assignN] at h
    subst h
    obtain ⟨n, t, s, m⟩ := st
    simp only at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [T, Nat.add_sub_cancel, HS.mk.injEq, true_and, and_true]
    rw [two_pow_succ_sub_one]
    push_cast
    ring

/-! ### Space: no leaks -/

/-- `s′=s`. -/
def S : Spec HS := fun st st' => st'.s = st.s

/-- The space version of the refinement: `if n=0 then ok else n:= n–1. s:= s+1. Pile. s:= s–1. ok.
s:= s+1. Pile. s:= s–1. n:= n+1` — "the recursive calls ... require that a return
address be pushed onto a stack at the start of the call, and popped off at the end". -/
def movePileSpace (Pile : Spec HS) : Spec HS :=
  cond (fun st => st.n = 0) ok
    (seq (assignN fun st => st.n - 1)
      (seq (assignS fun st => st.s + 1) (seq Pile (seq (assignS fun st => st.s - 1)
        (seq ok (seq (assignS fun st => st.s + 1) (seq Pile (seq (assignS fun st => st.s - 1)
          (assignN fun st => st.n + 1)))))))))

/-- `s′=s ⇐ …`: "the space occupied is the same at the end as at the start". -/
theorem space_refines : Refines S (movePileSpace S) := by
  rintro st st' (⟨-, rfl⟩ | ⟨-, h⟩)
  · rfl
  · rw [assignN_seq, assignS_seq] at h
    obtain ⟨c, hc, d, hd, e, he, f, hf, g, hg, i, hi, hn⟩ := h
    simp only [S] at hc
    rw [assignS] at hd
    subst hd
    rw [Spec.ok] at he
    subst he
    rw [assignS] at hf
    subst hf
    simp only [S] at hg
    rw [assignS] at hi
    subst hi
    rw [assignN] at hn
    subst hn
    simp only [S]
    rw [hg, hc, enat_add_one_sub_one, enat_add_one_sub_one]

/-! ### Maximum space (aPToP §4.3.0) -/

/-- `s ≤ m ≤ s+n ⇒ (m:= s+n)`: the maximum space occupied is `n` more than the initial space. -/
def MS : Spec HS := fun st st' => st.s ≤ st.m ∧ st.m ≤ st.s + st.n → st' = { st with m := st.s + st.n }

/-- "Implementability requires `m′≥m`": the specification never decreases the maximum. -/
theorem MS_m_le {st st' : HS} (h : MS st st') (h1 : st.s ≤ st.m) (h2 : st.m ≤ st.s + st.n) : st.m ≤ st'.m := by
  rw [h ⟨h1, h2⟩]
  exact h2

/-- The book's "long line": `s:= s+1. m:= m↑s. s ≤ m ≤ s+n ⇒ (m:= s+n). s:= s–1`. -/
def longLine (Pile : Spec HS) : Spec HS :=
  seq (assignS fun st => st.s + 1) (seq (assignM fun st => max st.m st.s) (seq Pile (assignS fun st => st.s - 1)))

/-- `m ≤ s+1+n ⇒ (m:= s+1+n)`, what the long line simplifies to. -/
def longLineSpec : Spec HS := fun st st' => st.m ≤ st.s + 1 + st.n → st' = { st with m := st.s + 1 + st.n }

/-- The long line refines `m ≤ s+1+n ⇒ (m:= s+1+n)` ("Use an Assertion Law ... Use
Substitution Law ... Simplify antecedent and rewrite consequent"). -/
theorem longLine_refines : Refines longLineSpec (longLine MS) := by
  intro st st' h hm
  rw [longLine, assignS_seq, assignM_seq] at h
  obtain ⟨u, hu, hs⟩ := h
  simp only at hu
  have hmax : max st.m (st.s + 1) ≤ st.s + 1 + st.n := max_le hm le_self_add
  rw [MS] at hu
  simp only at hu
  rw [hu ⟨le_max_right _ _, hmax⟩] at hs
  rw [assignS] at hs
  subst hs
  obtain ⟨n, t, s, m⟩ := st
  simp only [enat_add_one_sub_one]

/-- The maximum-space refinement, with the long lines: `s ≤ m ≤ s+n ⇒ (m:= s+n) ⇐ if n=0 then ok
else n:= n–1. (long line). ok. (long line). n:= n+1`. -/
def movePileMax (Pile : Spec HS) : Spec HS :=
  cond (fun st => st.n = 0) ok
    (seq (assignN fun st => st.n - 1) (seq (longLine Pile) (seq ok (seq (longLine Pile) (assignN fun st => st.n + 1)))))

/-- The last case with the long lines already simplified: `n:= n–1. m ≤ s+1+n ⇒ (m:= s+1+n).
m ≤ s+1+n ⇒ (m:= s+1+n). n:= n+1 ... = m ≤ s+n ⇒ (s+n ≤ s+n ⇒ s′=s ∧ m′=s+n ∧ n′=n) ⇒
s ≤ m ≤ s+n ⇒ (m:= s+n)`. -/
theorem max_case_refines :
    Refines MS (fun st st' => st.n ≠ 0 ∧
      seq (assignN fun st => st.n - 1) (seq longLineSpec (seq ok (seq longLineSpec (assignN fun st => st.n + 1)))) st st') := by
  rintro st st' ⟨hn, h⟩ ⟨-, hm⟩
  rw [assignN_seq] at h
  obtain ⟨b, hb, c, hc, d, hd, he⟩ := h
  obtain ⟨n, t, s, m⟩ := st
  simp only at hn hm
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [longLineSpec, Nat.add_sub_cancel] at hb
  have hm' : m ≤ s + 1 + (k : ℕ∞) := by
    calc m ≤ s + ((k + 1 : ℕ) : ℕ∞) := hm
      _ = s + 1 + (k : ℕ∞) := by push_cast; ring
  rw [hb hm'] at hc
  rw [Spec.ok] at hc
  subst hc
  simp only [longLineSpec] at hd
  rw [hd le_rfl] at he
  rw [assignN] at he
  subst he
  simp only [HS.mk.injEq, true_and]
  push_cast
  ring

/-- `s ≤ m ≤ s+n ⇒ (m:= s+n) ⇐ if n=0 then ok else n:= n–1. s:= s+1. m:= m↑s. s ≤ m ≤ s+n ⇒ (m:= s+n).
s:= s–1. ok. s:= s+1. m:= m↑s. s ≤ m ≤ s+n ⇒ (m:= s+n). s:= s–1. n:= n+1`: the maximum space
occupied by the Towers of Hanoi is `n` (above the initial space). -/
theorem maxSpace_refines : Refines MS (movePileMax MS) := by
  rintro st st' (⟨hn, hok⟩ | ⟨hn, h⟩)
  · rw [Spec.ok] at hok
    subst st'
    rintro ⟨h1, h2⟩
    obtain ⟨n, t, s, m⟩ := st
    simp only at hn h1 h2
    subst hn
    simp only [Nat.cast_zero, add_zero] at h2 ⊢
    rw [le_antisymm h2 h1]
  · refine max_case_refines st st' ⟨hn, ?_⟩
    exact refines_seq_mono (refines_refl _)
      (refines_seq_mono longLine_refines (refines_seq_mono (refines_refl _)
        (refines_seq_mono longLine_refines (refines_refl _)))) st st' h

end Hanoi

end LaPToP.ProgramTheory
