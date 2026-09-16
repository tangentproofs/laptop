import LaPToP.ProgramTheory.Time
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Space

This module formalizes Section 4.3 (Space) and Subsections 4.3.0 (Maximum
Space) and 4.3.1 (Average Space) of Eric Hehner's *A Practical Theory of
Programming* (aPToP), on the Towers of Hanoi (Exercise 293).

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

"To find the average space occupied during a computation, we find the
cumulative space-time product, and then divide by the execution time. Let `p`
be the cumulative space-time product at the start of execution, and `p′` be
the cumulative space-time product at the end of execution. ... An increase in
`p` occurs where there would be an increase in `t`, and the increase is `s`
times the increase in `t`. ... We prove `p:= p + s×(2^n – 1) + (n–2)×2^n + 2 ⇐ …`.
... The average space due to our computation is this additional amount
divided by the execution time. Thus the average space occupied by our
computation is `n + n/(2^n – 1) – 2`. ... Putting together all the proofs for
the Towers of Hanoi problem, we have `MovePile ⇐ if n=0 then ok else n:= n–1.
s:= s+1. m:= m↑s. MovePile. s:= s–1. t:= t+1. p:= p+s. ok. s:= s+1. m:= m↑s.
MovePile. s:= s–1. n:= n+1` where `MovePile` is the specification `n′=n ∧
t′ = t + 2^n – 1 ∧ s′=s ∧ (s ≤ m ≤ s+n ⇒ m′ = s+n) ∧ p′ = p + s×(2^n – 1) + (n–2)×2^n + 2`."

## The model

The state has the number of disks `n : ℕ`, the time `t`, the space `s` and the
maximum space `m`, the last three in `xnat`; disk positions and the tower
parameters are ignored, as the book does. The recursive calls are the
specifications being refined (Section 6.1), `MoveDisk` is `t:= t+1` (or `ok`
when only space is considered). All three refinements are proved by the
book's two cases, the last one via the book's simplified "long line"
`m ≤ s+1+n ⇒ (m:= s+1+n)`.

For the average space the term `(n–2)×2^n` is signed, so that subsection is
formalized on a state with integer space `s` and space-time product `p`
(recorded: the book's space is `xnat`; the values agree for finite space).
The combined `MovePile` at the end of the section is proved on a state with
`n : ℕ`, time and maximum space in `xnat`, finite space `s : ℕ` and `p : ℤ`.
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

/-! ### Average space (aPToP §4.3.1) -/

/-- The state for the space-time product: `n`, the space `s` and the product `p`,
as integers (the term `(n–2)×2^n` is signed). -/
structure AS where
  /-- The number of disks. -/
  n : ℕ
  /-- The space occupied. -/
  s : ℤ
  /-- The cumulative space-time product. -/
  p : ℤ

namespace Avg

/-- `n:= e`. -/
def assignN (e : AS → ℕ) : Spec AS := fun st st' => st' = { st with n := e st }
/-- `s:= e`. -/
def assignS (e : AS → ℤ) : Spec AS := fun st st' => st' = { st with s := e st }
/-- `p:= e`. -/
def assignP (e : AS → ℤ) : Spec AS := fun st st' => st' = { st with p := e st }

theorem assignN_seq (e : AS → ℕ) (P : Spec AS) : seq (assignN e) P = fun st st' => P { st with n := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignS_seq (e : AS → ℤ) (P : Spec AS) : seq (assignS e) P = fun st st' => P { st with s := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignP_seq (e : AS → ℤ) (P : Spec AS) : seq (assignP e) P = fun st st' => P { st with p := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- `s×(2^n – 1) + (n–2)×2^n + 2`, the increase of the space-time product. -/
def incr (n : ℕ) (s : ℤ) : ℤ := s * (2 ^ n - 1) + ((n : ℤ) - 2) * 2 ^ n + 2

/-- `p:= p + s×(2^n – 1) + (n–2)×2^n + 2`. -/
def Pavg : Spec AS := fun st st' => st' = { st with p := st.p + incr st.n st.s }

/-- `p:= p + s×(2^n – 1) + (n–2)×2^n + 2 ⇐ if n=0 then ok else n:= n–1. s:= s+1. (that). s:= s–1.
p:= p + s×1. s:= s+1. (that). s:= s–1. n:= n+1`: "use substitution law 10 times from
right to left ... simplify". -/
theorem avg_refines :
    Refines Pavg
      (cond (fun st => st.n = 0) ok
        (seq (assignN fun st => st.n - 1)
          (seq (assignS fun st => st.s + 1) (seq Pavg (seq (assignS fun st => st.s - 1)
            (seq (assignP fun st => st.p + st.s * 1)
              (seq (assignS fun st => st.s + 1) (seq Pavg (seq (assignS fun st => st.s - 1)
                (assignN fun st => st.n + 1)))))))))) := by
  rintro st st' (⟨hn, hok⟩ | ⟨hn, h⟩)
  · rw [Spec.ok] at hok
    subst st'
    obtain ⟨n, s, p⟩ := st
    simp only at hn
    subst hn
    simp [Pavg, incr]
  · rw [assignN_seq, assignS_seq] at h
    simp only [seq, Pavg, exists_eq_left, assignS, assignP, assignN] at h
    subst h
    obtain ⟨n, s, p⟩ := st
    simp only at hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Pavg, incr, Nat.add_sub_cancel, AS.mk.injEq]
    refine ⟨trivial, by ring, ?_⟩
    push_cast
    ring

/-- "The average space occupied by our computation is `n + n/(2^n – 1) – 2`": the
additional amount `(n–2)×2^n + 2` divided by the execution time `2^n – 1`. -/
theorem average_space (n : ℕ) (h : (2 : ℚ) ^ n - 1 ≠ 0) :
    ((n : ℚ) - 2) * 2 ^ n + 2 = (2 ^ n - 1) * ((n : ℚ) + n / (2 ^ n - 1) - 2) := by
  field_simp
  ring

end Avg

/-! ### The combined `MovePile` (aPToP §4.3, closing) -/

/-- The full state: `n`, the time and the maximum space in `xnat`, finite space `s`,
and the space-time product `p`. -/
structure FS where
  /-- The number of disks. -/
  n : ℕ
  /-- The time. -/
  t : ℕ∞
  /-- The space occupied. -/
  s : ℕ
  /-- The maximum space occupied so far. -/
  m : ℕ∞
  /-- The cumulative space-time product. -/
  p : ℤ

namespace Full

/-- `n:= e`. -/
def assignN (e : FS → ℕ) : Spec FS := fun st st' => st' = { st with n := e st }
/-- `s:= e`. -/
def assignS (e : FS → ℕ) : Spec FS := fun st st' => st' = { st with s := e st }
/-- `m:= e`. -/
def assignM (e : FS → ℕ∞) : Spec FS := fun st st' => st' = { st with m := e st }
/-- `t:= t+1`. -/
def tick : Spec FS := fun st st' => st' = { st with t := st.t + 1 }
/-- `p:= p+s`. -/
def addP : Spec FS := fun st st' => st' = { st with p := st.p + st.s }

theorem assignN_seq (e : FS → ℕ) (P : Spec FS) : seq (assignN e) P = fun st st' => P { st with n := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignS_seq (e : FS → ℕ) (P : Spec FS) : seq (assignS e) P = fun st st' => P { st with s := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem assignM_seq (e : FS → ℕ∞) (P : Spec FS) : seq (assignM e) P = fun st st' => P { st with m := e st } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem tick_seq (P : Spec FS) : seq tick P = fun st st' => P { st with t := st.t + 1 } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩
theorem addP_seq (P : Spec FS) : seq addP P = fun st st' => P { st with p := st.p + st.s } st' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- The specification `MovePile`: `n′=n ∧ t′ = t + 2^n – 1 ∧ s′=s ∧ (s ≤ m ≤ s+n ⇒ m′ = s+n)
∧ p′ = p + s×(2^n – 1) + (n–2)×2^n + 2`. -/
def MovePile : Spec FS := fun st st' =>
  st'.n = st.n ∧ st'.t = st.t + ((2 ^ st.n - 1 : ℕ) : ℕ∞) ∧ st'.s = st.s ∧
    ((st.s : ℕ∞) ≤ st.m ∧ st.m ≤ st.s + st.n → st'.m = st.s + st.n) ∧
    st'.p = st.p + Avg.incr st.n st.s

/-- The combined refinement: `MovePile ⇐ if n=0 then ok else n:= n–1. s:= s+1. m:= m↑s.
MovePile. s:= s–1. t:= t+1. p:= p+s. ok. s:= s+1. m:= m↑s. MovePile. s:= s–1. n:= n+1`. -/
def body : Spec FS :=
  cond (fun st => st.n = 0) ok
    (seq (assignN fun st => st.n - 1)
      (seq (assignS fun st => st.s + 1) (seq (assignM fun st => max st.m st.s) (seq MovePile
        (seq (assignS fun st => st.s - 1) (seq tick (seq addP (seq ok
          (seq (assignS fun st => st.s + 1) (seq (assignM fun st => max st.m st.s) (seq MovePile
            (seq (assignS fun st => st.s - 1) (assignN fun st => st.n + 1)))))))))))))

/-- "Putting together all the proofs for the Towers of Hanoi problem": `MovePile ⇐ body`. -/
theorem movePile_refines : Refines MovePile body := by
  rintro st st' (⟨hn, hok⟩ | ⟨hn, h⟩)
  · rw [Spec.ok] at hok
    subst st'
    obtain ⟨n, t, s, m, p⟩ := st
    simp only at hn
    subst hn
    refine ⟨rfl, by simp, rfl, fun ⟨h1, h2⟩ => ?_, by simp [Avg.incr]⟩
    simp only [Nat.cast_zero, add_zero] at h2 ⊢
    exact le_antisymm h2 h1
  · rw [assignN_seq, assignS_seq, assignM_seq] at h
    obtain ⟨u, ⟨hun, hut, hus, hum, hup⟩, h⟩ := h
    simp only at hun hut hus hum hup
    rw [assignS_seq, tick_seq, addP_seq, ok_seq, assignS_seq, assignM_seq] at h
    obtain ⟨v, ⟨hvn, hvt, hvs, hvm, hvp⟩, hst'⟩ := h
    simp only at hvn hvt hvs hvm hvp
    rw [assignS_seq, assignN] at hst'
    subst hst'
    obtain ⟨n, t, s, m, p⟩ := st
    simp only at hn hun hut hus hum hup hvn hvt hvs hvm hvp ⊢
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hun hut hus hum hup hvn hvt hvs hvm hvp ⊢
    simp only [hus, hun, Nat.add_sub_cancel] at hvn hvt hvs hvm hvp
    simp only [MovePile]
    refine ⟨by rw [hvn], ?_, by rw [hvs, Nat.add_sub_cancel], fun ⟨h1, h2⟩ => ?_, ?_⟩
    · -- time
      rw [hvt, hut, two_pow_succ_sub_one]
      push_cast
      ring
    · -- maximum space
      have hcast : ((k + 1 : ℕ) : ℕ∞) = 1 + (k : ℕ∞) := by push_cast; ring
      have h2' : m ≤ ((s + 1 : ℕ) : ℕ∞) + (k : ℕ∞) := by
        rw [hcast, ← add_assoc] at h2
        simpa using h2
      have hu : u.m = ((s + 1 : ℕ) : ℕ∞) + (k : ℕ∞) := hum ⟨le_max_right _ _, max_le h2' le_self_add⟩
      have hv : v.m = ((s + 1 : ℕ) : ℕ∞) + (k : ℕ∞) := by
        rw [hu, max_eq_left le_self_add] at hvm
        exact hvm ⟨le_self_add, le_rfl⟩
      rw [hv, hcast]
      push_cast
      ring
    · -- space-time product
      rw [hvp, hup]
      simp only [Avg.incr]
      push_cast
      ring

end Full

end Hanoi

end LaPToP.ProgramTheory
