import LaPToP.Interaction.Deadlock
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Power series multiplication

This module formalizes Subsection 9.1.10 (Power Series Multiplication) of
Eric Hehner's *A Practical Theory of Programming* (aPToP), Exercise 527.

"Write a program to read from channel `a` an infinite sequence of
coefficients `a0 a1 a2 a3 ...` of a power series ... and concurrently to read
from channel `b` an infinite sequence of coefficients `b0 b1 b2 b3 ...` ... and
concurrently to write on channel `c` the infinite sequence of coefficients
`c0 c1 c2 c3 ...` of the power series ... equal to the product of the two input
series. ... The question provides us with a notation for the coefficients:
`an = Ma ra+n`, `bn = Mb rb+n`, and `cn = Mc wc+n`. ... from which we see
`cn = Σi: 0,..n+1· ai×bn–i`. ... `A×B = a0×b0 + (a0×b1 + a1×b0)×x + (a0×B2 + A1×B1
+ A2×b0)×x2`. ... `P = ⟨c?! rat· C = A×B⟩`. We refine `P c` as follows.

    P c ⇐ (a? || b?). c! a×b.
          new a0: rat := a· new b0: rat := b· new d?! rat·
          P d || ((a? || b?). c! a0×b + a×b0. C = a0×B + D + A×b0)
    C = a0×B + D + A×b0 ⇐ (a? || b? || d?). c! a0×b + d + a×b0. C = a0×B + D + A×b0

That is the whole program: 4 lines! ... Both `P d` and its concurrent process
will be reading from channels `a` and `b` using separate read cursors. ...
The proof is completely straightforward."

## The model

Coefficients are rationals; the scripts are functions `ℕ → ℚ`. The
mathematical heart is the convolution identity
`c(n+2) = a0×b(n+2) + (A1×B1)n + a(n+2)×b0` (`conv_succ_succ`), with
`c0 = a0×b0` and `c1 = a0×b1 + a1×b0`.

The book proves the two refinements by "making all substitutions indicated
by assignment" and then reasoning about the resulting predicates in the
scripts and cursors. The loop refinement is proved here at the program
level: on a state with the cursors `ra`, `rb`, `rd`, `wc` (the local constants
`a0`, `b0` as parameters), with the recursive call as a specification and the
three inputs — on distinct channels, so they commute — composed sequentially
(`loop_refines`). The first refinement involves the local channel `d`, the
local constants, and the process `P d` reading `a` and `b` "using separate read
cursors" (a broadcast) concurrently with the main process; it is proved at the
level of the book's displayed line after the substitutions (`main_step`):
the conjuncts `Mc wc = Ma ra × Mb rb`, `∀n· dn = Σ…` (the specification `P d`),
`Mc wc+1 = Ma ra × Mb rb+1 + Ma ra+1 × Mb rb` and the loop specification at
the shifted cursors together imply `P c`. The substitution step itself, with
process generation and separate cursors, is not modelled as a program.
The book's remarks on where to place time increments are not formalized.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec Finset

namespace PowerSeries

/-- `cn = Σi: 0,..n+1· ai×bn–i`, the coefficients of the product of two power series. -/
def conv (a b : ℕ → ℚ) (n : ℕ) : ℚ := ∑ i ∈ range (n + 1), a i * b (n - i)

/-- `c0 = a0×b0`. -/
theorem conv_zero (a b : ℕ → ℚ) : conv a b 0 = a 0 * b 0 := by simp [conv]

/-- `c1 = a0×b1 + a1×b0`. -/
theorem conv_one (a b : ℕ → ℚ) : conv a b 1 = a 0 * b 1 + a 1 * b 0 := by
  simp [conv, sum_range_succ]

/-- `A×B = a0×b0 + (a0×b1 + a1×b0)×x + (a0×B2 + A1×B1 + A2×b0)×x²`, coefficientwise:
`c(n+2) = a0×b(n+2) + (A1×B1)n + a(n+2)×b0`. -/
theorem conv_succ_succ (a b : ℕ → ℚ) (n : ℕ) :
    conv a b (n + 2) = a 0 * b (n + 2) + conv (fun i => a (i + 1)) (fun i => b (i + 1)) n + a (n + 2) * b 0 := by
  unfold conv
  rw [sum_range_succ', sum_range_succ]
  have : ∀ i ∈ range (n + 1), a (i + 1) * b (n + 2 - (i + 1)) = a (i + 1) * b (n - i + 1) := by
    intro i hi
    rw [mem_range] at hi
    congr 2
    omega
  rw [sum_congr rfl this]
  simp only [Nat.sub_self, Nat.sub_zero]
  ring

/-! ### The specifications, in the scripts and cursors -/

/-- `P c = (C = A×B)`: `∀n· Mc wc+n = Σi: 0,..n+1· Ma ra+i × Mb rb+n–i`. -/
def P (a b c : ℕ → ℚ) (ra rb wc : ℕ) : Prop :=
  ∀ n, c (wc + n) = conv (fun i => a (ra + i)) (fun i => b (rb + i)) n

/-- `C = a0×B + D + A×b0`: `∀n· Mc wc+n = a0 × Mb rb+n + Md rd+n + Ma ra+n × b0`. -/
def Loop (a b d c : ℕ → ℚ) (a0 b0 : ℚ) (ra rb rd wc : ℕ) : Prop :=
  ∀ n, c (wc + n) = a0 * b (rb + n) + d (rd + n) + a (ra + n) * b0

/-- The loop refinement after the substitutions: "`Mc wc = a0 × Mb rb + Md rd + Ma ra × b0
∧ ∀n· Mc wc+1+n = a0 × Mb rb+1+n + Md rd+1+n + Ma ra+1+n × b0` — put the two conjuncts
together — `= ∀n· Mc wc+n = a0 × Mb rb+n + Md rd+n + Ma ra+n × b0`". -/
theorem loop_step (a b d c : ℕ → ℚ) (a0 b0 : ℚ) (ra rb rd wc : ℕ)
    (h0 : c wc = a0 * b rb + d rd + a ra * b0) (h : Loop a b d c a0 b0 (ra + 1) (rb + 1) (rd + 1) (wc + 1)) :
    Loop a b d c a0 b0 ra rb rd wc := by
  intro n
  cases n with
  | zero => simpa using h0
  | succ n =>
    have := h n
    rw [show wc + (n + 1) = wc + 1 + n by omega, show rb + (n + 1) = rb + 1 + n by omega,
      show rd + (n + 1) = rd + 1 + n by omega, show ra + (n + 1) = ra + 1 + n by omega]
    exact this

/-- The first refinement after the substitutions: "`Mc wc = Ma ra × Mb rb ∧ ∃a0, … ·
(∀n· dn = Σi: 0,..n+1· Ma ra+1+i × Mb rb+1+n–i) ∧ Mc wc+1 = Ma ra × Mb rb+1 + Ma ra+1 × Mb rb
∧ (∀n· Mc wc+2+n = Ma ra × Mb rb+2+n + dn + Ma ra+2+n × Mb rb)` — use the first
universal quantification to replace `dn` in the second ... now put the three
conjuncts together `= ∀n· Mc wc+n = Σi: 0,..n+1· Ma ra+i × Mb rb+n–i = P c`". Here
`d` is the local channel's message script read from cursor `0`. -/
theorem main_step (a b c d : ℕ → ℚ) (ra rb wc : ℕ)
    (h0 : c wc = a ra * b rb)
    (hd : ∀ n, d n = conv (fun i => a (ra + 1 + i)) (fun i => b (rb + 1 + i)) n)
    (h1 : c (wc + 1) = a ra * b (rb + 1) + a (ra + 1) * b rb)
    (hloop : Loop a b d c (a ra) (b rb) (ra + 2) (rb + 2) 0 (wc + 2)) :
    P a b c ra rb wc := by
  intro n
  rcases n with _ | _ | n
  · simpa [conv_zero] using h0
  · simpa [conv_one] using h1
  · rw [conv_succ_succ]
    have := hloop n
    rw [show wc + 2 + n = wc + (n + 2) by omega, show rb + 2 + n = rb + (n + 2) by omega,
      show ra + 2 + n = ra + (n + 2) by omega, Nat.zero_add, hd n] at this
    rw [this]
    congr 2
    unfold conv
    refine sum_congr rfl fun i _ => ?_
    simp only
    rw [show ra + 1 + i = ra + (i + 1) by omega, show rb + 1 + (n - i) = rb + (n - i + 1) by omega]

/-! ### The loop refinement at the program level -/

/-- The state of the loop: the time and the cursors `ra`, `rb`, `rd`, `wc`. -/
structure QS where
  /-- The time. -/
  t : ℕ∞
  /-- Read cursor of `a`. -/
  ra : ℕ
  /-- Read cursor of `b`. -/
  rb : ℕ
  /-- Read cursor of the local channel `d`. -/
  rd : ℕ
  /-- Write cursor of `c`. -/
  wc : ℕ

/-- `a?`. -/
def inputA : Spec QS := stepF fun s => { s with ra := s.ra + 1 }
/-- `b?`. -/
def inputB : Spec QS := stepF fun s => { s with rb := s.rb + 1 }
/-- `d?`. -/
def inputD : Spec QS := stepF fun s => { s with rd := s.rd + 1 }

/-- `c! v`. -/
def outputC (c : Scripts ℚ) (v : QS → ℚ) : Spec QS :=
  guardedF (fun s => c.M s.wc = v s ∧ c.T s.wc = s.t) fun s => { s with wc := s.wc + 1 }

/-- `a? || b? || d?`: inputs on distinct channels, composed sequentially (they commute). -/
def inputs : Spec QS := seq inputA (seq inputB inputD)

theorem inputA_inputB_comm : seq inputA inputB = seq inputB inputA := by
  refine Spec.ext fun s s' => ?_
  simp only [inputA, inputB, stepF_seq, stepF]

theorem inputB_inputD_comm : seq inputB inputD = seq inputD inputB := by
  refine Spec.ext fun s s' => ?_
  simp only [inputB, inputD, stepF_seq, stepF]

/-- `C = a0×B + D + A×b0` as a specification on the loop state. -/
def LoopSpec (a b d c : Scripts ℚ) (a0 b0 : ℚ) : Spec QS := fun s _ =>
  Loop a.M b.M d.M c.M a0 b0 s.ra s.rb s.rd s.wc

/-- `C = a0×B + D + A×b0 ⇐ (a? || b? || d?). c! a0×b + d + a×b0. C = a0×B + D + A×b0`, with
`a`, `b`, `d` the messages last read and the recursive call as a specification. -/
theorem loop_refines (a b d c : Scripts ℚ) (a0 b0 : ℚ) :
    Refines (LoopSpec a b d c a0 b0)
      (seq inputs
        (seq (outputC c fun s => a0 * b.M (s.rb - 1) + d.M (s.rd - 1) + a.M (s.ra - 1) * b0)
          (LoopSpec a b d c a0 b0))) := by
  rintro s s' ⟨u, hu, v, ⟨⟨hM, -⟩, rfl⟩, hL⟩
  simp only [inputs, inputA, inputB, inputD, stepF, seq, exists_eq_left] at hu
  subst hu
  simp only [Nat.add_sub_cancel] at hM
  exact loop_step _ _ _ _ a0 b0 _ _ _ _ hM hL

end PowerSeries

end LaPToP.Interaction
