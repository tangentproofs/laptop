import LaPToP.Interaction.ChannelDeclaration

/-!
# Deadlock and broadcast

This module formalizes Subsections 9.1.8 (Deadlock) and 9.1.9 (Broadcast) of
Eric Hehner's *A Practical Theory of Programming* (aPToP).

"Let's see what happens if we try to read first and write after (Exercise
528(a)). Inserting the input wait into `new c?! int· c?. c! 5` [we get]
`new c?! int· t:= t↑(T r + 1). c?. c! 5 = … = ∃M· ∃T· M0=5 ∧ T0 = t↑(T0 + 1) ∧ …`.
Look at the conjunct `T0 = t↑(T0 + 1)`. It says `T0 = ∞`. `= x′=x ∧ t′=∞`. The
theory tells us that execution takes forever because the wait for input is
infinite. ... Here's the more traditional example with two processes and two
local channels (Exercise 528(b)). `new c, d?! int· (c?. d! 6) || (d?. c! 7)`.
Inserting the input waits ... after a little work, we obtain
`= ∃Mc, Md· ∃Tc, Td· ∃rc, rc′, wc, wc′, rd, rd′, wd, wd′· Md0=6 ∧ Td0 = t↑(Tc0 + 1) ∧
Mc0=7 ∧ Tc0 = t↑(Td0 + 1) ∧ rc′=wc′=rd′=wd′=1 ∧ x′=x ∧ t′ = t↑(Tc0 + 1)↑(Td0 + 1)`.
The conjuncts `Td0 = t↑(Tc0 + 1)` and `Tc0 = t↑(Td0 + 1)` imply `Td0 = Tc0 = ∞`.
`= x′=x ∧ t′=∞`. To prove that a computation is free from deadlock, prove that
all message times are finite."

"A communication channel must have only a single writing process, but it can
have more than one reading process. This is called a broadcast. ...
Broadcast is achieved by several read cursors, one for each reading process.
Then all reading processes read the same messages, each at its own rate.
There is no harm in two processes reading the same message, even at the same
time. But there is a problem with broadcast: what is the final value of the
read cursor for the concurrent composition? ... For each channel, the final
value of the read cursor in a concurrent composition is the maximum of the
final values of the read cursors of the processes."

## The model

Exercise 528(a) is proved on the one-channel declaration of
`LaPToP.Interaction.ChannelDeclaration`; the key fact is the `xnat` lemma
`a = t↑(a+1) ⇒ a = ∞`. For Exercise 528(b) a two-channel declaration is
defined the same way, and the concurrent composition is taken as the book's
own expansion ("after a little work"), with the partition `rc, wd` to the
left process and `rd, wc` to the right; the mutual waits `Td0 = t↑(Tc0+1)`,
`Tc0 = t↑(Td0+1)` force both message times to `∞`. For broadcast, a channel
with one write cursor and `k` read cursors is defined, with the input of
reader `i` and the message it last read, and the concurrent composition of
readers with "the maximum of the final values of the read cursors"; two
readers reading the same message end with the same cursor.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec LaPToP.ProgramTheory.Time

universe u

/-- In `xnat`, `a + 1 ≤ a` only for `a = ∞`. -/
theorem enat_eq_top_of_add_one_le {a : ℕ∞} (h : a + 1 ≤ a) : a = ⊤ := by
  induction a using ENat.recTopCoe with
  | top => rfl
  | coe n => exact absurd h (by norm_cast; omega)

/-- "`T0 = t↑(T0 + 1)` says `T0 = ∞`." -/
theorem enat_eq_top_of_eq_max_succ {a t : ℕ∞} (h : a = max t (a + 1)) : a = ⊤ :=
  enat_eq_top_of_add_one_le ((le_max_right t (a + 1)).trans_eq h.symm)

/-- "The conjuncts `Td0 = t↑(Tc0 + 1)` and `Tc0 = t↑(Td0 + 1)` imply `Td0 = Tc0 = ∞`." -/
theorem enat_eq_top_of_mutual_wait {a b t : ℕ∞} (ha : a = max t (b + 1)) (hb : b = max t (a + 1)) :
    a = ⊤ ∧ b = ⊤ := by
  have h1 : b + 1 ≤ a := (le_max_right _ _).trans_eq ha.symm
  have h2 : a + 1 ≤ b := (le_max_right _ _).trans_eq hb.symm
  have ha' : a = ⊤ := enat_eq_top_of_add_one_le (le_trans (le_trans h2 le_self_add) h1)
  refine ⟨ha', ?_⟩
  rw [hb, ha']
  simp

/-! ### Exercise 528(a): reading first and writing after -/

namespace Channel

/-- `t:= t↑(T r + 1). c?. c! 5`. -/
def readThenWrite (sc : Scripts ℤ) : Spec CS := seq (wait sc) (seq input (output (fun _ => 5) sc))

/-- `new c?! int· t:= t↑(T r + 1). c?. c! 5 = x′=x ∧ t′=∞`: "execution takes forever
because the wait for input is infinite". -/
theorem newChannel_readThenWrite : newChannel readThenWrite = fun s s' : TSt => s'.x = s.x ∧ s'.t = ⊤ := by
  refine Spec.ext fun s s' => ?_
  simp only [newChannel, readThenWrite, wait, stepF_seq, input_seq, output]
  constructor
  · rintro ⟨M, T, r', w', -, hT, h⟩
    simp only [CS.mk.injEq] at h hT
    obtain ⟨ht, -, -, hx⟩ := h
    have hT' : T 0 = ⊤ := enat_eq_top_of_eq_max_succ hT
    refine ⟨hx, ?_⟩
    rw [ht, hT']
    simp
  · rintro ⟨hx, ht⟩
    refine ⟨fun _ => 5, fun _ => ⊤, 1, 1, rfl, by simp, ?_⟩
    simp only [CS.mk.injEq]
    exact ⟨by rw [ht]; simp, trivial, trivial, hx⟩

end Channel

/-! ### Exercise 528(b): two processes waiting on each other -/

/-- The state outside two local channels `c`, `d`: the time, `x`, and the four cursors. -/
structure DS where
  /-- The time. -/
  t : ℕ∞
  /-- The variable `x`. -/
  x : ℤ
  /-- Read cursor of `c`. -/
  rc : ℕ
  /-- Write cursor of `c`. -/
  wc : ℕ
  /-- Read cursor of `d`. -/
  rd : ℕ
  /-- Write cursor of `d`. -/
  wd : ℕ

/-- `new c, d?! T· S`: both channels' scripts and final cursors quantified, initial
cursors `0`. -/
def newChannel2 {α : Type u} (S : Scripts α → Scripts α → Spec DS) : Spec TSt := fun s s' =>
  ∃ (Mc : ℕ → α) (Tc : ℕ → ℕ∞) (Md : ℕ → α) (Td : ℕ → ℕ∞) (rc' wc' rd' wd' : ℕ),
    S ⟨Mc, Tc⟩ ⟨Md, Td⟩ ⟨s.t, s.x, 0, 0, 0, 0⟩ ⟨s'.t, s'.x, rc', wc', rd', wd'⟩

namespace Deadlock

/-- `(t:= t↑(Tc rc + 1). c?. d! 6) || (t:= t↑(Td rd + 1). d?. c! 7)`, as the book expands
it "after a little work": the left process owns `rc`, `wd`, the right owns `rd`, `wc`;
each finishes at its own time and `t′` is the maximum. -/
def mutualWait (c d : Scripts ℤ) : Spec DS := fun s s' =>
  d.M s.wd = 6 ∧ d.T s.wd = max s.t (c.T s.rc + 1) ∧ c.M s.wc = 7 ∧ c.T s.wc = max s.t (d.T s.rd + 1) ∧
    s'.rc = s.rc + 1 ∧ s'.wd = s.wd + 1 ∧ s'.rd = s.rd + 1 ∧ s'.wc = s.wc + 1 ∧ s'.x = s.x ∧
    s'.t = max (max s.t (c.T s.rc + 1)) (max s.t (d.T s.rd + 1))

/-- `new c, d?! int· (c?. d! 6) || (d?. c! 7) = x′=x ∧ t′=∞`: the two processes wait on
each other forever. -/
theorem newChannel2_mutualWait : newChannel2 mutualWait = fun s s' : TSt => s'.x = s.x ∧ s'.t = ⊤ := by
  refine Spec.ext fun s s' => ?_
  simp only [newChannel2, mutualWait]
  constructor
  · rintro ⟨Mc, Tc, Md, Td, rc', wc', rd', wd', -, hTd, -, hTc, -, -, -, -, hx, ht⟩
    obtain ⟨hd, hc⟩ := enat_eq_top_of_mutual_wait hTd hTc
    refine ⟨hx, ?_⟩
    rw [ht, hc]
    simp
  · rintro ⟨hx, ht⟩
    refine ⟨fun _ => 7, fun _ => ⊤, fun _ => 6, fun _ => ⊤, 1, 1, 1, 1, rfl, by simp, rfl, by simp,
      rfl, rfl, rfl, rfl, hx, ?_⟩
    rw [ht]
    simp

end Deadlock

/-! ### Broadcast (aPToP §9.1.9) -/

/-- A broadcast channel: one write cursor and `k` read cursors, "one for each
reading process". -/
structure BS (k : ℕ) where
  /-- The time. -/
  t : ℕ∞
  /-- The write cursor. -/
  w : ℕ
  /-- The read cursors of the `k` reading processes. -/
  r : Fin k → ℕ

namespace Broadcast

variable {α : Type u} {k : ℕ}

/-- `c?` in reading process `i`: its own read cursor advances. -/
def input (i : Fin k) : Spec (BS k) := stepF fun s => { s with r := Function.update s.r i (s.r i + 1) }

/-- `c` in reading process `i`: the message it last read. -/
def lastRead (sc : Scripts α) (i : Fin k) (s : BS k) : α := sc.M (s.r i - 1)

/-- `c! e`, by the single writing process. -/
def output (e : BS k → α) (sc : Scripts α) : Spec (BS k) :=
  guardedF (fun s => sc.M s.w = e s ∧ sc.T s.w = s.t) fun s => { s with w := s.w + 1 }

/-- The concurrent composition of two reading processes: "the final value of the
read cursor in a concurrent composition is the maximum of the final values of
the read cursors of the processes", and likewise for the time; neither writes. -/
def parReaders (R S : Spec (BS k)) : Spec (BS k) := fun s s' =>
  ∃ sR sS, R s sR ∧ S s sS ∧ s'.w = s.w ∧ (∀ i, s'.r i = max (sR.r i) (sS.r i)) ∧ s'.t = max sR.t sS.t

/-- "All reading processes read the same messages, each at its own rate": readers
`i` and `j` read the messages at their own cursors. -/
theorem input_lastRead (sc : Scripts α) (i : Fin k) (s s' : BS k) (h : input i s s') :
    lastRead sc i s' = sc.M (s.r i) := by
  rw [input, stepF] at h
  subst h
  simp [lastRead]

/-- "There is no harm in two processes reading the same message, even at the same
time": two readers each reading once end with each cursor advanced once. -/
theorem parReaders_input (i j : Fin k) (s s' : BS k) (h : parReaders (input i) (input j) s s') :
    s'.w = s.w ∧ s'.t = s.t ∧ s'.r i = s.r i + 1 ∧ s'.r j = s.r j + 1 := by
  obtain ⟨sR, sS, hR, hS, hw, hr, ht⟩ := h
  rw [input, stepF] at hR hS
  subst hR hS
  refine ⟨hw, by simpa using ht, ?_, ?_⟩
  · rw [hr i]
    simp only [Function.update_self]
    by_cases hij : j = i
    · subst hij; simp
    · rw [Function.update_of_ne (Ne.symm hij)]
      exact max_eq_left (Nat.le_succ _)
  · rw [hr j]
    simp only [Function.update_self]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Function.update_of_ne (Ne.symm hij)]
      exact max_eq_right (Nat.le_succ _)

end Broadcast

end LaPToP.Interaction
