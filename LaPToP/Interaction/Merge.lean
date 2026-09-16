import LaPToP.Interaction.CommunicationTiming

/-!
# Merge and monitor

This module formalizes Subsections 9.1.4 (Merge) and 9.1.5 (Monitor) of
Eric Hehner's *A Practical Theory of Programming* (aPToP).

"Merging means reading repeatedly from two or more input channels and
writing those inputs onto an output channel. The output is an interleaving
of the messages from the input channels. The output must be all and only the
messages read from the inputs, and it must preserve the order in which they
were read on each channel. ... Let the input channels be `c` and `d`, and the
output channel be `e`. Then `merge = (c?. e! c) ∨ (d?. e! d). merge`. ...
Exercise 521(a) (time merge) asks us to choose the first available input at
each step. ... `timemerge = (√c ∨ Tc rc ≤ Td rd) ∧ (c?. e! c) ∨ (√d ∨ Tc rc ≥ Td rd)
∧ (d?. e! d). timemerge`. To account for the time spent waiting for input, we
should insert `t:= t↑(T r + 1)` just before each input operation, and for
recursive time we should insert `t:= t+1` before the recursive call. ... Using
the same reasoning, we implement `timemerge` as follows.
`timemerge ⇐ if √c then c?. e! c else ok. if √d then d?. e! d else ok. t:= t+1. timemerge`
where time is an extended natural."

## The model

Three channels `c`, `d`, `e` (scripts as constants, cursors in the state
`MS`), the transit-time check `√c = Tc rc + 1 ≤ t` of Subsection 9.1.2, and the
recursive call as a specification, as in `LaPToP.Interaction.CommunicationTiming`.
`timemergeBody` includes the waits and the time increment the book says to
insert. Proved: one step of `merge` outputs exactly the message just read
("all and only the messages read"); an iteration of the implementation is a
`timemerge` step when input is available on exactly one channel.

*Honesty note.* The book asserts the refinement `timemerge ⇐ …` "using the
same reasoning" as for Exercise 516(a) and gives no proof. One iteration of
the implementation is *not* in general one step of `timemerge`: when input is
available on both channels the implementation reads both, and when on
neither it reads nothing and just lets time pass; `not_step_refines` gives
the two-inputs counterexample. The book's refinement is one of fixed points
(a two-input iteration is two `timemerge` steps, a no-input iteration is the
waiting hidden in `t:= t↑(T r + 1)`); it is not formalized here.

The monitor of Subsection 9.1.5 (two writers, two readers) is defined the
same way, with the criterion "`√xin0 ∨ Txin0 rxin0 = m`" where `m` is the
minimum of the next-input times, and the analogous one-available-input
lemma is proved for each of the four channels.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

/-- A deterministic step `σ:= f σ`. -/
def stepF {σ : Type} (f : σ → σ) : Spec σ := fun s s' => s' = f s

/-- A guarded deterministic step, `P ∧ (σ:= f σ)` — the shape of an output `c! e`. -/
def guardedF {σ : Type} (P : σ → Prop) (f : σ → σ) : Spec σ := fun s s' => P s ∧ s' = f s

theorem stepF_seq {σ : Type} (f : σ → σ) (Q : Spec σ) : seq (stepF f) Q = fun s s' => Q (f s) s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hQ⟩ => h ▸ hQ, fun hQ => ⟨_, rfl, hQ⟩⟩

theorem guardedF_seq {σ : Type} (P : σ → Prop) (f : σ → σ) (Q : Spec σ) :
    seq (guardedF P f) Q = fun s s' => P s ∧ Q (f s) s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, ⟨hP, h⟩, hQ⟩ => ⟨hP, h ▸ hQ⟩, fun ⟨hP, hQ⟩ => ⟨_, ⟨hP, rfl⟩, hQ⟩⟩

/-! ### Merge (aPToP §9.1.4) -/

/-- The state for merging: the time and the cursors of the channels `c`, `d`, `e`. -/
structure MS where
  /-- The time. -/
  t : ℕ∞
  /-- Read cursor of `c`. -/
  rc : ℕ
  /-- Write cursor of `c`. -/
  wc : ℕ
  /-- Read cursor of `d`. -/
  rd : ℕ
  /-- Write cursor of `d`. -/
  wd : ℕ
  /-- Read cursor of `e`. -/
  re : ℕ
  /-- Write cursor of `e`. -/
  we : ℕ

namespace Merge

variable (c d e : Scripts ℤ)

/-- `c?`. -/
def inputC : Spec MS := stepF fun s => { s with rc := s.rc + 1 }

/-- `d?`. -/
def inputD : Spec MS := stepF fun s => { s with rd := s.rd + 1 }

/-- `e! v`. -/
def outputE (v : MS → ℤ) : Spec MS :=
  guardedF (fun s => e.M s.we = v s ∧ e.T s.we = s.t) fun s => { s with we := s.we + 1 }

/-- `c = Mc (rc–1)`. -/
def lastC (s : MS) : ℤ := c.M (s.rc - 1)

/-- `d = Md (rd–1)`. -/
def lastD (s : MS) : ℤ := d.M (s.rd - 1)

/-- `√c = Tc rc + 1 ≤ t` (transit time measure). -/
def checkC (s : MS) : Prop := c.T s.rc + 1 ≤ s.t

/-- `√d`. -/
def checkD (s : MS) : Prop := d.T s.rd + 1 ≤ s.t

/-- `t:= t↑(Tc rc + 1)`, the wait before `c?`. -/
def waitC : Spec MS := stepF fun s => { s with t := max s.t (c.T s.rc + 1) }

/-- `t:= t↑(Td rd + 1)`. -/
def waitD : Spec MS := stepF fun s => { s with t := max s.t (d.T s.rd + 1) }

/-- `t:= t+1`. -/
def tick : Spec MS := stepF fun s => { s with t := s.t + 1 }

/-- `merge = (c?. e! c) ∨ (d?. e! d). merge`, as a function of the unknown `merge`. -/
def mergeBody (M : Spec MS) : Spec MS :=
  seq (or (seq inputC (outputE e (lastC c))) (seq inputD (outputE e (lastD d)))) M

/-- "The output must be all and only the messages read from the inputs": one step
of `merge` reads one message, from `c` or from `d`, and writes exactly that message
on `e` at the current time. -/
theorem mergeBody_step (M : Spec MS) (s s' : MS) (h : mergeBody c d e M s s') :
    ∃ u, M u s' ∧ u.we = s.we + 1 ∧ e.T s.we = s.t ∧ u.t = s.t ∧
      ((u.rc = s.rc + 1 ∧ u.rd = s.rd ∧ e.M s.we = c.M s.rc) ∨ (u.rd = s.rd + 1 ∧ u.rc = s.rc ∧ e.M s.we = d.M s.rd)) := by
  simp only [mergeBody, seq, Spec.or, inputC, inputD, outputE, stepF, guardedF, lastC, lastD, exists_eq_left] at h
  obtain ⟨u, (⟨⟨hM, hT⟩, rfl⟩ | ⟨⟨hM, hT⟩, rfl⟩), hu⟩ := h
  · simp only [Nat.add_sub_cancel] at hM
    exact ⟨_, hu, rfl, hT, rfl, Or.inl ⟨rfl, rfl, hM⟩⟩
  · simp only [Nat.add_sub_cancel] at hM
    exact ⟨_, hu, rfl, hT, rfl, Or.inr ⟨rfl, rfl, hM⟩⟩

/-- `timemerge = (√c ∨ Tc rc ≤ Td rd) ∧ (t:= t↑(Tc rc + 1). c?. e! c) ∨ (√d ∨ Tc rc ≥ Td rd)
∧ (t:= t↑(Td rd + 1). d?. e! d). t:= t+1. timemerge`, with the waits and the time
increment the book says to insert. -/
def timemergeBody (M : Spec MS) : Spec MS :=
  seq (or (and (fun s _ => checkC c s ∨ c.T s.rc ≤ d.T s.rd) (seq (waitC c) (seq inputC (outputE e (lastC c)))))
          (and (fun s _ => checkD d s ∨ d.T s.rd ≤ c.T s.rc) (seq (waitD d) (seq inputD (outputE e (lastD d))))))
    (seq tick M)

/-- The book's implementation, `if √c then c?. e! c else ok. if √d then d?. e! d else ok.
t:= t+1. timemerge`. -/
def implBody (M : Spec MS) : Spec MS :=
  seq (cond (checkC c) (seq inputC (outputE e (lastC c))) ok)
    (seq (cond (checkD d) (seq inputD (outputE e (lastD d))) ok) (seq tick M))

/-- When input is available on `c` and not on `d`, an iteration of the implementation
is a `timemerge` step. -/
theorem step_refines_c (M : Spec MS) :
    Refines (timemergeBody c d e M) (fun s s' => checkC c s ∧ ¬ checkD d s ∧ implBody c d e M s s') := by
  rintro s s' ⟨hc, hd, u, hu, v, hv, w, hw, hM⟩
  rcases hu with ⟨-, _, rfl, hP, rfl⟩ | ⟨hc', -⟩
  · rcases hv with ⟨hd', -⟩ | ⟨-, rfl⟩
    · exact absurd hd' hd
    rw [tick, stepF] at hw
    subst hw
    refine ⟨{ s with t := max s.t (c.T s.rc + 1), rc := s.rc + 1, we := s.we + 1 },
      Or.inl ⟨Or.inl hc, _, rfl, _, rfl, ?_, rfl⟩, _, rfl, ?_⟩
    · simpa [outputE, guardedF, lastC, max_eq_left hc] using hP
    · simpa [max_eq_left hc] using hM
  · exact absurd hc hc'

/-- When input is available on `d` and not on `c`, an iteration of the implementation
is a `timemerge` step. -/
theorem step_refines_d (M : Spec MS) :
    Refines (timemergeBody c d e M) (fun s s' => ¬ checkC c s ∧ checkD d s ∧ implBody c d e M s s') := by
  rintro s s' ⟨hc, hd, u, hu, v, hv, w, hw, hM⟩
  rcases hu with ⟨hc', -⟩ | ⟨-, hus⟩
  · exact absurd hc' hc
  subst u
  rcases hv with ⟨-, _, rfl, hP, rfl⟩ | ⟨hd', -⟩
  · rw [tick, stepF] at hw
    subst hw
    refine ⟨{ s with t := max s.t (d.T s.rd + 1), rd := s.rd + 1, we := s.we + 1 },
      Or.inr ⟨Or.inl hd, _, rfl, _, rfl, ?_, rfl⟩, _, rfl, ?_⟩
    · simpa [outputE, guardedF, lastD, max_eq_left hd] using hP
    · simpa [max_eq_left hd] using hM
  · exact absurd hd hd'

/-- The step-wise refinement does not hold in general: with input available on both
channels the implementation reads both, while one `timemerge` step reads one. -/
theorem not_step_refines :
    ¬ Refines (timemergeBody ⟨fun _ => 0, fun _ => 0⟩ ⟨fun _ => 0, fun _ => 0⟩ ⟨fun _ => 0, fun _ => 1⟩ ok)
        (implBody ⟨fun _ => 0, fun _ => 0⟩ ⟨fun _ => 0, fun _ => 0⟩ ⟨fun _ => 0, fun _ => 1⟩ ok) := by
  intro h
  have := h ⟨1, 0, 0, 0, 0, 0, 0⟩ ⟨2, 1, 0, 1, 0, 0, 2⟩
    ⟨_, Or.inl ⟨by simp [checkC], _, rfl, ⟨rfl, rfl⟩, rfl⟩,
     _, Or.inl ⟨by simp [checkD], _, rfl, ⟨rfl, rfl⟩, rfl⟩, _, rfl, rfl⟩
  obtain ⟨u, hu, w, hw, hM⟩ := this
  rw [tick, stepF] at hw
  simp only [Spec.ok] at hM
  subst hw
  rcases hu with ⟨-, _, rfl, _, rfl, -, rfl⟩ | ⟨-, _, rfl, _, rfl, -, rfl⟩ <;> simp at hM

end Merge

/-! ### Monitor (aPToP §9.1.5) -/

/-- The state of a monitor for `x` with two writers and two readers: the time, the
variable `x`, the read cursors of the input channels `xin0`, `xin1`, `xreq0`, `xreq1`
and the write cursors of the output channels `xack0`, `xack1`, `xout0`, `xout1`. -/
structure MonS where
  /-- The time. -/
  t : ℕ∞
  /-- The monitored variable `x`. -/
  x : ℤ
  /-- Read cursor of `xin0`. -/
  rin0 : ℕ
  /-- Read cursor of `xin1`. -/
  rin1 : ℕ
  /-- Read cursor of `xreq0`. -/
  rreq0 : ℕ
  /-- Read cursor of `xreq1`. -/
  rreq1 : ℕ
  /-- Write cursor of `xack0`. -/
  wack0 : ℕ
  /-- Write cursor of `xack1`. -/
  wack1 : ℕ
  /-- Write cursor of `xout0`. -/
  wout0 : ℕ
  /-- Write cursor of `xout1`. -/
  wout1 : ℕ

namespace Monitor

variable (in0 in1 : Scripts ℤ) (req0 req1 : Scripts Unit) (ack0 ack1 : Scripts Bool) (out0 out1 : Scripts ℤ)

/-- `√xin0`, `√xin1`, `√xreq0`, `√xreq1` (transit time measure). -/
def checkIn0 (s : MonS) : Prop := in0.T s.rin0 + 1 ≤ s.t
def checkIn1 (s : MonS) : Prop := in1.T s.rin1 + 1 ≤ s.t
def checkReq0 (s : MonS) : Prop := req0.T s.rreq0 + 1 ≤ s.t
def checkReq1 (s : MonS) : Prop := req1.T s.rreq1 + 1 ≤ s.t

/-- `m = ⇓[Txin0 rxin0; Txin1 rxin1; Txreq0 rxreq0; Txreq1 rxreq1]`, "the minimum of the
times of the next input on each of the input channels". -/
def m (s : MonS) : ℕ∞ := min (min (in0.T s.rin0) (in1.T s.rin1)) (min (req0.T s.rreq0) (req1.T s.rreq1))

/-- `xin0?. x:= xin0. xack0! ⊤`. -/
def act0 : Spec MonS :=
  seq (stepF fun s => { s with rin0 := s.rin0 + 1 })
    (seq (stepF fun s => { s with x := in0.M (s.rin0 - 1) })
      (guardedF (fun s => ack0.M s.wack0 = true ∧ ack0.T s.wack0 = s.t) fun s => { s with wack0 := s.wack0 + 1 }))

/-- `xin1?. x:= xin1. xack1! ⊤`. -/
def act1 : Spec MonS :=
  seq (stepF fun s => { s with rin1 := s.rin1 + 1 })
    (seq (stepF fun s => { s with x := in1.M (s.rin1 - 1) })
      (guardedF (fun s => ack1.M s.wack1 = true ∧ ack1.T s.wack1 = s.t) fun s => { s with wack1 := s.wack1 + 1 }))

/-- `xreq0?. xout0! x`. -/
def act2 : Spec MonS :=
  seq (stepF fun s => { s with rreq0 := s.rreq0 + 1 })
    (guardedF (fun s => out0.M s.wout0 = s.x ∧ out0.T s.wout0 = s.t) fun s => { s with wout0 := s.wout0 + 1 })

/-- `xreq1?. xout1! x`. -/
def act3 : Spec MonS :=
  seq (stepF fun s => { s with rreq1 := s.rreq1 + 1 })
    (guardedF (fun s => out1.M s.wout1 = s.x ∧ out1.T s.wout1 = s.t) fun s => { s with wout1 := s.wout1 + 1 })

/-- `t:= t+1`. -/
def tick : Spec MonS := stepF fun s => { s with t := s.t + 1 }

/-- `monitor = (√xin0 ∨ Txin0 rxin0 = m) ∧ (xin0?. x:= xin0. xack0! ⊤) ∨ … . t:= t+1. monitor`
(with the recursive-time increment, "just like `timemerge`"). -/
def monitorBody (Mo : Spec MonS) : Spec MonS :=
  seq (or (or (and (fun s _ => checkIn0 in0 s ∨ in0.T s.rin0 = m in0 in1 req0 req1 s) (act0 in0 ack0))
              (and (fun s _ => checkIn1 in1 s ∨ in1.T s.rin1 = m in0 in1 req0 req1 s) (act1 in1 ack1)))
          (or (and (fun s _ => checkReq0 req0 s ∨ req0.T s.rreq0 = m in0 in1 req0 req1 s) (act2 out0))
              (and (fun s _ => checkReq1 req1 s ∨ req1.T s.rreq1 = m in0 in1 req0 req1 s) (act3 out1))))
    (seq tick Mo)

/-- "Here's one way to implement a monitor": `if √xin0 then xin0?. x:= xin0. xack0! ⊤ else ok.
if √xin1 then … else ok. if √xreq0 then xreq0?. xout0! x else ok. if √xreq1 then … else ok. t:= t+1. monitor`. -/
def implBody (Mo : Spec MonS) : Spec MonS :=
  seq (cond (checkIn0 in0) (act0 in0 ack0) ok)
    (seq (cond (checkIn1 in1) (act1 in1 ack1) ok)
      (seq (cond (checkReq0 req0) (act2 out0) ok)
        (seq (cond (checkReq1 req1) (act3 out1) ok) (seq tick Mo))))

/-- Exactly one input channel has input available. -/
def onlyIn0 (s : MonS) : Prop := checkIn0 in0 s ∧ ¬ checkIn1 in1 s ∧ ¬ checkReq0 req0 s ∧ ¬ checkReq1 req1 s
def onlyIn1 (s : MonS) : Prop := ¬ checkIn0 in0 s ∧ checkIn1 in1 s ∧ ¬ checkReq0 req0 s ∧ ¬ checkReq1 req1 s
def onlyReq0 (s : MonS) : Prop := ¬ checkIn0 in0 s ∧ ¬ checkIn1 in1 s ∧ checkReq0 req0 s ∧ ¬ checkReq1 req1 s
def onlyReq1 (s : MonS) : Prop := ¬ checkIn0 in0 s ∧ ¬ checkIn1 in1 s ∧ ¬ checkReq0 req0 s ∧ checkReq1 req1 s

/-- When only `xin0` has input, an iteration of the implementation is a monitor step. -/
theorem step_refines_in0 (Mo : Spec MonS) :
    Refines (monitorBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo)
      (fun s s' => onlyIn0 in0 in1 req0 req1 s ∧ implBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo s s') := by
  rintro s s' ⟨⟨h0, h1, h2, h3⟩, u, hu, v, hv, p, hp, q, hq, w, hw, hM⟩
  rcases hu with ⟨-, hu⟩ | ⟨h0', -⟩
  · obtain ⟨_, rfl, _, rfl, hg, rfl⟩ := hu
    rcases hv with ⟨h1', -⟩ | ⟨-, rfl⟩
    · exact absurd h1' h1
    rcases hp with ⟨h2', -⟩ | ⟨-, rfl⟩
    · exact absurd h2' h2
    rcases hq with ⟨h3', -⟩ | ⟨-, rfl⟩
    · exact absurd h3' h3
    exact ⟨_, Or.inl (Or.inl ⟨Or.inl h0, _, rfl, _, rfl, hg, rfl⟩), w, hw, hM⟩
  · exact absurd h0 h0'

/-- When only `xin1` has input, an iteration of the implementation is a monitor step. -/
theorem step_refines_in1 (Mo : Spec MonS) :
    Refines (monitorBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo)
      (fun s s' => onlyIn1 in0 in1 req0 req1 s ∧ implBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo s s') := by
  rintro s s' ⟨⟨h0, h1, h2, h3⟩, u, hu, v, hv, p, hp, q, hq, w, hw, hM⟩
  rcases hu with ⟨h0', -⟩ | ⟨-, hus⟩
  · exact absurd h0' h0
  subst u
  rcases hv with ⟨-, hv⟩ | ⟨h1', -⟩
  · obtain ⟨_, rfl, _, rfl, hg, rfl⟩ := hv
    rcases hp with ⟨h2', -⟩ | ⟨-, rfl⟩
    · exact absurd h2' h2
    rcases hq with ⟨h3', -⟩ | ⟨-, rfl⟩
    · exact absurd h3' h3
    exact ⟨_, Or.inl (Or.inr ⟨Or.inl h1, _, rfl, _, rfl, hg, rfl⟩), w, hw, hM⟩
  · exact absurd h1 h1'

/-- When only `xreq0` has input, an iteration of the implementation is a monitor step. -/
theorem step_refines_req0 (Mo : Spec MonS) :
    Refines (monitorBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo)
      (fun s s' => onlyReq0 in0 in1 req0 req1 s ∧ implBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo s s') := by
  rintro s s' ⟨⟨h0, h1, h2, h3⟩, u, hu, v, hv, p, hp, q, hq, w, hw, hM⟩
  rcases hu with ⟨h0', -⟩ | ⟨-, hus⟩
  · exact absurd h0' h0
  subst u
  rcases hv with ⟨h1', -⟩ | ⟨-, hvs⟩
  · exact absurd h1' h1
  subst v
  rcases hp with ⟨-, hp⟩ | ⟨h2', -⟩
  · obtain ⟨_, rfl, hg, rfl⟩ := hp
    rcases hq with ⟨h3', -⟩ | ⟨-, rfl⟩
    · exact absurd h3' h3
    exact ⟨_, Or.inr (Or.inl ⟨Or.inl h2, _, rfl, hg, rfl⟩), w, hw, hM⟩
  · exact absurd h2 h2'

/-- When only `xreq1` has input, an iteration of the implementation is a monitor step. -/
theorem step_refines_req1 (Mo : Spec MonS) :
    Refines (monitorBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo)
      (fun s s' => onlyReq1 in0 in1 req0 req1 s ∧ implBody in0 in1 req0 req1 ack0 ack1 out0 out1 Mo s s') := by
  rintro s s' ⟨⟨h0, h1, h2, h3⟩, u, hu, v, hv, p, hp, q, hq, w, hw, hM⟩
  rcases hu with ⟨h0', -⟩ | ⟨-, hus⟩
  · exact absurd h0' h0
  subst u
  rcases hv with ⟨h1', -⟩ | ⟨-, hvs⟩
  · exact absurd h1' h1
  subst v
  rcases hp with ⟨h2', -⟩ | ⟨-, hps⟩
  · exact absurd h2' h2
  subst p
  rcases hq with ⟨-, hq⟩ | ⟨h3', -⟩
  · obtain ⟨_, rfl, hg, rfl⟩ := hq
    exact ⟨_, Or.inr (Or.inr ⟨Or.inl h3, _, rfl, hg, rfl⟩), w, hw, hM⟩
  · exact absurd h3 h3'

end Monitor

end LaPToP.Interaction
