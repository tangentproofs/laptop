import LaPToP.Interaction.Merge
import LaPToP.ProgramTheory.Time

/-!
# Channel declaration and the reaction controller

This module formalizes Subsections 9.1.7 (Channel Declaration) and 9.1.6
(Reaction Controller) of Eric Hehner's *A Practical Theory of Programming*
(aPToP).

"The next input on a channel is not necessarily the one that was last
previously written on that channel. In one variable `x` and one channel `c`
(ignoring time), `c! 2. c?. x:= c = Mw=2 ∧ w′=w+1 ∧ r′=r+1 ∧ x′=Mr`. We do not
know that initially `w=r`, so we cannot conclude that finally `x′=2`. ...
In order to achieve useful communication between processes, we have to
introduce a local channel. Channel declaration is similar to variable
declaration; it defines a new channel within some local portion of a program
or specification. `new c?! T· S = ∃Mc: ∞*T· ∃Tc: ∞*xnat· new rc, wc: xnat:= 0· S
= ∃Mc· ∃Tc· ∃rc, rc′, wc, wc′: xnat· rc=wc=0 ∧ S`. ... A local channel can be
used without concurrency as a queue, or buffer. For example,
`new c?! int· c! 3. c! 4. c?. x:= c. c?. x:= x+c` assigns `7` to `x`. ...
`new c?! int· c! 2 || (c?. x:= c) = x:= 2`. Replacing `2` by an arbitrary
expression, we have a general theorem equating communication on a local
channel with assignment. If we had included transit time, the result would
have been `x′=2 ∧ t′=t+1 ∧ (other variables unchanged) = x:= 2 || t:= t+1`."

## The model

The channel declaration `newChannel S` quantifies the scripts and the final
cursors existentially and fixes the initial cursors at `0` (the book's
`∃rc, rc′, wc, wc′· rc=wc=0 ∧ S` with the one-point law already applied); the
state outside the declaration is the time and the memory variable `x`
(`LaPToP.ProgramTheory.TSt`). The concurrent composition `c! e || (c?. x:= c)`
is taken as the book's own expansion `Mw=e ∧ w′=w+1 ∧ r′=r+1 ∧ x′=Mr` (with the
input wait for the transit-time variant); a general `||` on channel states is
not defined here. Proved: the "not the last written" example with a
counterexample to `x′=2`; a specification not mentioning the channel is
unchanged by the declaration; the buffer example with time, `x′=7 ∧ t′=t+1`;
and the general theorem `new c?! int· c! e || (c?. x:= c) = x:= e`, with
`t′=t+1` in the transit time measure.

The synchronizer of Subsection 9.1.6 is defined with the `||` of an input on
one channel and an output on another rendered as their sequential composition
(they commute, which is proved), and one step is shown to reply with the
latest datum.
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec LaPToP.ProgramTheory.Time

universe u

/-! ### The next input is not necessarily the last written (aPToP §9.1.7) -/

namespace Channel

/-- `x:= c`, "the message that was last previously read". -/
def assignLast (sc : Scripts ℤ) : Spec CS := stepF fun s => { s with x := lastRead sc s }

/-- `c! 2. c?. x:= c = Mw=2 ∧ Tw=t ∧ w′=w+1 ∧ r′=r+1 ∧ x′=Mr`. -/
theorem output_input_assign (sc : Scripts ℤ) :
    seq (output (fun _ => 2) sc) (seq input (assignLast sc)) =
      fun s s' => sc.M s.w = 2 ∧ sc.T s.w = s.t ∧ s' = ⟨s.t, s.r + 1, s.w + 1, sc.M s.r⟩ := by
  rw [output_seq, input_seq]
  simp only [assignLast, stepF]
  rfl

/-- "We do not know that initially `w=r`, so we cannot conclude that finally `x′=2`":
with an unread earlier output `1`, the input reads `1`. -/
theorem not_last_written :
    ∃ (sc : Scripts ℤ) (s s' : CS), seq (output (fun _ => 2) sc) (seq input (assignLast sc)) s s' ∧ s'.x ≠ 2 :=
  ⟨⟨fun i => if i = 1 then 2 else 1, fun _ => 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 2, 1⟩,
    by rw [output_input_assign]; exact ⟨rfl, rfl, rfl⟩, by decide⟩

end Channel

/-! ### Channel declaration (aPToP §9.1.7) -/

/-- `new c?! T· S = ∃Mc· ∃Tc· ∃rc, rc′, wc, wc′· rc=wc=0 ∧ S`: the scripts and the final
cursors are quantified, the initial cursors are `0`. -/
def newChannel {α : Type u} (S : Scripts α → Spec CS) : Spec TSt := fun s s' =>
  ∃ (M : ℕ → α) (T : ℕ → ℕ∞) (r' w' : ℕ), S ⟨M, T⟩ ⟨s.t, 0, 0, s.x⟩ ⟨s'.t, r', w', s'.x⟩

/-- A specification of the time and `x` only, inside the scope of a channel. -/
def liftChan {α : Type u} (S₀ : Spec TSt) : Scripts α → Spec CS := fun _ s s' => S₀ ⟨s.t, s.x⟩ ⟨s'.t, s'.x⟩

/-- A specification not mentioning the channel is unchanged by the declaration. -/
theorem newChannel_liftChan {α : Type u} [Inhabited α] (S₀ : Spec TSt) : newChannel (liftChan (α := α) S₀) = S₀ :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨_, _, _, _, h⟩ => h, fun h => ⟨fun _ => default, fun _ => 0, 0, 0, h⟩⟩

namespace Channel

/-- `t:= t↑(T r + 1)`, the input wait. -/
def wait (sc : Scripts ℤ) : Spec CS := stepF fun s => { s with t := max s.t (sc.T s.r + 1) }

/-- The buffer example with time:
`c! 3. c! 4. t:= t↑(T r + 1). c?. x:= c. t:= t↑(T r + 1). c?. x:= x+c`. -/
def buffer (sc : Scripts ℤ) : Spec CS :=
  seq (output (fun _ => 3) sc) (seq (output (fun _ => 4) sc)
    (seq (wait sc) (seq input (seq (assignLast sc)
      (seq (wait sc) (seq input (stepF fun s => { s with x := s.x + lastRead sc s })))))))

/-- `new c?! int· c! 3. c! 4. … = x′=7 ∧ t′ = t+1 ∧ (other variables unchanged)`. -/
theorem newChannel_buffer : newChannel buffer = fun s s' : TSt => s'.x = 7 ∧ s'.t = s.t + 1 := by
  refine Spec.ext fun s s' => ?_
  simp only [newChannel, buffer, output_seq, input_seq, wait, assignLast, lastRead, stepF_seq, stepF]
  constructor
  · rintro ⟨M, T, r', w', h3, hT0, h4, hT1, h⟩
    simp only [Nat.add_sub_cancel] at h3 hT0 h4 hT1 h
    rw [hT0, hT1, max_eq_right le_self_add, max_self] at h
    rw [CS.mk.injEq] at h
    obtain ⟨ht, -, -, hx⟩ := h
    exact ⟨by rw [hx, h3, h4]; norm_num, ht⟩
  · rintro ⟨hx, ht⟩
    refine ⟨fun i => if i = 0 then 3 else 4, fun _ => s.t, 2, 2, rfl, rfl, rfl, rfl, ?_⟩
    obtain ⟨t', x'⟩ := s'
    simp only at hx ht
    subst hx ht
    simp only [Nat.add_sub_cancel, max_eq_right le_self_add, max_self]
    norm_num

/-- `c! e || (c?. x:= c)`, "ignoring time", as the book expands it:
`Mw=e ∧ w′=w+1 ∧ r′=r+1 ∧ x′=Mr` (and `t′=t`). -/
def outParIn (e : ℤ) (sc : Scripts ℤ) : Spec CS := fun s s' =>
  sc.M s.w = e ∧ s'.w = s.w + 1 ∧ s'.r = s.r + 1 ∧ s'.x = sc.M s.r ∧ s'.t = s.t

/-- The same with transit time: the output is at time `t` and the input waits for it. -/
def outParInT (e : ℤ) (sc : Scripts ℤ) : Spec CS := fun s s' =>
  sc.M s.w = e ∧ sc.T s.w = s.t ∧ s'.w = s.w + 1 ∧ s'.r = s.r + 1 ∧ s'.x = sc.M s.r ∧ s'.t = max s.t (sc.T s.r + 1)

/-- "Again we cannot say `x′=2` because there may be a previous unread output." -/
theorem not_last_written_par :
    ∃ (sc : Scripts ℤ) (s s' : CS), outParIn 2 sc s s' ∧ s'.x ≠ 2 :=
  ⟨⟨fun i => if i = 1 then 2 else 1, fun _ => 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 2, 1⟩, ⟨rfl, rfl, rfl, rfl, rfl⟩, by decide⟩

/-- `new c?! int· c! e || (c?. x:= c) = x:= e`: "a general theorem equating communication
on a local channel with assignment". -/
theorem newChannel_outParIn (e : ℤ) : newChannel (outParIn e) = fun s s' : TSt => s' = { s with x := e } := by
  refine Spec.ext fun s s' => ?_
  simp only [newChannel, outParIn]
  constructor
  · rintro ⟨M, T, r', w', hM, -, -, hx, ht⟩
    obtain ⟨t', x'⟩ := s'
    rw [TSt.mk.injEq]
    exact ⟨ht, hx.trans hM⟩
  · rintro rfl
    exact ⟨fun _ => e, fun _ => 0, 1, 1, rfl, rfl, rfl, rfl, rfl⟩

/-- With transit time, `new c?! int· c! e || (c?. x:= c) = x′=e ∧ t′=t+1 = x:= e || t:= t+1`. -/
theorem newChannel_outParInT (e : ℤ) :
    newChannel (outParInT e) = fun s s' : TSt => s'.x = e ∧ s'.t = s.t + 1 := by
  refine Spec.ext fun s s' => ?_
  simp only [newChannel, outParInT]
  constructor
  · rintro ⟨M, T, r', w', hM, hT, -, -, hx, ht⟩
    rw [hT, max_eq_right le_self_add] at ht
    exact ⟨hx.trans hM, ht⟩
  · rintro ⟨hx, ht⟩
    exact ⟨fun _ => e, fun _ => s.t, 1, 1, rfl, rfl, rfl, rfl, hx, by rw [ht, max_eq_right le_self_add]⟩

end Channel

/-! ### Reaction controller (aPToP §9.1.6) -/

/-- The synchronizer's state: the time, the read cursors of `digitaldata` and
`request`, and the write cursor of `reply`. -/
structure SyS where
  /-- The time. -/
  t : ℕ∞
  /-- Read cursor of `digitaldata`. -/
  rdd : ℕ
  /-- Read cursor of `request`. -/
  rreq : ℕ
  /-- Write cursor of `reply`. -/
  wrep : ℕ

namespace Synchronizer

variable {α : Type u} (dd : Scripts α) (req : Scripts Unit) (rep : Scripts α)

/-- `digitaldata?`. -/
def inputDD : Spec SyS := stepF fun s => { s with rdd := s.rdd + 1 }

/-- `request?`. -/
def inputReq : Spec SyS := stepF fun s => { s with rreq := s.rreq + 1 }

/-- `digitaldata`, the latest datum read. -/
def latest (s : SyS) : α := dd.M (s.rdd - 1)

/-- `reply! v`. -/
def outputRep (v : SyS → α) : Spec SyS :=
  guardedF (fun s => rep.M s.wrep = v s ∧ rep.T s.wrep = s.t) fun s => { s with wrep := s.wrep + 1 }

/-- `√request` (transit time measure). -/
def checkReq (s : SyS) : Prop := req.T s.rreq + 1 ≤ s.t

/-- `request? || reply! digitaldata`: the two communications are on different
channels and commute, so the composition is rendered sequentially. -/
theorem inputReq_outputRep_comm :
    seq inputReq (outputRep rep (latest dd)) = seq (outputRep rep (latest dd)) inputReq := by
  refine Spec.ext fun s s' => ?_
  simp only [inputReq, outputRep, latest, stepF_seq, guardedF_seq, stepF, guardedF]

/-- `synchronizer = digitaldata?. if √request then request? || reply! digitaldata else ok. synchronizer`. -/
def synchronizerBody (Sy : Spec SyS) : Spec SyS :=
  seq inputDD (seq (cond (checkReq req) (seq inputReq (outputRep rep (latest dd))) ok) Sy)

/-- One step of the synchronizer reads a datum and, if there is a request, replies
with exactly that datum — "the latest". -/
theorem synchronizerBody_step (Sy : Spec SyS) (s s' : SyS) (h : synchronizerBody dd req rep Sy s s') :
    ∃ u, Sy u s' ∧ u.rdd = s.rdd + 1 ∧
      ((checkReq req { s with rdd := s.rdd + 1 } ∧ u.rreq = s.rreq + 1 ∧ u.wrep = s.wrep + 1 ∧ rep.M s.wrep = dd.M s.rdd) ∨
        (¬ checkReq req { s with rdd := s.rdd + 1 } ∧ u.rreq = s.rreq ∧ u.wrep = s.wrep)) := by
  simp only [synchronizerBody, inputDD, inputReq, outputRep, latest, stepF, guardedF, Spec.cond, Spec.ok, seq,
    exists_eq_left] at h
  obtain ⟨u, (⟨hc, ⟨hM, -⟩, rfl⟩ | ⟨hc, rfl⟩), hu⟩ := h
  · simp only [Nat.add_sub_cancel] at hM
    exact ⟨_, hu, rfl, Or.inl ⟨hc, rfl, rfl, hM⟩⟩
  · exact ⟨_, hu, rfl, Or.inr ⟨hc, rfl, rfl⟩⟩

end Synchronizer

end LaPToP.Interaction
