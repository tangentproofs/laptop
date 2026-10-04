import LaPToP.ProgramTheory.Network
import LaPToP.Interaction.Deadlock

/-!
# The network semantics and the book's channel declarations

`LaPToP/Interaction` expands the examples of Chapter 9 by hand: a channel
declaration quantifies its scripts existentially (`newChannel`, `newChannel2`)
and the processes are written out as specifications over those scripts. Here the
same examples are networks of `Network`, run by its machine, and the results are
shown to be the hand expansions':

* `c! e || (c?. x:= c)` gives `x′ = e ∧ t′ = t+1`, which is
  `newChannel (outParInT e)` (`sendRecv_book`);
* the buffer `c! 3. c! 4. c?. x:= c. c?. x:= x+c` gives `x′ = 7 ∧ t′ = t+1`,
  which is `newChannel buffer` (`buffer_book`);
* `(c?. d! 6) || (d?. c! 7)` deadlocks, and every behaviour of the book's
  semantics ends at `∞`, as `newChannel2 mutualWait` says (`mutualWait_book`).

In each case the network's book semantics (`NetSpec`) has exactly the behaviour
the machine computes, by `netSpec_of_reach` and `netSpec_unique`, or, for the
deadlock, by `deadlock_top`.
-/

namespace LaPToP.ProgramTheory.Interpreter.Network.Book

open Relation LaPToP.Interaction LaPToP.ProgramTheory.Time

/-- No named processes. -/
def noDefs : ℕ → NProc ℕ ℤ := fun _ => .act .ok

/-- The time a network finishes: when its last process does. -/
def finish (fin : List (PSt ℕ ℤ)) : ℕ∞ := fin.foldl (fun t f => max t f.t) 0

/-- Process `i`'s value of variable `x` at the end. -/
def valueOf (fin : List (PSt ℕ ℤ)) (i x : ℕ) : ℤ := (fin[i]?.map fun f => f.mem x).getD 0

/-! ### `c! e || (c?. x:= c)` -/

/-- `c! e || (c?. x:= c)`, with `x` variable `0`. -/
def sendRecv (e : ℤ) : Net ℕ ℤ :=
  ⟨noDefs, [⟨.send 0 fun _ => e, [0], []⟩, ⟨.recv 0 0, [], [0]⟩], fun _ => []⟩

theorem sendRecv_wf (e : ℤ) : (sendRecv e).WF where
  writer := by
    intro i j pri prj c hij hi hj hc
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp [sendRecv] at hi hj hij <;>
      subst hi hj <;> simp_all
  input := by intro i pr c _ _; rfl

/-- The start of a process. -/
def st₀ (s : Spec.State ℕ ℤ) (t : ℕ∞) : PSt ℕ ℤ := ⟨s, t, fun _ => 0, fun _ => 0⟩

/-- Where the machine ends. -/
def sendRecvEnd (e : ℤ) (s : Spec.State ℕ ℤ) (t : ℕ∞) : MCfg ℕ ℤ :=
  ⟨[⟨[], (st₀ s t).sent 0⟩, ⟨[], (st₀ s t).received 0 0 (e, t)⟩],
    Function.update (fun _ => []) 0 [(e, t)]⟩

/-- The machine runs it: the output, then the input. -/
theorem sendRecv_reach (e : ℤ) (s : Spec.State ℕ ℤ) (t : ℕ∞) :
    ReflTransGen (MStep (sendRecv e)) ((sendRecv e).init s t) (sendRecvEnd e s t) := by
  have h₁ : MStep (sendRecv e) ((sendRecv e).init s t)
      ⟨[⟨[], (st₀ s t).sent 0⟩, ⟨[.recv 0 0], st₀ s t⟩],
        Function.update (fun _ => []) 0 [(e, t)]⟩ := by
    have := MStep.mk (net := sendRecv e) (c := (sendRecv e).init s t) (i := 0)
      (a := ⟨[.send 0 fun _ => e], st₀ s t⟩) rfl
      (Act.send (pr := ⟨.send 0 fun _ => e, [0], []⟩) rfl (by simp) rfl)
    simpa [Net.init, sendRecv, Proc.start, st₀] using this
  have h₂ := MStep.mk (net := sendRecv e) (i := 1) (c := ⟨[⟨[], (st₀ s t).sent 0⟩,
      ⟨[.recv 0 0], st₀ s t⟩], Function.update (fun _ => []) 0 [(e, t)]⟩)
    (a := ⟨[.recv 0 0], st₀ s t⟩) rfl
    (Act.recv (pr := ⟨.recv 0 0, [], [0]⟩) (m := (e, t)) rfl (by simp) (by simp [st₀]))
  exact (ReflTransGen.single h₁).tail h₂

/-- The network has a behaviour with finite times: the machine's. -/
theorem sendRecv_exists (e : ℤ) (s : Spec.State ℕ ℤ) (t : ℕ) :
    ∃ fin S, NetSpec (sendRecv e) s t fin S ∧ ∀ f ∈ fin, f.t ≠ ⊤ :=
  ⟨_, _, netSpec_of_reach (sendRecv_wf e) (sendRecv_reach e s t)
    (by intro pc hpc; simp [sendRecvEnd] at hpc; rcases hpc with rfl | rfl <;> rfl),
    by intro f hf; simp [sendRecvEnd] at hf; rcases hf with rfl | rfl <;> simp [PSt.sent, PSt.received, st₀]⟩

/-- **`c! e || (c?. x:= c)` is `newChannel (outParInT e)`**: every behaviour of
the network's book semantics with finite times — and there is one — ends with
`x = e` at time `t+1`, which is what the hand expansion says. -/
theorem sendRecv_book (e : ℤ) (s : Spec.State ℕ ℤ) (t : ℕ) {fin : List (PSt ℕ ℤ)}
    {S : Scripts ℤ} (h : NetSpec (sendRecv e) s t fin S) (hfin : ∀ f ∈ fin, f.t ≠ ⊤) :
    newChannel (Channel.outParInT e) ⟨t, s 0⟩ ⟨finish fin, valueOf fin 1 0⟩ := by
  have hr := sendRecv_reach e s t
  have hs := netSpec_of_reach (sendRecv_wf e) hr (by intro pc hpc; simp [sendRecvEnd] at hpc; rcases hpc with rfl | rfl <;> rfl)
  obtain ⟨rfl, -⟩ := netSpec_unique (sendRecv_wf e) h hfin hs (by
    intro f hf
    simp [sendRecvEnd] at hf
    rcases hf with rfl | rfl
    · simp [PSt.sent, st₀]
    · simp [PSt.received, st₀])
  rw [Channel.newChannel_outParInT]
  simp [finish, valueOf, sendRecvEnd, PSt.sent, PSt.received, st₀]

/-! ### The buffer -/

/-- `x:= y`. -/
def setXY : Prog ℕ ℤ := .assign 0 fun s => s 1

/-- `x:= x + y`. -/
def addXY : Prog ℕ ℤ := .assign 0 fun s => s 0 + s 1

/-- `c! 3. c! 4. c?. x:= c. c?. x:= x + c`, a channel used as a buffer within one
process (`x` is variable `0`, the messages are input into `y`, variable `1`). -/
def buffer : Net ℕ ℤ :=
  ⟨noDefs, [⟨.seq (.send 0 fun _ => 3) (.seq (.send 0 fun _ => 4) (.seq (.recv 0 1)
    (.seq (.act setXY) (.seq (.recv 0 1) (.act addXY))))), [0], [0]⟩], fun _ => []⟩

theorem buffer_wf : buffer.WF where
  writer := by
    intro i j pri prj c hij hi hj _
    rcases i with _ | i <;> rcases j with _ | j <;> simp [buffer] at hi hj hij
  input := by intro i pr c _ _; rfl

/-- The machine runs the buffer to the end. -/
theorem buffer_reach (s : Spec.State ℕ ℤ) (t : ℕ∞) :
    ∃ c, ReflTransGen (MStep buffer) (buffer.init s t) c ∧ c.Done ∧
      valueOf (c.ps.map (·.st)) 0 0 = 7 ∧ finish (c.ps.map (·.st)) = max t (t + 1) := by
  have hpr : buffer.procs[0]? = some ⟨.seq (.send 0 fun _ => 3) (.seq (.send 0 fun _ => 4)
      (.seq (.recv 0 1) (.seq (.act setXY) (.seq (.recv 0 1) (.act addXY))))), [0], [0]⟩ := rfl
  refine ⟨_, ((((((((((ReflTransGen.refl.tail (MStep.mk (i := 0) rfl (.loc .seq))).tail
    (MStep.mk (i := 0) rfl (.send hpr (by simp) rfl))).tail
    (MStep.mk (i := 0) rfl (.loc .seq))).tail
    (MStep.mk (i := 0) rfl (.send hpr (by simp) rfl))).tail
    (MStep.mk (i := 0) rfl (.loc .seq))).tail
    (MStep.mk (i := 0) rfl (.recv hpr (by simp) (by simp [PSt.sent]; rfl)))).tail
    (MStep.mk (i := 0) rfl (.loc .seq))).tail
    (MStep.mk (i := 0) rfl (.loc (.act (p := setXY) trivial .assign)))).tail
    (MStep.mk (i := 0) rfl (.loc .seq))).tail
    (MStep.mk (i := 0) rfl (.recv hpr (by simp) (by simp [PSt.sent, PSt.received]; rfl)))).tail
    (MStep.mk (i := 0) rfl (.loc (.act (p := addXY) trivial .assign))), ?_, ?_, ?_⟩
  · intro pc hpc; simp [Net.init, buffer, Proc.start] at hpc; rw [hpc]
  · simp [valueOf, PSt.received, PSt.sent, setXY, addXY, Net.init, buffer]
  · simp [finish, PSt.received, PSt.sent, Net.init, buffer]

theorem le_foldl_max (l : List (PSt ℕ ℤ)) : ∀ acc : ℕ∞,
    acc ≤ l.foldl (fun t f => max t f.t) acc ∧ ∀ f ∈ l, f.t ≤ l.foldl (fun t f => max t f.t) acc := by
  induction l with
  | nil => intro acc; simp
  | cons g l ih =>
    intro acc
    obtain ⟨h₁, h₂⟩ := ih (max acc g.t)
    refine ⟨le_trans (le_max_left _ _) h₁, ?_⟩
    intro f hf
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact le_trans (le_max_right _ _) h₁
    · exact h₂ f hf

/-- Every process has finished by the time the network has. -/
theorem le_finish {fin : List (PSt ℕ ℤ)} {f : PSt ℕ ℤ} (hf : f ∈ fin) : f.t ≤ finish fin :=
  (le_foldl_max fin 0).2 f hf

/-- **The buffer is `newChannel buffer`**: every behaviour of its book semantics
with finite times ends with `x = 7` at time `t+1`, as the hand expansion says. -/
theorem buffer_book (s : Spec.State ℕ ℤ) (t : ℕ) {fin : List (PSt ℕ ℤ)} {S : Scripts ℤ}
    (h : NetSpec buffer s t fin S) (hfin : ∀ f ∈ fin, f.t ≠ ⊤) :
    newChannel Channel.buffer ⟨t, s 0⟩ ⟨finish fin, valueOf fin 0 0⟩ := by
  obtain ⟨c, hr, hd, hv, ht⟩ := buffer_reach s t
  have hs := netSpec_of_reach buffer_wf hr hd
  have hfin' : ∀ f ∈ c.ps.map (·.st), f.t ≠ ⊤ := by
    intro f hf
    have := le_finish hf
    rw [ht] at this
    exact ne_top_of_le_ne_top (by simp) this
  obtain ⟨rfl, -⟩ := netSpec_unique buffer_wf h hfin hs hfin'
  rw [Channel.newChannel_buffer]
  exact ⟨hv, by rw [ht, max_eq_right le_self_add]⟩

/-! ### The deadlock -/

/-- `(c?. d! 6) || (d?. c! 7)`: channel `c` is `0`, `d` is `1`, and each input is
kept in variable `0`. -/
def mutualWait : Net ℕ ℤ :=
  ⟨noDefs, [⟨.seq (.recv 0 0) (.send 1 fun _ => 6), [1], [0]⟩,
    ⟨.seq (.recv 1 0) (.send 0 fun _ => 7), [0], [1]⟩], fun _ => []⟩

theorem mutualWait_wf : mutualWait.WF where
  writer := by
    intro i j pri prj c hij hi hj hc
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp [mutualWait] at hi hj hij <;>
      subst hi hj <;> simp_all
  input := by intro i pr c _ _; rfl

/-- Where the machine stops: each process waiting for input. -/
def mutualWaitStuck (s : Spec.State ℕ ℤ) (t : ℕ∞) : MCfg ℕ ℤ :=
  ⟨[⟨[.recv 0 0, .send 1 fun _ => 6], st₀ s t⟩, ⟨[.recv 1 0, .send 0 fun _ => 7], st₀ s t⟩],
    fun _ => []⟩

theorem mutualWait_reach (s : Spec.State ℕ ℤ) (t : ℕ∞) :
    ReflTransGen (MStep mutualWait) (mutualWait.init s t) (mutualWaitStuck s t) := by
  have := (ReflTransGen.refl.tail (MStep.mk (net := mutualWait) (c := mutualWait.init s t) (i := 0)
    rfl (.loc .seq))).tail (MStep.mk (i := 1) rfl (.loc .seq))
  simpa [mutualWaitStuck, Net.init, mutualWait, Proc.start, st₀] using this

/-- No step is possible: both wait for a message that is not there. -/
theorem mutualWait_normal (s : Spec.State ℕ ℤ) (t : ℕ∞) : Normal mutualWait (mutualWaitStuck s t) := by
  intro c' hs
  obtain ⟨hi, ha⟩ := hs
  rename_i i a b L'
  rcases i with _ | _ | i <;> simp [mutualWaitStuck] at hi <;> subst hi <;>
    cases ha with
    | loc hl => cases hl
    | recv _ _ hm => simp [mutualWaitStuck] at hm

/-- **The deadlock is `newChannel2 mutualWait`**: in every behaviour of the
network's book semantics the time ends at `∞`, and `x` is unchanged, which is
what the hand expansion says. -/
theorem mutualWait_book (s : Spec.State ℕ ℤ) (t : ℕ) {fin : List (PSt ℕ ℤ)} {S : Scripts ℤ}
    (h : NetSpec mutualWait s t fin S) :
    newChannel2 Deadlock.mutualWait ⟨t, s 0⟩ ⟨finish fin, s 0⟩ := by
  obtain ⟨f, hf, hft⟩ := deadlock_top mutualWait_wf (mutualWait_reach s t) (mutualWait_normal s t)
    (by intro hd; have := hd ⟨[.recv 0 0, .send 1 fun _ => 6], st₀ s t⟩ (by simp [mutualWaitStuck]); simp at this) h
  rw [Deadlock.newChannel2_mutualWait]
  exact ⟨rfl, top_le_iff.mp (hft ▸ le_finish hf)⟩

end LaPToP.ProgramTheory.Interpreter.Network.Book
