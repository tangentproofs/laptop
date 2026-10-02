import LaPToP.ProgramTheory.InterpreterTime
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Communicating processes

Chapter 9 describes communication on a channel `c` by "two infinite strings `Mc`
and `Tc` called the message script and the time script, and two extended natural
variables `rc` and `wc` called the read cursor and the write cursor", with
`c! e = Mw = e ∧ Tw = t ∧ (w:= w+1)`, input `t:= t↑(T r + 1). c?` once
communication takes one unit of time (§9.1.2), and `c = M r–1`. "The scripts are
state constants, not state variables": a channel declaration quantifies them
existentially (`ChannelDeclaration.newChannel`), and the processes of a network
run concurrently against those constant scripts.

This module gives that account of a network of processes and a machine that
executes it, and proves the two the same.

## The model

A process is an `NProc`: chunks of ordinary programs (`act p`, run atomically
by the timed semantics of `InterpreterTime`) joined by `send`, `recv`,
sequencing, `if`, loops and calls. A chunk does not communicate, so running it
in one step loses nothing. Each process has its own memory, its own clock and
its own cursors; it sees another process's variables only at their initial
values, as Section 8.0 requires, and communicates only through channels. Each
channel has at most one writer and at most one reader (`Net.WF`).

* `PStep S` — one step of a process against *constant* scripts `S`: output must
  find its message already in the script at the write cursor, `M w = e ∧
  T w = t`; input reads the script at the read cursor and sets
  `t := max t (T r + 1)`; a message never written is never there, and input of
  it waits until `∞`.
* `NetSpec` — the book's semantics of a network: there are scripts `S` such that
  every process runs to completion against them, writing exactly them.
* `MStep` — the machine: the processes take turns; output appends to the
  channel's script, and input waits until the message it reads is there.

## What is proved

* `normal_unique` — **determinacy** (Kahn): from a start, the machine reaches at
  most one configuration in which no step is possible, whatever the order in
  which the processes take their turns (it is confluent: `mstep_diamond`).
* `netSpec_of_reach` — **soundness**: a run of the machine in which every
  process finishes is a behaviour of the book's semantics, with the scripts the
  machine wrote.
* `reach_of_netSpec` — **completeness**: a behaviour of the book's semantics in
  which every process finishes at a finite time is the machine's. The argument
  is the book's own reason that communication is well defined: a process waits
  only for a message sent earlier (`blocked_descent`).
* `netSpec_unique` — so the book's semantics has at most one behaviour with
  finite times, and `deadlock_top` — if the machine stops with a process
  unfinished, every behaviour of the book's semantics has a process at `∞`.
* `runNet_correct` — the executable round-robin runner `runNet` computes that
  behaviour.

## Honest scope

The book leaves a message that is never written arbitrary; here it never
arrives, so input of it waits until `∞` — a refinement of the book's
declaration, and the reading under which deadlock (§9.1.8) is `t′ = ∞`.
-/

namespace LaPToP.ProgramTheory.Interpreter.Network

open Timed Relation

universe u v

variable {Var : Type u} {Val : Type v}

/-! ### Processes -/

/-- A process. -/
inductive NProc (Var : Type u) (Val : Type v) : Type (max u v) where
  /-- A chunk of program that does not communicate, run in one step. -/
  | act (p : Prog Var Val)
  /-- `c! e`. -/
  | send (c : ℕ) (e : Spec.State Var Val → Val)
  /-- `c?. x:= c`: input, and keep the message in `x`. -/
  | recv (c : ℕ) (x : Var)
  /-- `P. Q`. -/
  | seq (p q : NProc Var Val)
  /-- `if b then P else Q`. -/
  | cond (b : Spec.State Var Val → Bool) (p q : NProc Var Val)
  /-- `while b do P od`. -/
  | loop (b : Spec.State Var Val → Bool) (p : NProc Var Val)
  /-- A call of a named process. -/
  | call (k : ℕ)

/-- A message: its value, and the time it was sent. -/
abbrev Msg (Val : Type v) := Val × ℕ∞

/-- The scripts of the channels: channel `c`'s messages in order. -/
abbrev Scripts (Val : Type v) := ℕ → List (Msg Val)

/-- The state of a process: its memory, its clock, and its cursors. -/
@[ext]
structure PSt (Var : Type u) (Val : Type v) where
  /-- The memory. -/
  mem : Spec.State Var Val
  /-- The clock. -/
  t : ℕ∞
  /-- The read cursors. -/
  r : ℕ → ℕ
  /-- The write cursors. -/
  w : ℕ → ℕ

/-- A process in the middle of running: what is left to do, and its state. -/
@[ext]
structure PCfg (Var : Type u) (Val : Type v) where
  /-- What is left to do, first item first. -/
  k : List (NProc Var Val)
  /-- The state. -/
  st : PSt Var Val

/-- A process of a network: its body, and the channels it writes and reads. -/
structure Proc (Var : Type u) (Val : Type v) where
  /-- The body. -/
  body : NProc Var Val
  /-- The channels it writes. -/
  outs : List ℕ
  /-- The channels it reads. -/
  ins : List ℕ

/-- A network: named processes to call, the processes, and the scripts of the
channels the environment writes. -/
structure Net (Var : Type u) (Val : Type v) where
  /-- The named processes. -/
  defs : ℕ → NProc Var Val
  /-- The processes. -/
  procs : List (Proc Var Val)
  /-- The scripts the environment supplies. -/
  input : Scripts Val

/-- A process starts with its body to do, from the common prestate, with its
cursors at `0`. -/
def Proc.start (pr : Proc Var Val) (s : Spec.State Var Val) (t : ℕ∞) : PCfg Var Val :=
  ⟨[pr.body], ⟨s, t, fun _ => 0, fun _ => 0⟩⟩

variable [DecidableEq Var] [Defs Var Val]

/-! ### Steps -/

/-- After output on `c`: the write cursor moves on. -/
def PSt.sent (st : PSt Var Val) (c : ℕ) : PSt Var Val :=
  { st with w := Function.update st.w c (st.w c + 1) }

/-- After input of message `m` on `c` into `x`: the book's
`t:= t↑(T r + 1). c?. x:= c`. -/
def PSt.received (st : PSt Var Val) (c : ℕ) (x : Var) (m : Msg Val) : PSt Var Val :=
  { st with mem := Function.update st.mem x m.1, t := max st.t (m.2 + 1),
            r := Function.update st.r c (st.r c + 1) }

/-- After input of a message that is never written: the wait is until `∞`. -/
def PSt.never (st : PSt Var Val) (c : ℕ) : PSt Var Val :=
  { st with t := ⊤, r := Function.update st.r c (st.r c + 1) }

/-- The steps of a process that do not touch a channel. -/
inductive LStep (defs : ℕ → NProc Var Val) : PCfg Var Val → PCfg Var Val → Prop
  /-- A chunk runs, by the timed semantics. It must be deterministic: a network
  of processes that choose has no one result to compute. -/
  | act {p : Prog Var Val} {k : List (NProc Var Val)} {st : PSt Var Val} {u : TState Var Val} :
      Det p → EvalT p ⟨st.mem, st.t⟩ u →
        LStep defs ⟨.act p :: k, st⟩ ⟨k, { st with mem := u.mem, t := u.t }⟩
  /-- `P. Q`. -/
  | seq {p q : NProc Var Val} {k : List (NProc Var Val)} {st : PSt Var Val} :
      LStep defs ⟨.seq p q :: k, st⟩ ⟨p :: q :: k, st⟩
  /-- `if` with a true condition. -/
  | condT {b : Spec.State Var Val → Bool} {p q : NProc Var Val} {k : List (NProc Var Val)}
      {st : PSt Var Val} (hb : b st.mem = true) :
      LStep defs ⟨.cond b p q :: k, st⟩ ⟨p :: k, st⟩
  /-- `if` with a false condition. -/
  | condF {b : Spec.State Var Val → Bool} {p q : NProc Var Val} {k : List (NProc Var Val)}
      {st : PSt Var Val} (hb : b st.mem = false) :
      LStep defs ⟨.cond b p q :: k, st⟩ ⟨q :: k, st⟩
  /-- A loop that goes round. -/
  | loopT {b : Spec.State Var Val → Bool} {p : NProc Var Val} {k : List (NProc Var Val)}
      {st : PSt Var Val} (hb : b st.mem = true) :
      LStep defs ⟨.loop b p :: k, st⟩ ⟨p :: .loop b p :: k, st⟩
  /-- A loop that exits. -/
  | loopF {b : Spec.State Var Val → Bool} {p : NProc Var Val} {k : List (NProc Var Val)}
      {st : PSt Var Val} (hb : b st.mem = false) :
      LStep defs ⟨.loop b p :: k, st⟩ ⟨k, st⟩
  /-- A call. -/
  | call {n : ℕ} {k : List (NProc Var Val)} {st : PSt Var Val} :
      LStep defs ⟨.call n :: k, st⟩ ⟨defs n :: k, st⟩


/-- **A step of a process against constant scripts** `S`, the book's reading:
output finds its message in the script at the write cursor (`M w = e ∧ T w = t`),
input reads the script at the read cursor, and a message never written makes the
input wait until `∞`. -/
inductive PStep (defs : ℕ → NProc Var Val) (pr : Proc Var Val) (S : Scripts Val) :
    PCfg Var Val → PCfg Var Val → Prop
  /-- A step that does not touch a channel. -/
  | loc {a b : PCfg Var Val} : LStep defs a b → PStep defs pr S a b
  /-- `c! e`. -/
  | send {c : ℕ} {e : Spec.State Var Val → Val} {k : List (NProc Var Val)} {st : PSt Var Val} :
      c ∈ pr.outs → (S c)[st.w c]? = some (e st.mem, st.t) →
        PStep defs pr S ⟨.send c e :: k, st⟩ ⟨k, st.sent c⟩
  /-- `c?`, of a message in the script. -/
  | recv {c : ℕ} {x : Var} {k : List (NProc Var Val)} {st : PSt Var Val} {m : Msg Val} :
      c ∈ pr.ins → (S c)[st.r c]? = some m →
        PStep defs pr S ⟨.recv c x :: k, st⟩ ⟨k, st.received c x m⟩
  /-- `c?`, of a message never written. -/
  | never {c : ℕ} {x : Var} {k : List (NProc Var Val)} {st : PSt Var Val} :
      c ∈ pr.ins → (S c)[st.r c]? = none →
        PStep defs pr S ⟨.recv c x :: k, st⟩ ⟨k, st.never c⟩

/-- **The book's semantics of a network**: there are scripts `S` such that every
process runs to completion against them, ending in its final state in `fin`,
having written exactly its channels' scripts; a channel no process writes has
the script the environment supplies. -/
def NetSpec (net : Net Var Val) (s : Spec.State Var Val) (t : ℕ∞) (fin : List (PSt Var Val))
    (S : Scripts Val) : Prop :=
  fin.length = net.procs.length ∧
  (∀ (i : ℕ) (pr : Proc Var Val) (f : PSt Var Val), net.procs[i]? = some pr → fin[i]? = some f →
    ReflTransGen (PStep net.defs pr S) (pr.start s t) ⟨[], f⟩ ∧
      ∀ c ∈ pr.outs, f.w c = (S c).length) ∧
  ∀ c, (∀ (i : ℕ) (pr : Proc Var Val), net.procs[i]? = some pr → c ∉ pr.outs) → S c = net.input c

/-- A network is well formed when each channel has at most one writer, and the
environment supplies nothing on a channel a process writes. (A channel may have
many readers, each with its own cursor: that is broadcast, §9.1.4.) -/
structure Net.WF (net : Net Var Val) : Prop where
  /-- One writer. -/
  writer : ∀ {i j : ℕ} {pri prj : Proc Var Val} {c : ℕ}, i ≠ j →
    net.procs[i]? = some pri → net.procs[j]? = some prj → c ∈ pri.outs → c ∉ prj.outs
  /-- Nothing supplied on a written channel. -/
  input : ∀ {i : ℕ} {pr : Proc Var Val} {c : ℕ}, net.procs[i]? = some pr → c ∈ pr.outs →
    net.input c = []

/-! ### The machine -/

/-- The machine's configuration: every process, and the scripts written so far. -/
@[ext]
structure MCfg (Var : Type u) (Val : Type v) where
  /-- The processes. -/
  ps : List (PCfg Var Val)
  /-- The scripts so far. -/
  L : Scripts Val

/-- The machine starts every process from the prestate, with the environment's
scripts. -/
def Net.init (net : Net Var Val) (s : Spec.State Var Val) (t : ℕ∞) : MCfg Var Val :=
  ⟨net.procs.map fun pr => pr.start s t, net.input⟩

/-- **What process `i` can do** when the scripts so far are `L`: a step that does
not touch a channel; output, which appends its message, stamped with the sender's
time, to the channel's script; or input of the message at its read cursor, if it
is there — if not, the process waits. -/
inductive Act (net : Net Var Val) (i : ℕ) :
    Scripts Val → PCfg Var Val → PCfg Var Val → Scripts Val → Prop
  /-- A step that does not touch a channel. -/
  | loc {L : Scripts Val} {a b : PCfg Var Val} : LStep net.defs a b → Act net i L a b L
  /-- Output. -/
  | send {L L' : Scripts Val} {pr : Proc Var Val} {ch : ℕ} {e : Spec.State Var Val → Val}
      {k : List (NProc Var Val)} {st : PSt Var Val} :
      net.procs[i]? = some pr → ch ∈ pr.outs →
        L' = Function.update L ch (L ch ++ [(e st.mem, st.t)]) →
        Act net i L ⟨.send ch e :: k, st⟩ ⟨k, st.sent ch⟩ L'
  /-- Input of a message that is there. -/
  | recv {L : Scripts Val} {pr : Proc Var Val} {ch : ℕ} {x : Var} {k : List (NProc Var Val)}
      {st : PSt Var Val} {m : Msg Val} :
      net.procs[i]? = some pr → ch ∈ pr.ins → (L ch)[st.r ch]? = some m →
        Act net i L ⟨.recv ch x :: k, st⟩ ⟨k, st.received ch x m⟩ L

/-- **A step of the machine**: one process acts. -/
inductive MStep (net : Net Var Val) : MCfg Var Val → MCfg Var Val → Prop
  /-- Process `i`, in `a`, acts. -/
  | mk {c : MCfg Var Val} {i : ℕ} {a b : PCfg Var Val} {L' : Scripts Val} :
      c.ps[i]? = some a → Act net i c.L a b L' → MStep net c ⟨c.ps.set i b, L'⟩

/-- Every process has finished. -/
def MCfg.Done (c : MCfg Var Val) : Prop := ∀ pc ∈ c.ps, pc.k = []

/-- No step is possible. -/
def Normal (net : Net Var Val) (c : MCfg Var Val) : Prop := ∀ c', ¬ MStep net c c'

/-- A machine where every process has finished takes no step. -/
theorem normal_of_done {net : Net Var Val} {c : MCfg Var Val} (h : c.Done) : Normal net c := by
  intro c' hs
  obtain ⟨hi, ha⟩ := hs
  have := h _ (List.mem_of_getElem? hi)
  cases ha with
  | loc hl => cases hl <;> simp_all
  | send => simp_all
  | recv => simp_all

/-! ### Determinacy -/

/-- A deterministic chunk has at most one outcome. -/
theorem evalT_det [DetDefs Var Val] {p : Prog Var Val} (hp : Det p) {st u₁ u₂ : TState Var Val}
    (h₁ : EvalT p st u₁) (h₂ : EvalT p st u₂) : u₁ = u₂ := by
  obtain ⟨f₁, hf₁⟩ := exists_runT_of_evalT hp h₁
  obtain ⟨f₂, hf₂⟩ := exists_runT_of_evalT hp h₂
  have := (runT_le hf₁ (le_max_left f₁ f₂)).symm.trans (runT_le hf₂ (le_max_right f₁ f₂))
  exact Option.some.inj this

/-- A step that does not touch a channel is determined. -/
theorem lstep_det [DetDefs Var Val] {defs : ℕ → NProc Var Val} {a b b' : PCfg Var Val}
    (h : LStep defs a b) (h' : LStep defs a b') : b = b' := by
  cases h with
  | act hp he => cases h' with | act _ he' => rw [evalT_det hp he he']
  | seq => cases h'; rfl
  | condT hb => cases h' with | condT => rfl | condF hb' => simp_all
  | condF hb => cases h' with | condT hb' => simp_all | condF => rfl
  | loopT hb => cases h' with | loopT => rfl | loopF hb' => simp_all
  | loopF hb => cases h' with | loopT hb' => simp_all | loopF => rfl
  | call => cases h'; rfl

/-- What a process does is determined. -/
theorem act_det [DetDefs Var Val] {net : Net Var Val} {i : ℕ} {L L₁ L₂ : Scripts Val}
    {a b₁ b₂ : PCfg Var Val} (h₁ : Act net i L a b₁ L₁) (h₂ : Act net i L a b₂ L₂) :
    b₁ = b₂ ∧ L₁ = L₂ := by
  cases h₁ with
  | loc hl =>
    cases h₂ with
    | loc hl' => exact ⟨lstep_det hl hl', rfl⟩
    | send => cases hl
    | recv => cases hl
  | send _ _ hL =>
    cases h₂ with
    | loc hl => cases hl
    | send _ _ hL' => exact ⟨rfl, hL.trans hL'.symm⟩
  | recv _ _ hm =>
    cases h₂ with
    | loc hl => cases hl
    | recv _ _ hm' => rw [hm] at hm'; cases hm'; exact ⟨rfl, rfl⟩

/-- A message in a script stays there as the script grows. -/
theorem getElem?_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {n : ℕ} {m : α}
    (hm : l₁[n]? = some m) : l₂[n]? = some m := by
  obtain ⟨u, rfl⟩ := h
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hm).1]
  exact hm

/-- **Two processes' actions commute.** Output on a channel only appends to it,
so it does not disturb another process's input; two outputs are on different
channels, as each channel has one writer. -/
theorem act_comm {net : Net Var Val} (hwf : net.WF) {i j : ℕ} (hij : i ≠ j)
    {L L₁ L₂ : Scripts Val} {a a' b b' : PCfg Var Val}
    (ha : Act net i L a a' L₁) (hb : Act net j L b b' L₂) :
    ∃ L₃, Act net j L₁ b b' L₃ ∧ Act net i L₂ a a' L₃ := by
  cases ha with
  | loc hl => exact ⟨L₂, hb, .loc hl⟩
  | @send _ pr ch e k st hpr hch hL =>
    subst hL
    cases hb with
    | loc hl => exact ⟨_, .loc hl, .send hpr hch rfl⟩
    | @send _ pr' ch' e' k' st' hpr' hch' hL' =>
      subst hL'
      have hne : ch ≠ ch' := fun h => hwf.writer hij hpr hpr' hch (h ▸ hch')
      refine ⟨Function.update (Function.update L ch (L ch ++ [(e st.mem, st.t)])) ch'
        (L ch' ++ [(e' st'.mem, st'.t)]), .send hpr' hch' ?_, .send hpr hch ?_⟩
      · rw [Function.update_of_ne hne.symm]
      · rw [Function.update_of_ne hne, Function.update_comm hne]
    | @recv pr' ch' x' k' st' m' hpr' hch' hm' =>
      refine ⟨_, .recv hpr' hch' ?_, .send hpr hch rfl⟩
      by_cases h : ch' = ch
      · subst h; rw [Function.update_self]; exact getElem?_of_prefix (List.prefix_append _ _) hm'
      · rw [Function.update_of_ne h]; exact hm'
  | @recv pr ch x k st m hpr hch hm =>
    cases hb with
    | loc hl => exact ⟨_, .loc hl, .recv hpr hch hm⟩
    | @send _ pr' ch' e' k' st' hpr' hch' hL' =>
      subst hL'
      refine ⟨_, .send hpr' hch' rfl, .recv hpr hch ?_⟩
      by_cases h : ch = ch'
      · subst h; rw [Function.update_self]; exact getElem?_of_prefix (List.prefix_append _ _) hm
      · rw [Function.update_of_ne h]; exact hm
    | recv hpr' hch' hm' => exact ⟨_, .recv hpr' hch' hm', .recv hpr hch hm⟩

/-- **The diamond**: two steps from one configuration are the same step, or each
can be completed by the other. -/
theorem mstep_diamond [DetDefs Var Val] {net : Net Var Val} (hwf : net.WF)
    {c c₁ c₂ : MCfg Var Val} (h₁ : MStep net c c₁) (h₂ : MStep net c c₂) :
    c₁ = c₂ ∨ ∃ d, MStep net c₁ d ∧ MStep net c₂ d := by
  obtain ⟨hi, ha⟩ := h₁
  rename_i i a a' L₁
  obtain ⟨hj, hb⟩ := h₂
  rename_i j b b' L₂
  by_cases hij : i = j
  · subst hij
    rw [hi] at hj; cases hj
    obtain ⟨rfl, rfl⟩ := act_det ha hb
    exact .inl rfl
  · right
    obtain ⟨L₃, hb₃, ha₃⟩ := act_comm hwf hij ha hb
    refine ⟨⟨(c.ps.set i a').set j b', L₃⟩, .mk ?_ hb₃, ?_⟩
    · simpa [List.getElem?_set_ne hij] using hj
    · rw [List.set_comm _ _ hij]
      exact .mk (by simpa [List.getElem?_set_ne (Ne.symm hij)] using hi) ha₃

/-- The machine is confluent. -/
theorem mstep_confluent [DetDefs Var Val] {net : Net Var Val} (hwf : net.WF)
    {c c₁ c₂ : MCfg Var Val} (h₁ : ReflTransGen (MStep net) c c₁)
    (h₂ : ReflTransGen (MStep net) c c₂) : Join (ReflTransGen (MStep net)) c₁ c₂ := by
  refine church_rosser (fun a b c hb hc => ?_) h₁ h₂
  rcases mstep_diamond hwf hb hc with rfl | ⟨d, hbd, hcd⟩
  · exact ⟨b, .refl, .refl⟩
  · exact ⟨d, .single hbd, .single hcd⟩

/-- From a configuration that takes no step, the machine goes nowhere. -/
theorem eq_of_normal {net : Net Var Val} {c c' : MCfg Var Val} (hn : Normal net c)
    (h : ReflTransGen (MStep net) c c') : c' = c := by
  cases h.cases_head with
  | inl h => exact h.symm
  | inr h => obtain ⟨d, hd, _⟩ := h; exact (hn d hd).elim

/-- **Determinacy** (Kahn): a network reaches at most one configuration in which
no step is possible, whatever the order in which its processes take turns. -/
theorem normal_unique [DetDefs Var Val] {net : Net Var Val} (hwf : net.WF)
    {c c₁ c₂ : MCfg Var Val} (h₁ : ReflTransGen (MStep net) c c₁) (hn₁ : Normal net c₁)
    (h₂ : ReflTransGen (MStep net) c c₂) (hn₂ : Normal net c₂) : c₁ = c₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := mstep_confluent hwf h₁ h₂
  rw [← eq_of_normal hn₁ hd₁, ← eq_of_normal hn₂ hd₂]

/-! ### Soundness -/

/-- A step that does not touch a channel leaves the cursors alone. -/
theorem LStep.w_eq {defs : ℕ → NProc Var Val} {a b : PCfg Var Val} (h : LStep defs a b) :
    b.st.w = a.st.w := by
  cases h <;> rfl

/-- The scripts only grow. -/
theorem Act.prefix {net : Net Var Val} {i : ℕ} {L L' : Scripts Val} {a b : PCfg Var Val}
    (h : Act net i L a b L') (c : ℕ) : L c <+: L' c := by
  cases h with
  | loc => exact List.prefix_rfl
  | send _ _ hL =>
    subst hL
    by_cases hc : c = ‹ℕ›
    · subst hc; rw [Function.update_self]; exact List.prefix_append _ _
    · rw [Function.update_of_ne hc]
  | recv => exact List.prefix_rfl

/-- A process changes only the scripts of the channels it writes. -/
theorem Act.eq_of_not_out {net : Net Var Val} {i : ℕ} {L L' : Scripts Val} {a b : PCfg Var Val}
    (h : Act net i L a b L') {c : ℕ} (hc : ∀ pr, net.procs[i]? = some pr → c ∉ pr.outs) :
    L' c = L c := by
  cases h with
  | loc => rfl
  | send hpr hch hL =>
    subst hL
    exact Function.update_of_ne (fun h => hc _ hpr (by subst h; exact hch)) _ _
  | recv => rfl

/-- **An action is a step against any scripts that extend what has been written**,
provided the process's write cursors count what it has written. -/
theorem Act.pstep {net : Net Var Val} {i : ℕ} {L L' : Scripts Val} {a b : PCfg Var Val}
    (h : Act net i L a b L') {pr : Proc Var Val} (hpr : net.procs[i]? = some pr)
    (hw : ∀ c ∈ pr.outs, a.st.w c = (L c).length) {S : Scripts Val}
    (hS : ∀ c, L' c <+: S c) : PStep net.defs pr S a b := by
  cases h with
  | loc hl => exact .loc hl
  | @send _ pr' ch e k st hpr' hch hL =>
    rw [hpr] at hpr'; cases hpr'
    subst hL
    refine .send hch (getElem?_of_prefix (hS ch) ?_)
    rw [Function.update_self, hw ch hch]
    simp
  | recv hpr' hch hm =>
    rw [hpr] at hpr'; cases hpr'
    exact .recv hch (getElem?_of_prefix (hS _) hm)

/-- What holds of every configuration the machine reaches. -/
structure Inv (net : Net Var Val) (s : Spec.State Var Val) (t : ℕ∞) (c : MCfg Var Val) :
    Prop where
  /-- A configuration for each process. -/
  length : c.ps.length = net.procs.length
  /-- A writer's cursor counts what it has written. -/
  w : ∀ {i : ℕ} {pr : Proc Var Val} {pc : PCfg Var Val}, net.procs[i]? = some pr →
    c.ps[i]? = some pc → ∀ ch ∈ pr.outs, pc.st.w ch = (c.L ch).length
  /-- A channel no process writes keeps what the environment supplied. -/
  input : ∀ ch, (∀ (i : ℕ) (pr : Proc Var Val), net.procs[i]? = some pr → ch ∉ pr.outs) →
    c.L ch = net.input ch
  /-- Against any scripts that extend what has been written, each process got where it
  is by the book's steps. -/
  path : ∀ S : Scripts Val, (∀ ch, c.L ch <+: S ch) → ∀ {i : ℕ} {pr : Proc Var Val}
    {pc : PCfg Var Val}, net.procs[i]? = some pr → c.ps[i]? = some pc →
    ReflTransGen (PStep net.defs pr S) (pr.start s t) pc

/-- The invariant holds at the start. -/
theorem inv_init {net : Net Var Val} (hwf : net.WF) (s : Spec.State Var Val) (t : ℕ∞) :
    Inv net s t (net.init s t) where
  length := by simp [Net.init]
  w := by
    intro i pr pc hpr hpc ch hch
    simp only [Net.init, List.getElem?_map, hpr, Option.map_some, Option.some.injEq] at hpc
    subst hpc
    simp [Proc.start, Net.init, hwf.input hpr hch]
  input := fun _ _ => rfl
  path := by
    intro S _ i pr pc hpr hpc
    simp only [Net.init, List.getElem?_map, hpr, Option.map_some, Option.some.injEq] at hpc
    subst hpc
    exact .refl

/-- The invariant is kept by every step. -/
theorem Inv.step {net : Net Var Val} (hwf : net.WF) {s : Spec.State Var Val} {t : ℕ∞}
    {c c' : MCfg Var Val} (hc : Inv net s t c) (h : MStep net c c') : Inv net s t c' := by
  obtain ⟨hi, ha⟩ := h
  rename_i i a b L'
  have hilt : i < c.ps.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨pri, hpri⟩ : ∃ pr, net.procs[i]? = some pr :=
    ⟨net.procs[i]'(hc.length ▸ hilt), List.getElem?_eq_getElem _⟩
  have hnot : ∀ ch, (∃ pr, net.procs[i]? = some pr ∧ ch ∈ pr.outs) ∨ L' ch = c.L ch := by
    intro ch
    by_cases h : ∃ pr, net.procs[i]? = some pr ∧ ch ∈ pr.outs
    · exact .inl h
    · exact .inr (ha.eq_of_not_out fun pr hpr hch => h ⟨pr, hpr, hch⟩)
  constructor
  · simpa using hc.length
  · intro j pr pc hpr hpc ch hch
    by_cases hij : i = j
    · subst hij
      rw [hpr] at hpri; cases hpri
      simp only [List.getElem?_set_self hilt, Option.some.injEq] at hpc
      subst hpc
      cases ha with
      | loc hl => rw [hl.w_eq]; exact hc.w hpr hi ch hch
      | @send _ pr' ch' e k st hpr' hch' hL =>
        subst hL
        have hw := hc.w hpr hi
        by_cases hcc : ch = ch'
        · subst hcc; simpa [PSt.sent] using hw ch hch
        · simpa [PSt.sent, Function.update_of_ne hcc] using hw ch hch
      | recv => exact hc.w hpr hi ch hch
    · rw [List.getElem?_set_ne hij] at hpc
      rcases hnot ch with ⟨pr', hpr', hch'⟩ | heq
      · exact (hwf.writer hij hpr' hpr hch' hch).elim
      · dsimp only; rw [heq]; exact hc.w hpr hpc ch hch
  · intro ch hch
    rcases hnot ch with ⟨pr', hpr', hch'⟩ | heq
    · exact (hch i pr' hpr' hch').elim
    · dsimp only; rw [heq]; exact hc.input ch hch
  · intro S hS j pr pc hpr hpc
    have hS' : ∀ ch, c.L ch <+: S ch := fun ch => (ha.prefix ch).trans (hS ch)
    by_cases hij : i = j
    · subst hij
      simp only [List.getElem?_set_self hilt, Option.some.injEq] at hpc
      subst hpc
      exact (hc.path S hS' hpr hi).tail (ha.pstep hpr (hc.w hpr hi) hS)
    · rw [List.getElem?_set_ne hij] at hpc
      exact hc.path S hS' hpr hpc

/-- The invariant holds of every configuration the machine reaches. -/
theorem inv_of_reach {net : Net Var Val} (hwf : net.WF) {s : Spec.State Var Val} {t : ℕ∞}
    {c : MCfg Var Val} (h : ReflTransGen (MStep net) (net.init s t) c) : Inv net s t c := by
  induction h with
  | refl => exact inv_init hwf s t
  | tail _ hs ih => exact ih.step hwf hs

/-- **Soundness**: when every process of a run of the machine has finished, the
final states and the scripts the machine wrote are a behaviour of the book's
semantics of the network. -/
theorem netSpec_of_reach {net : Net Var Val} (hwf : net.WF) {s : Spec.State Var Val} {t : ℕ∞}
    {c : MCfg Var Val} (h : ReflTransGen (MStep net) (net.init s t) c) (hd : c.Done) :
    NetSpec net s t (c.ps.map (·.st)) c.L := by
  have hc := inv_of_reach hwf h
  refine ⟨by simpa using hc.length, ?_, hc.input⟩
  intro i pr f hpr hf
  rw [List.getElem?_map] at hf
  obtain ⟨pc, hpc, rfl⟩ := Option.map_eq_some_iff.mp hf
  have hk : pc.k = [] := hd _ (List.mem_of_getElem? hpc)
  have hpc' : pc = ⟨[], pc.st⟩ := by ext1 <;> simp [hk]
  refine ⟨?_, hc.w hpr hpc⟩
  rw [← hpc']
  exact hc.path c.L (fun _ => List.prefix_rfl) hpr hpc

/-! ### Running a network -/

/-- `Det`, as a test. -/
def detB : Prog Var Val → Bool
  | .seq p q => detB p && detB q
  | .cond _ p q => detB p && detB q
  | .whileDo _ p => detB p
  | .newLocal _ _ p => detB p
  | .or _ _ => false
  | .par _ p q => detB p && detB q
  | .prob _ _ _ => false
  | _ => true

omit [DecidableEq Var] [Defs Var Val] in
/-- The test is right. -/
theorem det_of_detB : ∀ {p : Prog Var Val}, detB p = true → Det p := by
  intro p h
  induction p with
  | seq _ _ ihp ihq => simp only [detB, Bool.and_eq_true] at h; exact ⟨ihp h.1, ihq h.2⟩
  | cond _ _ _ ihp ihq => simp only [detB, Bool.and_eq_true] at h; exact ⟨ihp h.1, ihq h.2⟩
  | whileDo _ _ ih => exact ih h
  | newLocal _ _ _ ih => exact ih h
  | or => simp [detB] at h
  | par _ _ _ ihp ihq => simp only [detB, Bool.and_eq_true] at h; exact ⟨ihp h.1, ihq h.2⟩
  | prob => simp [detB] at h
  | _ => trivial

/-- Process `i` takes a step, if it can; a chunk is run with fuel `f`. -/
def stepAt (net : Net Var Val) (f : ℕ) (c : MCfg Var Val) (i : ℕ) : Option (MCfg Var Val) :=
  match c.ps[i]? with
  | some ⟨.act p :: k, st⟩ =>
      if detB p then (runT f p ⟨st.mem, st.t⟩).map fun u =>
        ⟨c.ps.set i ⟨k, { st with mem := u.mem, t := u.t }⟩, c.L⟩ else none
  | some ⟨.seq p q :: k, st⟩ => some ⟨c.ps.set i ⟨p :: q :: k, st⟩, c.L⟩
  | some ⟨.cond b p q :: k, st⟩ =>
      some ⟨c.ps.set i ⟨(if b st.mem then p else q) :: k, st⟩, c.L⟩
  | some ⟨.loop b p :: k, st⟩ =>
      some ⟨c.ps.set i ⟨if b st.mem then p :: .loop b p :: k else k, st⟩, c.L⟩
  | some ⟨.call n :: k, st⟩ => some ⟨c.ps.set i ⟨net.defs n :: k, st⟩, c.L⟩
  | some ⟨.send ch e :: k, st⟩ =>
      match net.procs[i]? with
      | some pr =>
        if ch ∈ pr.outs then
          some ⟨c.ps.set i ⟨k, st.sent ch⟩, Function.update c.L ch (c.L ch ++ [(e st.mem, st.t)])⟩
        else none
      | none => none
  | some ⟨.recv ch x :: k, st⟩ =>
      match net.procs[i]? with
      | some pr =>
        if ch ∈ pr.ins then
          ((c.L ch)[st.r ch]?).map fun m => ⟨c.ps.set i ⟨k, st.received ch x m⟩, c.L⟩
        else none
      | none => none
  | _ => none

/-- A step the runner takes is a step of the machine. -/
theorem mstep_of_stepAt {net : Net Var Val} {f : ℕ} {c c' : MCfg Var Val} {i : ℕ}
    (h : stepAt net f c i = some c') : MStep net c c' := by
  unfold stepAt at h
  split at h
  · rename_i p k st hps
    split_ifs at h with hd
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .mk hps (.loc (.act (det_of_detB hd) (evalT_iff_denoteT.mpr (denoteT_of_runT hu))))
  · rename_i hps; cases h; exact .mk hps (.loc .seq)
  · rename_i b p q k st hps
    cases h
    cases hb : b st.mem
    · simpa [hb] using MStep.mk (net := net) hps (.loc (.condF hb))
    · simpa [hb] using MStep.mk (net := net) hps (.loc (.condT hb))
  · rename_i b p k st hps
    cases h
    cases hb : b st.mem
    · simpa [hb] using MStep.mk (net := net) hps (.loc (.loopF hb))
    · simpa [hb] using MStep.mk (net := net) hps (.loc (.loopT hb))
  · rename_i hps; cases h; exact .mk hps (.loc .call)
  · rename_i ch e k st hps
    split at h
    · rename_i pr hpr
      split_ifs at h with hch
      cases h
      exact .mk hps (.send hpr hch rfl)
    · cases h
  · rename_i ch x k st hps
    split at h
    · rename_i pr hpr
      split_ifs at h with hch
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .mk hps (.recv hpr hch hm)
    · cases h
  · cases h

/-- One round: each process in turn takes a step if it can. Also says whether
any did. -/
def sweep (net : Net Var Val) (f : ℕ) (c : MCfg Var Val) : MCfg Var Val × Bool :=
  (List.range c.ps.length).foldl
    (fun acc i => match stepAt net f acc.1 i with
      | some c' => (c', true)
      | none => acc) (c, false)

/-- A round is a run of the machine. -/
theorem reach_sweep (net : Net Var Val) (f : ℕ) (c : MCfg Var Val) :
    ReflTransGen (MStep net) c (sweep net f c).1 := by
  unfold sweep
  generalize List.range c.ps.length = l
  suffices ∀ acc : MCfg Var Val × Bool, ReflTransGen (MStep net) c acc.1 →
      ReflTransGen (MStep net) c (l.foldl (fun acc i => match stepAt net f acc.1 i with
        | some c' => (c', true)
        | none => acc) acc).1 from this _ .refl
  induction l with
  | nil => exact fun _ h => h
  | cons i l ih =>
    intro acc hacc
    apply ih
    dsimp only
    split
    · rename_i c' h; exact hacc.tail (mstep_of_stepAt h)
    · exact hacc

/-- Run a network for at most `n` rounds, round robin, stopping early when no
process can move. Fuel `f` is for each chunk. -/
def runNet (net : Net Var Val) (f : ℕ) : ℕ → MCfg Var Val → MCfg Var Val
  | 0, c => c
  | n + 1, c => if (sweep net f c).2 then runNet net f n (sweep net f c).1 else c

/-- The runner's result is reached by the machine. -/
theorem reach_runNet (net : Net Var Val) (f : ℕ) :
    ∀ (n : ℕ) (c : MCfg Var Val), ReflTransGen (MStep net) c (runNet net f n c)
  | 0, _ => .refl
  | n + 1, c => by
    unfold runNet
    split_ifs
    · exact (reach_sweep net f c).trans (reach_runNet net f n _)
    · exact .refl

/-- Every process has finished, as a test. -/
def MCfg.done (c : MCfg Var Val) : Bool := c.ps.all fun pc => pc.k.isEmpty

omit [DecidableEq Var] [Defs Var Val] in
/-- The test is right. -/
theorem MCfg.Done.of_done {c : MCfg Var Val} (h : c.done = true) : c.Done := by
  intro pc hpc
  simpa using List.all_eq_true.mp h pc hpc

/-- **The runner computes the network**: when it ends with every process
finished, what it computed is a behaviour of the book's semantics, and it is the
only configuration without a next step that the machine can reach, under any
schedule. -/
theorem runNet_correct [DetDefs Var Val] {net : Net Var Val} (hwf : net.WF) (f n : ℕ)
    (s : Spec.State Var Val) (t : ℕ∞) (hd : (runNet net f n (net.init s t)).done = true) :
    NetSpec net s t ((runNet net f n (net.init s t)).ps.map (·.st))
        (runNet net f n (net.init s t)).L ∧
      ∀ c, ReflTransGen (MStep net) (net.init s t) c → Normal net c →
        c = runNet net f n (net.init s t) := by
  have hr := reach_runNet net f n (net.init s t)
  have hD := MCfg.Done.of_done hd
  exact ⟨netSpec_of_reach hwf hr hD, fun c hc hn => normal_unique hwf hc hn hr (normal_of_done hD)⟩

/-! ### Completeness -/

/-- `n` steps of `r`. -/
inductive Path {α : Type*} (r : α → α → Prop) : ℕ → α → α → Prop
  | refl {a : α} : Path r 0 a a
  | head {n : ℕ} {a b c : α} : r a b → Path r n b c → Path r (n + 1) a c

omit [DecidableEq Var] [Defs Var Val] in
/-- A run has a length. -/
theorem exists_path {α : Type*} {r : α → α → Prop} {a b : α} (h : ReflTransGen r a b) :
    ∃ n, Path r n a b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl⟩
  | head hab _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, .head hab hn⟩

/-- The book's step is determined too: given the scripts, a process has one
history. -/
theorem pstep_det [DetDefs Var Val] {defs : ℕ → NProc Var Val} {pr : Proc Var Val}
    {S : Scripts Val} {a b b' : PCfg Var Val} (h : PStep defs pr S a b)
    (h' : PStep defs pr S a b') : b = b' := by
  cases h with
  | loc hl =>
    cases h' with
    | loc hl' => exact lstep_det hl hl'
    | send => cases hl
    | recv => cases hl
    | never => cases hl
  | send =>
    cases h' with
    | loc hl => cases hl
    | send => rfl
  | recv _ hm =>
    cases h' with
    | loc hl => cases hl
    | recv _ hm' => rw [hm] at hm'; cases hm'; rfl
    | never _ hm' => rw [hm] at hm'; cases hm'
  | never _ hm =>
    cases h' with
    | loc hl => cases hl
    | recv _ hm' => rw [hm] at hm'; cases hm'
    | never => rfl

/-- A finished process takes no step. -/
theorem pstep_nil {defs : ℕ → NProc Var Val} {pr : Proc Var Val} {S : Scripts Val}
    {st : PSt Var Val} {b : PCfg Var Val} (h : PStep defs pr S ⟨[], st⟩ b) : False := by
  cases h with | loc hl => cases hl

/-- A finished process is where its history ends. -/
theorem path_nil {defs : ℕ → NProc Var Val} {pr : Proc Var Val} {S : Scripts Val} {n : ℕ}
    {a : PCfg Var Val} {f : PSt Var Val} (ha : a.k = [])
    (h : Path (PStep defs pr S) n a ⟨[], f⟩) : a.st = f := by
  cases h with
  | refl => rfl
  | head hs _ =>
    obtain ⟨k, st⟩ := a
    dsimp only at ha
    subst ha
    exact (pstep_nil hs).elim

/-- A step along a history leaves the rest of it. -/
theorem path_tail [DetDefs Var Val] {defs : ℕ → NProc Var Val} {pr : Proc Var Val}
    {S : Scripts Val} {n : ℕ} {a b : PCfg Var Val} {f : PSt Var Val}
    (h : Path (PStep defs pr S) n a ⟨[], f⟩) (hs : PStep defs pr S a b) :
    ∃ m, n = m + 1 ∧ Path (PStep defs pr S) m b ⟨[], f⟩ := by
  cases h with
  | refl => exact (pstep_nil hs).elim
  | head hs' hp => rw [pstep_det hs hs']; exact ⟨_, rfl, hp⟩

/-- Time does not go backward. -/
theorem PStep.t_le {defs : ℕ → NProc Var Val} {pr : Proc Var Val} {S : Scripts Val}
    {a b : PCfg Var Val} (h : PStep defs pr S a b) : a.st.t ≤ b.st.t := by
  cases h with
  | loc hl =>
    cases hl with
    | act _ he => exact time_le_of_evalT he
    | _ => exact le_rfl
  | send => exact le_rfl
  | recv => exact le_max_left _ _
  | never => exact le_top

/-- Time does not go backward. -/
theorem Path.t_le {defs : ℕ → NProc Var Val} {pr : Proc Var Val} {S : Scripts Val} {n : ℕ}
    {a b : PCfg Var Val} (h : Path (PStep defs pr S) n a b) : a.st.t ≤ b.st.t := by
  induction h with
  | refl => exact le_rfl
  | head hs _ ih => exact hs.t_le.trans ih

/-- **A message is stamped with a time between now and the end**: a message a
process will write is in the script, sent no earlier than the process's time now
and no later than its time at the end. -/
theorem Path.stamp {defs : ℕ → NProc Var Val} {pr : Proc Var Val} {S : Scripts Val} {n : ℕ}
    {a z : PCfg Var Val} (h : Path (PStep defs pr S) n a z) {ch idx : ℕ}
    (h₁ : a.st.w ch ≤ idx) (h₂ : idx < z.st.w ch) :
    ∃ m, (S ch)[idx]? = some m ∧ a.st.t ≤ m.2 ∧ m.2 ≤ z.st.t := by
  induction h with
  | refl => omega
  | head hs hp ih =>
    have ht := hs.t_le
    cases hs with
    | loc hl =>
      obtain ⟨m, hm, h₃, h₄⟩ := ih (by rw [hl.w_eq]; exact h₁) h₂
      exact ⟨m, hm, ht.trans h₃, h₄⟩
    | @send ch' e k st hch hS =>
      by_cases hc : ch' = ch ∧ st.w ch = idx
      · obtain ⟨rfl, rfl⟩ := hc
        exact ⟨_, hS, le_rfl, hp.t_le⟩
      · obtain ⟨m, hm, h₃, h₄⟩ := ih (by
          by_cases hcc : ch' = ch
          · subst hcc
            dsimp only at h₁
            simp only [PSt.sent, Function.update_self]
            have : st.w ch' ≠ idx := fun h => hc ⟨rfl, h⟩
            omega
          · simpa [PSt.sent, Function.update_of_ne (Ne.symm hcc)] using h₁) h₂
        exact ⟨m, hm, ht.trans h₃, h₄⟩
    | recv =>
      obtain ⟨m, hm, h₃, h₄⟩ := ih h₁ h₂
      exact ⟨m, hm, ht.trans h₃, h₄⟩
    | never =>
      obtain ⟨m, hm, h₃, h₄⟩ := ih h₁ h₂
      exact ⟨m, hm, ht.trans h₃, h₄⟩

omit [DecidableEq Var] [Defs Var Val] in
/-- A message added at the end of a prefix, as the script goes on. -/
theorem prefix_snoc {α : Type*} {l s : List α} {x : α} (h : l <+: s) (hx : s[l.length]? = some x) :
    l ++ [x] <+: s := by
  obtain ⟨u, rfl⟩ := h
  cases u with
  | nil => simp at hx
  | cons y u =>
    simp at hx
    subst hx
    exact ⟨u, by simp⟩

/-- A machine action that is the book's step keeps the scripts written a prefix
of the book's. -/
theorem Act.pre {net : Net Var Val} {i : ℕ} {L L' : Scripts Val} {a b : PCfg Var Val}
    (h : Act net i L a b L') {pr : Proc Var Val} (hpr : net.procs[i]? = some pr)
    (hw : ∀ c ∈ pr.outs, a.st.w c = (L c).length) {S : Scripts Val}
    (hs : PStep net.defs pr S a b) (hpre : ∀ c, L c <+: S c) : ∀ c, L' c <+: S c := by
  cases h with
  | loc => exact hpre
  | @send _ pr' ch e k st hpr' hch hL =>
    rw [hpr] at hpr'; cases hpr'
    subst hL
    cases hs with
    | loc hl => cases hl
    | send _ hS =>
      intro c
      by_cases hc : c = ch
      · subst hc
        rw [Function.update_self]
        exact prefix_snoc (hpre c) (by rw [← hw c hch]; exact hS)
      · rw [Function.update_of_ne hc]; exact hpre c
  | recv => exact hpre

/-- Process `i` waits at an input whose message — in the scripts `S` — has not
been written yet; it was sent at time `τ`. -/
def Blocked (net : Net Var Val) (S : Scripts Val) (c : MCfg Var Val) (i : ℕ) (τ : ℕ∞) : Prop :=
  ∃ (pr : Proc Var Val) (ch : ℕ) (x : Var) (k : List (NProc Var Val)) (st : PSt Var Val)
    (m : Msg Val), net.procs[i]? = some pr ∧ c.ps[i]? = some ⟨.recv ch x :: k, st⟩ ∧
    ch ∈ pr.ins ∧ (S ch)[st.r ch]? = some m ∧ m.2 = τ ∧ (c.L ch)[st.r ch]? = none

section Complete

variable [DetDefs Var Val] {net : Net Var Val} {s : Spec.State Var Val} {t : ℕ∞}
  {fin : List (PSt Var Val)} {S : Scripts Val} {c : MCfg Var Val}

/-- The machine is following the book's histories. -/
def Follows (net : Net Var Val) (fin : List (PSt Var Val)) (S : Scripts Val) (c : MCfg Var Val)
    (len : ℕ → ℕ) : Prop :=
  ∀ {i : ℕ} {pr : Proc Var Val} {pc : PCfg Var Val} {f : PSt Var Val}, net.procs[i]? = some pr →
    c.ps[i]? = some pc → fin[i]? = some f → Path (PStep net.defs pr S) (len i) pc ⟨[], f⟩

omit [DetDefs Var Val] in
/-- Each process's configuration belongs to a process. -/
theorem exists_proc (hc : Inv net s t c) {i : ℕ} {pc : PCfg Var Val} (hi : c.ps[i]? = some pc) :
    ∃ pr, net.procs[i]? = some pr := by
  have := (List.getElem?_eq_some_iff.mp hi).1
  exact ⟨net.procs[i]'(hc.length ▸ this), List.getElem?_eq_getElem _⟩

omit [DetDefs Var Val] in
/-- Each process has a configuration. -/
theorem exists_pcfg (hc : Inv net s t c) {i : ℕ} {pr : Proc Var Val}
    (hi : net.procs[i]? = some pr) : ∃ pc, c.ps[i]? = some pc := by
  have := (List.getElem?_eq_some_iff.mp hi).1
  exact ⟨c.ps[i]'(hc.length ▸ this), List.getElem?_eq_getElem _⟩

omit [DetDefs Var Val] in
/-- Each process has a final state. -/
theorem exists_fin (hspec : NetSpec net s t fin S) {i : ℕ} {pr : Proc Var Val}
    (hi : net.procs[i]? = some pr) : ∃ f, fin[i]? = some f := by
  have := (List.getElem?_eq_some_iff.mp hi).1
  exact ⟨fin[i]'(hspec.1 ▸ this), List.getElem?_eq_getElem _⟩

omit [DetDefs Var Val] in
/-- A process that has not finished can take the book's next step on the
machine, or is blocked. -/
theorem step_or_blocked (hspec : NetSpec net s t fin S) (hfin : ∀ f ∈ fin, f.t ≠ ⊤)
    (hc : Inv net s t c) (hpre : ∀ ch, c.L ch <+: S ch) {len : ℕ → ℕ}
    (hpath : Follows net fin S c len) {i : ℕ} {pc : PCfg Var Val} (hi : c.ps[i]? = some pc)
    (hk : pc.k ≠ []) :
    (∃ b L', Act net i c.L pc b L' ∧ ∀ pr, net.procs[i]? = some pr → PStep net.defs pr S pc b) ∨
      ∃ τ, Blocked net S c i τ := by
  obtain ⟨pr, hpr⟩ := exists_proc hc hi
  obtain ⟨f, hf⟩ := exists_fin hspec hpr
  have hp := hpath hpr hi hf
  generalize len i = n at hp
  cases hp with
  | refl => exact (hk rfl).elim
  | head hs hrest =>
    have same : ∀ {pr'}, net.procs[i]? = some pr' → pr' = pr := fun h => by
      rw [hpr] at h; exact (Option.some.inj h).symm
    cases hs with
    | loc hl => exact .inl ⟨_, _, .loc hl, fun _ _ => .loc hl⟩
    | send hch hS =>
      exact .inl ⟨_, _, .send hpr hch rfl, fun _ h => by rw [same h]; exact .send hch hS⟩
    | @recv ch x k st m hch hm =>
      cases hL : (c.L ch)[st.r ch]? with
      | none => exact .inr ⟨_, pr, ch, x, k, st, m, hpr, hi, hch, hm, rfl, hL⟩
      | some m' =>
        have := getElem?_of_prefix (hpre ch) hL
        rw [hm] at this; cases this
        exact .inl ⟨_, _, .recv hpr hch hL, fun _ h => by rw [same h]; exact .recv hch hm⟩
    | never =>
      have := hrest.t_le
      exact (hfin f (List.mem_of_getElem? hf) (top_le_iff.mp this)).elim

/-- **The time-ordering argument.** If every unfinished process is blocked, the
writer of the message a blocked process waits for is itself blocked, waiting for
a message sent strictly earlier: it receives that message before it sends the
one awaited, and a message is received one unit after it is sent. -/
theorem blocked_descent (hspec : NetSpec net s t fin S)
    (hfin : ∀ f ∈ fin, f.t ≠ ⊤) (hc : Inv net s t c)
    {len : ℕ → ℕ} (hpath : Follows net fin S c len)
    (hall : ∀ (j : ℕ) (pc : PCfg Var Val), c.ps[j]? = some pc → pc.k ≠ [] → ∃ τ, Blocked net S c j τ)
    {i : ℕ} {τ : ℕ∞} (hb : Blocked net S c i τ) : ∃ j τ', Blocked net S c j τ' ∧ τ' < τ := by
  obtain ⟨pr, ch, x, k, st, m, hpr, hi, hch, hm, rfl, hL⟩ := hb
  by_cases hw : ∃ (j : ℕ) (prj : Proc Var Val), net.procs[j]? = some prj ∧ ch ∈ prj.outs
  swap
  · push Not at hw
    have h₁ := hc.input ch hw
    have h₂ := hspec.2.2 ch hw
    rw [h₁, ← h₂, hm] at hL
    cases hL
  obtain ⟨j, prj, hprj, hchj⟩ := hw
  obtain ⟨pcj, hpcj⟩ := exists_pcfg hc hprj
  obtain ⟨fj, hfj⟩ := exists_fin hspec hprj
  have hwj := hc.w hprj hpcj ch hchj
  have hr : (c.L ch).length ≤ st.r ch := List.getElem?_eq_none_iff.mp hL
  have hfw := (hspec.2.1 j prj fj hprj hfj).2 ch hchj
  have hrS : st.r ch < (S ch).length := (List.getElem?_eq_some_iff.mp hm).1
  have hp := hpath hprj hpcj hfj
  by_cases hkj : pcj.k = []
  · have := path_nil hkj hp
    rw [this] at hwj
    omega
  obtain ⟨τ', hbj⟩ := hall j pcj hpcj hkj
  obtain ⟨prj', ch', x', k', st', m', hprj', hpcj', hch', hm', rfl, hL'⟩ := hbj
  rw [hprj] at hprj'; cases hprj'
  rw [hpcj] at hpcj'; cases hpcj'
  obtain ⟨n', _, hp'⟩ := path_tail hp (.recv hch' hm')
  dsimp only at hwj
  obtain ⟨m₂, hm₂, h₁, h₂⟩ := hp'.stamp (ch := ch) (idx := st.r ch)
    (by simp only [PSt.received]; omega) (by dsimp only; omega)
  rw [hm] at hm₂; cases hm₂
  refine ⟨j, m'.2, ⟨prj, ch', x', k', st', m', hprj, hpcj, hch', hm', rfl, hL'⟩, ?_⟩
  have hfj' : fj.t ≠ ⊤ := hfin fj (List.mem_of_getElem? hfj)
  have h₃ : m'.2 + 1 ≤ m.2 := le_trans (le_max_right _ _) h₁
  have h₄ : m.2 ≠ ⊤ := ne_top_of_le_ne_top hfj' h₂
  have h₅ : m'.2 ≠ ⊤ := fun h => h₄ (top_le_iff.mp (by simpa [h] using h₃))
  exact (ENat.add_one_le_iff h₅).mp h₃

/-- No process is blocked, if every unfinished one is. -/
theorem not_blocked (hspec : NetSpec net s t fin S)
    (hfin : ∀ f ∈ fin, f.t ≠ ⊤) (hc : Inv net s t c)
    {len : ℕ → ℕ} (hpath : Follows net fin S c len)
    (hall : ∀ (j : ℕ) (pc : PCfg Var Val), c.ps[j]? = some pc → pc.k ≠ [] → ∃ τ, Blocked net S c j τ) (τ : ℕ∞) :
    ∀ i, ¬ Blocked net S c i τ := by
  refine WellFoundedLT.induction (motive := fun τ => ∀ i, ¬ Blocked net S c i τ) τ ?_
  intro τ ih i hb
  obtain ⟨j, τ', hb', hlt⟩ := blocked_descent hspec hfin hc hpath hall hb
  exact ih τ' hlt j hb'

/-- **Progress**: while some process has not finished, the machine can take the
book's next step for one of them. -/
theorem progress (hspec : NetSpec net s t fin S)
    (hfin : ∀ f ∈ fin, f.t ≠ ⊤) (hc : Inv net s t c) (hpre : ∀ ch, c.L ch <+: S ch)
    {len : ℕ → ℕ} (hpath : Follows net fin S c len)
    (hnd : ∃ (i : ℕ) (pc : PCfg Var Val), c.ps[i]? = some pc ∧ pc.k ≠ []) :
    ∃ i pc b L', c.ps[i]? = some pc ∧ Act net i c.L pc b L' ∧
      ∀ pr, net.procs[i]? = some pr → PStep net.defs pr S pc b := by
  by_cases hall : ∀ (j : ℕ) (pc : PCfg Var Val), c.ps[j]? = some pc → pc.k ≠ [] → ∃ τ, Blocked net S c j τ
  · obtain ⟨i, pc, hi, hk⟩ := hnd
    obtain ⟨τ, hb⟩ := hall i pc hi hk
    exact (not_blocked hspec hfin hc hpath hall τ i hb).elim
  · push Not at hall
    obtain ⟨j, pc, hj, hk, hnb⟩ := hall
    rcases step_or_blocked hspec hfin hc hpre hpath hj hk with ⟨b, L', ha, hps⟩ | ⟨τ, hb⟩
    · exact ⟨j, pc, b, L', hj, ha, hps⟩
    · exact (hnb τ hb).elim

/-- One round of the completeness argument: the machine has finished, as the
book says it does, or it takes a step and the histories left get shorter. -/
theorem complete_step (hwf : net.WF) (hspec : NetSpec net s t fin S)
    (hfin : ∀ f ∈ fin, f.t ≠ ⊤) (hr : ReflTransGen (MStep net) (net.init s t) c)
    (hpre : ∀ ch, c.L ch <+: S ch) {len : ℕ → ℕ} (hpath : Follows net fin S c len) :
    (c.Done ∧ c.ps.map (·.st) = fin ∧ c.L = S) ∨
      ∃ c' len', ReflTransGen (MStep net) (net.init s t) c' ∧ (∀ ch, c'.L ch <+: S ch) ∧
        Follows net fin S c' len' ∧
        ∑ i ∈ Finset.range net.procs.length, len' i < ∑ i ∈ Finset.range net.procs.length, len i := by
  have hc := inv_of_reach hwf hr
  by_cases hnd : ∃ (i : ℕ) (pc : PCfg Var Val), c.ps[i]? = some pc ∧ pc.k ≠ []
  · right
    obtain ⟨i, pc, b, L', hi, ha, hps⟩ := progress hspec hfin hc hpre hpath hnd
    obtain ⟨pr, hpr⟩ := exists_proc hc hi
    obtain ⟨f, hf⟩ := exists_fin hspec hpr
    obtain ⟨m, hm, hp⟩ := path_tail (hpath hpr hi hf) (hps pr hpr)
    have hilt : i < c.ps.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨⟨c.ps.set i b, L'⟩, Function.update len i m, hr.tail (.mk hi ha),
      ha.pre hpr (hc.w hpr hi) (hps pr hpr) hpre, ?_, ?_⟩
    · intro j prj pcj fj hprj hpcj hfj
      by_cases hij : i = j
      · subst hij
        simp only [List.getElem?_set_self hilt, Option.some.injEq] at hpcj
        subst hpcj
        rw [hpr] at hprj; cases hprj
        rw [hf] at hfj; cases hfj
        simpa using hp
      · rw [List.getElem?_set_ne hij] at hpcj
        rw [Function.update_of_ne (Ne.symm hij)]
        exact hpath hprj hpcj hfj
    · apply Finset.sum_lt_sum
      · intro j _
        by_cases hij : j = i
        · subst hij; simp [hm]
        · simp [Function.update_of_ne hij]
      · refine ⟨i, Finset.mem_range.mpr (hc.length ▸ hilt), ?_⟩
        simp [hm]
  · left
    push Not at hnd
    have hfinal : ∀ {i : ℕ} {pr : Proc Var Val} {pc : PCfg Var Val} {f : PSt Var Val},
        net.procs[i]? = some pr → c.ps[i]? = some pc → fin[i]? = some f →
        pc.st = f := fun hpr hi hf => path_nil (hnd _ _ hi) (hpath hpr hi hf)
    refine ⟨fun pc hpc => ?_, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hpc
      exact hnd i pc hi
    · apply List.ext_getElem?
      intro i
      rw [List.getElem?_map]
      cases hi : c.ps[i]? with
      | none =>
        have h₁ := List.getElem?_eq_none_iff.mp hi
        have h₂ : fin.length ≤ i := by rw [hspec.1, ← hc.length]; exact h₁
        exact (List.getElem?_eq_none_iff.mpr h₂).symm
      | some pc =>
        obtain ⟨pr, hpr⟩ := exists_proc hc hi
        obtain ⟨f, hf⟩ := exists_fin hspec hpr
        rw [hf, Option.map_some, hfinal hpr hi hf]
    · funext ch
      by_cases hw : ∃ (j : ℕ) (prj : Proc Var Val), net.procs[j]? = some prj ∧ ch ∈ prj.outs
      · obtain ⟨j, prj, hprj, hchj⟩ := hw
        obtain ⟨pcj, hpcj⟩ := exists_pcfg hc hprj
        obtain ⟨fj, hfj⟩ := exists_fin hspec hprj
        have hwj := hc.w hprj hpcj ch hchj
        rw [hfinal hprj hpcj hfj, (hspec.2.1 j prj fj hprj hfj).2 ch hchj] at hwj
        exact (hpre ch).eq_of_length hwj.symm
      · push Not at hw
        rw [hc.input ch hw, hspec.2.2 ch hw]

/-- Completeness, by induction on the length of the histories left. -/
theorem complete_aux (hwf : net.WF) (hspec : NetSpec net s t fin S)
    (hfin : ∀ f ∈ fin, f.t ≠ ⊤) (N : ℕ) :
    ∀ (c : MCfg Var Val) (len : ℕ → ℕ), ReflTransGen (MStep net) (net.init s t) c →
      (∀ ch, c.L ch <+: S ch) → Follows net fin S c len →
      ∑ i ∈ Finset.range net.procs.length, len i ≤ N →
      ∃ c', ReflTransGen (MStep net) (net.init s t) c' ∧ c'.Done ∧ c'.ps.map (·.st) = fin ∧
        c'.L = S := by
  induction N with
  | zero =>
    intro c len hr hpre hpath hN
    rcases complete_step hwf hspec hfin hr hpre hpath with h | ⟨_, _, _, _, _, hlt⟩
    · exact ⟨c, hr, h⟩
    · omega
  | succ N ih =>
    intro c len hr hpre hpath hN
    rcases complete_step hwf hspec hfin hr hpre hpath with h | ⟨c', len', hr', hpre', hpath', hlt⟩
    · exact ⟨c, hr, h⟩
    · exact ih c' len' hr' hpre' hpath' (by omega)

/-- **Completeness**: a behaviour of the book's semantics in which every process
finishes at a finite time is computed by the machine — it reaches a
configuration where every process has finished in its final state, having
written exactly the book's scripts. -/
theorem reach_of_netSpec (hwf : net.WF) (hspec : NetSpec net s t fin S)
    (hfin : ∀ f ∈ fin, f.t ≠ ⊤) :
    ∃ c, ReflTransGen (MStep net) (net.init s t) c ∧ c.Done ∧ c.ps.map (·.st) = fin ∧
      c.L = S := by
  have : ∀ i : ℕ, ∃ n, ∀ {pr : Proc Var Val} {pc : PCfg Var Val} {f : PSt Var Val},
      net.procs[i]? = some pr → (net.init s t).ps[i]? = some pc → fin[i]? = some f →
      Path (PStep net.defs pr S) n pc ⟨[], f⟩ := by
    intro i
    rcases hpr : net.procs[i]? with _ | pr
    · exact ⟨0, fun h => by cases h⟩
    rcases hf : fin[i]? with _ | f
    · exact ⟨0, fun _ _ h => by cases h⟩
    obtain ⟨n, hn⟩ := exists_path (hspec.2.1 i pr f hpr hf).1
    refine ⟨n, fun h₁ h₂ h₃ => ?_⟩
    cases h₁; cases h₃
    simp only [Net.init, List.getElem?_map, hpr, Option.map_some, Option.some.injEq] at h₂
    subst h₂
    exact hn
  choose len hlen using this
  refine complete_aux hwf hspec hfin _ (net.init s t) len .refl ?_ (fun h₁ h₂ h₃ => hlen _ h₁ h₂ h₃)
    le_rfl
  intro ch
  by_cases hw : ∃ (j : ℕ) (prj : Proc Var Val), net.procs[j]? = some prj ∧ ch ∈ prj.outs
  · obtain ⟨j, prj, hprj, hchj⟩ := hw
    simp [Net.init, hwf.input hprj hchj]
  · push Not at hw
    simp [Net.init, hspec.2.2 ch hw]

/-- **The book's semantics has one behaviour with finite times**, and it is the
machine's. -/
theorem netSpec_unique (hwf : net.WF) {fin₁ fin₂ : List (PSt Var Val)} {S₁ S₂ : Scripts Val}
    (h₁ : NetSpec net s t fin₁ S₁) (hf₁ : ∀ f ∈ fin₁, f.t ≠ ⊤)
    (h₂ : NetSpec net s t fin₂ S₂) (hf₂ : ∀ f ∈ fin₂, f.t ≠ ⊤) : fin₁ = fin₂ ∧ S₁ = S₂ := by
  obtain ⟨c₁, r₁, d₁, e₁, l₁⟩ := reach_of_netSpec hwf h₁ hf₁
  obtain ⟨c₂, r₂, d₂, e₂, l₂⟩ := reach_of_netSpec hwf h₂ hf₂
  have := normal_unique hwf r₁ (normal_of_done d₁) r₂ (normal_of_done d₂)
  subst this
  exact ⟨e₁.symm.trans e₂, l₁.symm.trans l₂⟩

/-- **Deadlock** (§9.1.8): if the machine stops with a process unfinished, then
in every behaviour of the book's semantics some process ends at time `∞`. -/
theorem deadlock_top (hwf : net.WF) (hr : ReflTransGen (MStep net) (net.init s t) c)
    (hn : Normal net c) (hnd : ¬ c.Done) (hspec : NetSpec net s t fin S) :
    ∃ f ∈ fin, f.t = ⊤ := by
  by_contra h
  push Not at h
  obtain ⟨c', r', d', _⟩ := reach_of_netSpec hwf hspec h
  have := normal_unique hwf hr hn r' (normal_of_done d')
  subst this
  exact hnd d'

end Complete

/-! ### Demonstrations -/

namespace Demonstration

/-- Processes over numbered variables holding integers. -/
abbrev NP := NProc ℕ ℤ

/-- All variables `0`. -/
def zero : Spec.State ℕ ℤ := fun _ => 0

/-- No named processes. -/
def noDefs : ℕ → NP := fun _ => .act .ok

/-- What a run shows: each process's variables `0` and `1`, and its clock. -/
def show2 (c : MCfg ℕ ℤ) : List (ℤ × ℤ × ℕ∞) := c.ps.map fun pc => (pc.st.mem 0, pc.st.mem 1, pc.st.t)

/-- `c! 2 || (c?. x:= c)`, channel `0`, `x` variable `0`. -/
def sendRecv : Net ℕ ℤ :=
  ⟨noDefs, [⟨.send 0 fun _ => 2, [0], []⟩, ⟨.recv 0 0, [], [0]⟩], fun _ => []⟩

/-- The message arrives, one unit of time after it was sent. -/
theorem sendRecv_run :
    show2 (runNet sendRecv 10 10 (sendRecv.init zero 0)) = [(0, 0, 0), (2, 0, 1)] := by
  decide +kernel

/-- The book's buffer (§9.1.2 example): `c! 3. t:= t+1. c! 4 || (c?. c?. x:= c)`
— the reader waits for the second message, sent at time 1, so it has it at
time 2. -/
def buffer : Net ℕ ℤ :=
  ⟨noDefs,
    [⟨.seq (.send 0 fun _ => 3) (.seq (.act .tick) (.send 0 fun _ => 4)), [0], []⟩,
     ⟨.seq (.recv 0 1) (.recv 0 0), [], [0]⟩], fun _ => []⟩

theorem buffer_run :
    show2 (runNet buffer 10 10 (buffer.init zero 0)) = [(0, 0, 1), (4, 3, 2)] ∧
      (runNet buffer 10 10 (buffer.init zero 0)).L 0 = [(3, 0), (4, 1)] := by
  decide +kernel

/-- The book's deadlock (§9.1.8): each process waits for the other.
`(c?. d! 2) || (d?. c! 1)`. -/
def deadlock : Net ℕ ℤ :=
  ⟨noDefs,
    [⟨.seq (.recv 0 0) (.send 1 fun _ => 2), [1], [0]⟩,
     ⟨.seq (.recv 1 0) (.send 0 fun _ => 1), [0], [1]⟩], fun _ => []⟩

/-- Neither moves past its input. -/
theorem deadlock_run :
    (runNet deadlock 10 10 (deadlock.init zero 0)).done = false ∧
      (runNet deadlock 10 10 (deadlock.init zero 0)).ps.map (·.k.length) = [2, 2] := by
  decide +kernel

/-- The doubler, `S ⇐ c?. d! 2×c. S`, reading what the environment supplies on
`c` (channel `0`) and writing `d` (channel `1`); named process `0` is `S`. -/
def doubler : Net ℕ ℤ :=
  ⟨fun _ => .seq (.recv 0 0) (.seq (.send 1 fun s => 2 * s 0) (.call 0)),
    [⟨.call 0, [1], [0]⟩], fun c => if c = 0 then [(1, 0), (2, 0), (5, 3)] else []⟩

/-- It doubles what it is given, each output one unit after its input arrived,
and then waits for more. -/
theorem doubler_run :
    (runNet doubler 10 50 (doubler.init zero 0)).L 1 = [(2, 1), (4, 1), (10, 4)] := by
  decide +kernel

end Demonstration

end LaPToP.ProgramTheory.Interpreter.Network
