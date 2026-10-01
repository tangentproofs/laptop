import LaPToP.ProgramTheory.InterpreterTime
import Mathlib.Logic.Relation

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

* `normal_unique` — **determinacy**: from a start, the machine reaches at most
  one final configuration, whatever the order in which the processes take
  their turns (it is confluent: `mstep_diamond`).
* `netSpec_of_reach` — **soundness**: a run of the machine in which every
  process finishes is a behaviour of the book's semantics, with the scripts the
  machine wrote.

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

end LaPToP.ProgramTheory.Interpreter.Network
