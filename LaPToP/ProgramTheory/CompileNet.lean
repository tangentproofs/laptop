import LaPToP.ProgramTheory.CompileB4
import LaPToP.ProgramTheory.Network

/-!
# A swarm of b4 machines runs a network

The processes of a network (`Network`), written in the compiler's statements
(`CompileB4.Stmt`, with `tick`, `c! e` and `c?. x:= c`), are compiled each to its
own b4 machine, and the machines run together as a swarm (`B4.Swarm`), joined by
channels through `io`. This module proves that the swarm does what the network
machine does: every run of the network in which no value or time leaves 32 bits
is matched, step for step, by a run of the swarm (`swarm_simulates`), so when the
network finishes, the machines halt with the variables, clocks and channel
scripts the network computed (`swarm_correct`) — which, by `Network`, is the
book's semantics.
-/

namespace LaPToP.ProgramTheory.CompileNet

open B4 Relation
open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.Interpreter.Network
open LaPToP.ProgramTheory.CompileB4

/-! ### Processes -/

/-- A statement as a process of the network machine: each assignment and `tick`
is a chunk, communication is communication, and the control structure stays. A
call's return is a chunk that does nothing. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.toNP : Stmt → NProc ℕ Value
  | .ok => .act .ok
  | .assign x e => .act (Lang.assign x e)
  | .tick => .act .tick
  | .seq p q => .seq p.toNP q.toNP
  | .cond c p q => .cond c.test p.toNP q.toNP
  | .loop c p => .loop c.test p.toNP
  | .send ch e => .send ch e.eval
  | .recv ch x => .recv ch x
  | .call k => .call k
  | .scope x e p => .scope x e.eval p.toNP
  | .ret => .act .ok
  | .restore x v => .restore x v
  | .check ch x => .check ch x .bool
  | .store x i e => .act (assignIdx x [i] e)
  -- Backtracking is compiled for a lone program (`CompileBT`), not in a network.
  | .choice p _ => p.toNP
  | .ensure c => .act (Lang.ensure c)

/-- A statement a program is written in: no return or end of scope, which only
running makes. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.clean : Stmt → Bool
  | .seq p q => p.clean && q.clean
  | .cond _ p q => p.clean && q.clean
  | .loop _ p => p.clean
  | .scope _ _ p => p.clean
  | .choice p q => p.clean && q.clean
  | .ret => false
  | .restore _ _ => false
  | _ => true

/-- How many entries what is left keeps on the control stack: one for each
return and each end of scope. -/
def frames (ks : List Stmt) : ℕ := ks.countP fun p => !p.clean

/-- A process: its statement, and the channels it writes and reads. -/
structure SProc where
  /-- The body. -/
  body : Stmt
  /-- The channels it writes. -/
  outs : List ℕ
  /-- The channels it reads. -/
  ins : List ℕ

/-- A network of statements, the named statements its processes call, and the
scripts the environment supplies. -/
structure SNet where
  /-- The processes. -/
  procs : List SProc
  /-- The input. -/
  input : Scripts Value
  /-- The named statements. -/
  defs : ℕ → Stmt := fun _ => .ok

/-- The network the network machine runs: a call runs the named statement and
then returns. -/
def SNet.toNet (net : SNet) : Net ℕ Value :=
  ⟨fun k => .seq (net.defs k).toNP (.act .ok),
    net.procs.map fun pr => ⟨pr.body.toNP, pr.outs, pr.ins⟩, net.input⟩

/-- A configuration: each process's statements still to run and its state, and
the scripts so far. -/
structure SCfg where
  /-- The processes. -/
  ps : List (List Stmt × PSt ℕ Value)
  /-- The scripts. -/
  L : Scripts Value

/-- The configuration of the network machine it is. -/
def SCfg.toM (c : SCfg) : MCfg ℕ Value := ⟨c.ps.map fun (ks, st) => ⟨ks.map Stmt.toNP, st⟩, c.L⟩

/-- Every process at its start. -/
def SNet.init (net : SNet) (s : St) : SCfg :=
  ⟨net.procs.map fun pr => ([pr.body], ⟨s, 0, fun _ => 0, fun _ => 0⟩), net.input⟩

theorem SNet.init_toM (net : SNet) (s : St) : (net.init s).toM = net.toNet.init s 0 := by
  simp [SNet.init, SCfg.toM, Net.init, SNet.toNet, Proc.start]

/-- A time the machine's clock holds: finite, and in 31 bits. -/
def TFits (t : ℕ∞) : Prop := t < (2 ^ 31 : ℕ)

/-- **What process `i` can do, in 32 bits**: the network machine's actions,
with every expression fitting (`Fits`), every condition a binary, every variable
assigned or input having a cell, every time fitting, every call of a defined
name, and the control stack not overflowing. -/
inductive SAct (L : Layout) (pr : SProc) :
    Scripts Value → List Stmt × PSt ℕ Value → List Stmt × PSt ℕ Value → Scripts Value → Prop
  /-- `ok`. -/
  | ok {Λ ks st} : SAct L pr Λ (.ok :: ks, st) (ks, st) Λ
  /-- `x:= e`. -/
  | assign {Λ ks st x e} : x < L.n → L.arrayAt x = none → Fits L st.mem e →
      SAct L pr Λ (.assign x e :: ks, st)
        (ks, { st with mem := Function.update st.mem x (e.eval st.mem) }) Λ
  /-- `t:= t+1`. -/
  | tick {Λ ks st} : TFits (st.t + 1) → SAct L pr Λ (.tick :: ks, st) (ks, { st with t := st.t + 1 }) Λ
  /-- `P. Q`. -/
  | seq {Λ ks st p q} : SAct L pr Λ (.seq p q :: ks, st) (p :: q :: ks, st) Λ
  /-- `if` with a true condition. -/
  | condT {Λ ks st c p q} : Fits L st.mem c → c.eval st.mem = .bool true →
      SAct L pr Λ (.cond c p q :: ks, st) (p :: ks, st) Λ
  /-- `if` with a false condition. -/
  | condF {Λ ks st c p q} : Fits L st.mem c → c.eval st.mem = .bool false →
      SAct L pr Λ (.cond c p q :: ks, st) (q :: ks, st) Λ
  /-- A loop that goes round. -/
  | loopT {Λ ks st c p} : Fits L st.mem c → c.eval st.mem = .bool true →
      SAct L pr Λ (.loop c p :: ks, st) (p :: .loop c p :: ks, st) Λ
  /-- A loop that exits. -/
  | loopF {Λ ks st c p} : Fits L st.mem c → c.eval st.mem = .bool false →
      SAct L pr Λ (.loop c p :: ks, st) (ks, st) Λ
  /-- `c! e`. -/
  | send {Λ ks st ch e} : ch ∈ pr.outs → Fits L st.mem e →
      SAct L pr Λ (.send ch e :: ks, st) (ks, st.sent ch)
        (Function.update Λ ch (Λ ch ++ [(e.eval st.mem, st.t)]))
  /-- `c?. x:= c`. -/
  | recv {Λ ks st ch x m} : ch ∈ pr.ins → (Λ ch)[st.r ch]? = some m → x < L.n →
      L.arrayAt x = none →
      TFits (max st.t (m.2 + 1)) →
      SAct L pr Λ (.recv ch x :: ks, st) (ks, st.received ch x m) Λ
  /-- A call: the named statement, then the return. -/
  | call {Λ ks st k} : k ∈ L.keys → (L.defs k).clean = true → frames ks < STACKSZ →
      SAct L pr Λ (.call k :: ks, st) (L.defs k :: .ret :: ks, st) Λ
  /-- The return. -/
  | ret {Λ ks st} : SAct L pr Λ (.ret :: ks, st) (ks, st) Λ
  /-- A scope begins: `x` holds `e`, and gets its value back at the end. -/
  | scope {Λ ks st x e p} : x < L.n → L.arrayAt x = none → Fits L st.mem e → frames ks < STACKSZ →
      SAct L pr Λ (.scope x e p :: ks, st)
        (p :: .restore x (st.mem x) :: ks,
          { st with mem := Function.update st.mem x (e.eval st.mem) }) Λ
  /-- A scope ends. -/
  | restore {Λ ks st x v} : SAct L pr Λ (.restore x v :: ks, st)
      (ks, { st with mem := Function.update st.mem x v }) Λ
  /-- `A i:= e`. -/
  | store {Λ ks st x i e} : Fits L st.mem (.index (.var x) i) → Fits L st.mem e →
      SAct L pr Λ (.store x i e :: ks, st)
        (ks, { st with mem := (Function.update st.mem x
          ((st.mem x).update [(i.eval st.mem).toInt] (e.eval st.mem))) }) Λ

/-- **A step of the network, in 32 bits**: one process acts. -/
inductive SStep (L : Layout) (net : SNet) : SCfg → SCfg → Prop
  /-- Process `i` acts. -/
  | mk {c : SCfg} {i : ℕ} {pr : SProc} {a b : List Stmt × PSt ℕ Value} {Λ : Scripts Value} :
      net.procs[i]? = some pr → c.ps[i]? = some a → SAct L pr c.L a b Λ →
      SStep L net c ⟨c.ps.set i b, Λ⟩

/-- An action in 32 bits, other than a call, is an action of the network machine. -/
theorem SAct.act {L : Layout} {net : SNet} {i : ℕ} {pr : SProc} (hpr : net.procs[i]? = some pr)
    {Λ Λ' : Scripts Value} {a b : List Stmt × PSt ℕ Value} (h : SAct L pr Λ a b Λ')
    (hnc : ∀ k ks, a.1 ≠ .call k :: ks) {Q : ℕ∞ → Prop} :
    Act net.toNet i Q Λ ⟨a.1.map Stmt.toNP, a.2⟩ ⟨b.1.map Stmt.toNP, b.2⟩ Λ' := by
  have hpr' : net.toNet.procs[i]? = some ⟨pr.body.toNP, pr.outs, pr.ins⟩ := by
    simp [SNet.toNet, hpr]
  cases h with
  | ok => exact .loc (.act (u := ⟨_, _⟩) trivial .ok)
  | assign => exact .loc (.act (p := Lang.assign _ _) trivial .assign)
  | tick => exact .loc (.act (p := .tick) trivial .tick)
  | seq => exact .loc .seq
  | condT _ hc => exact .loc (.condT (by simp [Exp.test, hc]))
  | condF _ hc => exact .loc (.condF (by simp [Exp.test, hc]))
  | loopT _ hc => exact .loc (.loopT (by simp [Exp.test, hc]))
  | loopF _ hc => exact .loc (.loopF (by simp [Exp.test, hc]))
  | send hch _ => exact .send hpr' hch rfl
  | recv hch hm _ _ => exact .recv hpr' hch hm
  | call => exact (hnc _ _ rfl).elim
  | ret => exact .loc (.act (u := ⟨_, _⟩) trivial .ok)
  | scope => exact .loc .scope
  | restore => exact .loc .restore
  | store => exact .loc (.act (p := assignIdx _ [_] _) trivial .assign)

/-- A step in 32 bits is one or two steps of the network machine: a call is the
call and then the start of the named statement and its return. -/
theorem SStep.msteps {L : Layout} {net : SNet} (hdefs : L.defs = net.defs) {c c' : SCfg}
    (h : SStep L net c c') : TransGen (MStep net.toNet) c.toM c'.toM := by
  obtain ⟨hpr, ha, hact⟩ := h
  rename_i i pr a b Λ
  have hlt : i < c.ps.length := (List.getElem?_eq_some_iff.mp ha).1
  have hps : c.toM.ps[i]? = some ⟨a.1.map Stmt.toNP, a.2⟩ := by simp [SCfg.toM, ha]
  have one : (∀ k ks, a.1 ≠ .call k :: ks) →
      TransGen (MStep net.toNet) c.toM (SCfg.toM ⟨c.ps.set i b, Λ⟩) := fun hc => by
    have := MStep.mk (net := net.toNet) (c := c.toM) hps (hact.act hpr hc)
    exact .single (by simpa [SCfg.toM, List.map_set] using this)
  cases hact with
  | @call ks st k _ _ _ =>
    refine .tail (.single (MStep.mk (net := net.toNet) (c := c.toM) hps (.loc .call))) ?_
    have h₂ := MStep.mk (net := net.toNet)
      (c := ⟨c.toM.ps.set i ⟨net.toNet.defs k :: ks.map Stmt.toNP, st⟩, c.toM.L⟩) (i := i)
      (a := ⟨.seq (net.defs k).toNP (.act .ok) :: ks.map Stmt.toNP, st⟩)
      (by simp [SCfg.toM, hlt, SNet.toNet]) (.loc .seq)
    simpa [SCfg.toM, List.map_set, SNet.toNet, hdefs, Stmt.toNP] using h₂
  | ok => exact one (by simp)
  | assign => exact one (by simp)
  | tick => exact one (by simp)
  | seq => exact one (by simp)
  | condT => exact one (by simp)
  | condF => exact one (by simp)
  | loopT => exact one (by simp)
  | loopF => exact one (by simp)
  | send => exact one (by simp)
  | recv => exact one (by simp)
  | ret => exact one (by simp)
  | scope => exact one (by simp)
  | restore => exact one (by simp)
  | store => exact one (by simp)

/-- A run in 32 bits is a run of the network machine. -/
theorem reach_of_sSteps {L : Layout} {net : SNet} (hdefs : L.defs = net.defs) {c c' : SCfg}
    (h : ReflTransGen (SStep L net) c c') : ReflTransGen (MStep net.toNet) c.toM c'.toM := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (hs.msteps hdefs).to_reflTransGen

/-! ### Code that continues -/

/-- What is left for a process to do, laid out in memory `m` from `a`, with the
control stack `cs`: the statements one after another, perhaps reached through
jumps, ending at `hl`; a return goes where the control stack says, and the end
of a scope gives a variable back the value the control stack keeps. -/
inductive Cont (L : Layout) (m : ℕ → UInt8) : List UInt32 → List Stmt → ℕ → Prop
  /-- Nothing is left: `hl`. -/
  | nil {a : ℕ} : 256 ≤ a → a < L.base → m a = 0xFF → Cont L m [] [] a
  /-- A statement's code, and what follows it. -/
  | cons {cs : List UInt32} {p : Stmt} {ks : List Stmt} {a : ℕ} : 256 ≤ a → a + slen L p ≤ L.base →
      sdepth p ≤ STACKSZ → p.clean = true → CodeAt m a (scode L a p) →
      Cont L m cs ks (a + slen L p) → Cont L m cs (p :: ks) a
  /-- A jump to it. -/
  | jump {cs : List UInt32} {ks : List Stmt} {a b : ℕ} : 256 ≤ a → a + 5 ≤ L.base →
      CodeAt m a (jmTo b) → Cont L m cs ks b → Cont L m cs ks a
  /-- A return, `rt`, to `b`. -/
  | ret {cs : List UInt32} {ks : List Stmt} {a b : ℕ} : 256 ≤ a → a < L.base → m a = 0x9E →
      Cont L m cs ks b → Cont L m (cs ++ [UInt32.ofNat b]) (.ret :: ks) a
  /-- The end of a scope, `cd li x wi`, giving `x` back `v`. -/
  | restore {cs : List UInt32} {ks : List Stmt} {a x : ℕ} {v : Value} : 256 ≤ a → a + 7 ≤ L.base →
      x < L.n → L.arrayAt x = none →
      CodeAt m a ([0x91] ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])) →
      Cont L m cs ks (a + 7) → Cont L m (cs ++ [enc v]) (.restore x v :: ks) a

/-- What is left, without a jump first. -/
inductive Direct (L : Layout) (m : ℕ → UInt8) : List UInt32 → List Stmt → ℕ → Prop
  /-- Nothing is left: `hl`. -/
  | nil {a : ℕ} : 256 ≤ a → a < L.base → m a = 0xFF → Direct L m [] [] a
  /-- A statement's code, and what follows it. -/
  | cons {cs : List UInt32} {p : Stmt} {ks : List Stmt} {a : ℕ} : 256 ≤ a → a + slen L p ≤ L.base →
      sdepth p ≤ STACKSZ → p.clean = true → CodeAt m a (scode L a p) →
      Cont L m cs ks (a + slen L p) → Direct L m cs (p :: ks) a
  /-- A return. -/
  | ret {cs : List UInt32} {ks : List Stmt} {a b : ℕ} : 256 ≤ a → a < L.base → m a = 0x9E →
      Cont L m cs ks b → Direct L m (cs ++ [UInt32.ofNat b]) (.ret :: ks) a
  /-- The end of a scope. -/
  | restore {cs : List UInt32} {ks : List Stmt} {a x : ℕ} {v : Value} : 256 ≤ a → a + 7 ≤ L.base →
      x < L.n → L.arrayAt x = none →
      CodeAt m a ([0x91] ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])) →
      Cont L m cs ks (a + 7) → Direct L m (cs ++ [enc v]) (.restore x v :: ks) a

theorem Cont.bounds {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {ks : List Stmt} {a : ℕ}
    (h : Cont L m cs ks a) : 256 ≤ a ∧ a ≤ L.base := by
  cases h with
  | nil h₁ h₂ _ => exact ⟨h₁, by omega⟩
  | cons h₁ h₂ _ _ _ _ => exact ⟨h₁, by omega⟩
  | jump h₁ h₂ _ _ => exact ⟨h₁, by omega⟩
  | ret h₁ h₂ _ _ => exact ⟨h₁, by omega⟩
  | restore h₁ h₂ _ _ _ _ => exact ⟨h₁, by omega⟩

theorem Direct.cont {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {ks : List Stmt} {a : ℕ}
    (h : Direct L m cs ks a) : Cont L m cs ks a := by
  cases h with
  | nil h₁ h₂ h₃ => exact .nil h₁ h₂ h₃
  | cons h₁ h₂ h₃ h₄ h₅ h₆ => exact .cons h₁ h₂ h₃ h₄ h₅ h₆
  | ret h₁ h₂ h₃ h₄ => exact .ret h₁ h₂ h₃ h₄
  | restore h₁ h₂ h₃ h₃' h₄ h₅ => exact .restore h₁ h₂ h₃ h₃' h₄ h₅

/-- What is left survives writes above the code. -/
theorem Cont.mono {L : Layout} {m m' : ℕ → UInt8} (hm : ∀ i < L.base, m' i = m i)
    {cs : List UInt32} {ks : List Stmt} {a : ℕ} (h : Cont L m cs ks a) : Cont L m' cs ks a := by
  induction h with
  | nil h₁ h₂ h₃ => exact .nil h₁ h₂ (by rw [hm _ h₂]; exact h₃)
  | cons h₁ h₂ h₃ h₄ h₅ _ ih =>
    exact .cons h₁ h₂ h₃ h₄ (h₅.mono hm (by rw [length_scode]; exact h₂)) ih
  | jump h₁ h₂ h₃ _ ih => exact .jump h₁ h₂ (h₃.mono hm (by simpa using h₂)) ih
  | ret h₁ h₂ h₃ _ ih => exact .ret h₁ h₂ (by rw [hm _ h₂]; exact h₃) ih
  | restore h₁ h₂ h₃ h₃' h₄ _ ih => exact .restore h₁ h₂ h₃ h₃' (h₄.mono hm (by simpa using h₂)) ih

/-- The control stack holds an entry for each return and end of scope. -/
theorem Cont.frames {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {ks : List Stmt} {a : ℕ}
    (h : Cont L m cs ks a) : cs.length = frames ks := by
  induction h with
  | nil => rfl
  | cons _ _ _ h₄ _ _ ih => simp [CompileNet.frames, h₄] at ih ⊢; exact ih
  | jump _ _ _ _ ih => exact ih
  | ret _ _ _ _ ih => simp [CompileNet.frames, Stmt.clean] at ih ⊢; exact ih
  | restore _ _ _ _ _ _ ih => simp [CompileNet.frames, Stmt.clean] at ih ⊢; exact ih

theorem frames_cons_clean {p : Stmt} {ks : List Stmt} (h : p.clean = true) :
    frames (p :: ks) = frames ks := by
  simp [CompileNet.frames, h]

theorem Cont.cast {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {ks : List Stmt} {a b : ℕ}
    (h : Cont L m cs ks a) (e : a = b) : Cont L m cs ks b := e ▸ h

/-! ### The swarm, machine by machine -/

theorem ioCmd_of_notIo {s : State} (h : NotIo s) : ioCmd s = none := by
  unfold ioCmd; rw [ite_eq_right h]

/-- **A machine's own run is a run of the swarm**: the other machines and the
channels wait. -/
theorem swarm_lift {w : Swarm} {i : ℕ} {s s' : State} (hi : w.ms[i]? = some s)
    (h : Steps s s') : Swarm.Steps w { w with ms := w.ms.set i s' } := by
  have hlt : i < w.ms.length := (List.getElem?_eq_some_iff.mp hi).1
  induction h with
  | refl =>
    have : w.ms.set i s = w.ms := by
      apply List.ext_getElem?; intro j
      by_cases hij : i = j
      · subst hij; rw [List.getElem?_set_self hlt, hi]
      · rw [List.getElem?_set_ne hij]
    rw [this]; exact .refl
  | @tail s₁ s₂ _ hs ih =>
    obtain ⟨hr, hn, rfl⟩ := hs
    refine ih.tail ⟨i, ?_⟩
    have h₁ : ({ w with ms := w.ms.set i s₁ } : Swarm).ms[i]? = some s₁ := by
      simp [List.getElem?_set_self hlt]
    rw [Swarm.stepAt_other h₁ ((running_iff _).mpr hr) (by rw [ioCmd_of_notIo hn]; simp)
      (by rw [ioCmd_of_notIo hn]; simp) (by rw [ioCmd_of_notIo hn]; simp)]
    simp

/-- Follow the jumps before what is left. -/
theorem follow (L : Layout) (hL : L.Ok) {m : ℕ → UInt8} {cs : List UInt32} {ks : List Stmt} {a : ℕ}
    (hc : Cont L m cs ks a) : ∀ s, high s = m → cstack s = cs → WF s → Running s → getIP s = a →
      ∃ s', Steps s s' ∧ Same s s' ∧ WF s' ∧ dstack s' = dstack s ∧ Direct L m cs ks (getIP s') := by
  induction hc with
  | nil h₁ h₂ h₃ =>
    intro s hm hcs hw hr hip
    exact ⟨s, .refl, Same.refl s, hw, rfl, hip ▸ .nil h₁ h₂ h₃⟩
  | cons h₁ h₂ h₃ h₄ h₅ h₆ =>
    intro s hm hcs hw hr hip
    exact ⟨s, .refl, Same.refl s, hw, rfl, hip ▸ .cons h₁ h₂ h₃ h₄ h₅ h₆⟩
  | ret h₁ h₂ h₃ h₄ =>
    intro s hm hcs hw hr hip
    exact ⟨s, .refl, Same.refl s, hw, rfl, hip ▸ .ret h₁ h₂ h₃ h₄⟩
  | restore h₁ h₂ h₃ h₃' h₄ h₅ =>
    intro s hm hcs hw hr hip
    exact ⟨s, .refl, Same.refl s, hw, rfl, hip ▸ .restore h₁ h₂ h₃ h₃' h₄ h₅⟩
  | @jump cs ks a b h₁ h₂ h₃ hcb ih =>
    intro s hm hcs hw hr hip
    have hb := hcb.bounds
    have hJ : CodeAt (high s) (getIP s) (jmTo b) := by rw [hm, hip]; exact h₃
    obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_jm' hL hw (by omega) (by omega) hJ hb.1 hb.2
    obtain ⟨s', r', sm', w', d', hd'⟩ := ih (step s) (by rw [sm₁.high, hm]) (by rw [sm₁.cs, hcs]) w₁
      (sm₁.running hr) i₁
    exact ⟨s', (Steps.one hr (notIo_jm (by omega) hJ)).trans r', sm₁.trans sm', w',
      by rw [d', d₁], hd'⟩

/-! ### Time -/

/-- A time as the clock holds it. -/
def encT (t : ℕ∞) : UInt32 := UInt32.ofNat t.toNat

/-- A script as the swarm holds it. -/
def encS (l : List (Msg Value)) : List B4.Msg := l.map fun m => (enc m.1, encT m.2)

theorem TFits.ne_top {t : ℕ∞} (h : TFits t) : t ≠ ⊤ := ne_top_of_lt h

theorem TFits.toNat_lt {t : ℕ∞} (h : TFits t) : t.toNat < 2 ^ 31 := by
  have := h.ne_top
  lift t to ℕ using this
  simpa [TFits] using h

theorem TFits.mono {t u : ℕ∞} (h : TFits u) (htu : t ≤ u) : TFits t := lt_of_le_of_lt htu h

theorem encT_succ {t : ℕ∞} (h : TFits (t + 1)) :
    fromInt32 (toInt32 (encT t) + toInt32 1) = encT (t + 1) := by
  have h₁ := h.toNat_lt
  have ht : t ≠ ⊤ := fun e => h.ne_top (by simp [e])
  lift t to ℕ using ht
  simp only [encT, ENat.toNat_natCast] at h₁ ⊢
  rw [show ((t : ℕ∞) + 1).toNat = t + 1 by norm_cast] at h₁ ⊢
  have h1 : (1 : UInt32).toNat = 1 := rfl
  unfold toInt32 fromInt32
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', h1]
  split_ifs <;> omega

theorem high_ip {s : State} {op : UInt8} {a : ℕ} {bs : List UInt8} (hc : CodeAt (high s) a bs)
    (j : ℕ) (hj : j < bs.length) (hb : bs.getD j 0 = op) : high s (a + j) = op := by
  rw [hc j hj, hb]

/-- **`tick`**: read the clock, add one, write it back. -/
theorem tick_runs {s : State} {t : ℕ∞} (hw : WF s) (hr : Running s) (hlo : 256 ≤ getIP s)
    (hhi : getIP s + 8 + 8 < MAXBYTE) (hc : CodeAt (high s) (getIP s) (scode L (getIP s) .tick))
    (hd : dstack s = []) (hclk : getClk s = encT t) (hfit : TFits (t + 1)) :
    ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧ getIP s' = getIP s + 8 ∧ dstack s' = [] ∧
      getClk s' = encT (t + 1) ∧ high s' = high s ∧ cstack s' = cstack s ∧ s'.ob = s.ob := by
  simp only [scode] at hc
  rw [CodeAt.append, CodeAt.append] at hc
  obtain ⟨⟨hA, hB⟩, hC⟩ := hc
  rw [show (0x97 : UInt8) :: le4 1 = [0x97] ++ le4 1 from rfl, CodeAt.append] at hB
  obtain ⟨hB₁, hB₂⟩ := hB
  have hop₀ : high s (getIP s) = 0x34 := by simpa using hA 0 (by simp)
  obtain ⟨w₁, i₁, d₁, sm₁⟩ := step_rdT s [] hw hlo (by unfold MAXBYTE at hhi; omega) hop₀ hd
    (by simp [STACKSZ])
  set s₁ := step s with hs₁
  have hop₁ : high s₁ (getIP s₁) = 0x97 := by
    rw [sm₁.high, i₁]; simpa using hB₁ 0 (by simp)
  have hc₁ : CodeAt (high s₁) (getIP s₁ + 1) (le4 1) := by
    rw [sm₁.high, i₁]; simpa using hB₂
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_li s₁ [getClk s] w₁ (by rw [i₁]; omega)
    (by rw [i₁]; omega) hop₁ (by simpa using d₁) (by simp [STACKSZ])
  rw [word_le4 hc₁] at d₂
  set s₂ := step s₁ with hs₂
  have hop₂ : high s₂ (getIP s₂) = 0x80 := by
    rw [sm₂.high, sm₁.high, i₂, i₁]; have := hC 0 (by simp); simp at this
    rw [show getIP s + 1 + 5 = getIP s + 1 + (1 + 4) + 0 by omega]; simpa using this
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := step_binop' s₂ 0x80 (fun x y => fromInt32 (toInt32 x + toInt32 y))
    [] (getClk s) 1 w₂ (by rw [i₂, i₁]; omega) (by rw [i₂, i₁]; unfold MAXBYTE at hhi; omega)
    hop₂ (by simpa using d₂) runOp_ad
  set s₃ := step s₂ with hs₃
  have hop₃ : high s₃ (getIP s₃) = 0x54 := by
    rw [sm₃.high, sm₂.high, sm₁.high, i₃, i₂, i₁]; have := hC 1 (by simp); simp at this
    rw [show getIP s + 1 + 5 + 1 = getIP s + 1 + (1 + 4) + 1 by omega]; simpa using this
  obtain ⟨w₄, i₄, d₄, k₄, c₄, st₄, db₄, h₄, o₄⟩ := step_wrT s₃ [] _ w₃
    (by rw [i₃, i₂, i₁]; omega) (by rw [i₃, i₂, i₁]; unfold MAXBYTE at hhi; omega) hop₃
    (by simpa using d₃)
  have r₁ := sm₁.running hr
  have r₂ := sm₂.running r₁
  have r₃ := sm₃.running r₂
  refine ⟨step s₃, (((Steps.one hr (notIo_of_hop hlo hop₀)).tail
    ⟨r₁, notIo_of_hop (by rw [i₁]; omega) hop₁, rfl⟩).tail
    ⟨r₂, notIo_of_hop (by rw [i₂, i₁]; omega) hop₂, rfl⟩).tail
    ⟨r₃, notIo_of_hop (by rw [i₃, i₂, i₁]; omega) hop₃, rfl⟩, w₄,
    ⟨st₄.trans r₃.1, db₄.trans r₃.2⟩, by rw [i₄, i₃, i₂, i₁], d₄, ?_,
    by rw [h₄, sm₃.high, sm₂.high, sm₁.high], by rw [c₄, sm₃.cs, sm₂.cs, sm₁.cs],
    by rw [o₄, sm₃.ob, sm₂.ob, sm₁.ob]⟩
  rw [k₄, hclk]
  exact encT_succ hfit

/-! ### `io` in the swarm -/

theorem ioCmd_eq {s : State} {xs : List UInt32} {v : UInt32} (hlo : 256 ≤ getIP s)
    (hop : high s (getIP s) = 0xFD) (hd : dstack s = xs ++ [v]) : ioCmd s = some v := by
  unfold ioCmd
  rw [get!_ip s hlo, hop, ite_eq_left rfl, hd]
  simp

theorem Swarm.send_eq (w : Swarm) (i : ℕ) (s : State) :
    w.send i s = ⟨w.ms.set i (setIP (dpop (dpop (dpop s).2).2).2
        (getIP (dpop (dpop (dpop s).2).2).2 + 1)),
      fun c => if c = (dpop (dpop s).2).1.toNat then
        w.chans c ++ [((dpop (dpop (dpop s).2).2).1, getClk (dpop (dpop (dpop s).2).2).2)]
        else w.chans c, w.rd, w.owner⟩ := rfl

/-- **Send** in the swarm: with the value, the channel and `'s'` on the stack at
an `io`, the message goes on the channel's script, stamped with the clock. -/
theorem swarm_send {w : Swarm} {i : ℕ} {s : State} {v : UInt32} {ch : ℕ}
    (hi : w.ms[i]? = some s) (hw : WF s) (hr : Running s) (hlo : 256 ≤ getIP s)
    (hhi : getIP s + 1 < MAXBYTE) (hop : high s (getIP s) = 0xFD)
    (hd : dstack s = [v, UInt32.ofNat ch, SEND]) (hch : ch < 2 ^ 32) (ho : w.owner ch = some i) :
    ∃ s', w.stepAt i = some ⟨w.ms.set i s',
        fun c => if c = ch then w.chans c ++ [(v, getClk s)] else w.chans c, w.rd, w.owner⟩ ∧
      WF s' ∧ getIP s' = getIP s + 1 ∧ dstack s' = [] ∧ Same s s' := by
  have hio : ioCmd s = some SEND := ioCmd_eq (xs := [v, UInt32.ofNat ch]) hlo hop (by simpa using hd)
  have hsc : sendChan s = ch := by
    obtain ⟨_, w₁, -, d₁, -⟩ := dpop_same s [v, UInt32.ofNat ch] SEND hw (by simpa using hd)
    obtain ⟨e₂, -, -, -, -⟩ := dpop_same _ [v] (UInt32.ofNat ch) w₁ (by simpa using d₁)
    unfold sendChan; rw [e₂, UInt32.toNat_ofNat']; omega
  rw [Swarm.stepAt_send hi ((running_iff _).mpr hr) hio (by rw [hsc]; exact ho)]
  obtain ⟨e₁, w₁, i₁, d₁, sm₁⟩ := dpop_same s [v, UInt32.ofNat ch] SEND hw (by simpa using hd)
  obtain ⟨e₂, w₂, i₂, d₂, sm₂⟩ := dpop_same _ [v] (UInt32.ofNat ch) w₁ (by simpa using d₁)
  obtain ⟨e₃, w₃, i₃, d₃, sm₃⟩ := dpop_same _ [] v w₂ (by simpa using d₂)
  obtain ⟨w₄, i₄, d₄, sm₄⟩ := setIP_same (dpop (dpop (dpop s).2).2).2
    (getIP (dpop (dpop (dpop s).2).2).2 + 1) w₃ (by rw [i₃, i₂, i₁]; unfold MAXBYTE at hhi; omega)
  refine ⟨_, ?_, w₄, by rw [i₄, i₃, i₂, i₁], d₄.trans d₃, sm₁.trans (sm₂.trans (sm₃.trans sm₄))⟩
  have htn : (UInt32.ofNat ch).toNat = ch := by rw [UInt32.toNat_ofNat']; omega
  rw [Swarm.send_eq, e₂, e₃, htn, (sm₁.trans (sm₂.trans sm₃)).clk]

/-- The machine after it receives `(v, τ)`. -/
def recvState (s : State) (v τ : UInt32) : State :=
  setIP (setClk (dpush (dpop (dpop s).2).2 v) (later (getClk (dpush (dpop (dpop s).2).2 v)) (τ + 1)))
    (getIP (setClk (dpush (dpop (dpop s).2).2 v)
      (later (getClk (dpush (dpop (dpop s).2).2 v)) (τ + 1))) + 1)

theorem recvState_view {s : State} {ch : UInt32} {v τ : UInt32} (hw : WF s)
    (hhi : getIP s + 1 < MAXBYTE) (hd : dstack s = [ch, RECV]) :
    WF (recvState s v τ) ∧ getIP (recvState s v τ) = getIP s + 1 ∧ dstack (recvState s v τ) = [v] ∧
      getClk (recvState s v τ) = later (getClk s) (τ + 1) ∧ high (recvState s v τ) = high s ∧
      cstack (recvState s v τ) = cstack s ∧ getRST (recvState s v τ) = getRST s ∧
      getRDB (recvState s v τ) = getRDB s ∧ (recvState s v τ).ob = s.ob := by
  obtain ⟨e₁, w₁, i₁, d₁, sm₁⟩ := dpop_same s [ch] RECV hw (by simpa using hd)
  obtain ⟨e₂, w₂, i₂, d₂, sm₂⟩ := dpop_same _ [] ch w₁ (by simpa using d₁)
  generalize hs₂ : (dpop (dpop s).2).2 = s₂ at w₂ i₂ d₂ sm₂
  have hl : getDSH s₂ < STACKSZ := by
    have := dstack_length _ w₂; rw [d₂] at this; simp at this; rw [← this]; decide
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := dpush_same s₂ v w₂ hl
  generalize hs₃ : dpush s₂ v = s₃ at w₃ i₃ d₃ sm₃
  have w₄ : WF (setClk s₃ (later (getClk s₃) (τ + 1))) :=
    ⟨by simpa using w₃.mem, w₃.ds, w₃.cs, by rw [getDSH_setClk]; exact w₃.dsh,
      by rw [getCSH_setClk]; exact w₃.csh⟩
  obtain ⟨w₅, i₅, d₅, sm₅⟩ := setIP_same (setClk s₃ (later (getClk s₃) (τ + 1)))
    (getIP (setClk s₃ (later (getClk s₃) (τ + 1))) + 1) w₄
    (by rw [getIP_setClk, i₃, i₂, i₁]; unfold MAXBYTE at hhi; omega)
  have hsm := sm₁.trans (sm₂.trans sm₃)
  have hr : recvState s v τ = setIP (setClk s₃ (later (getClk s₃) (τ + 1)))
      (getIP (setClk s₃ (later (getClk s₃) (τ + 1))) + 1) := by
    rw [← hs₃, ← hs₂]; rfl
  rw [hr]
  refine ⟨w₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [i₅, getIP_setClk, i₃, i₂, i₁]
  · rw [d₅, dstack, getDSH_setClk]; exact d₃.trans (by rw [d₂]; rfl)
  · rw [sm₅.clk, getClk_setClk _ _ w₃.mem, hsm.clk]
  · rw [sm₅.high, high_setClk]; exact hsm.high
  · rw [sm₅.cs, cstack, getCSH_setClk]; exact hsm.cs
  · rw [sm₅.st, getRST_setClk]; exact hsm.st
  · rw [sm₅.db, getRDB_setClk]; exact hsm.db
  · rw [sm₅.ob]; exact hsm.ob

/-- **Receive** in the swarm: with the channel and `'r'` on the stack at an
`io`, and the message at the read cursor there, its value is pushed, the clock
moves to one past its time if that is later, and the cursor moves on. -/
theorem swarm_recv {w : Swarm} {i : ℕ} {s : State} {ch : ℕ} {v τ : UInt32}
    (hi : w.ms[i]? = some s) (hw : WF s) (hr : Running s) (hlo : 256 ≤ getIP s)
    (hop : high s (getIP s) = 0xFD) (hd : dstack s = [UInt32.ofNat ch, RECV]) (hch : ch < 2 ^ 32)
    (hm : (w.chans ch)[(w.rd.getD i fun _ => 0) ch]? = some (v, τ)) :
    w.stepAt i = some ⟨w.ms.set i (recvState s v τ), w.chans,
        w.rd.set i (fun c => if c = ch then (w.rd.getD i fun _ => 0) ch + 1
          else (w.rd.getD i fun _ => 0) c), w.owner⟩ := by
  have hio : ioCmd s = some RECV := ioCmd_eq (xs := [UInt32.ofNat ch]) hlo hop (by simpa using hd)
  rw [Swarm.stepAt_recv hi ((running_iff _).mpr hr) hio]
  have htn : (UInt32.ofNat ch).toNat = ch := by rw [UInt32.toNat_ofNat']; omega
  obtain ⟨e₁, w₁, -, d₁, -⟩ := dpop_same s [UInt32.ofNat ch] RECV hw (by simpa using hd)
  obtain ⟨e₂, -, -, -, -⟩ := dpop_same _ [] (UInt32.ofNat ch) w₁ (by simpa using d₁)
  unfold Swarm.recv
  simp only [e₂, htn, hm]
  rfl

/-! ### One process, one machine -/

/-- **A process and its machine agree**: the machine is running with an empty
stack, what is left of the process is laid out from the pointer, the cells hold
its variables, the clock its time, and the swarm's cursors its cursors. -/
structure PRel (L : Layout) (ks : List Stmt) (st : PSt ℕ Value) (s : State) (r : ℕ → ℕ) :
    Prop where
  /-- The machine is well formed. -/
  wf : WF s
  /-- It is running. -/
  run : Running s
  /-- Its data stack is empty. -/
  stack : dstack s = []
  /-- What is left is laid out from the pointer, with the control stack. -/
  cont : Cont L (high s) (cstack s) ks (getIP s)
  /-- The cells hold the variables. -/
  vars : VarsOk L (high s) st.mem
  /-- The clock holds the time. -/
  clk : getClk s = encT st.t
  /-- The time fits. -/
  tfit : TFits st.t
  /-- The cursors are the process's. -/
  rd : ∀ c, r c = st.r c
  /-- The named statements are laid out. -/
  image : L.Image (high s)

theorem Direct.cons_inv {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {p : Stmt}
    {ks : List Stmt} {a : ℕ} (h : Direct L m cs (p :: ks) a) (hr : p ≠ .ret)
    (hs : ∀ x v, p ≠ .restore x v) : 256 ≤ a ∧ a + slen L p ≤ L.base ∧ sdepth p ≤ STACKSZ ∧
      CodeAt m a (scode L a p) ∧ Cont L m cs ks (a + slen L p) ∧ p.clean = true := by
  cases h with
  | cons h₁ h₂ h₃ h₄ h₅ h₆ => exact ⟨h₁, h₂, h₃, h₅, h₆, h₄⟩
  | ret => exact (hr rfl).elim
  | restore => exact (hs _ _ rfl).elim

theorem Direct.nil_inv {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {a : ℕ}
    (h : Direct L m cs [] a) : 256 ≤ a ∧ a < L.base ∧ m a = 0xFF := by
  cases h with
  | nil h₁ h₂ h₃ => exact ⟨h₁, h₂, h₃⟩

theorem Direct.ret_inv {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {ks : List Stmt} {a : ℕ}
    (h : Direct L m cs (.ret :: ks) a) : ∃ cs' b, cs = cs' ++ [UInt32.ofNat b] ∧ 256 ≤ a ∧
      a < L.base ∧ m a = 0x9E ∧ Cont L m cs' ks b := by
  cases h with
  | cons _ _ _ h₄ => simp [Stmt.clean] at h₄
  | ret h₁ h₂ h₃ h₄ => exact ⟨_, _, rfl, h₁, h₂, h₃, h₄⟩

theorem Direct.restore_inv {L : Layout} {m : ℕ → UInt8} {cs : List UInt32} {ks : List Stmt} {a x : ℕ}
    {v : Value} (h : Direct L m cs (.restore x v :: ks) a) : ∃ cs', cs = cs' ++ [enc v] ∧ 256 ≤ a ∧
      a + 7 ≤ L.base ∧ x < L.n ∧ L.arrayAt x = none ∧
      CodeAt m a ([0x91] ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])) ∧
      Cont L m cs' ks (a + 7) := by
  cases h with
  | cons _ _ _ h₄ => simp [Stmt.clean] at h₄
  | restore h₁ h₂ h₃ h₃' h₄ h₅ => exact ⟨_, rfl, h₁, h₂, h₃, h₃', h₄, h₅⟩

/-- **The machine does a process's step** that is not communication. -/
theorem machine_sim (L : Layout) (hL : L.Ok) {pr : SProc} {Λ Λ' : Scripts Value}
    {a b : List Stmt × PSt ℕ Value} (h : SAct L pr Λ a b Λ')
    (hsend : ∀ ch e ks, a.1 ≠ .send ch e :: ks) (hrecv : ∀ ch x ks, a.1 ≠ .recv ch x :: ks)
    {s : State} {r : ℕ → ℕ} (hp : PRel L a.1 a.2 s r)
    (hd : Direct L (high s) (cstack s) a.1 (getIP s)) :
    ∃ s', Steps s s' ∧ PRel L b.1 b.2 s' r ∧ ∀ i, L.top ≤ i → high s' i = high s i := by
  have hb := hL.2
  cases h with
  | @ok ks st =>
    obtain ⟨-, -, -, -, hk, -⟩ := hd.cons_inv (by simp) (by simp)
    exact ⟨s, .refl, ⟨hp.wf, hp.run, hp.stack, by simpa [slen] using hk, hp.vars, hp.clk, hp.tfit,
      hp.rd, hp.image⟩, fun _ _ => rfl⟩
  | @assign ks st x e hx ha hf =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd.cons_inv (by simp) (by simp)
    obtain ⟨s', r', w', run', i', d', v', k'⟩ := assign_runs L hL hx ha hf s (getIP s)
      ⟨hp.wf, hp.run, rfl, h₁, h₂, h₄, hp.vars, hp.stack, h₃, rfl, hp.image⟩
    refine ⟨s', r', ⟨w', run', d', ?_, v', by rw [k'.clk]; exact hp.clk, hp.tfit, hp.rd,
      hp.image.mono k'.low⟩, k'.top⟩
    rw [i', k'.cs]; exact hk.mono k'.low
  | @store ks st x i e hfi hf =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd.cons_inv (by simp) (by simp)
    obtain ⟨s', r', w', run', i', d', v', k'⟩ := store_runs L hL hfi hf s (getIP s)
      ⟨hp.wf, hp.run, rfl, h₁, h₂, h₄, hp.vars, hp.stack, h₃, rfl, hp.image⟩
    refine ⟨s', r', ⟨w', run', d', ?_, v', by rw [k'.clk]; exact hp.clk, hp.tfit, hp.rd,
      hp.image.mono k'.low⟩, k'.top⟩
    rw [i', k'.cs]; exact hk.mono k'.low
  | @tick ks st hfit =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd.cons_inv (by simp) (by simp)
    obtain ⟨s', r', w', run', i', d', c', hi', hcs', -⟩ := tick_runs (L := L) hp.wf hp.run h₁
      (by simp [slen] at h₂; omega) h₄ hp.stack hp.clk hfit
    refine ⟨s', r', ⟨w', run', d', by rw [hi', i', hcs']; simpa [slen] using hk,
      by rw [hi']; exact hp.vars, c', hfit, hp.rd, by rw [hi']; exact hp.image⟩, fun i _ => by rw [hi']⟩
  | @seq ks st p q =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, hcl⟩ := hd.cons_inv (by simp) (by simp)
    simp only [Stmt.clean, Bool.and_eq_true] at hcl
    simp only [scode] at h₄
    rw [CodeAt.append, length_scode] at h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    exact ⟨s, .refl, ⟨hp.wf, hp.run, hp.stack, .cons h₁ (by omega) (by omega) hcl.1 h₄.1
      (.cons (by omega) (by omega) (by omega) hcl.2 h₄.2 (by rwa [Nat.add_assoc])), hp.vars, hp.clk,
      hp.tfit, hp.rd, hp.image⟩, fun _ _ => rfl⟩
  | @condT ks st c p q hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, hcl⟩ := hd.cons_inv (by simp) (by simp)
    simp only [Stmt.clean, Bool.and_eq_true] at hcl
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    have hcode := h₄; simp only [scode] at hcode
    obtain ⟨s', r', w', run', i', d', sm'⟩ := run_cond (b := true) hL hf hc hp.wf hp.run rfl h₁
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) hp.vars
      hp.stack (by omega)
    simp only [ite_true] at i'
    refine ⟨s', r', ⟨w', run', d', ?_, by rw [sm'.high]; exact hp.vars,
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd, by rw [sm'.high]; exact hp.image⟩, fun i _ => by rw [sm'.high]⟩
    rw [i', sm'.high, sm'.cs]
    refine .cons (by omega) (by omega) (by omega) hcl.1 hP (.jump (by omega) (by omega) hJ' ?_)
    convert hk using 1; omega
  | @condF ks st c p q hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, hcl⟩ := hd.cons_inv (by simp) (by simp)
    simp only [Stmt.clean, Bool.and_eq_true] at hcl
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    have hcode := h₄; simp only [scode] at hcode
    obtain ⟨s', r', w', run', i', d', sm'⟩ := run_cond (b := false) hL hf hc hp.wf hp.run rfl h₁
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) hp.vars
      hp.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i'
    refine ⟨s', r', ⟨w', run', d', ?_, by rw [sm'.high]; exact hp.vars,
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd, by rw [sm'.high]; exact hp.image⟩, fun i _ => by rw [sm'.high]⟩
    rw [i', sm'.high, sm'.cs]
    refine .jump (by omega) (by omega) hJ (.cons (by omega) (by omega) (by omega) hcl.2 hQ ?_)
    convert hk using 1; omega
  | @loopT ks st c p hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, hcl⟩ := hd.cons_inv (by simp) (by simp)
    have hcl' : p.clean = true := by simpa [Stmt.clean] using hcl
    obtain ⟨hE, hT, hJ, hP, hJ'⟩ := loop_code h₄
    have h₂' := h₂; have h₃' := h₃
    simp only [slen, sdepth] at h₂ h₃
    have hcode := h₄; simp only [scode] at hcode
    obtain ⟨s', r', w', run', i', d', sm'⟩ := run_cond (b := true) hL hf hc hp.wf hp.run rfl h₁
      (rest := jmTo _ ++ scode L _ p ++ jmTo (getIP s))
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) hp.vars
      hp.stack (by omega)
    simp only [ite_true] at i'
    refine ⟨s', r', ⟨w', run', d', ?_, by rw [sm'.high]; exact hp.vars,
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd, by rw [sm'.high]; exact hp.image⟩, fun i _ => by rw [sm'.high]⟩
    rw [i', sm'.high, sm'.cs]
    exact .cons (by omega) (by omega) (by omega) hcl' hP
      (.jump (by omega) (by omega) hJ' (.cons h₁ h₂' h₃' hcl h₄ hk))
  | @loopF ks st c p hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd.cons_inv (by simp) (by simp)
    obtain ⟨hE, hT, hJ, hP, hJ'⟩ := loop_code h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    have hcode := h₄; simp only [scode] at hcode
    obtain ⟨s', r', w', run', i', d', sm'⟩ := run_cond (b := false) hL hf hc hp.wf hp.run rfl h₁
      (rest := jmTo _ ++ scode L _ p ++ jmTo (getIP s))
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) hp.vars
      hp.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i'
    refine ⟨s', r', ⟨w', run', d', ?_, by rw [sm'.high]; exact hp.vars,
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd, by rw [sm'.high]; exact hp.image⟩, fun i _ => by rw [sm'.high]⟩
    rw [i', sm'.high, sm'.cs]
    refine .jump (by omega) (by omega) hJ ?_
    convert hk using 1; omega
  | send => exact (hsend _ _ _ rfl).elim
  | recv => exact (hrecv _ _ _ rfl).elim
  | @call ks st k hk hcl hfr =>
    obtain ⟨h₁, h₂, -, h₄, hk', -⟩ := hd.cons_inv (by simp) (by simp)
    simp only [slen] at h₂ hk'
    simp only [scode] at h₄
    rw [show (0x9D : UInt8) :: le4 (UInt32.ofNat (L.entry k)) =
      [0x9D] ++ le4 (UInt32.ofNat (L.entry k)) from rfl, CodeAt.append] at h₄
    obtain ⟨he₁, he₂, he₃, he₄⟩ := hp.image k hk
    have hop : high s (getIP s) = 0x9D := by simpa using h₄.1 0 (by simp)
    have hword : word (high s) (getIP s + 1) = UInt32.ofNat (L.entry k) :=
      word_le4 (by simpa using h₄.2)
    have hen : (UInt32.ofNat (L.entry k)).toNat = L.entry k := toNat_ofNat_addr (by omega)
    have hcsl : (cstack s).length < STACKSZ := by
      rw [hp.cont.frames, frames_cons_clean rfl]; exact hfr
    obtain ⟨w₁, i₁, d₁, c₁, f₁⟩ := step_cl s hp.wf h₁ (by omega) hop
      (by rw [hword, hen]; exact he₁) hcsl
    rw [hword, hen] at i₁
    have hc₂ := CodeAt.append.mp he₄
    rw [length_scode] at hc₂
    refine ⟨step s, Steps.one hp.run (notIo_of_hop h₁ hop),
      ⟨w₁, ⟨f₁.st.trans hp.run.1, f₁.db.trans hp.run.2⟩, by rw [d₁]; exact hp.stack, ?_,
        by rw [f₁.high]; exact hp.vars, by rw [f₁.clk]; exact hp.clk, hp.tfit, hp.rd,
        by rw [f₁.high]; exact hp.image⟩, fun i _ => by rw [f₁.high]⟩
    rw [i₁, f₁.high, c₁]
    exact .cons he₁ (by omega) he₃ hcl hc₂.1
      (.ret (by omega) (by omega) (by simpa using hc₂.2 0 (by simp)) hk')
  | @ret ks st =>
    obtain ⟨cs', b', hcs, h₁, h₂, h₃, hk⟩ := hd.ret_inv
    have hb' := hk.bounds
    have hbn : (UInt32.ofNat b').toNat = b' := toNat_ofNat_addr (by omega)
    obtain ⟨w₁, i₁, d₁, c₁, f₁⟩ := step_rt s cs' (UInt32.ofNat b') hp.wf h₁ h₃ hcs
      (by rw [hbn]; exact hb'.1)
    refine ⟨step s, Steps.one hp.run (notIo_of_hop h₁ h₃),
      ⟨w₁, ⟨f₁.st.trans hp.run.1, f₁.db.trans hp.run.2⟩, by rw [d₁]; exact hp.stack,
        by rw [i₁, hbn, f₁.high, c₁]; exact hk, by rw [f₁.high]; exact hp.vars,
        by rw [f₁.clk]; exact hp.clk, hp.tfit, hp.rd, by rw [f₁.high]; exact hp.image⟩, fun i _ => by rw [f₁.high]⟩
  | @scope ks st x e p hx ha hf hfr =>
    obtain ⟨h₁, h₂, h₃, h₄, hk, hcl⟩ := hd.cons_inv (by simp) (by simp)
    have hcsl : (cstack s).length < STACKSZ := by
      rw [hp.cont.frames, frames_cons_clean hcl]; exact hfr
    simp only [Stmt.clean] at hcl
    simp only [slen, sdepth] at h₂ h₃ hk
    simp only [scode] at h₄
    rw [CodeAt.append, CodeAt.append, CodeAt.append] at h₄
    obtain ⟨⟨⟨hA, hB⟩, hP⟩, hC⟩ := h₄
    simp only [List.length_append, List.length_cons, length_le4, length_scode] at hB hP hC
    replace hP : CodeAt (high s) (getIP s + 7 + ((ecode L e).length + 6))
        (scode L (getIP s + 7 + ((ecode L e).length + 6)) p) :=
      hP.cast (by first | omega | (simp; omega))
    replace hC : CodeAt (high s) (getIP s + 7 + ((ecode L e).length + 6) + slen L p)
        ([0x91] ++ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])) := by
      have := hC.cast (b := getIP s + 7 + ((ecode L e).length + 6) + slen L p)
        (by first | omega | (simp; omega))
      rwa [List.append_assoc] at this
    obtain ⟨s₁, r₁, w₁, run₁, i₁, d₁, c₁, f₁⟩ := enter_runs L hL hx hp.wf hp.run h₁ (by omega) hA
      hp.vars hp.stack hcsl
    obtain ⟨s₂, r₂, w₂, run₂, i₂, d₂, v₂, k₂⟩ := assign_runs L hL (d := (cstack s₁).length) hx ha hf
      s₁ (getIP s + 7)
      ⟨w₁, run₁, i₁, by omega, by simp [slen]; omega, by rw [f₁.high]; simpa [scode] using hB,
        by rw [f₁.high]; exact hp.vars, d₁, by simp [sdepth]; omega, rfl,
        by rw [f₁.high]; exact hp.image⟩
    simp only [slen] at i₂
    have hhigh : ∀ i < L.base, high s₂ i = high s i := fun i hi => by rw [k₂.low i hi, f₁.high]
    refine ⟨s₂, r₁.trans r₂, ⟨w₂, run₂, d₂, ?_, v₂, by rw [k₂.clk, f₁.clk]; exact hp.clk, hp.tfit,
      hp.rd, hp.image.mono hhigh⟩, fun i hi => by rw [k₂.top i hi, f₁.high]⟩
    rw [i₂, k₂.cs, c₁]
    refine .cons (by omega) (by omega) (by omega) hcl
      (hP.mono hhigh (by rw [length_scode]; omega)) ?_
    refine .restore (by omega) (by omega) hx ha (hC.mono hhigh (by simp; omega)) ?_
    exact (hk.mono hhigh).cast (by omega)
  | @restore ks st x v =>
    obtain ⟨cs', hcs, h₁, h₂, hx, ha, h₄, hk⟩ := hd.restore_inv
    obtain ⟨s', r', w', run', i', d', c', v', lo', -, k', top'⟩ := restore_runs L hL hx ha hp.wf hp.run h₁
      h₂ h₄ hp.vars hp.stack hcs
    exact ⟨s', r', ⟨w', run', d', by rw [i', c']; exact hk.mono lo', v', by rw [k']; exact hp.clk,
      hp.tfit, hp.rd, hp.image.mono lo'⟩, top'⟩

theorem toNat_encT {t : ℕ∞} (h : TFits t) : (encT t).toNat = t.toNat := by
  have := h.toNat_lt
  simp only [encT, UInt32.toNat_ofNat']; omega

/-- The clock after an input is the encoded `t ↑ (τ + 1)`. -/
theorem later_encT {t τ : ℕ∞} (ht : TFits t) (h : TFits (max t (τ + 1))) :
    later (encT t) (encT τ + 1) = encT (max t (τ + 1)) := by
  have hτ1 : TFits (τ + 1) := h.mono (le_max_right _ _)
  have hτ : TFits τ := hτ1.mono le_self_add
  have h₁ := ht.toNat_lt; have h₂ := hτ1.toNat_lt
  lift t to ℕ using ht.ne_top
  lift τ to ℕ using hτ.ne_top
  simp only [ENat.toNat_natCast] at h₁
  rw [show ((τ : ℕ∞) + 1).toNat = τ + 1 by norm_cast] at h₂
  have hs : encT (τ : ℕ∞) + 1 = encT ((τ + 1 : ℕ) : ℕ∞) := by
    apply UInt32.toNat_inj.mp
    simp only [encT, ENat.toNat_natCast, UInt32.toNat_add, UInt32.toNat_ofNat']
    have : (1 : UInt32).toNat = 1 := rfl
    rw [this]; omega
  rw [hs]
  unfold later
  simp only [encT, ENat.toNat_natCast, UInt32.toNat_ofNat']
  rw [show max (t : ℕ∞) ((τ : ℕ∞) + 1) = ((max t (τ + 1) : ℕ) : ℕ∞) by rfl,
    ENat.toNat_natCast]
  split_ifs with hlt
  · congr 1; omega
  · congr 1; omega

/-- **The swarm and the network agree**: a machine for each process, related
as `PRel` says, and the channels holding the scripts. -/
structure Rel (L : Layout) (c : SCfg) (w : Swarm) : Prop where
  /-- A machine for each process. -/
  len : w.ms.length = c.ps.length
  /-- Cursors for each process. -/
  rdlen : w.rd.length = c.ps.length
  /-- Each process and its machine agree. -/
  proc : ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State}, c.ps[i]? = some (ks, st) →
    w.ms[i]? = some s → PRel L ks st s (w.rd.getD i fun _ => 0)
  /-- The channels hold the scripts. -/
  chans : ∀ ch, w.chans ch = encS (c.L ch)

/-- Replace one machine and one process, keeping the cursors. -/
theorem Rel.set {L : Layout} {c : SCfg} {w : Swarm} (hr : Rel L c w) {i : ℕ}
    (hi : i < c.ps.length) {ks : List Stmt} {st : PSt ℕ Value} {s : State} {Λ : Scripts Value}
    (hp : PRel L ks st s (w.rd.getD i fun _ => 0)) (hch : ∀ ch, w.chans ch = encS (Λ ch)) :
    Rel L ⟨c.ps.set i (ks, st), Λ⟩ { w with ms := w.ms.set i s } := by
  refine ⟨by simp [hr.len], by simp [hr.rdlen], ?_, hch⟩
  intro j ks' st' s' hc hm
  by_cases hij : i = j
  · subst hij
    simp only [List.getElem?_set_self hi, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.getElem?_set_self (hr.len ▸ hi), Option.some.injEq] at hm
    subst hm; exact hp
  · simp only [List.getElem?_set_ne hij] at hc hm
    exact hr.proc hc hm

theorem swarm_set_set (w : Swarm) (i : ℕ) (s s' : State) :
    ({ { w with ms := w.ms.set i s } with ms := ({ w with ms := w.ms.set i s } : Swarm).ms.set i s' } :
      Swarm) = { w with ms := w.ms.set i s' } := by
  simp

/-- **Send**, on the machine and then in the swarm. -/
theorem send_sim (L : Layout) (hL : L.Ok) {w : Swarm} {i : ℕ} {s : State} {ch : ℕ} {e : Exp}
    {ks : List Stmt} {st : PSt ℕ Value} {r : ℕ → ℕ} (hi : w.ms[i]? = some s)
    (hp : PRel L (.send ch e :: ks) st s r)
    (hd : Direct L (high s) (cstack s) (.send ch e :: ks) (getIP s))
    (hf : Fits L st.mem e) (hch : ch < 2 ^ 32) (ho : w.owner ch = some i) :
    ∃ s', Swarm.Steps w ⟨w.ms.set i s',
        fun c => if c = ch then w.chans c ++ [(enc (e.eval st.mem), encT st.t)] else w.chans c,
        w.rd, w.owner⟩ ∧ PRel L ks (st.sent ch) s' r := by
  have hb := hL.2
  obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd.cons_inv (by simp) (by simp)
  simp only [slen, sdepth] at h₂ h₃
  simp only [scode, List.append_assoc] at h₄
  have hA : At L st.mem s (ecode L e ++ ((0x97 :: le4 (UInt32.ofNat ch)) ++
      ((0x97 :: le4 SEND) ++ [0xFD]))) (max (depth e) 3) :=
    ⟨hp.wf, hp.run, h₁, by simp; omega, h₄, hp.vars, by rw [hp.stack]; simpa using h₃⟩
  obtain ⟨s₁, r₁, w₁, i₁, d₁, sm₁⟩ := exp_runs L hL st.mem e s hf (hA.left (le_max_left _ _))
  have hA₁ := hA.after (d₂ := 2) (by omega) w₁ i₁ d₁ sm₁
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_li hA₁ (by omega)
  have hA₂ := hA₁.after (bs₁ := 0x97 :: le4 (UInt32.ofNat ch)) (d₂ := 1) (by omega) w₂
    (by rw [i₂]; rfl) d₂ sm₂
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_li hA₂ (by omega)
  have hA₃ := hA₂.after (bs₁ := 0x97 :: le4 SEND) (d₂ := 0) (by omega) w₃
    (by rw [i₃]; rfl) d₃ sm₃
  have hrun : Steps s (step (step s₁)) :=
    (r₁.tail ⟨hA₁.run, notIo_li hA₁, rfl⟩).tail ⟨hA₂.run, notIo_li hA₂, rfl⟩
  have hop : high (step (step s₁)) (getIP (step (step s₁))) = 0xFD := by
    simpa using hA₃.code 0 (by simp)
  have hlift := swarm_lift hi hrun
  obtain ⟨s', hst, w', i', d', sm'⟩ := swarm_send (w := { w with ms := w.ms.set i (step (step s₁)) })
    (i := i) (v := enc (e.eval st.mem)) (ch := ch)
    (by simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]) hA₃.wf hA₃.run hA₃.lo
    (by have := hA₃.hi; simp at this; omega) hop
    (by rw [d₃, d₂, d₁, hp.stack]; rfl) hch ho
  have hsm := sm₁.trans (sm₂.trans (sm₃.trans sm'))
  refine ⟨s', ?_, ⟨w', hsm.running hp.run, d', ?_, by rw [hsm.high]; exact hp.vars,
    by rw [hsm.clk]; exact hp.clk, hp.tfit, hp.rd, by rw [hsm.high]; exact hp.image⟩⟩
  · refine hlift.tail ⟨i, ?_⟩
    rw [hst]
    simp only [List.set_set]
    rw [(sm₁.trans (sm₂.trans sm₃)).clk, hp.clk]
  · rw [i', i₃, i₂, i₁, hsm.high, hsm.cs]
    convert hk using 1
    simp [slen]; omega

/-- **Receive**, in the swarm and then on the machine. -/
theorem recv_sim (L : Layout) (hL : L.Ok) {w : Swarm} {i : ℕ} {s : State} {ch x : ℕ}
    {ks : List Stmt} {st : PSt ℕ Value} {m : Msg Value} {Λ : Scripts Value} (hi : w.ms[i]? = some s)
    (hp : PRel L (.recv ch x :: ks) st s (w.rd.getD i fun _ => 0))
    (hd : Direct L (high s) (cstack s) (.recv ch x :: ks) (getIP s)) (hch : ch < 2 ^ 32)
    (hchan : w.chans ch = encS (Λ ch)) (hm : (Λ ch)[st.r ch]? = some m) (hx : x < L.n)
    (ha : L.arrayAt x = none)
    (hfit : TFits (max st.t (m.2 + 1))) :
    ∃ s', Swarm.Steps w ⟨w.ms.set i s', w.chans,
        w.rd.set i (fun c => if c = ch then (w.rd.getD i fun _ => 0) ch + 1
          else (w.rd.getD i fun _ => 0) c), w.owner⟩ ∧
      PRel L ks (st.received ch x m)
        s' (fun c => if c = ch then (w.rd.getD i fun _ => 0) ch + 1 else (w.rd.getD i fun _ => 0) c) := by
  have hb := hL.2
  have hlt : i < w.ms.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd.cons_inv (by simp) (by simp)
  simp only [slen, sdepth] at h₂ h₃
  simp only [scode, List.append_assoc] at h₄
  have hA : At L st.mem s ((0x97 :: le4 (UInt32.ofNat ch)) ++ ((0x97 :: le4 RECV) ++ ([0xFD] ++
      ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])))) 2 :=
    ⟨hp.wf, hp.run, h₁, by simp; omega, h₄, hp.vars, by rw [hp.stack]; decide⟩
  obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li hA (by omega)
  have hA₁ := hA.after (bs₁ := 0x97 :: le4 (UInt32.ofNat ch)) (d₂ := 1) (by omega) w₁
    (by rw [i₁]; rfl) d₁ sm₁
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_li hA₁ (by omega)
  have hA₂ := hA₁.after (bs₁ := 0x97 :: le4 RECV) (d₂ := 0) (by omega) w₂
    (by rw [i₂]; rfl) d₂ sm₂
  set s₂ := step (step s) with hs₂
  have hrun : Steps s s₂ := (Steps.one hp.run (notIo_li hA)).tail ⟨hA₁.run, notIo_li hA₁, rfl⟩
  have hop : high s₂ (getIP s₂) = 0xFD := by simpa using hA₂.code 0 (by simp)
  have hlift := swarm_lift hi hrun
  have hst₂ : dstack s₂ = [UInt32.ofNat ch, RECV] := by rw [d₂, d₁, hp.stack]; rfl
  have hm' : (w.chans ch)[(w.rd.getD i fun _ => 0) ch]? = some (enc m.1, encT m.2) := by
    rw [hchan, hp.rd ch, encS, List.getElem?_map, hm]; rfl
  have hstep := swarm_recv (w := { w with ms := w.ms.set i s₂ }) (i := i) (ch := ch)
    (by simp [List.getElem?_set_self hlt]) hA₂.wf hA₂.run hA₂.lo hop hst₂ hch hm'
  obtain ⟨w₃, i₃, d₃, c₃, h₃', cs₃, st₃, db₃, o₃⟩ :=
    recvState_view (v := enc m.1) (τ := encT m.2) hA₂.wf (by have := hA₂.hi; simp at this; omega) hst₂
  set s₃ := recvState s₂ (enc m.1) (encT m.2) with hs₃
  -- `li addr; wi`
  have hc₃ : CodeAt (high s₃) (getIP s₃) ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]) := by
    rw [h₃', i₃]; have := (CodeAt.append.mp hA₂.code).2; simpa using this
  have hA₃ : At L st.mem s₃ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]) 1 :=
    ⟨w₃, ⟨st₃.trans hA₂.run.1, db₃.trans hA₂.run.2⟩, by rw [i₃]; have := hA₂.lo; omega,
      by rw [i₃]; have := hA₂.hi; simp at this ⊢; omega, hc₃,
      by rw [h₃', sm₂.high, sm₁.high]; exact hp.vars, by rw [d₃]; simp [STACKSZ]⟩
  obtain ⟨w₄, i₄, d₄, sm₄⟩ := run_li hA₃ le_rfl
  have haddr : L.addr x + 3 < MAXBYTE := by unfold Layout.addr; omega
  have hop₄ : high (step s₃) (getIP (step s₃)) = 0x95 := by
    rw [sm₄.high, i₄]; have := (CodeAt.append.mp hc₃).2 0 (by simp); simpa using this
  have hip₄ : 256 ≤ getIP (step s₃) := by rw [i₄]; have := hA₃.lo; omega
  have hd₄ : dstack (step s₃) = [] ++ [enc m.1, UInt32.ofNat (L.addr x)] := by rw [d₄, d₃]; rfl
  have ha₄ : 256 ≤ (UInt32.ofNat (L.addr x)).toNat := by
    rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega
  obtain ⟨w₅, i₅, d₅, c₅, st₅, db₅, hi₅, o₅⟩ := step_wi (step s₃) [] (enc m.1)
    (UInt32.ofNat (L.addr x)) w₄ hip₄ (by rw [i₄]; have := hA₃.hi; unfold MAXBYTE at this; simp at this; omega)
    hop₄ hd₄ ha₄ (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
  have hclk₅ := step_wi_clk (step s₃) [] (enc m.1) (UInt32.ofNat (L.addr x)) w₄ hip₄ hop₄ hd₄ ha₄
  rw [toNat_ofNat_addr (by omega)] at hi₅
  have run₃ : Running s₃ := hA₃.run
  have run₄ : Running (step s₃) := sm₄.running run₃
  have hrun₂ : Steps s₃ (step (step s₃)) :=
    (Steps.one run₃ (notIo_li hA₃)).tail ⟨run₄, notIo_of_hop hip₄ hop₄, rfl⟩
  have hlow : ∀ j < L.base, high (step (step s₃)) j = high s j := by
    intro j hj
    rw [hi₅, sm₄.high, h₃', sm₂.high, sm₁.high]
    unfold writeWord Layout.addr
    simp [show j ≠ L.base + 4 * x by omega, show j ≠ L.base + 4 * x + 1 by omega,
      show j ≠ L.base + 4 * x + 2 by omega, show j ≠ L.base + 4 * x + 3 by omega]
  refine ⟨step (step s₃), ?_, ⟨w₅, ⟨st₅.trans run₄.1, db₅.trans run₄.2⟩, d₅, ?_, ?_, ?_, hfit, ?_,
    hp.image.mono hlow⟩⟩
  · refine (hlift.tail ⟨i, hstep⟩).trans ?_
    have := swarm_lift (w := ⟨w.ms.set i s₃, w.chans, w.rd.set i (fun c => if c = ch then
      (w.rd.getD i fun _ => 0) ch + 1 else (w.rd.getD i fun _ => 0) c), w.owner⟩) (i := i) (s := s₃)
      (by simp [List.getElem?_set_self hlt]) hrun₂
    simpa using this
  · rw [i₅, i₄, i₃, i₂, i₁, c₅, sm₄.cs, cs₃, sm₂.cs, sm₁.cs]
    exact Cont.mono hlow (by convert hk using 1; simp [slen])
  · rw [hi₅, sm₄.high, h₃', sm₂.high, sm₁.high]
    exact varsOk_write hp.vars hx ha
  · rw [hclk₅, sm₄.clk, c₃, (sm₁.trans sm₂).clk, hp.clk]
    exact later_encT hp.tfit hfit
  · intro c
    simp only [PSt.received, Function.update_apply]
    by_cases hc : c = ch
    · subst hc; simp [hp.rd]
    · simp [hc, hp.rd]

/-- Replace one machine, its cursors and one process. -/
theorem Rel.setRd {L : Layout} {c : SCfg} {w : Swarm} (hr : Rel L c w) {i : ℕ}
    (hi : i < c.ps.length) {ks : List Stmt} {st : PSt ℕ Value} {s : State} {Λ : Scripts Value}
    {r : ℕ → ℕ} {chans : ℕ → List B4.Msg} (hp : PRel L ks st s r) (hch : ∀ ch, chans ch = encS (Λ ch)) :
    Rel L ⟨c.ps.set i (ks, st), Λ⟩ ⟨w.ms.set i s, chans, w.rd.set i r, w.owner⟩ := by
  refine ⟨by simp [hr.len], by simp [hr.rdlen], ?_, hch⟩
  intro j ks' st' s' hc hm
  have hrd : i < w.rd.length := hr.rdlen ▸ hi
  by_cases hij : i = j
  · subst hij
    simp only [List.getElem?_set_self hi, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [List.getElem?_set_self (hr.len ▸ hi), Option.some.injEq] at hm
    subst hm
    simpa [List.getD_eq_getElem?_getD, List.getElem?_set_self hrd] using hp
  · simp only [List.getElem?_set_ne hij] at hc hm
    have := hr.proc hc hm
    simpa [List.getD_eq_getElem?_getD, List.getElem?_set_ne hij] using this

theorem Rel.machine {L : Layout} {c : SCfg} {w : Swarm} (hr : Rel L c w) {i : ℕ}
    {ks : List Stmt} {st : PSt ℕ Value} (ha : c.ps[i]? = some (ks, st)) :
    ∃ s, w.ms[i]? = some s ∧ PRel L ks st s (w.rd.getD i fun _ => 0) := by
  have hlt : i < w.ms.length := hr.len ▸ (List.getElem?_eq_some_iff.mp ha).1
  exact ⟨_, List.getElem?_eq_getElem hlt, hr.proc ha (List.getElem?_eq_getElem hlt)⟩

/-- Follow the jumps of machine `i` in the swarm. -/
theorem Rel.follow (L : Layout) (hL : L.Ok) {w : Swarm} {i : ℕ} {s : State} {ks : List Stmt}
    {st : PSt ℕ Value} {r : ℕ → ℕ} (hi : w.ms[i]? = some s) (hp : PRel L ks st s r) :
    ∃ s₁, Swarm.Steps w { w with ms := w.ms.set i s₁ } ∧ Steps s s₁ ∧ PRel L ks st s₁ r ∧
      Direct L (high s₁) (cstack s₁) ks (getIP s₁) := by
  obtain ⟨s₁, r₁, sm₁, w₁, d₁, hd₁⟩ := LaPToP.ProgramTheory.CompileNet.follow L hL hp.cont s rfl
    rfl hp.wf hp.run rfl
  exact ⟨s₁, swarm_lift hi r₁, r₁, ⟨w₁, sm₁.running hp.run, d₁.trans hp.stack,
    by rw [sm₁.high, sm₁.cs]; exact hd₁.cont, by rw [sm₁.high]; exact hp.vars,
    by rw [sm₁.clk]; exact hp.clk, hp.tfit, hp.rd, by rw [sm₁.high]; exact hp.image⟩,
    by rw [sm₁.high, sm₁.cs]; exact hd₁⟩

/-- **One step of the network, in 32 bits, is some steps of the swarm**, which
keep them agreeing. -/
theorem sim_step (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {c c' : SCfg} (h : SStep L net c c') {w : Swarm} (hr : Rel L c w)
    (hown : ∀ {i : ℕ} {pr : SProc} {ch : ℕ}, net.procs[i]? = some pr → ch ∈ pr.outs →
      w.owner ch = some i) :
    ∃ w', Swarm.Steps w w' ∧ w'.owner = w.owner ∧ Rel L c' w' := by
  obtain ⟨hpr, ha, hact⟩ := h
  rename_i i pr a b Λ
  obtain ⟨ks, st⟩ := a
  have hlt : i < c.ps.length := (List.getElem?_eq_some_iff.mp ha).1
  have hprm : pr ∈ net.procs := List.mem_of_getElem? hpr
  obtain ⟨s, hs, hp⟩ := hr.machine ha
  obtain ⟨s₁, hw₁, r₁, hp₁, hd₁⟩ := Rel.follow L hL hs hp
  have hs₁ : ({ w with ms := w.ms.set i s₁ } : Swarm).ms[i]? = some s₁ := by
    simp [List.getElem?_set_self (hr.len ▸ hlt)]
  -- the actions that do not communicate
  have local_case : ∀ {b' : List Stmt × PSt ℕ Value}, SAct L pr c.L (ks, st) b' c.L →
      (∀ ch e ks', ks ≠ .send ch e :: ks') → (∀ ch x ks', ks ≠ .recv ch x :: ks') →
      ∃ w', Swarm.Steps w w' ∧ w'.owner = w.owner ∧ Rel L ⟨c.ps.set i b', c.L⟩ w' := by
    intro b' hb' hs' hr'
    obtain ⟨s₂, r₂, hp₂, -⟩ := machine_sim L hL hb' hs' hr' hp₁ hd₁
    refine ⟨{ w with ms := w.ms.set i s₂ }, ?_, rfl, ?_⟩
    · have := swarm_lift hs₁ r₂; simp at this; exact hw₁.trans (by simpa using this)
    · have := hr.set hlt (ks := b'.1) (st := b'.2) (s := s₂) (Λ := c.L) hp₂ hr.chans
      simpa using this
  cases hact with
  | ok => exact local_case .ok (by simp) (by simp)
  | assign hx hax hf => exact local_case (.assign hx hax hf) (by simp) (by simp)
  | tick hfit => exact local_case (.tick hfit) (by simp) (by simp)
  | seq => exact local_case .seq (by simp) (by simp)
  | condT hf hc => exact local_case (.condT hf hc) (by simp) (by simp)
  | condF hf hc => exact local_case (.condF hf hc) (by simp) (by simp)
  | loopT hf hc => exact local_case (.loopT hf hc) (by simp) (by simp)
  | loopF hf hc => exact local_case (.loopF hf hc) (by simp) (by simp)
  | call hk hcl hfr => exact local_case (.call hk hcl hfr) (by simp) (by simp)
  | ret => exact local_case .ret (by simp) (by simp)
  | scope hx hax hf hfr => exact local_case (.scope hx hax hf hfr) (by simp) (by simp)
  | store hfi hf => exact local_case (.store hfi hf) (by simp) (by simp)
  | restore => exact local_case .restore (by simp) (by simp)
  | @send ks' _ ch e hch hf =>
    obtain ⟨s₂, hw₂, hp₂⟩ := send_sim L hL hs₁ hp₁ hd₁ hf (hchb pr hprm ch (.inl hch))
      (hown hpr hch)
    refine ⟨_, hw₁.trans hw₂, rfl, ?_⟩
    have := hr.setRd hlt (ks := ks') (st := st.sent ch) (s := s₂)
      (Λ := Function.update c.L ch (c.L ch ++ [(e.eval st.mem, st.t)]))
      (chans := fun c' => if c' = ch then w.chans c' ++ [(enc (e.eval st.mem), encT st.t)]
        else w.chans c') (r := w.rd.getD i fun _ => 0) (by simpa using hp₂) (by
        intro c'
        by_cases hc : c' = ch
        · subst hc; simp [hr.chans, encS]
        · simp [hc, hr.chans])
    have hrd : w.rd.set i (w.rd.getD i fun _ => 0) = w.rd := by
      apply List.ext_getElem?; intro j
      by_cases hij : i = j
      · subst hij
        rw [List.getElem?_set_self (hr.rdlen ▸ hlt), List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (hr.rdlen ▸ hlt)]; rfl
      · rw [List.getElem?_set_ne hij]
    rw [hrd] at this; simpa using this
  | @recv ks' _ ch x m hch hm hx hax hfit =>
    obtain ⟨s₂, hw₂, hp₂⟩ := recv_sim L hL (Λ := c.L) hs₁ (by simpa using hp₁) hd₁
      (hchb pr hprm ch (.inr hch)) (by simpa using hr.chans ch) hm hx hax hfit
    refine ⟨_, hw₁.trans hw₂, rfl, ?_⟩
    have := hr.setRd hlt (ks := ks') (st := st.received ch x m) (s := s₂) (Λ := c.L)
      (chans := w.chans) hp₂ hr.chans
    simpa using this

/-- **Runs**: every run of the network in 32 bits is matched by a run of the
swarm. -/
theorem swarm_simulates (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {c c' : SCfg} (h : ReflTransGen (SStep L net) c c') {w : Swarm} (hr : Rel L c w)
    (hown : ∀ {i : ℕ} {pr : SProc} {ch : ℕ}, net.procs[i]? = some pr → ch ∈ pr.outs →
      w.owner ch = some i) :
    ∃ w', Swarm.Steps w w' ∧ w'.owner = w.owner ∧ Rel L c' w' := by
  induction h with
  | refl => exact ⟨w, .refl, rfl, hr⟩
  | tail _ hs ih =>
    obtain ⟨w₁, r₁, o₁, h₁⟩ := ih
    obtain ⟨w₂, r₂, o₂, h₂⟩ := sim_step L hL hchb hs h₁ (fun hp hc => o₁ ▸ hown hp hc)
    exact ⟨w₂, r₁.trans r₂, o₂.trans o₁, h₂⟩

/-! ### Loading the swarm -/

theorem getClk_load (L : Layout) (hL : L.Ok) (p : Stmt) (st : St)
    (hfit : L.start + slen L p + 1 ≤ L.base) : getClk (load L p st) = 0 := by
  have hlow := loadMem_low L p st hfit hL
  have hload : load L p st = setRST (setIP ⟨loadMem L p st, Array.replicate STACKSZ 0,
      Array.replicate STACKSZ 0, ""⟩ L.start) 1 := rfl
  rw [hload, getClk_setRST, getClk_setIP]
  exact getVal_of_zero _ _ fun i _ hi => hlow i (by simp [CLK_OFF, Register.toNat] at hi; omega)

/-- The swarm for a network: each process compiled and loaded into its own
machine, from the prestate `s`, with the environment's scripts on the channels. -/
def SNet.load (L : Layout) (net : SNet) (s : St) : Swarm :=
  ⟨net.procs.map fun pr => CompileB4.load L pr.body s, fun ch => encS (net.input ch),
    net.procs.map (fun _ _ => 0), fun ch => net.procs.findIdx? fun pr => pr.outs.contains ch⟩

/-- In the loaded swarm, each channel's writer is its owner. -/
theorem load_owner (L : Layout) {net : SNet} (hwf : net.toNet.WF) (s : St) {i : ℕ} {pr : SProc}
    {ch : ℕ} (hpr : net.procs[i]? = some pr) (hch : ch ∈ pr.outs) :
    (net.load L s).owner ch = some i := by
  simp only [SNet.load]
  rw [List.findIdx?_eq_some_iff_getElem]
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hpr
  refine ⟨hlt, by simp [hget, hch], fun j hj => ?_⟩
  have hjlt : j < net.procs.length := by omega
  simp only [List.contains_iff_mem]
  intro hj'
  have h₁ : net.toNet.procs[j]? = some ⟨net.procs[j].body.toNP, net.procs[j].outs, net.procs[j].ins⟩ := by
    simp [SNet.toNet, hjlt]
  have h₂ : net.toNet.procs[i]? = some ⟨pr.body.toNP, pr.outs, pr.ins⟩ := by
    simp [SNet.toNet, hpr]
  exact hwf.writer (by omega) h₁ h₂ hj' hch

/-- The code of each process, after the named statements', fits below the
variables, and its stack; and each is written in the language. -/
def SNet.Fits (L : Layout) (net : SNet) : Prop :=
  ∀ pr ∈ net.procs, L.Fit pr.body ∧ pr.body.clean = true

/-- **At the start, the swarm and the network agree.** -/
theorem rel_init (L : Layout) (hL : L.Ok) (net : SNet) (hfit : net.Fits L) (s : St) :
    Rel L (net.init s) (net.load L s) := by
  refine ⟨by simp [SNet.load, SNet.init], by simp [SNet.load, SNet.init], ?_, fun ch => rfl⟩
  intro i ks st m hc hm
  simp only [SNet.init, List.getElem?_map, Option.map_eq_some_iff] at hc
  obtain ⟨pr, hpr, hpe⟩ := hc
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  simp only [SNet.load, List.getElem?_map, hpr, Option.map_some, Option.some.injEq] at hm
  subst hm
  obtain ⟨hF, hcl⟩ := hfit pr (List.mem_of_getElem? hpr)
  have hf₁ := hF.hi
  obtain ⟨hw, hrun, hip, hc, hv, hd, hcs⟩ := load_ready L hL pr.body s hf₁
  obtain ⟨hc₁, hc₂⟩ := L.main_of_compile hc
  have hs : 256 ≤ L.start := by unfold Layout.start; omega
  refine ⟨hw, hrun, hd, ?_, hv, by rw [getClk_load L hL _ _ hf₁]; rfl,
    by simp [TFits], fun _ => by simp [SNet.load, List.getD_eq_getElem?_getD],
    L.image_of_compile hF hc⟩
  rw [hip, hcs]
  exact .cons hs (by omega) hF.depth hcl hc₁ (.nil (by omega) (by omega) hc₂)

/-! ### The end -/

/-- A machine that has halted holding a process's final state. -/
structure Halted (L : Layout) (st : PSt ℕ Value) (s : State) : Prop where
  stopped : getRST s = 0
  vars : VarsOk L (high s) st.mem
  clk : getClk s = encT st.t

/-- A machine whose process has finished halts. -/
theorem halt_one (L : Layout) (hL : L.Ok) {w : Swarm} {i : ℕ} {s : State} {st : PSt ℕ Value}
    {r : ℕ → ℕ} (hi : w.ms[i]? = some s) (hp : PRel L [] st s r) :
    ∃ s', Swarm.Steps w { w with ms := w.ms.set i s' } ∧ Halted L st s' := by
  obtain ⟨s₁, hw₁, -, hp₁, hd₁⟩ := Rel.follow L hL hi hp
  obtain ⟨h₁, h₂, h₃⟩ := hd₁.nil_inv
  · have hs₁ : ({ w with ms := w.ms.set i s₁ } : Swarm).ms[i]? = some s₁ := by
      simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]
    have hn : NotIo s₁ := notIo_of_hop h₁ h₃
    refine ⟨step s₁, hw₁.tail ⟨i, ?_⟩, ⟨step_hl s₁ hp₁.wf h₁ h₃, ?_, ?_⟩⟩
    · rw [Swarm.stepAt_other hs₁ ((running_iff _).mpr hp₁.run) (by rw [ioCmd_of_notIo hn]; simp)
        (by rw [ioCmd_of_notIo hn]; simp) (by rw [ioCmd_of_notIo hn]; simp)]
      simp
    · rw [step_of s₁ _ h₁ h₃, runOp_hl]; simpa using hp₁.vars
    · rw [step_of s₁ _ h₁ h₃, runOp_hl]; simpa using hp₁.clk

/-- Halt the machines of finished processes one by one. -/
theorem halt_upto (L : Layout) (hL : L.Ok) {c : SCfg} {w : Swarm} (hr : Rel L c w)
    (hdone : ∀ p ∈ c.ps, p.1 = []) (k : ℕ) :
    ∃ w', Swarm.Steps w w' ∧ w'.ms.length = c.ps.length ∧ w'.chans = w.chans ∧
      ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) →
        ∃ s, w'.ms[i]? = some s ∧
          (if i < k then Halted L st s else PRel L ks st s (w.rd.getD i fun _ => 0)) := by
  induction k with
  | zero =>
    refine ⟨w, .refl, hr.len, rfl, fun hc => ?_⟩
    obtain ⟨s, hs, hp⟩ := hr.machine hc
    exact ⟨s, hs, by simpa using hp⟩
  | succ k ih =>
    obtain ⟨w₁, r₁, l₁, c₁, h₁⟩ := ih
    by_cases hk : k < c.ps.length
    · obtain ⟨ks, st⟩ := c.ps[k]
      have hck : c.ps[k]? = some (c.ps[k].1, c.ps[k].2) := by simp [hk]
      obtain ⟨s, hs, hp⟩ := h₁ hck
      rw [ite_eq_right (by omega)] at hp
      have hnil : c.ps[k].1 = [] := hdone _ (List.getElem_mem hk)
      rw [hnil] at hp
      obtain ⟨s', r', hh⟩ := halt_one L hL hs hp
      refine ⟨_, r₁.trans r', by simp [l₁], by simp [c₁], fun {i ks' st'} hc => ?_⟩
      by_cases hik : i = k
      · subst hik
        rw [hck] at hc; cases hc
        exact ⟨s', by simp [List.getElem?_set_self (l₁ ▸ hk)], by rw [ite_eq_left (by omega)]; exact hh⟩
      · obtain ⟨s'', hs'', hq⟩ := h₁ hc
        refine ⟨s'', by simpa [List.getElem?_set_ne (Ne.symm hik)] using hs'', ?_⟩
        by_cases hlt : i < k
        · rw [ite_eq_left hlt] at hq; rw [ite_eq_left (by omega)]; exact hq
        · rw [ite_eq_right hlt] at hq; rw [ite_eq_right (by omega)]; exact hq
    · refine ⟨w₁, r₁, l₁, c₁, fun {i ks st} hc => ?_⟩
      obtain ⟨s, hs, hq⟩ := h₁ hc
      have : i < c.ps.length := (List.getElem?_eq_some_iff.mp hc).1
      refine ⟨s, hs, ?_⟩
      rw [ite_eq_left (by omega)]; rw [ite_eq_left (by omega)] at hq; exact hq

/-- **The swarm computes the network.** If the network, started from `s`, runs
in 32 bits to a configuration where every process has finished, then the swarm
of compiled processes, loaded from `s`, runs to a state where every machine has
halted with its process's final variables in its cells and its final time on
its clock, and the channels hold the scripts the network wrote. -/
theorem swarm_correct (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF) (hfit : net.Fits L)
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32) (s : St)
    {c : SCfg} (h : ReflTransGen (SStep L net) (net.init s) c) (hdone : ∀ p ∈ c.ps, p.1 = []) :
    ∃ w, Swarm.Steps (net.load L s) w ∧ w.ms.length = c.ps.length ∧
      (∀ ch, w.chans ch = encS (c.L ch)) ∧
      ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) →
        ∃ m, w.ms[i]? = some m ∧ Halted L st m := by
  obtain ⟨w₁, r₁, -, h₁⟩ := swarm_simulates L hL hchb h (rel_init L hL net hfit s)
    (load_owner L hwf s)
  obtain ⟨w₂, r₂, l₂, c₂, h₂⟩ := halt_upto L hL h₁ hdone c.ps.length
  refine ⟨w₂, r₁.trans r₂, l₂, fun ch => by rw [c₂, h₁.chans], fun hc => ?_⟩
  obtain ⟨m, hm, hh⟩ := h₂ hc
  rw [ite_eq_left (List.getElem?_eq_some_iff.mp hc).1] at hh
  exact ⟨m, hm, hh⟩

/-- **The swarm computes the book's semantics.** When the network runs in 32
bits until every process has finished, its final states and scripts are a
behaviour of the book's semantics of the network (`Network.NetSpec`), and the
swarm halts holding exactly them. -/
theorem swarm_book (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF) (hfit : net.Fits L)
    (hdefs : L.defs = net.defs)
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32) (s : St)
    {c : SCfg} (h : ReflTransGen (SStep L net) (net.init s) c) (hdone : ∀ p ∈ c.ps, p.1 = []) :
    NetSpec net.toNet s 0 (c.ps.map (·.2)) c.L ∧
      ∃ w, Swarm.Steps (net.load L s) w ∧ (∀ ch, w.chans ch = encS (c.L ch)) ∧
        ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) →
          ∃ m, w.ms[i]? = some m ∧ Halted L st m := by
  have hm := reach_of_sSteps hdefs h
  rw [SNet.init_toM] at hm
  have hd : c.toM.Done := by
    intro pc hpc
    simp only [SCfg.toM, List.mem_map] at hpc
    obtain ⟨⟨ks, st⟩, hmem, rfl⟩ := hpc
    have := hdone _ hmem
    simp only at this ⊢
    simp [this]
  have hs := netSpec_of_reach hwf hm hd
  obtain ⟨w, hw, -, hch, hh⟩ := swarm_correct L hL hwf hfit hchb s h hdone
  refine ⟨?_, w, hw, hch, hh⟩
  have heq : c.toM.ps.map (·.st) = c.ps.map (·.2) := by simp [SCfg.toM, Function.comp_def]
  rw [← heq]; exact hs

/-! ### Demonstrations -/

namespace Demo

/-- Run a swarm and show each machine's variables `0..n-1`, its clock, and channel
`0` and `1`'s scripts. -/
def display (L : Layout) (w : Swarm) : List (List ℤ × UInt32) × List (List B4.Msg) :=
  (w.ms.map fun m => (readVars L m, getClk m), [w.chans 0, w.chans 1])

/-- Cells above 64 bytes of code. -/
def layout : Layout := { base := 0x400, n := 3 }

/-- `c! 2 || (c?. x:= c)`. -/
def sendRecv : SNet :=
  { procs := [⟨.send 0 (.lit (.int 2)), [0], []⟩, ⟨.recv 0 0, [], [0]⟩], input := fun _ => [] }

-- The receiver has `x = 2` at time `1`.
#eval display layout ((sendRecv.load layout fun _ => .int 0).run 1000)

/-- The buffer: `(c! 3. tick. c! 4) || (c?. y:= c. c?. x:= c)`, `x`, `y` variables `0`, `1`. -/
def buffer : SNet :=
  { procs := [⟨.seq (.send 0 (.lit (.int 3))) (.seq .tick (.send 0 (.lit (.int 4)))), [0], []⟩,
      ⟨.seq (.recv 0 1) (.recv 0 0), [], [0]⟩], input := fun _ => [] }

-- `y = 3`, `x = 4`, the reader at time `2`; the script `[(3, 0), (4, 1)]`.
#eval display layout ((buffer.load layout fun _ => .int 0).run 1000)

/-- A pipeline: `(c! 1. c! 2) || (c?. d! c+10. c?. d! c+10) || (d?. x:= d. d?. y:= d)`. -/
def pipeline : SNet :=
  { procs := [⟨.seq (.send 0 (.lit (.int 1))) (.send 0 (.lit (.int 2))), [0], []⟩,
      ⟨.seq (.recv 0 0) (.seq (.send 1 (.bin .add (.var 0) (.lit (.int 10))))
        (.seq (.recv 0 0) (.send 1 (.bin .add (.var 0) (.lit (.int 10)))))), [1], [0]⟩,
      ⟨.seq (.recv 1 0) (.recv 1 1), [], [1]⟩], input := fun _ => [] }

-- The last process has `x = 11`, `y = 12` at time `2`.
#eval display layout ((pipeline.load layout fun _ => .int 0).run 1000)

end Demo

end LaPToP.ProgramTheory.CompileNet
