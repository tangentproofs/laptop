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
is a chunk, communication is communication, and the control structure stays. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Stmt.toNP : Stmt → NProc ℕ Value
  | .ok => .act .ok
  | .assign x e => .act (Lang.assign x e)
  | .tick => .act .tick
  | .seq p q => .seq p.toNP q.toNP
  | .cond c p q => .cond c.test p.toNP q.toNP
  | .loop c p => .loop c.test p.toNP
  | .send ch e => .send ch e.eval
  | .recv ch x => .recv ch x

/-- A process: its statement, and the channels it writes and reads. -/
structure SProc where
  /-- The body. -/
  body : Stmt
  /-- The channels it writes. -/
  outs : List ℕ
  /-- The channels it reads. -/
  ins : List ℕ

/-- A network of statements, and the scripts the environment supplies. -/
structure SNet where
  /-- The processes. -/
  procs : List SProc
  /-- The input. -/
  input : Scripts Value

/-- The network the network machine runs. -/
def SNet.toNet (net : SNet) : Net ℕ Value :=
  ⟨fun _ => .act .ok, net.procs.map fun pr => ⟨pr.body.toNP, pr.outs, pr.ins⟩, net.input⟩

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
assigned or input having a cell, and every time fitting. -/
inductive SAct (L : Layout) (pr : SProc) :
    Scripts Value → List Stmt × PSt ℕ Value → List Stmt × PSt ℕ Value → Scripts Value → Prop
  /-- `ok`. -/
  | ok {Λ ks st} : SAct L pr Λ (.ok :: ks, st) (ks, st) Λ
  /-- `x:= e`. -/
  | assign {Λ ks st x e} : x < L.n → Fits L st.mem e →
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
      TFits (max st.t (m.2 + 1)) →
      SAct L pr Λ (.recv ch x :: ks, st) (ks, st.received ch x m) Λ

/-- **A step of the network, in 32 bits**: one process acts. -/
inductive SStep (L : Layout) (net : SNet) : SCfg → SCfg → Prop
  | mk {c : SCfg} {i : ℕ} {pr : SProc} {a b : List Stmt × PSt ℕ Value} {Λ : Scripts Value} :
      net.procs[i]? = some pr → c.ps[i]? = some a → SAct L pr c.L a b Λ →
      SStep L net c ⟨c.ps.set i b, Λ⟩

/-- An action in 32 bits is an action of the network machine. -/
theorem SAct.act {L : Layout} {net : SNet} {i : ℕ} {pr : SProc} (hpr : net.procs[i]? = some pr)
    {Λ Λ' : Scripts Value} {a b : List Stmt × PSt ℕ Value} (h : SAct L pr Λ a b Λ') :
    Act net.toNet i Λ ⟨a.1.map Stmt.toNP, a.2⟩ ⟨b.1.map Stmt.toNP, b.2⟩ Λ' := by
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

/-- A step in 32 bits is a step of the network machine. -/
theorem SStep.mstep {L : Layout} {net : SNet} {c c' : SCfg} (h : SStep L net c c') :
    MStep net.toNet c.toM c'.toM := by
  obtain ⟨hpr, ha, hact⟩ := h
  have := MStep.mk (net := net.toNet) (c := c.toM) (by simp [SCfg.toM, ha]) (hact.act hpr)
  simpa [SCfg.toM, List.map_set] using this

/-- A run in 32 bits is a run of the network machine. -/
theorem reach_of_sSteps {L : Layout} {net : SNet} {c c' : SCfg}
    (h : ReflTransGen (SStep L net) c c') : ReflTransGen (MStep net.toNet) c.toM c'.toM := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail hs.mstep

/-! ### Code that continues -/

/-- What is left for a process to do, laid out in memory `m` from `a`: the
statements one after another, perhaps reached through jumps, ending at `hl`. -/
inductive Cont (L : Layout) (m : ℕ → UInt8) : List Stmt → ℕ → Prop
  /-- Nothing is left: `hl`. -/
  | nil {a : ℕ} : 256 ≤ a → a < L.base → m a = 0xFF → Cont L m [] a
  /-- A statement's code, and what follows it. -/
  | cons {p : Stmt} {ks : List Stmt} {a : ℕ} : 256 ≤ a → a + slen L p ≤ L.base →
      sdepth p ≤ STACKSZ → CodeAt m a (scode L a p) → Cont L m ks (a + slen L p) →
      Cont L m (p :: ks) a
  /-- A jump to it. -/
  | jump {ks : List Stmt} {a b : ℕ} : 256 ≤ a → a + 5 ≤ L.base → CodeAt m a (jmTo b) →
      Cont L m ks b → Cont L m ks a

/-- What is left, without a jump first. -/
inductive Direct (L : Layout) (m : ℕ → UInt8) : List Stmt → ℕ → Prop
  /-- Nothing is left: `hl`. -/
  | nil {a : ℕ} : 256 ≤ a → a < L.base → m a = 0xFF → Direct L m [] a
  /-- A statement's code, and what follows it. -/
  | cons {p : Stmt} {ks : List Stmt} {a : ℕ} : 256 ≤ a → a + slen L p ≤ L.base →
      sdepth p ≤ STACKSZ → CodeAt m a (scode L a p) → Cont L m ks (a + slen L p) →
      Direct L m (p :: ks) a

theorem Cont.bounds {L : Layout} {m : ℕ → UInt8} {ks : List Stmt} {a : ℕ} (h : Cont L m ks a) :
    256 ≤ a ∧ a ≤ L.base := by
  cases h with
  | nil h₁ h₂ _ => exact ⟨h₁, by omega⟩
  | cons h₁ h₂ _ _ _ => exact ⟨h₁, by omega⟩
  | jump h₁ h₂ _ _ => exact ⟨h₁, by omega⟩

theorem Direct.cont {L : Layout} {m : ℕ → UInt8} {ks : List Stmt} {a : ℕ} (h : Direct L m ks a) :
    Cont L m ks a := by
  cases h with
  | nil h₁ h₂ h₃ => exact .nil h₁ h₂ h₃
  | cons h₁ h₂ h₃ h₄ h₅ => exact .cons h₁ h₂ h₃ h₄ h₅

/-- What is left survives writes above the code. -/
theorem Cont.mono {L : Layout} {m m' : ℕ → UInt8} (hm : ∀ i < L.base, m' i = m i)
    {ks : List Stmt} {a : ℕ} (h : Cont L m ks a) : Cont L m' ks a := by
  induction h with
  | nil h₁ h₂ h₃ => exact .nil h₁ h₂ (by rw [hm _ h₂]; exact h₃)
  | cons h₁ h₂ h₃ h₄ _ ih =>
    exact .cons h₁ h₂ h₃ (h₄.mono hm (by rw [length_scode]; exact h₂)) ih
  | jump h₁ h₂ h₃ _ ih => exact .jump h₁ h₂ (h₃.mono hm (by simpa using h₂)) ih

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
      (by rw [ioCmd_of_notIo hn]; simp)]
    simp

/-- Follow the jumps before what is left. -/
theorem follow (L : Layout) (hL : L.Ok) {m : ℕ → UInt8} {ks : List Stmt} {a : ℕ}
    (hc : Cont L m ks a) : ∀ s, high s = m → WF s → Running s → getIP s = a →
      ∃ s', Steps s s' ∧ Same s s' ∧ WF s' ∧ dstack s' = dstack s ∧ Direct L m ks (getIP s') := by
  induction hc with
  | nil h₁ h₂ h₃ =>
    intro s hm hw hr hip
    exact ⟨s, .refl, Same.refl s, hw, rfl, hip ▸ .nil h₁ h₂ h₃⟩
  | cons h₁ h₂ h₃ h₄ h₅ =>
    intro s hm hw hr hip
    exact ⟨s, .refl, Same.refl s, hw, rfl, hip ▸ .cons h₁ h₂ h₃ h₄ h₅⟩
  | @jump ks a b h₁ h₂ h₃ hcb ih =>
    intro s hm hw hr hip
    have hb := hcb.bounds
    have hJ : CodeAt (high s) (getIP s) (jmTo b) := by rw [hm, hip]; exact h₃
    obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_jm' hL hw (by omega) (by omega) hJ hb.1 hb.2
    obtain ⟨s', r', sm', w', d', hd'⟩ := ih (step s) (by rw [sm₁.high, hm]) w₁
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
        else w.chans c, w.rd⟩ := rfl

/-- **Send** in the swarm: with the value, the channel and `'s'` on the stack at
an `io`, the message goes on the channel's script, stamped with the clock. -/
theorem swarm_send {w : Swarm} {i : ℕ} {s : State} {v : UInt32} {ch : ℕ}
    (hi : w.ms[i]? = some s) (hw : WF s) (hr : Running s) (hlo : 256 ≤ getIP s)
    (hhi : getIP s + 1 < MAXBYTE) (hop : high s (getIP s) = 0xFD)
    (hd : dstack s = [v, UInt32.ofNat ch, SEND]) (hch : ch < 2 ^ 32) :
    ∃ s', w.stepAt i = some ⟨w.ms.set i s',
        fun c => if c = ch then w.chans c ++ [(v, getClk s)] else w.chans c, w.rd⟩ ∧
      WF s' ∧ getIP s' = getIP s + 1 ∧ dstack s' = [] ∧ Same s s' := by
  have hio : ioCmd s = some SEND := ioCmd_eq (xs := [v, UInt32.ofNat ch]) hlo hop (by simpa using hd)
  rw [Swarm.stepAt_send hi ((running_iff _).mpr hr) hio]
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
        w.rd.set i fun c => if c = ch then (w.rd.getD i fun _ => 0) ch + 1
          else (w.rd.getD i fun _ => 0) c⟩ := by
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
  wf : WF s
  run : Running s
  stack : dstack s = []
  cont : Cont L (high s) ks (getIP s)
  vars : VarsOk L (high s) st.mem
  clk : getClk s = encT st.t
  tfit : TFits st.t
  rd : ∀ c, r c = st.r c

theorem Direct.cons_inv {L : Layout} {m : ℕ → UInt8} {p : Stmt} {ks : List Stmt} {a : ℕ}
    (h : Direct L m (p :: ks) a) : 256 ≤ a ∧ a + slen L p ≤ L.base ∧ sdepth p ≤ STACKSZ ∧
      CodeAt m a (scode L a p) ∧ Cont L m ks (a + slen L p) := by
  cases h with
  | cons h₁ h₂ h₃ h₄ h₅ => exact ⟨h₁, h₂, h₃, h₄, h₅⟩

/-- **The machine does a process's step** that is not communication. -/
theorem machine_sim (L : Layout) (hL : L.Ok) {pr : SProc} {Λ Λ' : Scripts Value}
    {a b : List Stmt × PSt ℕ Value} (h : SAct L pr Λ a b Λ')
    (hsend : ∀ ch e ks, a.1 ≠ .send ch e :: ks) (hrecv : ∀ ch x ks, a.1 ≠ .recv ch x :: ks)
    {s : State} {r : ℕ → ℕ} (hp : PRel L a.1 a.2 s r) (hd : Direct L (high s) a.1 (getIP s)) :
    ∃ s', Steps s s' ∧ PRel L b.1 b.2 s' r := by
  have hb := hL.2
  cases h with
  | @ok ks st =>
    obtain ⟨-, -, -, -, hk⟩ := hd.cons_inv
    exact ⟨s, .refl, ⟨hp.wf, hp.run, hp.stack, by simpa [slen] using hk, hp.vars, hp.clk, hp.tfit,
      hp.rd⟩⟩
  | @assign ks st x e hx hf =>
    obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
    obtain ⟨s', r', w', run', i', d', v', k'⟩ := assign_runs L hL hx hf s (getIP s)
      ⟨hp.wf, hp.run, rfl, h₁, h₂, h₄, hp.vars, hp.stack, h₃⟩
    refine ⟨s', r', ⟨w', run', d', ?_, v', by rw [k'.clk]; exact hp.clk, hp.tfit, hp.rd⟩⟩
    rw [i']; exact hk.mono k'.low
  | @tick ks st hfit =>
    obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
    obtain ⟨s', r', w', run', i', d', c', hi', -, -⟩ := tick_runs (L := L) hp.wf hp.run h₁
      (by simp [slen] at h₂; omega) h₄ hp.stack hp.clk hfit
    refine ⟨s', r', ⟨w', run', d', by rw [hi', i']; simpa [slen] using hk,
      by rw [hi']; exact hp.vars, c', hfit, hp.rd⟩⟩
  | @seq ks st p q =>
    obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
    simp only [scode] at h₄
    rw [CodeAt.append, length_scode] at h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    exact ⟨s, .refl, ⟨hp.wf, hp.run, hp.stack, .cons h₁ (by omega) (by omega) h₄.1
      (.cons (by omega) (by omega) (by omega) h₄.2 (by rwa [Nat.add_assoc])), hp.vars, hp.clk,
      hp.tfit, hp.rd⟩⟩
  | @condT ks st c p q hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    have hcode := h₄; simp only [scode] at hcode
    obtain ⟨s', r', w', run', i', d', sm'⟩ := run_cond (b := true) hL hf hc hp.wf hp.run rfl h₁
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) hp.vars
      hp.stack (by omega)
    simp only [ite_true] at i'
    refine ⟨s', r', ⟨w', run', d', ?_, by rw [sm'.high]; exact hp.vars,
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd⟩⟩
    rw [i', sm'.high]
    refine .cons (by omega) (by omega) (by omega) hP (.jump (by omega) (by omega) hJ' ?_)
    convert hk using 1; omega
  | @condF ks st c p q hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    have hcode := h₄; simp only [scode] at hcode
    obtain ⟨s', r', w', run', i', d', sm'⟩ := run_cond (b := false) hL hf hc hp.wf hp.run rfl h₁
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) hp.vars
      hp.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i'
    refine ⟨s', r', ⟨w', run', d', ?_, by rw [sm'.high]; exact hp.vars,
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd⟩⟩
    rw [i', sm'.high]
    refine .jump (by omega) (by omega) hJ (.cons (by omega) (by omega) (by omega) hQ ?_)
    convert hk using 1; omega
  | @loopT ks st c p hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
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
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd⟩⟩
    rw [i', sm'.high]
    exact .cons (by omega) (by omega) (by omega) hP
      (.jump (by omega) (by omega) hJ' (.cons h₁ h₂' h₃' h₄ hk))
  | @loopF ks st c p hf hc =>
    obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
    obtain ⟨hE, hT, hJ, hP, hJ'⟩ := loop_code h₄
    simp only [slen, sdepth] at h₂ h₃ hk
    have hcode := h₄; simp only [scode] at hcode
    obtain ⟨s', r', w', run', i', d', sm'⟩ := run_cond (b := false) hL hf hc hp.wf hp.run rfl h₁
      (rest := jmTo _ ++ scode L _ p ++ jmTo (getIP s))
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) hp.vars
      hp.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i'
    refine ⟨s', r', ⟨w', run', d', ?_, by rw [sm'.high]; exact hp.vars,
      by rw [sm'.clk]; exact hp.clk, hp.tfit, hp.rd⟩⟩
    rw [i', sm'.high]
    refine .jump (by omega) (by omega) hJ ?_
    convert hk using 1; omega
  | send => exact (hsend _ _ _ rfl).elim
  | recv => exact (hrecv _ _ _ rfl).elim

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
  len : w.ms.length = c.ps.length
  rdlen : w.rd.length = c.ps.length
  proc : ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State}, c.ps[i]? = some (ks, st) →
    w.ms[i]? = some s → PRel L ks st s (w.rd.getD i fun _ => 0)
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
    (hp : PRel L (.send ch e :: ks) st s r) (hd : Direct L (high s) (.send ch e :: ks) (getIP s))
    (hf : Fits L st.mem e) (hch : ch < 2 ^ 32) :
    ∃ s', Swarm.Steps w ⟨w.ms.set i s',
        fun c => if c = ch then w.chans c ++ [(enc (e.eval st.mem), encT st.t)] else w.chans c,
        w.rd⟩ ∧ PRel L ks (st.sent ch) s' r := by
  have hb := hL.2
  obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
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
    (by rw [d₃, d₂, d₁, hp.stack]; rfl) hch
  have hsm := sm₁.trans (sm₂.trans (sm₃.trans sm'))
  refine ⟨s', ?_, ⟨w', hsm.running hp.run, d', ?_, by rw [hsm.high]; exact hp.vars,
    by rw [hsm.clk]; exact hp.clk, hp.tfit, hp.rd⟩⟩
  · refine hlift.tail ⟨i, ?_⟩
    rw [hst]
    simp only [List.set_set]
    rw [(sm₁.trans (sm₂.trans sm₃)).clk, hp.clk]
  · rw [i', i₃, i₂, i₁, hsm.high]
    convert hk using 1
    simp [slen]; omega

/-- **Receive**, in the swarm and then on the machine. -/
theorem recv_sim (L : Layout) (hL : L.Ok) {w : Swarm} {i : ℕ} {s : State} {ch x : ℕ}
    {ks : List Stmt} {st : PSt ℕ Value} {m : Msg Value} {Λ : Scripts Value} (hi : w.ms[i]? = some s)
    (hp : PRel L (.recv ch x :: ks) st s (w.rd.getD i fun _ => 0))
    (hd : Direct L (high s) (.recv ch x :: ks) (getIP s)) (hch : ch < 2 ^ 32)
    (hchan : w.chans ch = encS (Λ ch)) (hm : (Λ ch)[st.r ch]? = some m) (hx : x < L.n)
    (hfit : TFits (max st.t (m.2 + 1))) :
    ∃ s', Swarm.Steps w ⟨w.ms.set i s', w.chans,
        w.rd.set i fun c => if c = ch then (w.rd.getD i fun _ => 0) ch + 1
          else (w.rd.getD i fun _ => 0) c⟩ ∧
      PRel L ks (st.received ch x m)
        s' (fun c => if c = ch then (w.rd.getD i fun _ => 0) ch + 1 else (w.rd.getD i fun _ => 0) c) := by
  have hb := hL.2
  have hlt : i < w.ms.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨h₁, h₂, h₃, h₄, hk⟩ := hd.cons_inv
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
  refine ⟨step (step s₃), ?_, ⟨w₅, ⟨st₅.trans run₄.1, db₅.trans run₄.2⟩, d₅, ?_, ?_, ?_, hfit, ?_⟩⟩
  · refine (hlift.tail ⟨i, hstep⟩).trans ?_
    have := swarm_lift (w := ⟨w.ms.set i s₃, w.chans, w.rd.set i fun c => if c = ch then
      (w.rd.getD i fun _ => 0) ch + 1 else (w.rd.getD i fun _ => 0) c⟩) (i := i) (s := s₃)
      (by simp [List.getElem?_set_self hlt]) hrun₂
    simpa using this
  · rw [hi₅, sm₄.high, h₃', sm₂.high, sm₁.high, i₅, i₄, i₃, i₂, i₁]
    refine Cont.mono (fun j hj => ?_) (by convert hk using 1; simp [slen])
    unfold writeWord Layout.addr
    simp [show j ≠ L.base + 4 * x by omega, show j ≠ L.base + 4 * x + 1 by omega,
      show j ≠ L.base + 4 * x + 2 by omega, show j ≠ L.base + 4 * x + 3 by omega]
  · rw [hi₅, sm₄.high, h₃', sm₂.high, sm₁.high]
    exact varsOk_write hp.vars
  · rw [hclk₅, sm₄.clk, c₃, (sm₁.trans sm₂).clk, hp.clk]
    exact later_encT hp.tfit hfit
  · intro c
    simp only [PSt.received, Function.update_apply]
    by_cases hc : c = ch
    · subst hc; simp [hp.rd]
    · simp [hc, hp.rd]

end LaPToP.ProgramTheory.CompileNet
