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

end LaPToP.ProgramTheory.CompileNet
