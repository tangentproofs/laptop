import LaPToP.ProgramTheory.CompileNetDeadlock

/-!
# `√c` on the swarm: settling a check

A check `x:= √c` whose message is there is a step of the network in 32 bits
(`SAct.check`), and the swarm does it (`check_sim`). A check whose message is
not there is settled by the network machine once no process can send before
now (`Network.Act.check` under `MCfg.Quiet`), to false; the runner of the swarm
settles one once no machine can move (`B4.Swarm.settle`): the machine waiting at
a check with the earliest clock, the first of those, answers false.

The runs here take that order: a step of a process (`SStep`), or, when every
process has finished or waits for a message that is not there
(`SNet.Pending`), the settling of the earliest check (`QStep.settle`), which
is a step of the network machine (`QStep.msteps`). The swarm runs to the same
point and its runner settles the same check (`settle_sim`), so every such run
of the network is a run of the swarm with its runner (`swarm_simulatesK`), and
when every process finishes, every machine halts with its process's final
state (`swarm_correctK`), a behaviour of the book's semantics
(`swarm_bookK`).

To relate the two while machines wait, a machine may stand where its process
is (`PRel`), or have run on to the `io` of the input or check its process
waits at, or have halted when its process has finished (`MRel`).
-/

namespace LaPToP.ProgramTheory.CompileNet

open B4 Relation
open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.Interpreter.Network
open LaPToP.ProgramTheory.CompileB4

/-! ### Machines that wait -/

/-- A machine that has stopped for its process: run on to the `io` of the
input or the check the process is at, or halted when the process has
finished. -/
inductive Parked (L : Layout) : List Stmt → PSt ℕ Value → State → (ℕ → ℕ) → Prop
  /-- At the `io` of an input. -/
  | recv {ch x : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State} {r : ℕ → ℕ} :
      PRel L (.recv ch x :: ks) st s r → Direct L (high s) (cstack s) (.recv ch x :: ks) (getIP s) →
      Parked L (.recv ch x :: ks) st (step (step s)) r
  /-- At the `io` of a check. -/
  | check {ch x : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State} {r : ℕ → ℕ} :
      PRel L (.check ch x :: ks) st s r → Direct L (high s) (cstack s) (.check ch x :: ks) (getIP s) →
      Parked L (.check ch x :: ks) st (step (step s)) r
  /-- Halted. -/
  | halt {st : PSt ℕ Value} {s : State} {r : ℕ → ℕ} : Halted L st s → Parked L [] st s r

/-- **A machine and its process**: the machine where the process is, or
stopped for it. -/
inductive MRel (L : Layout) (ks : List Stmt) (st : PSt ℕ Value) (s : State) (r : ℕ → ℕ) : Prop
  /-- Where the process is. -/
  | at : PRel L ks st s r → MRel L ks st s r
  /-- Stopped for it. -/
  | park : Parked L ks st s r → MRel L ks st s r

/-- **The swarm and the network agree**, machines allowed to wait. -/
structure RelK (L : Layout) (c : SCfg) (w : Swarm) : Prop where
  /-- A machine for each process. -/
  len : w.ms.length = c.ps.length
  /-- Cursors for each process. -/
  rdlen : w.rd.length = c.ps.length
  /-- Each process and its machine agree. -/
  proc : ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State}, c.ps[i]? = some (ks, st) →
    w.ms[i]? = some s → MRel L ks st s (w.rd.getD i fun _ => 0)
  /-- The channels hold the scripts. -/
  chans : ∀ ch, w.chans ch = encS (c.L ch)

theorem Rel.relK {L : Layout} {c : SCfg} {w : Swarm} (hr : Rel L c w) : RelK L c w :=
  ⟨hr.len, hr.rdlen, fun hc hm => .at (hr.proc hc hm), hr.chans⟩

theorem RelK.machine {L : Layout} {c : SCfg} {w : Swarm} (hr : RelK L c w) {i : ℕ}
    {ks : List Stmt} {st : PSt ℕ Value} (ha : c.ps[i]? = some (ks, st)) :
    ∃ s, w.ms[i]? = some s ∧ MRel L ks st s (w.rd.getD i fun _ => 0) := by
  have hlt : i < w.ms.length := hr.len ▸ (List.getElem?_eq_some_iff.mp ha).1
  exact ⟨_, List.getElem?_eq_getElem hlt, hr.proc ha (List.getElem?_eq_getElem hlt)⟩

/-- Replace one machine, its cursors and one process. -/
theorem RelK.setRd {L : Layout} {c : SCfg} {w : Swarm} (hr : RelK L c w) {i : ℕ}
    (hi : i < c.ps.length) {ks : List Stmt} {st : PSt ℕ Value} {s : State} {Λ : Scripts Value}
    {r : ℕ → ℕ} {chans : ℕ → List B4.Msg} (hp : MRel L ks st s r) (hch : ∀ ch, chans ch = encS (Λ ch)) :
    RelK L ⟨c.ps.set i (ks, st), Λ⟩ ⟨w.ms.set i s, chans, w.rd.set i r, w.owner⟩ := by
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

theorem rd_set_self {w : Swarm} {i : ℕ} (h : i < w.rd.length) :
    w.rd.set i (w.rd.getD i fun _ => 0) = w.rd := by
  apply List.ext_getElem?; intro j
  by_cases hij : i = j
  · subst hij
    rw [List.getElem?_set_self h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
  · rw [List.getElem?_set_ne hij]

/-- Replace one machine and one process, keeping the cursors. -/
theorem RelK.set {L : Layout} {c : SCfg} {w : Swarm} (hr : RelK L c w) {i : ℕ}
    (hi : i < c.ps.length) {ks : List Stmt} {st : PSt ℕ Value} {s : State} {Λ : Scripts Value}
    (hp : MRel L ks st s (w.rd.getD i fun _ => 0)) (hch : ∀ ch, w.chans ch = encS (Λ ch)) :
    RelK L ⟨c.ps.set i (ks, st), Λ⟩ { w with ms := w.ms.set i s } := by
  have := hr.setRd hi hp hch
  rw [rd_set_self (hr.rdlen ▸ hi)] at this
  exact this

/-! ### A step of a process -/

/-- **A step of a process, on its machine where it is**: some steps of the
swarm, which change that machine, its cursors and the channels. -/
theorem act_sim (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {w : Swarm} {i : ℕ} {pr : SProc} {s : State} {ks : List Stmt} {st : PSt ℕ Value}
    {b : List Stmt × PSt ℕ Value} {Λ Λ' : Scripts Value}
    (hpr : net.procs[i]? = some pr) (hs : w.ms[i]? = some s) (hrd : i < w.rd.length)
    (hp : PRel L ks st s (w.rd.getD i fun _ => 0)) (hch : ∀ ch, w.chans ch = encS (Λ ch))
    (hact : SAct L pr Λ (ks, st) b Λ') (hown : ∀ {ch : ℕ}, ch ∈ pr.outs → w.owner ch = some i) :
    ∃ s' chans r, Swarm.Steps w ⟨w.ms.set i s', chans, w.rd.set i r, w.owner⟩ ∧
      PRel L b.1 b.2 s' r ∧ ∀ ch, chans ch = encS (Λ' ch) := by
  have hlt : i < w.ms.length := (List.getElem?_eq_some_iff.mp hs).1
  have hprm : pr ∈ net.procs := List.mem_of_getElem? hpr
  obtain ⟨s₁, hw₁, r₁, hp₁, hd₁⟩ := Rel.follow L hL hs hp
  have hs₁ : ({ w with ms := w.ms.set i s₁ } : Swarm).ms[i]? = some s₁ := by
    simp [List.getElem?_set_self hlt]
  have local_case : ∀ {b' : List Stmt × PSt ℕ Value}, SAct L pr Λ (ks, st) b' Λ →
      (∀ ch e ks', ks ≠ .send ch e :: ks') → (∀ ch x ks', ks ≠ .recv ch x :: ks') →
      (∀ ch x ks', ks ≠ .check ch x :: ks') →
      ∃ s' chans r, Swarm.Steps w ⟨w.ms.set i s', chans, w.rd.set i r, w.owner⟩ ∧
        PRel L b'.1 b'.2 s' r ∧ ∀ ch, chans ch = encS (Λ ch) := by
    intro b' hb' hs' hr' hk'
    obtain ⟨s₂, r₂, hp₂, -, -, -⟩ := machine_sim L hL hb' hs' hr' hk' hp₁ hd₁
    refine ⟨s₂, w.chans, w.rd.getD i fun _ => 0, ?_, hp₂, hch⟩
    rw [rd_set_self hrd]
    have := swarm_lift hs₁ r₂; simp at this; exact hw₁.trans (by simpa using this)
  cases hact with
  | ok => exact local_case .ok (by simp) (by simp) (by simp)
  | assign hx hax hf => exact local_case (.assign hx hax hf) (by simp) (by simp) (by simp)
  | tick hfit => exact local_case (.tick hfit) (by simp) (by simp) (by simp)
  | seq => exact local_case .seq (by simp) (by simp) (by simp)
  | condT hf hc => exact local_case (.condT hf hc) (by simp) (by simp) (by simp)
  | condF hf hc => exact local_case (.condF hf hc) (by simp) (by simp) (by simp)
  | loopT hf hc => exact local_case (.loopT hf hc) (by simp) (by simp) (by simp)
  | loopF hf hc => exact local_case (.loopF hf hc) (by simp) (by simp) (by simp)
  | call hk hcl hfr => exact local_case (.call hk hcl hfr) (by simp) (by simp) (by simp)
  | ret => exact local_case .ret (by simp) (by simp) (by simp)
  | scope hx hax hf hfr => exact local_case (.scope hx hax hf hfr) (by simp) (by simp) (by simp)
  | store hfi hf => exact local_case (.store hfi hf) (by simp) (by simp) (by simp)
  | fill hx hvs hl hf => exact local_case (.fill hx hvs hl hf) (by simp) (by simp) (by simp)
  | restore => exact local_case .restore (by simp) (by simp) (by simp)
  | @send ks' _ ch e hchi hf =>
    obtain ⟨s₂, hw₂, hp₂⟩ := send_sim L hL hs₁ hp₁ hd₁ hf (hchb pr hprm ch (.inl hchi))
      (hown hchi)
    refine ⟨s₂, fun c' => if c' = ch then w.chans c' ++ [(enc (e.eval st.mem), encT st.t)]
        else w.chans c', w.rd.getD i fun _ => 0, ?_, by simpa using hp₂, ?_⟩
    · rw [rd_set_self hrd]; exact hw₁.trans (by simpa using hw₂)
    · intro c'
      by_cases hc : c' = ch
      · subst hc; simp [hch, encS]
      · simp [hc, hch]
  | @recv ks' _ ch x m hchi hm hx hax hfit =>
    obtain ⟨s₂, hw₂, hp₂⟩ := recv_sim L hL (Λ := Λ) hs₁ (by simpa using hp₁) hd₁
      (hchb pr hprm ch (.inr hchi)) (by simpa using hch ch) hm hx hax hfit
    exact ⟨s₂, w.chans, _, hw₁.trans (by simpa using hw₂), hp₂, hch⟩
  | @check ks' _ ch x m hchi hm hx hax hτ =>
    obtain ⟨s₂, hw₂, hp₂⟩ := check_sim L hL (Λ := Λ) hs₁ (by simpa using hp₁) hd₁
      (hchb pr hprm ch (.inr hchi)) (by simpa using hch ch) hm hx hax hτ
    refine ⟨s₂, w.chans, w.rd.getD i fun _ => 0, ?_, by simpa using hp₂, hch⟩
    rw [rd_set_self hrd]; exact hw₁.trans (by simpa using hw₂)

/-- **One step of the network, in 32 bits, is some steps of the swarm**, with
machines allowed to wait. -/
theorem sim_stepK (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {c c' : SCfg} (h : SStep L net c c') {w : Swarm} (hr : RelK L c w)
    (hown : ∀ {i : ℕ} {pr : SProc} {ch : ℕ}, net.procs[i]? = some pr → ch ∈ pr.outs →
      w.owner ch = some i) :
    ∃ w', Swarm.Steps w w' ∧ w'.owner = w.owner ∧ RelK L c' w' := by
  obtain ⟨hpr, ha, hact⟩ := h
  rename_i i pr a b Λ
  obtain ⟨ks, st⟩ := a
  have hlt : i < c.ps.length := (List.getElem?_eq_some_iff.mp ha).1
  have hrd : i < w.rd.length := hr.rdlen ▸ hlt
  have hprm : pr ∈ net.procs := List.mem_of_getElem? hpr
  obtain ⟨s, hs, hm⟩ := hr.machine ha
  rcases hm with hp | hk
  · obtain ⟨s', chans, r, hw, hp', hch⟩ := act_sim L hL hchb hpr hs hrd hp hr.chans hact
      (hown hpr)
    exact ⟨_, hw, rfl, hr.setRd hlt (.at hp') hch⟩
  · cases hk with
    | @recv ch x ks' st s₀ r hp hd =>
      cases hact with
      | @recv _ _ _ _ m hchi hm hx hax hfit =>
        obtain ⟨s₂, hw₂, hp₂⟩ := recv_sim_at L hL (Λ := c.L) hp hd hs
          (hchb pr hprm ch (.inr hchi)) (hr.chans ch) hm hx hax hfit
        exact ⟨_, hw₂, rfl, hr.setRd hlt (.at hp₂) hr.chans⟩
    | @check ch x ks' st s₀ r hp hd =>
      cases hact with
      | @check _ _ _ _ m hchi hm hx hax hτ =>
        obtain ⟨s₂, hw₂, hp₂⟩ := check_sim_at L hL (Λ := c.L) hp hd hs
          (hchb pr hprm ch (.inr hchi)) (hr.chans ch) hm hx hax hτ
        exact ⟨_, hw₂, rfl, hr.set hlt (.at hp₂) hr.chans⟩
    | halt => cases hact

/-! ### Settling a check -/

/-- **Everything waits**: every process has finished, or waits, at an input or
a check, on one of its channels whose script has no message at its read
cursor. -/
def SNet.Pending (net : SNet) (c : SCfg) : Prop :=
  ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) → ks = [] ∨
    ∃ pr ch x ks', net.procs[i]? = some pr ∧ ch ∈ pr.ins ∧
      (ks = .recv ch x :: ks' ∨ ks = .check ch x :: ks') ∧ (c.L ch)[st.r ch]? = none

/-- Process `i`, at time `t`, is the one the runner settles: no process at a
check has an earlier time, and none before it the same. -/
def SCfg.Earliest (c : SCfg) (i : ℕ) (t : ℕ∞) : Prop :=
  ∀ {j ch x : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[j]? = some (.check ch x :: ks, st) →
    t ≤ st.t ∧ (j < i → t < st.t)

theorem SCfg.Earliest.unique {c : SCfg} {i j : ℕ} {chi xi chj xj : ℕ} {ki kj : List Stmt}
    {sti stj : PSt ℕ Value} (hi : c.ps[i]? = some (.check chi xi :: ki, sti))
    (hj : c.ps[j]? = some (.check chj xj :: kj, stj)) (ei : c.Earliest i sti.t)
    (ej : c.Earliest j stj.t) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd (ei hj).1 (not_le.mpr ((ej hi).2 h))
  · exact h
  · exact absurd (ej hi).1 (not_le.mpr ((ei hj).2 h))

/-- **A step of the network, in 32 bits, with checks settled as the runner
does**: a step of a process, or, when everything waits, the earliest check
answered false. -/
inductive QStep (L : Layout) (net : SNet) : SCfg → SCfg → Prop
  /-- A step of a process. -/
  | step {c c' : SCfg} : SStep L net c c' → QStep L net c c'
  /-- The earliest check, settled. -/
  | settle {c : SCfg} {i ch x : ℕ} {ks : List Stmt} {st : PSt ℕ Value} :
      net.Pending c → c.ps[i]? = some (.check ch x :: ks, st) → c.Earliest i st.t → x < L.n →
      L.arrayAt x = none → QStep L net c ⟨c.ps.set i (ks, st.checked x (.bool false)), c.L⟩

/-- When everything waits, no process can send before the time of the
earliest check. -/
theorem quiet_of_pending {net : SNet} {c : SCfg} (hp : net.Pending c) {i ch x : ℕ}
    {ks : List Stmt} {st : PSt ℕ Value} (hi : c.ps[i]? = some (.check ch x :: ks, st))
    (he : c.Earliest i st.t) : c.toM.Quiet st.t := by
  intro pc hpc
  simp only [SCfg.toM, List.mem_map] at hpc
  obtain ⟨⟨ks', st'⟩, hmem, rfl⟩ := hpc
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hmem
  have hj' : c.ps[j]? = some (ks', st') := by rw [List.getElem?_eq_getElem hj, hje]
  rcases hp hj' with rfl | ⟨pr, ch', x', ks'', -, -, hk | hk, hnone⟩
  · exact .inl rfl
  · subst hk
    exact .inr (.inr ⟨ch', x', _, rfl, fun m hm => by simp [SCfg.toM, hnone] at hm⟩)
  · subst hk
    exact .inr (.inl (he hj').1)

/-- **A step settling a check is a step of the network machine.** -/
theorem QStep.msteps {L : Layout} {net : SNet} (hdefs : L.defs = net.defs) {c c' : SCfg}
    (h : QStep L net c c') : ReflTransGen (MStep net.toNet) c.toM c'.toM := by
  cases h with
  | step h => exact (h.msteps hdefs).to_reflTransGen
  | @settle i ch x ks st hp hi he hx ha =>
    rcases hp hi with h0 | ⟨pr, ch', x', ks', hpr, hin, hk | hk, hnone⟩
    · cases h0
    · cases hk
    · simp only [List.cons.injEq, Stmt.check.injEq] at hk
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hk
      have hpr' : net.toNet.procs[i]? = some ⟨pr.body.toNP, pr.outs, pr.ins⟩ := by
        simp [SNet.toNet, hpr]
      have hm : c.toM.ps[i]? = some ⟨.check ch x .bool :: ks.map Stmt.toNP, st⟩ := by
        simp [SCfg.toM, hi, Stmt.toNP]
      have hq := quiet_of_pending hp hi he
      refine .single ?_
      have hs := MStep.mk hm (Act.check (Q := c.toM.Quiet) (L := c.toM.L) (k := ks.map Stmt.toNP)
        (b := .bool) hpr' hin (.inr hq))
      have hrd : ready (c.toM.L ch) (st.r ch) st.t = false := by
        simp [SCfg.toM, ready, hnone]
      rw [hrd] at hs
      convert hs using 1
      simp [SCfg.toM, List.map_set]

theorem reach_of_qSteps {L : Layout} {net : SNet} (hdefs : L.defs = net.defs) {c c' : SCfg}
    (h : ReflTransGen (QStep L net) c c') : ReflTransGen (MStep net.toNet) c.toM c'.toM := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (hs.msteps hdefs)

/-! ### The swarm and its runner -/

/-- **A step of the swarm with its runner**: a step of a machine, or, when none
can move, the settling of a check. -/
inductive KStep : Swarm → Swarm → Prop
  /-- A step of a machine. -/
  | step {w w' : Swarm} : Swarm.Step w w' → KStep w w'
  /-- A check settled. -/
  | settle {w w' : Swarm} : Stuck w → w.settle = some w' → KStep w w'

theorem kSteps_of_steps {w w' : Swarm} (h : Swarm.Steps w w') : ReflTransGen KStep w w' := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (.step hs)

/-- **`Swarm.runK` runs the swarm with its runner.** -/
theorem runK_spec : ∀ (n : ℕ) (w : Swarm), ReflTransGen KStep w (Swarm.runK n w)
  | 0, w => .refl
  | n + 1, w => by
    simp only [Swarm.runK]
    obtain ⟨h₁, h₂⟩ := run_spec (n + 1) w
    split_ifs with hs
    · exact kSteps_of_steps h₁
    · split
      · rename_i w' hw'
        exact (kSteps_of_steps h₁).trans (.head (.settle (h₂ (by simpa using hs)) hw') (runK_spec n w'))
      · exact kSteps_of_steps h₁

/-! ### Machines run on to where they wait -/

/-- A machine stopped at the `io` of an input or a check. -/
theorem io_view (L : Layout) (hL : L.Ok) {p : Stmt} {ks : List Stmt} {st : PSt ℕ Value}
    {s : State} {r : ℕ → ℕ} {ch x : ℕ} {cmd : UInt32} (hp : PRel L (p :: ks) st s r)
    (hd : Direct L (high s) (cstack s) (p :: ks) (getIP s)) (hr : p ≠ .ret)
    (hs : ∀ y v, p ≠ .restore y v)
    (hcode : ∀ a, scode L a p = (0x97 :: le4 (UInt32.ofNat ch)) ++ ((0x97 :: le4 cmd) ++ ([0xFD] ++
      ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95]))))
    (hlen : slen L p = 17) (hdep : sdepth p = 2) :
    Running (step (step s)) ∧ ioCmd (step (step s)) = some cmd ∧
      (dpop (dpop (step (step s))).2).1 = UInt32.ofNat ch ∧ getClk (step (step s)) = encT st.t := by
  obtain ⟨-, hA₂, hst₂, -, sm₂, -⟩ := io_pre L hL hp hd hr hs hcode hlen hdep
  have hop : high (step (step s)) (getIP (step (step s))) = 0xFD := by
    simpa using hA₂.code 0 (by simp)
  obtain ⟨-, w₁, -, d₁, -⟩ := dpop_same _ [UInt32.ofNat ch] cmd hA₂.wf (by simpa using hst₂)
  obtain ⟨e₂, -, -, -, -⟩ := dpop_same _ [] (UInt32.ofNat ch) w₁ (by simpa using d₁)
  exact ⟨hA₂.run, ioCmd_eq (xs := [UInt32.ofNat ch]) hA₂.lo hop (by simpa using hst₂), e₂,
    by rw [sm₂.clk, hp.clk]⟩

theorem io_view_recv (L : Layout) (hL : L.Ok) {ks : List Stmt} {st : PSt ℕ Value}
    {s : State} {r : ℕ → ℕ} {ch x : ℕ} (hp : PRel L (.recv ch x :: ks) st s r)
    (hd : Direct L (high s) (cstack s) (.recv ch x :: ks) (getIP s)) :
    Running (step (step s)) ∧ ioCmd (step (step s)) = some RECV ∧
      (dpop (dpop (step (step s))).2).1 = UInt32.ofNat ch ∧ getClk (step (step s)) = encT st.t :=
  io_view L hL (x := x) hp hd (by simp) (by simp) (fun _ => by simp [scode, List.append_assoc])
    (by simp [slen]) (by simp [sdepth])

theorem io_view_check (L : Layout) (hL : L.Ok) {ks : List Stmt} {st : PSt ℕ Value}
    {s : State} {r : ℕ → ℕ} {ch x : ℕ} (hp : PRel L (.check ch x :: ks) st s r)
    (hd : Direct L (high s) (cstack s) (.check ch x :: ks) (getIP s)) :
    Running (step (step s)) ∧ ioCmd (step (step s)) = some CHECK ∧
      (dpop (dpop (step (step s))).2).1 = UInt32.ofNat ch ∧ getClk (step (step s)) = encT st.t :=
  io_view L hL (x := x) hp hd (by simp) (by simp) (fun _ => by simp [scode, List.append_assoc])
    (by simp [slen]) (by simp [sdepth])

theorem swarm_set_self {w : Swarm} {i : ℕ} {s : State} (h : w.ms[i]? = some s) :
    ({ w with ms := w.ms.set i s } : Swarm) = w := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  simp

/-- A machine whose process waits, or has finished, runs on to where it stops. -/
theorem park_one (L : Layout) (hL : L.Ok) {w : Swarm} {i : ℕ} {s : State} {ks : List Stmt}
    {st : PSt ℕ Value} {r : ℕ → ℕ} (hi : w.ms[i]? = some s) (hm : MRel L ks st s r)
    (hw : ks = [] ∨ ∃ ch x ks', ks = .recv ch x :: ks' ∨ ks = .check ch x :: ks') :
    ∃ s', Swarm.Steps w { w with ms := w.ms.set i s' } ∧ Parked L ks st s' r := by
  rcases hm with hp | hk
  · rcases hw with rfl | ⟨ch, x, ks', rfl | rfl⟩
    · obtain ⟨s', hw', hh⟩ := halt_one L hL hi hp
      exact ⟨s', hw', .halt hh⟩
    · obtain ⟨s₁, hw₁, -, hp₁, hd₁⟩ := Rel.follow L hL hi hp
      obtain ⟨hrun, -⟩ := io_pre L hL (ch := ch) (x := x) (cmd := RECV) hp₁ hd₁
        (by simp) (by simp) (fun _ => by simp [scode, List.append_assoc]) (by simp [slen])
        (by simp [sdepth])
      have := swarm_lift (w := { w with ms := w.ms.set i s₁ }) (i := i)
        (by simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]) hrun
      exact ⟨_, hw₁.trans (by simpa using this), .recv hp₁ hd₁⟩
    · obtain ⟨s₁, hw₁, -, hp₁, hd₁⟩ := Rel.follow L hL hi hp
      obtain ⟨hrun, -⟩ := io_pre L hL (ch := ch) (x := x) (cmd := CHECK) hp₁ hd₁
        (by simp) (by simp) (fun _ => by simp [scode, List.append_assoc]) (by simp [slen])
        (by simp [sdepth])
      have := swarm_lift (w := { w with ms := w.ms.set i s₁ }) (i := i)
        (by simp [List.getElem?_set_self (List.getElem?_eq_some_iff.mp hi).1]) hrun
      exact ⟨_, hw₁.trans (by simpa using this), .check hp₁ hd₁⟩
  · exact ⟨s, by rw [swarm_set_self hi]; exact .refl, hk⟩

/-- Run the machines on one by one, while everything waits. -/
theorem park_upto (L : Layout) (hL : L.Ok) {net : SNet} {c : SCfg} {w : Swarm} (hr : RelK L c w)
    (hpend : net.Pending c) (k : ℕ) :
    ∃ w', Swarm.Steps w w' ∧ w'.chans = w.chans ∧ w'.rd = w.rd ∧ w'.owner = w.owner ∧
      RelK L c w' ∧ ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State}, i < k →
        c.ps[i]? = some (ks, st) → w'.ms[i]? = some s → Parked L ks st s (w.rd.getD i fun _ => 0) := by
  induction k with
  | zero => exact ⟨w, .refl, rfl, rfl, rfl, hr, fun h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨w₁, r₁, c₁, d₁, o₁, h₁, p₁⟩ := ih
    by_cases hk : k < c.ps.length
    · have hck : c.ps[k]? = some (c.ps[k].1, c.ps[k].2) := by simp [hk]
      obtain ⟨s, hs, hm⟩ := h₁.machine hck
      have hw : c.ps[k].1 = [] ∨ ∃ ch x ks', c.ps[k].1 = .recv ch x :: ks' ∨
          c.ps[k].1 = .check ch x :: ks' := by
        rcases hpend hck with h | ⟨-, ch, x, ks', -, -, h, -⟩
        · exact .inl h
        · exact .inr ⟨ch, x, ks', h⟩
      obtain ⟨s', r', hp'⟩ := park_one L hL hs hm hw
      have hset : RelK L c { w₁ with ms := w₁.ms.set k s' } := by
        have := h₁.set hk (.park hp') h₁.chans
        have hc' : ({ ps := c.ps.set k (c.ps[k].1, c.ps[k].2), L := c.L } : SCfg) = c := by
          cases c; simp
        rwa [hc'] at this
      refine ⟨_, r₁.trans r', by simp [c₁], by simp [d₁], by simp [o₁], hset, fun {i ks st s''} hik hc hm' => ?_⟩
      by_cases hie : i = k
      · subst hie
        rw [hck] at hc; cases hc
        simp only [List.getElem?_set_self (h₁.len ▸ hk), Option.some.injEq] at hm'
        subst hm'; rw [← d₁]; exact hp'
      · simp only [List.getElem?_set_ne (Ne.symm hie)] at hm'
        exact p₁ (by omega) hc hm'
    · refine ⟨w₁, r₁, c₁, d₁, o₁, h₁, fun {i ks st s} hik hc hm => p₁ ?_ hc hm⟩
      have : i < c.ps.length := (List.getElem?_eq_some_iff.mp hc).1
      omega

/-- While everything waits, the swarm runs on to where no machine can move,
every machine stopped for its process. -/
theorem park_all (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {c : SCfg} {w : Swarm} (hr : RelK L c w) (hpend : net.Pending c) :
    ∃ w', Swarm.Steps w w' ∧ w'.owner = w.owner ∧ RelK L c w' ∧ Stuck w' ∧
      ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State}, c.ps[i]? = some (ks, st) →
        w'.ms[i]? = some s → Parked L ks st s (w'.rd.getD i fun _ => 0) := by
  obtain ⟨w', r', c', d', o', h', p'⟩ := park_upto L hL hr hpend c.ps.length
  have hpk : ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State}, c.ps[i]? = some (ks, st) →
      w'.ms[i]? = some s → Parked L ks st s (w'.rd.getD i fun _ => 0) := fun hc hm => by
    rw [d']; exact p' (List.getElem?_eq_some_iff.mp hc).1 hc hm
  refine ⟨w', r', o', h', fun i => ?_, hpk⟩
  by_cases hi : i < c.ps.length
  · have hc : c.ps[i]? = some (c.ps[i].1, c.ps[i].2) := by simp [hi]
    obtain ⟨s, hs, -⟩ := h'.machine hc
    have hk := hpk hc hs
    rcases hpend hc with h0 | ⟨pr, ch, x, ks', hpr, hin, hks, hnone⟩
    · rw [h0] at hk
      cases hk with
      | halt hh => exact stepAt_halted hs hh.stopped
    · have hch := hchb pr (List.mem_of_getElem? hpr) ch (.inr hin)
      have htn : (UInt32.ofNat ch).toNat = ch := by rw [UInt32.toNat_ofNat']; omega
      rcases hks with hks | hks <;> rw [hks] at hk
      · cases hk with
        | recv hp hd =>
          obtain ⟨hrun, hio, hch', -⟩ := io_view_recv L hL hp hd
          refine stepAt_blocked hs ⟨hrun, hio, ?_⟩
          rw [hch', htn, h'.chans, hp.rd ch, encS, List.getElem?_map, hnone]; rfl
      · cases hk with
        | check hp hd =>
          obtain ⟨hrun, hio, hch', -⟩ := io_view_check L hL hp hd
          rw [Swarm.stepAt_check hs ((running_iff _).mpr hrun) hio]
          unfold Swarm.check
          simp only
          rw [hch', htn, h'.chans, hp.rd ch, encS, List.getElem?_map, hnone]; rfl
  · simp [Swarm.stepAt, List.getElem?_eq_none (by rw [h'.len]; omega : w'.ms.length ≤ i)]

/-! ### The runner's choice -/

/-- The machines the runner may settle. -/
def waitF (w : Swarm) (i : ℕ) : Bool :=
  match w.ms[i]? with
  | some s => running s && ioCmd s == some CHECK
  | none => false

/-- The runner's search for the earliest of them. -/
def bestF (w : Swarm) (best : Option ℕ) (i : ℕ) : Option ℕ :=
  match best, w.ms[i]?, (best.bind (w.ms[·]?)) with
  | none, _, _ => some i
  | some b, some s, some sb => if (getClk s).toNat < (getClk sb).toNat then some i else some b
  | some b, _, _ => some b

theorem answer_eq (w : Swarm) (i : ℕ) (s : State) (b : Bool) :
    w.answer i s b = { w with ms := w.ms.set i (answerState s b) } := rfl

theorem settle_eq (w : Swarm) : w.settle =
    match ((List.range w.ms.length).filter (waitF w)).foldl (bestF w) none with
    | some i => (w.ms[i]?).map fun s => w.answer i s false
    | none => none := rfl

/-- A machine's clock, as a number. -/
def key (w : Swarm) (i : ℕ) : ℕ :=
  match w.ms[i]? with
  | some s => (getClk s).toNat
  | none => 0

/-- **The runner finds the earliest**: the first machine it may settle with
the earliest clock. -/
theorem bestF_spec (w : Swarm) : ∀ n, n ≤ w.ms.length →
    (((List.range n).filter (waitF w)).foldl (bestF w) none = none ↔
      (List.range n).filter (waitF w) = []) ∧
    ∀ b, ((List.range n).filter (waitF w)).foldl (bestF w) none = some b →
      b ∈ (List.range n).filter (waitF w) ∧ ∀ k ∈ (List.range n).filter (waitF w),
        key w b ≤ key w k ∧ (k < b → key w b < key w k)
  | 0, _ => by simp
  | n + 1, hn => by
    obtain ⟨ih₁, ih₂⟩ := bestF_spec w n (by omega)
    rw [List.range_succ, List.filter_append, List.foldl_append]
    have hmn : w.ms[n]? = some w.ms[n] := List.getElem?_eq_getElem (by omega)
    have hkn : key w n = (getClk w.ms[n]).toNat := by simp [key, hmn]
    by_cases hf : waitF w n = true
    · simp only [List.filter_cons, hf, ↓reduceIte, List.filter_nil, List.foldl_cons, List.foldl_nil]
      cases hr : ((List.range n).filter (waitF w)).foldl (bestF w) none with
      | none =>
        have hl := ih₁.mp hr
        simp only [hl, List.nil_append, bestF]
        refine ⟨by simp, fun b hb => ?_⟩
        cases hb; simp
      | some b =>
        obtain ⟨hbm, hbk⟩ := ih₂ b hr
        have hbn : b < n := List.mem_range.mp (List.mem_filter.mp hbm).1
        have hmb : w.ms[b]? = some w.ms[b] := List.getElem?_eq_getElem (by omega)
        have hkb : key w b = (getClk w.ms[b]).toNat := by simp [key, hmb]
        have hbest : bestF w (some b) n =
            if key w n < key w b then some n else some b := by
          simp only [bestF, hmn, Option.bind_some, hmb, hkn, hkb]
        rw [hbest]
        refine ⟨by split_ifs <;> simp, fun b' hb' => ?_⟩
        split_ifs at hb' with hlt
        · cases hb'
          refine ⟨by simp, fun k hk => ?_⟩
          rcases List.mem_append.mp hk with hk | hk
          · have := (hbk k hk).1
            have hkn' : k < n := List.mem_range.mp (List.mem_filter.mp hk).1
            exact ⟨by omega, fun _ => by omega⟩
          · simp at hk; subst hk; simp
        · cases hb'
          refine ⟨List.mem_append_left _ hbm, fun k hk => ?_⟩
          rcases List.mem_append.mp hk with hk | hk
          · exact hbk k hk
          · simp at hk; subst hk; exact ⟨by omega, fun h => by omega⟩
    · have hf' : waitF w n = false := by simpa using hf
      simp only [List.filter_cons, hf', Bool.false_eq_true, ↓reduceIte, List.filter_nil,
        List.foldl_nil, List.append_nil]
      exact ⟨ih₁, ih₂⟩

theorem toNat_le_iff {a b : ℕ∞} (ha : TFits a) (hb : TFits b) : a.toNat ≤ b.toNat ↔ a ≤ b := by
  lift a to ℕ using ha.ne_top
  lift b to ℕ using hb.ne_top
  simp

theorem toNat_lt_iff {a b : ℕ∞} (ha : TFits a) (hb : TFits b) : a.toNat < b.toNat ↔ a < b := by
  lift a to ℕ using ha.ne_top
  lift b to ℕ using hb.ne_top
  simp

/-- **The runner settles the earliest check**: with every machine stopped for its
process, the runner answers false the check of process `i`, the earliest. -/
theorem settle_step (L : Layout) (hL : L.Ok) {c : SCfg} {w : Swarm}
    (hr : RelK L c w) (hpk : ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value} {s : State},
      c.ps[i]? = some (ks, st) → w.ms[i]? = some s → Parked L ks st s (w.rd.getD i fun _ => 0))
    {i ch x : ℕ} {ks : List Stmt} {st : PSt ℕ Value}
    (hi : c.ps[i]? = some (.check ch x :: ks, st)) (he : c.Earliest i st.t) (hx : x < L.n)
    (ha : L.arrayAt x = none) :
    ∃ w', w.settle = some w' ∧ ∃ w'', Swarm.Steps w' w'' ∧ w''.owner = w.owner ∧
      RelK L ⟨c.ps.set i (ks, st.checked x (.bool false)), c.L⟩ w'' := by
  -- the machines the runner may settle are those of the processes at a check
  have hwait : ∀ {j : ℕ}, j < w.ms.length → waitF w j = true →
      ∃ ch' x' ks' st' s₀, c.ps[j]? = some (.check ch' x' :: ks', st') ∧
        w.ms[j]? = some (step (step s₀)) ∧ PRel L (.check ch' x' :: ks') st' s₀ (w.rd.getD j fun _ => 0) ∧
        Direct L (high s₀) (cstack s₀) (.check ch' x' :: ks') (getIP s₀) := by
    intro j hj hf
    have hj' : j < c.ps.length := hr.len ▸ hj
    have hc : c.ps[j]? = some (c.ps[j].1, c.ps[j].2) := by simp [hj']
    have hm : w.ms[j]? = some w.ms[j] := List.getElem?_eq_getElem hj
    have hk := hpk hc hm
    simp only [waitF, hm, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨hrun, hio⟩ := hf
    generalize c.ps[j].1 = ks' at hk hc
    generalize w.ms[j] = s at hk hm hrun hio
    cases hk with
    | recv hp hd =>
      rw [(io_view_recv L hL hp hd).2.1] at hio; cases hio
    | check hp hd => exact ⟨_, _, _, _, _, hc, hm, hp, hd⟩
    | halt hh => simp [running, hh.stopped] at hrun
  have hwait' : ∀ {j ch' x' : ℕ} {ks' : List Stmt} {st' : PSt ℕ Value},
      c.ps[j]? = some (.check ch' x' :: ks', st') →
      j ∈ (List.range w.ms.length).filter (waitF w) ∧ key w j = st'.t.toNat ∧ TFits st'.t := by
    intro j ch' x' ks' st' hc
    have hj : j < w.ms.length := hr.len ▸ (List.getElem?_eq_some_iff.mp hc).1
    have hm : w.ms[j]? = some w.ms[j] := List.getElem?_eq_getElem hj
    have hk := hpk hc hm
    generalize w.ms[j] = s at hk hm
    cases hk with
    | check hp hd =>
      obtain ⟨hrun, hio, -, hclk⟩ := io_view_check L hL hp hd
      refine ⟨List.mem_filter.mpr ⟨List.mem_range.mpr hj, ?_⟩, ?_, hp.tfit⟩
      · simp [waitF, hm, (running_iff _).mpr hrun, hio]
      · simp [key, hm, hclk, toNat_encT hp.tfit]
  obtain ⟨hn₁, hn₂⟩ := bestF_spec w w.ms.length le_rfl
  have hne : ((List.range w.ms.length).filter (waitF w)).foldl (bestF w) none ≠ none := by
    rw [Ne, hn₁]; intro h; rw [h] at hwait'; simpa using (hwait' hi).1
  obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨hjm, hjk⟩ := hn₂ j hj
  have hjl : j < w.ms.length := List.mem_range.mp (List.mem_filter.mp hjm).1
  obtain ⟨chj, xj, ksj, stj, s₀, hcj, hmj, hpj, hdj⟩ := hwait hjl (List.mem_filter.mp hjm).2
  -- `j` is the earliest, so it is `i`
  have hej : c.Earliest j stj.t := by
    intro k ch' x' ks' st' hc
    obtain ⟨hkm, hkk, hkt⟩ := hwait' hc
    obtain ⟨-, hjk', hjt⟩ := hwait' hcj
    obtain ⟨h₁, h₂⟩ := hjk k hkm
    rw [hjk', hkk] at h₁ h₂
    exact ⟨(toNat_le_iff hjt hkt).mp h₁, fun h => (toNat_lt_iff hjt hkt).mp (h₂ h)⟩
  have hij := SCfg.Earliest.unique hi hcj he hej
  subst hij
  rw [hi] at hcj
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Stmt.check.injEq] at hcj
  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hcj
  have hlt : i < c.ps.length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨{ w with ms := w.ms.set i (answerState (step (step s₀)) false) },
    by rw [settle_eq, hj]; simp [hmj, answer_eq], ?_⟩
  obtain ⟨s', hw', hp'⟩ := answer_sim L hL
    (w := { w with ms := w.ms.set i (answerState (step (step s₀)) false) }) (i := i)
    (b := false) hpj hdj (by simp [List.getElem?_set_self (hr.len ▸ hlt)]) hx ha
  refine ⟨{ w with ms := w.ms.set i s' }, by simpa using hw', rfl, ?_⟩
  exact hr.set hlt (ks := ks) (st := st.checked x (.bool false)) (s := s') (Λ := c.L)
    (.at hp') hr.chans

/-- **Settling, on the network and on the swarm**: when everything waits, the
swarm runs on until no machine can move, and its runner then settles the check
the network settles. -/
theorem settle_sim (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {c : SCfg} {w : Swarm} (hr : RelK L c w) (hpend : net.Pending c) {i ch x : ℕ}
    {ks : List Stmt} {st : PSt ℕ Value} (hi : c.ps[i]? = some (.check ch x :: ks, st))
    (he : c.Earliest i st.t) (hx : x < L.n) (ha : L.arrayAt x = none) :
    ∃ w', ReflTransGen KStep w w' ∧ w'.owner = w.owner ∧
      RelK L ⟨c.ps.set i (ks, st.checked x (.bool false)), c.L⟩ w' := by
  obtain ⟨w₁, r₁, o₁, h₁, hst, hpk⟩ := park_all L hL hchb hr hpend
  obtain ⟨w₂, hw₂, w₃, r₃, o₃, h₃⟩ := settle_step L hL h₁ hpk hi he hx ha
  exact ⟨w₃, (kSteps_of_steps r₁).trans (.head (.settle hst hw₂) (kSteps_of_steps r₃)),
    o₃.trans o₁, h₃⟩

/-- **Runs**: every run of the network in 32 bits, its checks settled as the
runner does, is matched by a run of the swarm with its runner. -/
theorem swarm_simulatesK (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {c c' : SCfg} (h : ReflTransGen (QStep L net) c c') {w : Swarm} (hr : RelK L c w)
    (hown : ∀ {i : ℕ} {pr : SProc} {ch : ℕ}, net.procs[i]? = some pr → ch ∈ pr.outs →
      w.owner ch = some i) :
    ∃ w', ReflTransGen KStep w w' ∧ w'.owner = w.owner ∧ RelK L c' w' := by
  induction h with
  | refl => exact ⟨w, .refl, rfl, hr⟩
  | tail _ hs ih =>
    obtain ⟨w₁, r₁, o₁, h₁⟩ := ih
    cases hs with
    | step hs =>
      obtain ⟨w₂, r₂, o₂, h₂⟩ := sim_stepK L hL hchb hs h₁ (fun hp hc => o₁ ▸ hown hp hc)
      exact ⟨w₂, r₁.trans (kSteps_of_steps r₂), o₂.trans o₁, h₂⟩
    | settle hp hi he hx ha =>
      obtain ⟨w₂, r₂, o₂, h₂⟩ := settle_sim L hL hchb h₁ hp hi he hx ha
      exact ⟨w₂, r₁.trans r₂, o₂.trans o₁, h₂⟩

/-- **The swarm with its runner computes the network.** If the network, started
from `s`, runs in 32 bits, its checks settled as the runner does, to a
configuration where every process has finished, then the swarm, loaded from
`s`, runs with its runner to a state where every machine has halted with its
process's final variables in its cells and final time on its clock, and the
channels hold the scripts the network wrote. -/
theorem swarm_correctK (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF)
    (hfit : net.Fits L) (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    (s : St) {c : SCfg} (h : ReflTransGen (QStep L net) (net.init s) c)
    (hdone : ∀ p ∈ c.ps, p.1 = []) :
    ∃ w, ReflTransGen KStep (net.load L s) w ∧ (∀ ch, w.chans ch = encS (c.L ch)) ∧
      ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) →
        ∃ m, w.ms[i]? = some m ∧ Halted L st m := by
  obtain ⟨w₁, r₁, -, h₁⟩ := swarm_simulatesK L hL hchb h (rel_init L hL net hfit s).relK
    (load_owner L hwf s)
  have hpend : net.Pending c := fun hc => .inl (hdone _ (List.mem_of_getElem? hc))
  obtain ⟨w₂, r₂, -, h₂, -, hpk⟩ := park_all L hL hchb h₁ hpend
  refine ⟨w₂, r₁.trans (kSteps_of_steps r₂), h₂.chans, fun {i ks st} hc => ?_⟩
  obtain ⟨m, hm, -⟩ := h₂.machine hc
  have hk := hpk hc hm
  have h0 : ks = [] := hdone _ (List.mem_of_getElem? hc)
  subst h0
  cases hk with
  | halt hh => exact ⟨m, hm, hh⟩

/-- **The swarm with its runner computes the book's semantics.** When the network
runs in 32 bits, its checks settled as the runner does, until every process has
finished, its final states and scripts are a behaviour of the book's semantics
of the network, and the swarm with its runner halts holding exactly them. -/
theorem swarm_bookK (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF) (hfit : net.Fits L)
    (hdefs : L.defs = net.defs)
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32) (s : St)
    {c : SCfg} (h : ReflTransGen (QStep L net) (net.init s) c) (hdone : ∀ p ∈ c.ps, p.1 = []) :
    NetSpec net.toNet s 0 (c.ps.map (·.2)) c.L ∧
      ∃ w, ReflTransGen KStep (net.load L s) w ∧ (∀ ch, w.chans ch = encS (c.L ch)) ∧
        ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) →
          ∃ m, w.ms[i]? = some m ∧ Halted L st m := by
  have hm := reach_of_qSteps hdefs h
  rw [SNet.init_toM] at hm
  have hd : c.toM.Done := by
    intro pc hpc
    simp only [SCfg.toM, List.mem_map] at hpc
    obtain ⟨⟨ks, st⟩, hmem, rfl⟩ := hpc
    have := hdone _ hmem
    simp only at this ⊢
    simp [this]
  have hs := netSpec_of_reach hwf hm hd
  obtain ⟨w, hw, hch, hh⟩ := swarm_correctK L hL hwf hfit hchb s h hdone
  refine ⟨?_, w, hw, hch, hh⟩
  have heq : c.toM.ps.map (·.st) = c.ps.map (·.2) := by simp [SCfg.toM, Function.comp_def]
  rw [← heq]; exact hs

end LaPToP.ProgramTheory.CompileNet
