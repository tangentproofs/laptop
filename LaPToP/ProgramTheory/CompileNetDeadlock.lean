import LaPToP.ProgramTheory.CompileNet

/-!
# Deadlock, on the network and on the swarm

A swarm of b4 machines (`B4.Swarm`) whose channels each have one writer is
confluent: steps of different machines commute, so whatever order the machines
run in, the swarm reaches at most one state in which no machine can move
(`stuck_unique`). With the simulation of `CompileNet`, this gives the
correspondence between a swarm that stops and a network that deadlocks:

* when the network, in 32 bits, reaches a deadlock — every process finished or
  waiting for input that never comes, and not all finished — the swarm reaches
  a state where no machine can move and some machine has not halted
  (`stuck_of_waiting`), and every run of the swarm that stops, stops there
  (`never_halts`); the network machine is then deadlocked too, so by the book's
  semantics some process ends at time `∞` (`waiting_book`);
* when the swarm stops with some machine not halted, the network has no run in
  32 bits in which every process finishes (`no_finish_of_stuck`) — which is what
  `interp --b4` reports as a deadlock (`no_finish_of_run`).
-/

namespace LaPToP.ProgramTheory.CompileNet

open B4 Relation
open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.Interpreter.Network
open LaPToP.ProgramTheory.CompileB4

/-! ### What a step changes -/

/-- Replace machine `i`. -/
def _root_.B4.Swarm.setM (w : Swarm) (i : ℕ) (s : State) : Swarm := { w with ms := w.ms.set i s }

/-- Append a message to channel `c`. -/
def _root_.B4.Swarm.app (w : Swarm) (c : ℕ) (m : B4.Msg) : Swarm :=
  { w with chans := fun c' => if c' = c then w.chans c' ++ [m] else w.chans c' }

/-- Replace machine `i`'s cursors. -/
def _root_.B4.Swarm.setR (w : Swarm) (i : ℕ) (r : ℕ → ℕ) : Swarm := { w with rd := w.rd.set i r }

/-- What a step of a machine does to the swarm: replace the machine, and for a
send append a message to a channel, for a receive replace the machine's
cursors. -/
inductive Eff where
  /-- An instruction of the machine's own. -/
  | other (s : State)
  /-- A send. -/
  | send (s : State) (c : ℕ) (m : B4.Msg)
  /-- A receive. -/
  | recv (s : State) (r : ℕ → ℕ)

/-- The effect, on machine `i`. -/
def Eff.apply (i : ℕ) : Eff → Swarm → Swarm
  | .other s, w => w.setM i s
  | .send s c m, w => (w.setM i s).app c m
  | .recv s r, w => (w.setM i s).setR i r

/-- A send is on a channel machine `i` owns. -/
def Eff.Owned (w : Swarm) (i : ℕ) : Eff → Prop
  | .send _ c _ => w.owner c = some i
  | _ => True

/-- What machine `i`'s step reads stays as it was, and the channels only grew. -/
structure Ext (i : ℕ) (w w' : Swarm) : Prop where
  ms : w'.ms[i]? = w.ms[i]?
  rd : w'.rd.getD i (fun _ => 0) = w.rd.getD i (fun _ => 0)
  owner : w'.owner = w.owner
  chans : ∀ c, w.chans c <+: w'.chans c

/-- **A step is an effect**, which machine `i` has in any swarm that extends this one. -/
theorem stepAt_eff {w w' : Swarm} {i : ℕ} (h : w.stepAt i = some w') :
    ∃ e : Eff, w' = e.apply i w ∧ e.Owned w i ∧
      ∀ w₁, Ext i w w₁ → w₁.stepAt i = some (e.apply i w₁) := by
  cases hs : w.ms[i]? with
  | none => simp [Swarm.stepAt, hs] at h
  | some s =>
    by_cases hr : running s = true
    · rw [Swarm.stepAt_eq hs hr] at h
      by_cases hS : ioCmd s = some SEND
      · rw [ite_eq_left hS] at h
        by_cases ho : w.owner (sendChan s) = some i
        · rw [ite_eq_left ho] at h
          cases h
          refine ⟨.send (setIP (dpop (dpop (dpop s).2).2).2
              (getIP (dpop (dpop (dpop s).2).2).2 + 1)) (sendChan s)
              ((dpop (dpop (dpop s).2).2).1, getClk (dpop (dpop (dpop s).2).2).2), rfl, ho, ?_⟩
          intro w₁ hx
          rw [Swarm.stepAt_eq (by rw [hx.ms, hs]) hr, ite_eq_left hS, ite_eq_left (by rw [hx.owner]; exact ho)]
          rfl
        · rw [ite_eq_right ho] at h; cases h
      · rw [ite_eq_right hS] at h
        by_cases hR : ioCmd s = some RECV
        · rw [ite_eq_left hR] at h
          unfold Swarm.recv at h
          simp only at h
          split at h
          · cases h
          · rename_i m hm
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨.recv (setIP (setClk (dpush (dpop (dpop s).2).2 m.1)
                (later (getClk (dpush (dpop (dpop s).2).2 m.1)) (m.2 + 1)))
                (getIP (setClk (dpush (dpop (dpop s).2).2 m.1)
                  (later (getClk (dpush (dpop (dpop s).2).2 m.1)) (m.2 + 1))) + 1))
              (fun c' => if c' = (dpop (dpop s).2).1.toNat then
                (w.rd.getD i fun _ => 0) (dpop (dpop s).2).1.toNat + 1 else (w.rd.getD i fun _ => 0) c'),
              rfl, trivial, ?_⟩
            intro w₁ hx
            rw [Swarm.stepAt_eq (by rw [hx.ms, hs]) hr, ite_eq_right hS, ite_eq_left hR]
            unfold Swarm.recv
            simp only
            rw [hx.rd, getElem?_of_prefix (hx.chans _) hm]
            rfl
        · rw [ite_eq_right hR] at h
          by_cases hK : ioCmd s = some CHECK
          · rw [ite_eq_left hK] at h
            unfold Swarm.check at h
            simp only at h
            split at h
            · cases h
            · rename_i m hm
              simp only [Option.some.injEq] at h
              subst h
              refine ⟨.other (setIP (dpush (dpop (dpop s).2).2
                  (if decide (m.2.toNat < (getClk s).toNat) then 0xFFFFFFFF else 0))
                  (getIP (dpush (dpop (dpop s).2).2
                    (if decide (m.2.toNat < (getClk s).toNat) then 0xFFFFFFFF else 0)) + 1)),
                rfl, trivial, fun w₁ hx => ?_⟩
              rw [Swarm.stepAt_eq (by rw [hx.ms, hs]) hr, ite_eq_right hS, ite_eq_right hR,
                ite_eq_left hK]
              unfold Swarm.check
              simp only
              rw [hx.rd, getElem?_of_prefix (hx.chans _) hm]
              rfl
          · rw [ite_eq_right hK] at h
            cases h
            refine ⟨.other (step s), rfl, trivial, fun w₁ hx => ?_⟩
            rw [Swarm.stepAt_eq (by rw [hx.ms, hs]) hr, ite_eq_right hS, ite_eq_right hR,
              ite_eq_right hK]
            rfl
    · simp [Swarm.stepAt, hs, hr] at h

/-- Another machine's effect extends the swarm, for machine `i`. -/
theorem ext_apply {w : Swarm} {i j : ℕ} (hij : i ≠ j) (e : Eff) : Ext i w (e.apply j w) := by
  have hms : ∀ s, (w.ms.set j s)[i]? = w.ms[i]? := fun s => List.getElem?_set_ne (Ne.symm hij)
  have hrd : ∀ r, (w.rd.set j r).getD i (fun _ => 0) = w.rd.getD i (fun _ => 0) := fun r => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hij)]
  cases e with
  | other s => exact ⟨hms s, rfl, rfl, fun _ => List.prefix_rfl⟩
  | send s c m =>
    refine ⟨hms s, rfl, rfl, fun c' => ?_⟩
    simp only [Eff.apply, Swarm.app, Swarm.setM]
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_rfl
  | recv s r => exact ⟨hms s, hrd r, rfl, fun _ => List.prefix_rfl⟩

/-- **Effects of different machines commute**, a send of each on its own channel. -/
theorem apply_comm {w : Swarm} {i j : ℕ} (hij : i ≠ j) {e e' : Eff} (ho : e.Owned w i)
    (ho' : e'.Owned w j) : e.apply i (e'.apply j w) = e'.apply j (e.apply i w) := by
  obtain ⟨ms, chans, rd, owner⟩ := w
  cases e <;> cases e' <;>
    simp only [Eff.apply, Swarm.setM, Swarm.app, Swarm.setR, Swarm.mk.injEq,
      List.set_comm _ _ hij, true_and, and_true]
  · rename_i s c m s' c' m'
    have hcc : c ≠ c' := by
      rintro rfl
      simp only [Eff.Owned] at ho ho'
      rw [ho] at ho'; exact hij (Option.some.inj ho')
    funext x
    by_cases h₁ : x = c <;> by_cases h₂ : x = c' <;> simp_all

/-- **The swarm has the diamond property**: two steps from one swarm are the same
step, or each can be followed by the other's to the same swarm. -/
theorem swarm_diamond {a b c : Swarm} (hb : Swarm.Step a b) (hc : Swarm.Step a c) :
    b = c ∨ ∃ d, Swarm.Step b d ∧ Swarm.Step c d := by
  obtain ⟨i, hi⟩ := hb
  obtain ⟨j, hj⟩ := hc
  by_cases hij : i = j
  · subst hij; rw [hi] at hj; exact .inl (Option.some.inj hj)
  · right
    obtain ⟨e, rfl, ho, he⟩ := stepAt_eff hi
    obtain ⟨e', rfl, ho', he'⟩ := stepAt_eff hj
    exact ⟨e'.apply j (e.apply i a), ⟨j, he' _ (ext_apply (Ne.symm hij) e)⟩,
      ⟨i, by rw [he _ (ext_apply hij e'), apply_comm hij ho ho']⟩⟩

theorem steps_iff {a b : Swarm} : Swarm.Steps a b ↔ ReflTransGen Swarm.Step a b := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail hs
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hs ih => exact ih.tail hs

/-- The swarm is confluent. -/
theorem swarm_confluent {a b c : Swarm} (hb : Swarm.Steps a b) (hc : Swarm.Steps a c) :
    Join (ReflTransGen Swarm.Step) b c := by
  refine church_rosser (fun a b c hb hc => ?_) (steps_iff.mp hb) (steps_iff.mp hc)
  rcases swarm_diamond hb hc with rfl | ⟨d, hbd, hcd⟩
  · exact ⟨b, .refl, .refl⟩
  · exact ⟨d, .single hbd, .single hcd⟩

/-- No machine can move. -/
def Stuck (w : Swarm) : Prop := ∀ i, w.stepAt i = none

theorem eq_of_stuck {a b : Swarm} (hs : Stuck a) (h : ReflTransGen Swarm.Step a b) : b = a := by
  cases h.cases_head with
  | inl h => exact h.symm
  | inr h => obtain ⟨d, ⟨i, hi⟩, _⟩ := h; rw [hs i] at hi; cases hi

/-- **The swarm stops in at most one state**, whatever order its machines run in. -/
theorem stuck_unique {w a b : Swarm} (ha : Swarm.Steps w a) (hsa : Stuck a) (hb : Swarm.Steps w b)
    (hsb : Stuck b) : a = b := by
  obtain ⟨d, hd₁, hd₂⟩ := swarm_confluent ha hb
  rw [← eq_of_stuck hsa hd₁, ← eq_of_stuck hsb hd₂]

/-! ### Running the swarm -/

theorem sweep_fold (l : List ℕ) : ∀ (w : Swarm) (b : Bool),
    let r := l.foldl (fun acc i => match acc.1.stepAt i with
      | some w' => (w', true)
      | none => acc) (w, b)
    Swarm.Steps w r.1 ∧ (r.2 = false → b = false ∧ r.1 = w ∧ ∀ i ∈ l, w.stepAt i = none) := by
  induction l with
  | nil => intro w b; exact ⟨.refl, fun h => ⟨h, rfl, by simp⟩⟩
  | cons i l ih =>
    intro w b
    simp only [List.foldl_cons]
    cases hi : w.stepAt i with
    | none =>
      obtain ⟨h₁, h₂⟩ := ih w b
      refine ⟨h₁, fun h => ?_⟩
      obtain ⟨hb, hw, hall⟩ := h₂ h
      exact ⟨hb, hw, by simpa [hi] using hall⟩
    | some w' =>
      obtain ⟨h₁, h₂⟩ := ih w' true
      exact ⟨(Swarm.Steps.single ⟨i, hi⟩).trans h₁, fun h => absurd (h₂ h).1 (by simp)⟩

/-- A round of the swarm is a run of it; a round in which no machine moved
leaves a swarm in which none can. -/
theorem sweep_spec (w : Swarm) :
    Swarm.Steps w w.sweep.1 ∧ (w.sweep.2 = false → Stuck w) := by
  obtain ⟨h₁, h₂⟩ := sweep_fold (List.range w.ms.length) w false
  refine ⟨h₁, fun h i => ?_⟩
  obtain ⟨-, -, hall⟩ := h₂ h
  by_cases hi : i < w.ms.length
  · exact hall i (List.mem_range.mpr hi)
  · simp [Swarm.stepAt, List.getElem?_eq_none (by omega : w.ms.length ≤ i)]

/-- `Swarm.run` runs the swarm, and when it stops early, no machine can move. -/
theorem run_spec : ∀ (n : ℕ) (w : Swarm),
    Swarm.Steps w (Swarm.run n w) ∧ ((Swarm.run n w).sweep.2 = false → Stuck (Swarm.run n w))
  | 0, w => ⟨.refl, (sweep_spec w).2⟩
  | n + 1, w => by
    simp only [Swarm.run]
    split_ifs with h
    · obtain ⟨h₁, h₂⟩ := run_spec n w.sweep.1
      exact ⟨(sweep_spec w).1.trans h₁, h₂⟩
    · exact ⟨.refl, (sweep_spec w).2⟩

/-! ### A network that deadlocks -/

/-- **A deadlock of the network, in 32 bits**: every process has finished, or
waits for input on one of its channels whose script has no message at its read
cursor. -/
def SNet.Waiting (net : SNet) (c : SCfg) : Prop :=
  ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) → ks = [] ∨
    ∃ pr ch x ks', net.procs[i]? = some pr ∧ ch ∈ pr.ins ∧ ks = .recv ch x :: ks' ∧
      (c.L ch)[st.r ch]? = none

/-- In a deadlock the network machine takes no step. -/
theorem SNet.Waiting.normal {net : SNet} {c : SCfg} (h : net.Waiting c) : Normal net.toNet c.toM := by
  intro c' hs
  obtain ⟨hi, ha⟩ := hs
  rename_i i a b L'
  simp only [SCfg.toM, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨⟨ks, st⟩, hp, rfl⟩ := hi
  rcases h hp with rfl | ⟨pr, ch, x, ks', -, -, rfl, hm⟩
  · simp only [List.map_nil] at ha
    cases ha with
    | loc hl => cases hl
  · simp only [List.map_cons, Stmt.toNP] at ha
    cases ha with
    | loc hl => cases hl
    | recv _ _ hm' => simp [SCfg.toM, hm] at hm'

/-- **A deadlock of the network in 32 bits is the book's `∞`**: in every behaviour
of the book's semantics, some process ends at time `∞`. -/
theorem waiting_book (L : Layout) {net : SNet} (hwf : net.toNet.WF) (hdefs : L.defs = net.defs)
    {s : St} {c : SCfg} (h : ReflTransGen (SStep L net) (net.init s) c) (hwt : net.Waiting c)
    (hnd : ∃ p ∈ c.ps, p.1 ≠ []) {fin : List (PSt ℕ Value)} {S : Scripts Value}
    (hspec : NetSpec net.toNet s 0 fin S) : ∃ f ∈ fin, f.t = ⊤ := by
  have hm := reach_of_sSteps hdefs h
  rw [SNet.init_toM] at hm
  refine deadlock_top hwf hm hwt.normal ?_ hspec
  intro hd
  obtain ⟨p, hp, hne⟩ := hnd
  have := hd ⟨p.1.map Stmt.toNP, p.2⟩ (by simp only [SCfg.toM, List.mem_map]; exact ⟨p, hp, rfl⟩)
  exact hne (by simpa using this)

/-! ### Machines that cannot move -/

/-- A machine waiting at `io` for a message on a channel whose script has none at
its cursor. -/
structure Blocked (chans : ℕ → List B4.Msg) (r : ℕ → ℕ) (m : State) : Prop where
  run : Running m
  io : ioCmd m = some RECV
  none : (chans (dpop (dpop m).2).1.toNat)[r (dpop (dpop m).2).1.toNat]? = none

theorem stepAt_blocked {w : Swarm} {i : ℕ} {m : State} (hm : w.ms[i]? = some m)
    (hb : Blocked w.chans (w.rd.getD i fun _ => 0) m) : w.stepAt i = none := by
  rw [Swarm.stepAt_recv hm ((running_iff _).mpr hb.run) hb.io]
  unfold Swarm.recv
  simp only
  rw [hb.none]

theorem stepAt_halted {w : Swarm} {i : ℕ} {m : State} (hm : w.ms[i]? = some m)
    (h : getRST m = 0) : w.stepAt i = none := by
  simp [Swarm.stepAt, hm, running, h]

/-- A machine whose process waits for input that never comes runs to its `io`
and waits there. -/
theorem wait_one (L : Layout) (hL : L.Ok) {w : Swarm} {i : ℕ} {s : State} {ch x : ℕ}
    {ks : List Stmt} {st : PSt ℕ Value} {Λ : Scripts Value} (hi : w.ms[i]? = some s)
    (hp : PRel L (.recv ch x :: ks) st s (w.rd.getD i fun _ => 0)) (hch : ch < 2 ^ 32)
    (hchan : w.chans ch = encS (Λ ch)) (hm : (Λ ch)[st.r ch]? = none) :
    ∃ s', Swarm.Steps w { w with ms := w.ms.set i s' } ∧
      Blocked w.chans (w.rd.getD i fun _ => 0) s' := by
  have hb := hL.2
  have hlt : i < w.ms.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨s₁, hw₁, -, hp₁, hd₁⟩ := Rel.follow L hL hi hp
  obtain ⟨h₁, h₂, h₃, h₄, -, -⟩ := hd₁.cons_inv (by simp) (by simp)
  simp only [slen, sdepth] at h₂ h₃
  simp only [scode, List.append_assoc] at h₄
  have hA : At L st.mem s₁ ((0x97 :: le4 (UInt32.ofNat ch)) ++ ((0x97 :: le4 RECV) ++ ([0xFD] ++
      ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x95])))) 2 :=
    ⟨hp₁.wf, hp₁.run, h₁, by simp; omega, h₄, hp₁.vars, by rw [hp₁.stack]; decide⟩
  obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li hA (by omega)
  have hA₁ := hA.after (bs₁ := 0x97 :: le4 (UInt32.ofNat ch)) (d₂ := 1) (by omega) w₁
    (by rw [i₁]; rfl) d₁ sm₁
  obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_li hA₁ (by omega)
  have hA₂ := hA₁.after (bs₁ := 0x97 :: le4 RECV) (d₂ := 0) (by omega) w₂
    (by rw [i₂]; rfl) d₂ sm₂
  have hrun : Steps s₁ (step (step s₁)) :=
    (Steps.one hp₁.run (notIo_li hA)).tail ⟨hA₁.run, notIo_li hA₁, rfl⟩
  have hop : high (step (step s₁)) (getIP (step (step s₁))) = 0xFD := by
    simpa using hA₂.code 0 (by simp)
  have hst₂ : dstack (step (step s₁)) = [UInt32.ofNat ch, RECV] := by rw [d₂, d₁, hp₁.stack]; rfl
  refine ⟨step (step s₁), ?_, ⟨hA₂.run,
    ioCmd_eq (xs := [UInt32.ofNat ch]) hA₂.lo hop (by simpa using hst₂), ?_⟩⟩
  · have := swarm_lift (w := { w with ms := w.ms.set i s₁ }) (i := i) (s := s₁)
      (by simp [List.getElem?_set_self hlt]) hrun
    exact hw₁.trans (by simpa using this)
  · obtain ⟨-, w₁', -, d₁', -⟩ := dpop_same (step (step s₁)) [UInt32.ofNat ch] RECV hA₂.wf
      (by simpa using hst₂)
    obtain ⟨e₂, -, -, -, -⟩ := dpop_same _ [] (UInt32.ofNat ch) w₁' (by simpa using d₁')
    have htn : (UInt32.ofNat ch).toNat = ch := by rw [UInt32.toNat_ofNat']; omega
    rw [e₂, htn, hchan, hp.rd ch, encS, List.getElem?_map, hm]
    rfl

/-- How a machine ends when its process is at a deadlock: halted if the process
finished, waiting at its `io` if not. -/
def Settled (w : Swarm) (i : ℕ) (ks : List Stmt) (m : State) : Prop :=
  (ks = [] ∧ getRST m = 0) ∨ (ks ≠ [] ∧ Blocked w.chans (w.rd.getD i fun _ => 0) m)

/-- Settle the machines one by one. -/
theorem settle_upto (L : Layout) (hL : L.Ok) {net : SNet}
    (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    {c : SCfg} {w : Swarm} (hr : Rel L c w) (hwt : net.Waiting c) (k : ℕ) :
    ∃ w', Swarm.Steps w w' ∧ w'.ms.length = c.ps.length ∧ w'.chans = w.chans ∧ w'.rd = w.rd ∧
      ∀ {i : ℕ} {ks : List Stmt} {st : PSt ℕ Value}, c.ps[i]? = some (ks, st) →
        ∃ m, w'.ms[i]? = some m ∧
          (if i < k then Settled w i ks m else PRel L ks st m (w.rd.getD i fun _ => 0)) := by
  induction k with
  | zero =>
    refine ⟨w, .refl, hr.len, rfl, rfl, fun hc => ?_⟩
    obtain ⟨s, hs, hp⟩ := hr.machine hc
    exact ⟨s, hs, by simpa using hp⟩
  | succ k ih =>
    obtain ⟨w₁, r₁, l₁, c₁, d₁, h₁⟩ := ih
    by_cases hk : k < c.ps.length
    · have hck : c.ps[k]? = some (c.ps[k].1, c.ps[k].2) := by simp [hk]
      obtain ⟨s, hs, hp⟩ := h₁ hck
      rw [ite_eq_right (by omega)] at hp
      have hset : ∀ m, (({ w₁ with ms := w₁.ms.set k m } : Swarm).ms)[k]? = some m := fun m => by
        simp [List.getElem?_set_self (l₁ ▸ hk)]
      -- settle machine `k`
      have hk' : ∃ s', Swarm.Steps w₁ { w₁ with ms := w₁.ms.set k s' } ∧
          Settled w k c.ps[k].1 s' := by
        rcases hwt hck with hnil | ⟨pr, ch, x, ks', hpr, hin, hks, hm⟩
        · rw [hnil] at hp
          obtain ⟨s', r', hh⟩ := halt_one L hL hs hp
          exact ⟨s', r', .inl ⟨hnil, hh.stopped⟩⟩
        · rw [hks, ← d₁] at hp
          obtain ⟨s', r', hbl⟩ := wait_one L hL hs hp
            (hchb pr (List.mem_of_getElem? hpr) ch (.inr hin)) (by rw [c₁]; exact hr.chans ch) hm
          refine ⟨s', r', .inr ⟨by rw [hks]; simp, ?_⟩⟩
          rw [c₁, d₁] at hbl; exact hbl
      obtain ⟨s', r', hst⟩ := hk'
      refine ⟨_, r₁.trans r', by simp [l₁], by simp [c₁], by simp [d₁], fun {i ks' st'} hc => ?_⟩
      by_cases hik : i = k
      · subst hik
        rw [hck] at hc; cases hc
        exact ⟨s', hset s', by rw [ite_eq_left (by omega)]; exact hst⟩
      · obtain ⟨s'', hs'', hq⟩ := h₁ hc
        refine ⟨s'', by simpa [List.getElem?_set_ne (Ne.symm hik)] using hs'', ?_⟩
        by_cases hlt : i < k
        · rw [ite_eq_left hlt] at hq; rw [ite_eq_left (by omega)]; exact hq
        · rw [ite_eq_right hlt] at hq; rw [ite_eq_right (by omega)]; exact hq
    · refine ⟨w₁, r₁, l₁, c₁, d₁, fun {i ks st} hc => ?_⟩
      obtain ⟨s, hs, hq⟩ := h₁ hc
      have : i < c.ps.length := (List.getElem?_eq_some_iff.mp hc).1
      refine ⟨s, hs, ?_⟩
      rw [ite_eq_left (by omega)]; rw [ite_eq_left (by omega)] at hq; exact hq

/-! ### The correspondence -/

/-- **A deadlock of the network is a swarm that stops**: when the network, in 32
bits, reaches a deadlock with some process unfinished, the swarm of its compiled
processes reaches a state where no machine can move and some machine is still
running — waiting at its `io` for a message that never comes. -/
theorem stuck_of_waiting (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF)
    (hfit : net.Fits L) (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    (s : St) {c : SCfg} (h : ReflTransGen (SStep L net) (net.init s) c) (hwt : net.Waiting c)
    (hnd : ∃ p ∈ c.ps, p.1 ≠ []) :
    ∃ w, Swarm.Steps (net.load L s) w ∧ Stuck w ∧ ∃ (i : ℕ) (m : State), w.ms[i]? = some m ∧ Running m := by
  obtain ⟨w₁, r₁, -, h₁⟩ := swarm_simulates L hL hchb h (rel_init L hL net hfit s)
    (load_owner L hwf s)
  obtain ⟨w₂, r₂, l₂, c₂, d₂, h₂⟩ := settle_upto L hL hchb h₁ hwt c.ps.length
  have hset : ∀ {i ks st}, c.ps[i]? = some (ks, st) → ∃ m, w₂.ms[i]? = some m ∧ Settled w₁ i ks m :=
    fun hc => by
      obtain ⟨m, hm, hs⟩ := h₂ hc
      exact ⟨m, hm, by rwa [ite_eq_left (List.getElem?_eq_some_iff.mp hc).1] at hs⟩
  refine ⟨w₂, r₁.trans r₂, fun i => ?_, ?_⟩
  · by_cases hi : i < c.ps.length
    · have hc : c.ps[i]? = some (c.ps[i].1, c.ps[i].2) := by simp [hi]
      obtain ⟨m, hm, hs⟩ := hset hc
      rcases hs with ⟨-, hh⟩ | ⟨-, hb⟩
      · exact stepAt_halted hm hh
      · exact stepAt_blocked hm (by rw [c₂, d₂]; exact hb)
    · simp [Swarm.stepAt, List.getElem?_eq_none (by omega : w₂.ms.length ≤ i)]
  · obtain ⟨p, hp, hne⟩ := hnd
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨m, hm, hs⟩ := hset (i := i) (ks := c.ps[i].1) (st := c.ps[i].2) (by simp [hi])
    rcases hs with ⟨h0, -⟩ | ⟨-, hb⟩
    · exact (hne h0).elim
    · exact ⟨i, m, hm, hb.run⟩

/-- **And every run of the swarm that stops, stops there**: after a deadlock of
the network, no run of the swarm ends with every machine halted. -/
theorem never_halts (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF)
    (hfit : net.Fits L) (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    (s : St) {c : SCfg} (h : ReflTransGen (SStep L net) (net.init s) c) (hwt : net.Waiting c)
    (hnd : ∃ p ∈ c.ps, p.1 ≠ []) {w' : Swarm} (hw' : Swarm.Steps (net.load L s) w')
    (hst : Stuck w') : ∃ (i : ℕ) (m : State), w'.ms[i]? = some m ∧ Running m := by
  obtain ⟨w, hw, hs, hrun⟩ := stuck_of_waiting L hL hwf hfit hchb s h hwt hnd
  rw [stuck_unique hw' hst hw hs]
  exact hrun

/-- **A swarm that stops is a network that cannot finish**: if the swarm of
compiled processes reaches a state where no machine can move and some machine
has not halted, then the network has no run in 32 bits in which every process
finishes. -/
theorem no_finish_of_stuck (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF)
    (hfit : net.Fits L) (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    (s : St) {w : Swarm} (hw : Swarm.Steps (net.load L s) w) (hst : Stuck w) {i : ℕ} {m : State}
    (hm : w.ms[i]? = some m) (hrun : getRST m ≠ 0) :
    ¬ ∃ c, ReflTransGen (SStep L net) (net.init s) c ∧ ∀ p ∈ c.ps, p.1 = [] := by
  rintro ⟨c, h, hdone⟩
  obtain ⟨w', hw', hl, -, hh⟩ := swarm_correct L hL hwf hfit hchb s h hdone
  have hhalt : ∀ {j : ℕ} {m' : State}, w'.ms[j]? = some m' → getRST m' = 0 := by
    intro j m' hj
    have hlt : j < c.ps.length := hl ▸ (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨m'', hm'', hH⟩ := hh (i := j) (ks := c.ps[j].1) (st := c.ps[j].2) (by simp [hlt])
    rw [hj] at hm''; cases hm''
    exact hH.stopped
  have hst' : Stuck w' := fun j => by
    cases hj : w'.ms[j]? with
    | none => simp [Swarm.stepAt, hj]
    | some m' => exact stepAt_halted hj (hhalt hj)
  rw [stuck_unique hw hst hw' hst'] at hm
  exact hrun (hhalt hm)

/-- **What `interp --b4` reports as a deadlock is one**: if `Swarm.run` stops with
no machine able to move and some machine not halted, the network has no run in
32 bits in which every process finishes. -/
theorem no_finish_of_run (L : Layout) (hL : L.Ok) {net : SNet} (hwf : net.toNet.WF)
    (hfit : net.Fits L) (hchb : ∀ pr ∈ net.procs, ∀ ch, ch ∈ pr.outs ∨ ch ∈ pr.ins → ch < 2 ^ 32)
    (s : St) (n : ℕ) (hsw : (Swarm.run n (net.load L s)).sweep.2 = false) {i : ℕ} {m : State}
    (hm : (Swarm.run n (net.load L s)).ms[i]? = some m) (hrun : getRST m ≠ 0) :
    ¬ ∃ c, ReflTransGen (SStep L net) (net.init s) c ∧ ∀ p ∈ c.ps, p.1 = [] :=
  no_finish_of_stuck L hL hwf hfit hchb s (run_spec n _).1 ((run_spec n _).2 hsw) hm hrun

end LaPToP.ProgramTheory.CompileNet
