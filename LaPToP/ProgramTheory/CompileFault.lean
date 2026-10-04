import LaPToP.ProgramTheory.CompileB4

/-!
# Faults: a run that fails a run-time check

The compiler's theorems speak of runs in 32 bits, with every array index
inside its array (`Fits`). Outside them the machine reads and writes where the
program did not mean to. `interp --b4` therefore puts a run-time check before
every access to an array (`Stmt.guard`), and its code stops the machine, with
`FAULT` (`-3`) on the stack, when the check fails.

`SFault L d p s` says the run of `p` from `s` in 32 bits reaches a check that
fails, every step before it being a step of `SEval`. Then the machine halts with
`FAULT` alone on its stack (`fault_runs`, `load_fault`). A guard that holds is
`ok` (`SEval.guard`), so a run that passes its checks is computed as before
(`load_correct`).
-/

namespace LaPToP.ProgramTheory.CompileB4

open B4
open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang

/-- **A run in 32 bits that fails a check**: the run of the statement reaches a
`guard` whose condition is false, each step before it a step in 32 bits. -/
inductive SFault (L : Layout) : ℕ → Stmt → St → Prop
  /-- The check fails. -/
  | guard {d : ℕ} {c : Exp} {s : St} : Fits L s c → c.eval s = .bool false →
      SFault L d (.guard c) s
  /-- In the first statement. -/
  | seqL {d : ℕ} {p q : Stmt} {s : St} : SFault L d p s → SFault L d (.seq p q) s
  /-- In the second. -/
  | seqR {d : ℕ} {p q : Stmt} {s t : St} : SEval L d p s t → SFault L d q t →
      SFault L d (.seq p q) s
  /-- In the `then` branch. -/
  | condT {d : ℕ} {c : Exp} {p q : Stmt} {s : St} : Fits L s c → c.eval s = .bool true →
      SFault L d p s → SFault L d (.cond c p q) s
  /-- In the `else` branch. -/
  | condF {d : ℕ} {c : Exp} {p q : Stmt} {s : St} : Fits L s c → c.eval s = .bool false →
      SFault L d q s → SFault L d (.cond c p q) s
  /-- In the body of a loop. -/
  | loopB {d : ℕ} {c : Exp} {p : Stmt} {s : St} : Fits L s c → c.eval s = .bool true →
      SFault L d p s → SFault L d (.loop c p) s
  /-- In a later round. -/
  | loopN {d : ℕ} {c : Exp} {p : Stmt} {s t : St} : Fits L s c → c.eval s = .bool true →
      SEval L d p s t → SFault L d (.loop c p) t → SFault L d (.loop c p) s
  /-- In a called statement. -/
  | call {d : ℕ} {k : ℕ} {s : St} : k ∈ L.keys → d < STACKSZ →
      SFault L (d + 1) (L.defs k) s → SFault L d (.call k) s
  /-- In a scope's body. -/
  | scope {d : ℕ} {x : ℕ} {e : Exp} {p : Stmt} {s : St} : x < L.n → L.arrayAt x = none →
      Fits L s e → d < STACKSZ → SFault L (d + 1) p (Function.update s x (e.eval s)) →
      SFault L d (.scope x e p) s

/-- What a statement's code does when its run fails a check: the machine halts
with `FAULT` alone on its stack. -/
def FRuns (L : Layout) (d : ℕ) (p : Stmt) (st : St) : Prop :=
  ∀ s a, SAt L d st s a p → ∃ s', Steps s s' ∧ getRST s' = 0 ∧ dstack s' = [FAULT]

/-- **A run that fails a check halts with `FAULT`.** -/
theorem fault_runs (L : Layout) (hL : L.Ok) {d : ℕ} {p : Stmt} {st : St}
    (h : SFault L d p st) : FRuns L d p st := by
  induction h with
  | @guard _ c s hf hc =>
    intro σ a h
    obtain ⟨hJ, -, hF⟩ := guard_code h.code
    have hb := hL.2
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := false) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ jmTo _ ++ ((0x97 :: le4 FAULT) ++ [0xFF]))
      (by simp; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i₁
    have hJ₁ := (show CodeAt (high σ₁) (getIP σ₁) (jmTo (a + (ecode L c).length + 13)) by
      rw [i₁, sm₁.high]; exact hJ)
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_jm' hL w₁ (by rw [i₁]; omega) (by rw [i₁]; omega)
      hJ₁ (by omega) (by omega)
    have run₂ : Running (step σ₁) := sm₂.running run₁
    have hAt : At L s (step σ₁) ((0x97 :: le4 FAULT) ++ [0xFF]) 1 :=
      ⟨w₂, run₂, by rw [i₂]; omega, by rw [i₂]; simp; omega,
        by rw [i₂, sm₂.high, sm₁.high]; exact hF, by rw [sm₂.high, sm₁.high]; exact h.vars,
        by rw [d₂, d₁]; simp [STACKSZ]⟩
    obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_li hAt le_rfl
    have hip : 256 ≤ getIP (step (step σ₁)) := by rw [i₃, i₂]; omega
    have hop : high (step (step σ₁)) (getIP (step (step σ₁))) = 0xFF := by
      rw [sm₃.high, i₃]; have := (CodeAt.append.mp hAt.code).2 0 (by simp); simpa using this
    refine ⟨step (step (step σ₁)), ((r₁.tail ⟨run₁, notIo_jm (by rw [i₁]; omega) hJ₁, rfl⟩).tail
      ⟨run₂, notIo_li hAt, rfl⟩).tail ⟨sm₃.running run₂, notIo_of_hop hip hop, rfl⟩,
      step_hl _ w₃ hip hop, ?_⟩
    have hd₃ : dstack (step (step σ₁)) = [FAULT] := by rw [d₃, d₂, d₁]; rfl
    rw [step_of _ _ hip hop, runOp_hl, ← hd₃]
    simp only [dstack, getDSH_setIP, getDSH_setRST, ds_setIP, ds_setRST]
  | @seqL _ p q s _ ih =>
    intro σ a h
    have hc := CodeAt.append.mp h.code
    rw [length_scode] at hc
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    exact ih σ a ⟨h.wf, h.run, h.ip, h.lo, by omega, hc.1, h.vars, h.stack, by omega, h.cs, h.image⟩
  | @seqR _ p q s t hp _ ih =>
    intro σ a h
    have hc := CodeAt.append.mp h.code
    rw [length_scode] at hc
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, v₁, k₁⟩ := stmt_runs L hL hp σ a
      ⟨h.wf, h.run, h.ip, h.lo, by omega, hc.1, h.vars, h.stack, by omega, h.cs, h.image⟩
    obtain ⟨σ₂, r₂, h₂⟩ := ih σ₁ (a + slen L p)
      ⟨w₁, run₁, i₁, by omega, by omega,
        hc.2.mono k₁.low (by rw [length_scode]; omega), v₁, d₁, by omega,
        by rw [k₁.cs]; exact h.cs, h.image.mono k₁.low⟩
    exact ⟨σ₂, r₁.trans r₂, h₂⟩
  | @condT _ c p q s hf hc _ ih =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := true) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [ite_true] at i₁
    obtain ⟨σ₂, r₂, h₂⟩ := ih σ₁ _
      ⟨w₁, run₁, i₁, by omega, by omega, by rw [sm₁.high]; exact hP,
        by rw [sm₁.high]; exact h.vars, d₁, by omega, by rw [sm₁.cs]; exact h.cs,
        by rw [sm₁.high]; exact h.image⟩
    exact ⟨σ₂, r₁.trans r₂, h₂⟩
  | @condF _ c p q s hf hc _ ih =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ', hQ⟩ := cond_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := false) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo _ ++ scode L _ q)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [Bool.false_eq_true, ite_false] at i₁
    have hJ₁ := (show CodeAt (high σ₁) (getIP σ₁) (jmTo (a + (ecode L c).length + 8 + slen L p + 5)) by
      rw [i₁, sm₁.high]; exact hJ)
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := run_jm' hL w₁ (by rw [i₁]; omega) (by rw [i₁]; omega)
      hJ₁ (by omega) (by omega)
    obtain ⟨σ₃, r₃, h₃⟩ := ih (step σ₁) _
      ⟨w₂, sm₂.running run₁, i₂, by omega, by omega, by rw [sm₂.high, sm₁.high]; exact hQ,
        by rw [sm₂.high, sm₁.high]; exact h.vars, by rw [d₂, d₁], by omega,
        by rw [sm₂.cs, sm₁.cs]; exact h.cs, by rw [sm₂.high, sm₁.high]; exact h.image⟩
    exact ⟨σ₃, (r₁.tail ⟨run₁, notIo_jm (by rw [i₁]; omega) hJ₁, rfl⟩).trans r₃, h₃⟩
  | @loopB _ c p s hf hc _ ih =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ'⟩ := loop_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := true) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo a)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [ite_true] at i₁
    obtain ⟨σ₂, r₂, h₂⟩ := ih σ₁ _
      ⟨w₁, run₁, i₁, by omega, by omega, by rw [sm₁.high]; exact hP,
        by rw [sm₁.high]; exact h.vars, d₁, by omega, by rw [sm₁.cs]; exact h.cs,
        by rw [sm₁.high]; exact h.image⟩
    exact ⟨σ₂, r₁.trans r₂, h₂⟩
  | @loopN _ c p s t hf hc hp _ ih =>
    intro σ a h
    obtain ⟨hE, hT, hJ, hP, hJ'⟩ := loop_code h.code
    have hdep := h.depth; simp only [sdepth] at hdep
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hcode := h.code; simp only [scode] at hcode
    obtain ⟨σ₁, r₁, w₁, run₁, i₁, d₁, sm₁⟩ := run_cond (b := true) hL hf hc h.wf h.run h.ip h.lo
      (rest := jmTo _ ++ scode L _ p ++ jmTo a)
      (by simp [length_scode]; omega) (by simpa only [List.append_assoc] using hcode) h.vars
      h.stack (by omega)
    simp only [ite_true] at i₁
    obtain ⟨σ₂, r₂, w₂, run₂, i₂, d₂, v₂, k₂⟩ := stmt_runs L hL hp σ₁ _
      ⟨w₁, run₁, i₁, by omega, by omega, by rw [sm₁.high]; exact hP,
        by rw [sm₁.high]; exact h.vars, d₁, by omega, by rw [sm₁.cs]; exact h.cs,
        by rw [sm₁.high]; exact h.image⟩
    have hJ₂ : CodeAt (high σ₂) (getIP σ₂) (jmTo a) := by
      rw [i₂]; exact (hJ'.mono (fun i hi => by rw [k₂.low i hi, sm₁.high]) (by simp; omega))
    obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_jm' hL w₂ (by rw [i₂]; omega) (by rw [i₂]; omega) hJ₂
      (by omega) (by omega)
    have k₃ : Keeps L σ (step σ₂) := sm₁.keeps.trans (k₂.trans sm₃.keeps)
    obtain ⟨σ₄, r₄, h₄⟩ := ih (step σ₂) a
      ⟨w₃, sm₃.running run₂, i₃, hlo, h.hi, h.code.mono (fun i hi => k₃.low i hi)
        (by rw [length_scode]; exact h.hi), by rw [sm₃.high]; exact v₂, by rw [d₃, d₂], h.depth,
        by rw [k₃.cs]; exact h.cs, h.image.mono k₃.low⟩
    exact ⟨σ₄, ((r₁.trans r₂).tail ⟨run₂, notIo_jm (by rw [i₂]; omega) hJ₂, rfl⟩).trans r₄, h₄⟩
  | @call d k s hk hd _ ih =>
    intro σ a h
    have hcode := h.code; simp only [scode] at hcode
    rw [show (0x9D : UInt8) :: le4 (UInt32.ofNat (L.entry k)) =
      [0x9D] ++ le4 (UInt32.ofNat (L.entry k)) from rfl, CodeAt.append] at hcode
    obtain ⟨he₁, he₂, he₃, he₄⟩ := h.image k hk
    have hb := hL.2
    have hhi := h.hi; simp only [slen] at hhi
    have hlo := h.lo
    have hop : high σ (getIP σ) = 0x9D := by rw [h.ip]; simpa using hcode.1 0 (by simp)
    have hword : word (high σ) (getIP σ + 1) = UInt32.ofNat (L.entry k) := by
      rw [h.ip]; exact word_le4 (by simpa using hcode.2)
    have hen : (UInt32.ofNat (L.entry k)).toNat = L.entry k := toNat_ofNat_addr (by omega)
    obtain ⟨w₁, i₁, d₁, c₁, f₁⟩ := step_cl σ h.wf (by rw [h.ip]; omega) (by rw [h.ip]; omega) hop
      (by rw [hword, hen]; exact he₁) (by rw [h.cs]; exact hd)
    rw [hword, hen] at i₁
    have hc₂ := CodeAt.append.mp he₄
    rw [length_scode] at hc₂
    have run₁ : Running (step σ) := ⟨f₁.st.trans h.run.1, f₁.db.trans h.run.2⟩
    obtain ⟨σ₂, r₂, h₂⟩ := ih (step σ) (L.entry k)
      ⟨w₁, run₁, i₁, he₁, by omega, by rw [f₁.high]; exact hc₂.1, by rw [f₁.high]; exact h.vars,
        by rw [d₁]; exact h.stack, he₃, by rw [c₁]; simp [h.cs], by rw [f₁.high]; exact h.image⟩
    exact ⟨σ₂, (Steps.one h.run (notIo_of_hop (by rw [h.ip]; omega) hop)).trans r₂, h₂⟩
  | @scope d x e p s hx ha hf hd _ ih =>
    intro σ a h
    have hb := hL.2
    have hhi := h.hi; simp only [slen] at hhi
    have hdep := h.depth; simp only [sdepth] at hdep
    have hlo := h.lo
    have hcode := h.code
    simp only [scode] at hcode
    have hcode' := hcode
    rw [CodeAt.append, CodeAt.append, CodeAt.append] at hcode'
    obtain ⟨⟨⟨hA, hB⟩, hP⟩, hC⟩ := hcode'
    simp only [List.length_append, List.length_cons, length_le4, length_scode] at hB hP hC
    replace hP : CodeAt (high σ) (a + 7 + ((ecode L e).length + 6))
        (scode L (a + 7 + ((ecode L e).length + 6)) p) := by
      exact hP.cast (by first | omega | (simp; omega))
    have haddr : L.addr x + 3 < MAXBYTE := by unfold Layout.addr; omega
    have haddr' : 256 ≤ (UInt32.ofNat (L.addr x)).toNat := by
      rw [toNat_ofNat_addr (by omega)]; unfold Layout.addr; have := hL.1; omega
    -- `li x ri dc`: the old value goes on the control stack
    have hAt : At L s σ ((0x97 :: le4 (UInt32.ofNat (L.addr x))) ++ [0x93, 0x90]) 1 :=
      ⟨h.wf, h.run, by rw [h.ip]; omega, by rw [h.ip]; simp; omega, by rw [h.ip]; exact hA, h.vars,
        by rw [h.stack]; simp [STACKSZ]⟩
    obtain ⟨w₁, i₁, d₁, sm₁⟩ := run_li hAt le_rfl
    have hA₂ := (CodeAt.append.mp hA).2
    simp only [List.length_cons, length_le4] at hA₂
    have hop₁ : high (step σ) (getIP (step σ)) = 0x93 := by
      rw [sm₁.high, i₁, h.ip]; simpa using hA₂ 0 (by simp)
    obtain ⟨w₂, i₂, d₂, sm₂⟩ := step_ri (step σ) [] (UInt32.ofNat (L.addr x)) w₁
      (by rw [i₁, h.ip]; omega) (by rw [i₁, h.ip]; unfold MAXBYTE at hb; omega) hop₁
      (by rw [d₁, h.stack]) haddr' (by rw [toNat_ofNat_addr (by omega)]; exact haddr)
    rw [toNat_ofNat_addr (by omega), sm₁.high, h.vars.1 x hx] at d₂
    have hop₂ : high (step (step σ)) (getIP (step (step σ))) = 0x90 := by
      rw [sm₂.high, sm₁.high, i₂, i₁, h.ip]; simpa using hA₂ 1 (by simp)
    obtain ⟨w₃, i₃, d₃, c₃, f₃⟩ := step_dc (step (step σ)) [] (enc (s x)) w₂
      (by rw [i₂, i₁, h.ip]; omega) (by rw [i₂, i₁, h.ip]; unfold MAXBYTE at hb; omega) hop₂ d₂
      (by rw [sm₂.cs, sm₁.cs, h.cs]; exact hd)
    set σ₃ := step (step (step σ)) with hσ₃
    have sm₁₂ := sm₁.trans sm₂
    have run₃ : Running σ₃ := ⟨f₃.st.trans (sm₁₂.running h.run).1, f₃.db.trans (sm₁₂.running h.run).2⟩
    have hip₃ : getIP σ₃ = a + 7 := by rw [i₃, i₂, i₁, h.ip]
    have hcs₃ : cstack σ₃ = cstack σ ++ [enc (s x)] := by rw [c₃, sm₂.cs, sm₁.cs]
    have hhigh₃ : high σ₃ = high σ := by rw [f₃.high, sm₂.high, sm₁.high]
    -- `x:= e`
    obtain ⟨σ₄, r₄, w₄, run₄, i₄, d₄, v₄, k₄⟩ := assign_runs L hL (d := d + 1) hx ha hf σ₃ (a + 7)
      ⟨w₃, run₃, hip₃, by omega, by simp [slen]; omega,
        by rw [hhigh₃]; simpa [scode] using hB, by rw [hhigh₃]; exact h.vars, d₃,
        by simp [sdepth]; omega, by rw [hcs₃]; simp [h.cs], by rw [hhigh₃]; exact h.image⟩
    simp only [slen] at i₄
    -- the body
    obtain ⟨σ₅, r₅, h₅⟩ := ih σ₄ (a + 7 + ((ecode L e).length + 6))
      ⟨w₄, run₄, by rw [i₄], by omega, by omega,
        hP.mono (m' := high σ₄) (fun i hi => by rw [k₄.low i hi, hhigh₃])
          (by rw [length_scode]; omega), v₄, d₄, by omega,
        by rw [k₄.cs, hcs₃]; simp [h.cs], (h.image.mono fun i hi => by rw [k₄.low i hi, hhigh₃])⟩
    refine ⟨σ₅, ?_, h₅⟩
    exact ((((Steps.one h.run (notIo_li hAt)).tail ⟨sm₁.running h.run,
      notIo_of_hop (by rw [i₁, h.ip]; omega) hop₁, rfl⟩).tail ⟨sm₁₂.running h.run,
      notIo_of_hop (by rw [i₂, i₁, h.ip]; omega) hop₂, rfl⟩).trans r₄).trans r₅

/-- **Compiled, a run that fails a check stops with `FAULT`**: the machine,
run long enough, halts with `FAULT` alone on its stack. -/
theorem compile_fault (L : Layout) (hL : L.Ok) {p : Stmt} {st : St} (h : SFault L 0 p st)
    (hF : L.Fit p) (s : State) (hw : WF s) (hr : Running s) (hip : getIP s = L.start)
    (hc : CodeAt (high s) 0x100 (compile L p)) (hv : VarsOk L (high s) st) (hd : dstack s = [])
    (hcs : cstack s = []) :
    ∃ n, getRST (runN n s) = 0 ∧ dstack (runN n s) = [FAULT] := by
  have hfit := hF.hi
  have hs : 256 ≤ L.start := by unfold Layout.start; omega
  have himg := L.image_of_compile hF hc
  obtain ⟨hc₁, -⟩ := L.main_of_compile hc
  obtain ⟨s', r', h0, hd'⟩ := fault_runs L hL h s L.start
    ⟨hw, hr, hip, hs, by omega, hc₁, hv, hd, hF.depth, by rw [hcs]; rfl, himg⟩
  obtain ⟨n, hn⟩ := runN_of_steps r'
  exact ⟨n, by rw [hn]; exact h0, by rw [hn]; exact hd'⟩

/-- **Compiled and loaded, a run that fails a check stops with `FAULT`.** -/
theorem load_fault (L : Layout) (hL : L.Ok) {p : Stmt} {st : St} (h : SFault L 0 p st)
    (hF : L.Fit p) :
    ∃ n, getRST (runN n (load L p st)) = 0 ∧ dstack (runN n (load L p st)) = [FAULT] := by
  obtain ⟨hw, hr, hip, hc, hv, hd, hcs⟩ := load_ready L hL p st hF.hi
  exact compile_fault L hL h hF _ hw hr hip hc hv hd hcs

/-! ### Putting the checks in -/

/-- `0 ≤ i ∧ i < k`. -/
def inBounds (i : Exp) (k : ℕ) : Exp :=
  .bin .and (.un .not (.bin .lt i (.lit (.int 0)))) (.bin .lt i (.lit (.int k)))

/-- The check before `A i` is read or written, `A` with `k` cells if it is an array. -/
def bound (cap : ℕ → Option ℕ) (x : ℕ) (i : Exp) : Stmt :=
  match cap x with
  | some k => .guard (inBounds i k)
  | none => .ok

/-- **The checks of an expression**, in the order its code computes it: before
each item of an array is read, that its index is inside the array. -/
def _root_.LaPToP.ProgramTheory.Interpreter.Lang.Exp.guards (cap : ℕ → Option ℕ) : Exp → Stmt
  | .un _ a => a.guards cap
  | .bin _ a b => .seq (a.guards cap) (b.guards cap)
  | .index (.var x) i => .seq (i.guards cap) (bound cap x i)
  | .cond c a b => .seq (c.guards cap) (.cond c (a.guards cap) (b.guards cap))
  | _ => .ok

/-- The checks of a list of expressions, one after another. -/
def guardsList (cap : ℕ → Option ℕ) (es : List Exp) : Stmt :=
  es.foldr (fun e g => .seq (e.guards cap) g) .ok

/-- **A statement with its checks**: before each statement, the checks of the
expressions it computes; in a loop, before each test of its condition. -/
def Stmt.guarded (cap : ℕ → Option ℕ) : Stmt → Stmt
  | .assign x e => .seq (e.guards cap) (.assign x e)
  | .seq p q => .seq (p.guarded cap) (q.guarded cap)
  | .cond c p q => .seq (c.guards cap) (.cond c (p.guarded cap) (q.guarded cap))
  | .loop c p => .seq (c.guards cap) (.loop c (.seq (p.guarded cap) (c.guards cap)))
  | .send ch e => .seq (e.guards cap) (.send ch e)
  | .scope x e p => .seq (e.guards cap) (.scope x e (p.guarded cap))
  | .store x i e => .seq (e.guards cap) (.seq (i.guards cap) (.seq (bound cap x i) (.store x i e)))
  | .fill x es => .seq (guardsList cap es) (.fill x es)
  | .choice p q => .choice (p.guarded cap) (q.guarded cap)
  | .ensure c => .seq (c.guards cap) (.ensure c)
  | .prob a b p q => .seq (a.guards cap) (.seq (b.guards cap) (.prob a b (p.guarded cap) (q.guarded cap)))
  | p => p

/-- **Two layouts for a program and its checked version**: the same variables
and arrays, each named statement checked, and the checks' bounds the arrays'. -/
structure Checked (L L' : Layout) (cap : ℕ → Option ℕ) : Prop where
  n : L'.n = L.n
  arrayAt : ∀ x, L'.arrayAt x = L.arrayAt x
  keys : L'.keys = L.keys
  fits : ∀ s e, Fits L' s e ↔ Fits L s e
  defs : ∀ k, L'.defs k = (L.defs k).guarded cap
  cap : ∀ x, cap x = (L.arrayAt x).map Prod.snd
  small : ∀ x a₀ k, L.arrayAt x = some (a₀, k) → k < 2 ^ 31

/-! ### Checks change nothing -/

/-- A statement that only checks: whatever it ends in is where it started. -/
def IsGuard (L : Layout) (g : Stmt) : Prop := ∀ {d : ℕ} {s t : St}, SEval L d g s t → t = s

theorem isGuard_ok (L : Layout) : IsGuard L .ok := fun h => by cases h; rfl

theorem isGuard_guard (L : Layout) (c : Exp) : IsGuard L (.guard c) := fun h => by cases h; rfl

theorem isGuard_seq {L : Layout} {g₁ g₂ : Stmt} (h₁ : IsGuard L g₁) (h₂ : IsGuard L g₂) :
    IsGuard L (.seq g₁ g₂) := fun h => by
  cases h with
  | seq a b => rw [h₂ b, h₁ a]

theorem isGuard_cond {L : Layout} {c : Exp} {g₁ g₂ : Stmt} (h₁ : IsGuard L g₁) (h₂ : IsGuard L g₂) :
    IsGuard L (.cond c g₁ g₂) := fun h => by
  cases h with
  | condT _ _ a => exact h₁ a
  | condF _ _ a => exact h₂ a

theorem isGuard_bound (L : Layout) (cap : ℕ → Option ℕ) (x : ℕ) (i : Exp) :
    IsGuard L (bound cap x i) := by
  unfold bound; split
  · exact isGuard_guard L _
  · exact isGuard_ok L

theorem isGuard_guards (L : Layout) (cap : ℕ → Option ℕ) : ∀ e : Exp, IsGuard L (e.guards cap)
  | .lit _ | .var _ | .nil | .cons _ _ => isGuard_ok L
  | .un _ a => isGuard_guards L cap a
  | .bin _ a b => isGuard_seq (isGuard_guards L cap a) (isGuard_guards L cap b)
  | .index (.var x) i => isGuard_seq (isGuard_guards L cap i) (isGuard_bound L cap x i)
  | .index (.lit _) _ | .index (.un _ _) _ | .index (.bin _ _ _) _ | .index .nil _
  | .index (.cons _ _) _ | .index (.index _ _) _ | .index (.cond _ _ _) _ => isGuard_ok L
  | .cond c a b => isGuard_seq (isGuard_guards L cap c)
      (isGuard_cond (isGuard_guards L cap a) (isGuard_guards L cap b))

theorem isGuard_guardsList (L : Layout) (cap : ℕ → Option ℕ) :
    ∀ es : List Exp, IsGuard L (guardsList cap es)
  | [] => isGuard_ok L
  | e :: es => isGuard_seq (isGuard_guards L cap e) (isGuard_guardsList L cap es)

theorem guards_id {L : Layout} {cap : ℕ → Option ℕ} {e : Exp} {d : ℕ} {s t : St}
    (h : SEval L d (e.guards cap) s t) : t = s := isGuard_guards L cap e h

/-! ### A run in 32 bits passes its checks -/

theorem inBounds_holds {L : Layout} {s : St} {i : Exp} {j : ℤ} {k : ℕ} (hf : Fits L s i)
    (hj : i.eval s = .int j) (h0 : 0 ≤ j) (hk : j.toNat < k) (hsmall : k < 2 ^ 31) :
    Fits L s (inBounds i k) ∧ (inBounds i k).eval s = .bool true := by
  have hjk : j < k := by omega
  have hr : InRange j := ⟨by omega, by omega⟩
  have hrk : InRange (k : ℤ) := ⟨by omega, by omega⟩
  refine ⟨?_, ?_⟩
  · simp only [inBounds, Fits, Exp.eval, hj]
    refine ⟨⟨⟨hf, .inl ⟨0, rfl, by norm_num [InRange]⟩, ⟨j, rfl, hr⟩, ⟨0, rfl, by norm_num [InRange]⟩⟩, ?_⟩,
      ⟨hf, .inl ⟨k, rfl, hrk⟩, ⟨j, rfl, hr⟩, ⟨k, rfl, hrk⟩⟩, ?_, ?_⟩
    · simp [BinOp.apply, UnOp.apply]
    · simp [BinOp.apply, UnOp.apply]
    · simp [BinOp.apply]
  · simp [inBounds, Exp.eval, hj, BinOp.apply, UnOp.apply]; omega

/-- The checks of an expression that fits all hold. -/
theorem guards_pass {L L' : Layout} {cap : ℕ → Option ℕ} (hc : Checked L L' cap) {d : ℕ} {s : St} :
    ∀ e : Exp, Fits L s e → SEval L' d (e.guards cap) s s
  | .lit _, _ => .ok
  | .var _, _ => .ok
  | .nil, _ => .ok
  | .cons _ _, _ => .ok
  | .un op a, hf => by
    show SEval L' d (a.guards cap) s s
    cases op <;> (try simp only [Fits] at hf)
    all_goals first
      | exact guards_pass hc a hf.1
      | (cases a <;> simp only [Fits] at hf <;> first | exact .ok | exact hf.elim)
  | .bin op a b, hf => by
    show SEval L' d (.seq (a.guards cap) (b.guards cap)) s s
    cases op <;> (try simp only [Fits] at hf)
    all_goals first
      | exact .seq (guards_pass hc a hf.1) (guards_pass hc b hf.2.1)
      | exact hf.elim
  | .index a i, hf => by
    cases a with
    | var x =>
      simp only [Fits] at hf
      obtain ⟨hfi, a₀, k, vs, j, hx, -, hj, h0, hk, -⟩ := hf
      simp only [Exp.guards, bound, hc.cap x, hx, Option.map_some]
      obtain ⟨hf', hv⟩ := inBounds_holds hfi hj h0 hk (hc.small x a₀ k hx)
      exact .seq (guards_pass hc i hfi) (.guard ((hc.fits _ _).mpr hf') hv)
    | _ => simp only [Fits] at hf
  | .cond c a b, hf => by
    simp only [Fits] at hf
    obtain ⟨hfc, ⟨v, hv⟩, -, -, hb⟩ := hf
    simp only [Exp.guards]
    cases v with
    | true =>
      simp only [hv, Value.toBool, ite_true] at hb
      exact .seq (guards_pass hc c hfc) (.condT ((hc.fits _ _).mpr hfc) hv (guards_pass hc a hb))
    | false =>
      simp only [hv, Value.toBool, Bool.false_eq_true, ite_false] at hb
      exact .seq (guards_pass hc c hfc) (.condF ((hc.fits _ _).mpr hfc) hv (guards_pass hc b hb))

theorem guardsList_pass {L L' : Layout} {cap : ℕ → Option ℕ} (hc : Checked L L' cap) {d : ℕ}
    {s : St} : ∀ es : List Exp, (∀ e ∈ es, Fits L s e) → SEval L' d (guardsList cap es) s s
  | [], _ => .ok
  | e :: es, hf => .seq (guards_pass hc e (hf e (by simp)))
      (guardsList_pass hc es fun e he => hf e (by simp [he]))

/-- **The checks never stop a run in 32 bits**: what the program does in 32
bits, its checked version does. -/
theorem guarded_complete {L L' : Layout} {cap : ℕ → Option ℕ} (hc : Checked L L' cap) {d : ℕ}
    {p : Stmt} {s t : St} (h : SEval L d p s t) : SEval L' d (p.guarded cap) s t := by
  have hn := hc.n; have ha := hc.arrayAt; have hk := hc.keys
  have hf : ∀ {s e}, Fits L s e → Fits L' s e := fun h => (hc.fits _ _).mpr h
  induction h with
  | ok => exact .ok
  | assign hx hax hfe =>
    exact .seq (guards_pass hc _ hfe) (.assign (by rw [hn]; exact hx) (by rw [ha]; exact hax) (hf hfe))
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | condT hfc hcv _ ih => exact .seq (guards_pass hc _ hfc) (.condT (hf hfc) hcv ih)
  | condF hfc hcv _ ih => exact .seq (guards_pass hc _ hfc) (.condF (hf hfc) hcv ih)
  | @loopT _ c p s t u hfc hcv _ _ ih₁ ih₂ =>
    simp only [Stmt.guarded] at ih₂ ⊢
    cases ih₂ with
    | @seq _ _ _ _ t₁ _ hG hl =>
      have hG' := hG
      have : t₁ = t := guards_id hG
      subst this
      exact .seq (guards_pass hc _ hfc) (.loopT (hf hfc) hcv (.seq ih₁ hG') hl)
  | loopF hfc hcv => exact .seq (guards_pass hc _ hfc) (.loopF (hf hfc) hcv)
  | call hkk hd _ ih =>
    refine .call (by rw [hk]; exact hkk) hd ?_
    rw [hc.defs]; exact ih
  | scope hx hax hfe hd _ ih =>
    exact .seq (guards_pass hc _ hfe) (.scope (by rw [hn]; exact hx) (by rw [ha]; exact hax) (hf hfe) hd ih)
  | @store _ x i e s hfi hfe =>
    have hfi' := hfi
    simp only [Fits] at hfi'
    obtain ⟨hfi₀, a₀, k, vs, j, hx, -, hj, h0, hjk, -⟩ := hfi'
    obtain ⟨hb, hv⟩ := inBounds_holds hfi₀ hj h0 hjk (hc.small x a₀ k hx)
    simp only [Stmt.guarded, bound, hc.cap x, hx, Option.map_some]
    exact .seq (guards_pass hc _ hfe) (.seq (guards_pass hc _ hfi₀)
      (.seq (.guard (hf hb) hv) (.store (hf hfi) (hf hfe))))
  | fill hx hvs hl hfe =>
    exact .seq (guardsList_pass hc _ hfe) (.fill (by rw [ha]; exact hx) hvs hl fun e he => hf (hfe e he))
  | guard hfc hcv => exact .guard (hf hfc) hcv

/-! ### A checked run is a run -/

/-- **`q` is `p` with checks put in**: checks before or after, and the parts
likewise. -/
inductive Gd (L : Layout) : Stmt → Stmt → Prop
  /-- The same. -/
  | refl {p : Stmt} : Gd L p p
  /-- A check before. -/
  | pre {g p q : Stmt} : IsGuard L g → Gd L p q → Gd L p (.seq g q)
  /-- A check after. -/
  | post {g p q : Stmt} : IsGuard L g → Gd L p q → Gd L p (.seq q g)
  /-- In both parts of a sequence. -/
  | seq {p₁ p₂ q₁ q₂ : Stmt} : Gd L p₁ q₁ → Gd L p₂ q₂ → Gd L (.seq p₁ p₂) (.seq q₁ q₂)
  /-- In both branches. -/
  | cond {c : Exp} {p₁ p₂ q₁ q₂ : Stmt} : Gd L p₁ q₁ → Gd L p₂ q₂ →
      Gd L (.cond c p₁ p₂) (.cond c q₁ q₂)
  /-- In a loop's body. -/
  | loop {c : Exp} {p q : Stmt} : Gd L p q → Gd L (.loop c p) (.loop c q)
  /-- In a scope's body. -/
  | scope {x : ℕ} {e : Exp} {p q : Stmt} : Gd L p q → Gd L (.scope x e p) (.scope x e q)
  /-- In both choices. -/
  | choice {p₁ p₂ q₁ q₂ : Stmt} : Gd L p₁ q₁ → Gd L p₂ q₂ → Gd L (.choice p₁ p₂) (.choice q₁ q₂)
  /-- In both branches of a probabilistic choice. -/
  | prob {a b : Exp} {p₁ p₂ q₁ q₂ : Stmt} : Gd L p₁ q₁ → Gd L p₂ q₂ →
      Gd L (.prob a b p₁ p₂) (.prob a b q₁ q₂)

/-- A statement and its checked version. -/
theorem gd_guarded (L : Layout) (cap : ℕ → Option ℕ) : ∀ p : Stmt, Gd L p (p.guarded cap)
  | .assign _ e => .pre (isGuard_guards L cap e) .refl
  | .seq p q => .seq (gd_guarded L cap p) (gd_guarded L cap q)
  | .cond c p q => .pre (isGuard_guards L cap c) (.cond (gd_guarded L cap p) (gd_guarded L cap q))
  | .loop c p => .pre (isGuard_guards L cap c)
      (.loop (.post (isGuard_guards L cap c) (gd_guarded L cap p)))
  | .send _ e => .pre (isGuard_guards L cap e) .refl
  | .scope _ e p => .pre (isGuard_guards L cap e) (.scope (gd_guarded L cap p))
  | .store x i e => .pre (isGuard_guards L cap e) (.pre (isGuard_guards L cap i)
      (.pre (isGuard_bound L cap x i) .refl))
  | .fill _ es => .pre (isGuard_guardsList L cap es) .refl
  | .choice p q => .choice (gd_guarded L cap p) (gd_guarded L cap q)
  | .ensure c => .pre (isGuard_guards L cap c) .refl
  | .prob a b p q => .pre (isGuard_guards L cap a) (.pre (isGuard_guards L cap b)
      (.prob (gd_guarded L cap p) (gd_guarded L cap q)))
  | .ok | .tick | .recv _ _ | .call _ | .ret | .restore _ _ | .check _ _ | .guard _ => .refl

/-- **A checked run is a run**: what a statement with checks put in does in 32
bits, with each named statement checked, the statement itself does. -/
theorem gd_sound {L L' : Layout} (hn : L'.n = L.n) (ha : ∀ x, L'.arrayAt x = L.arrayAt x)
    (hk : L'.keys = L.keys) (hf : ∀ s e, Fits L' s e ↔ Fits L s e)
    (hdefs : ∀ k, Gd L' (L.defs k) (L'.defs k)) {d : ℕ} {q : Stmt} {s t : St}
    (h : SEval L' d q s t) : ∀ {p : Stmt}, Gd L' p q → SEval L d p s t := by
  induction h with
  | ok => intro p hg; cases hg; exact .ok
  | assign hx hax hfe =>
    intro p hg; cases hg
    exact .assign (by rw [← hn]; exact hx) (by rw [← ha]; exact hax) ((hf _ _).mp hfe)
  | @seq _ q₁ q₂ s t u h₁ h₂ ih₁ ih₂ =>
    intro p hg
    cases hg with
    | refl => exact .seq (ih₁ .refl) (ih₂ .refl)
    | pre hG hq => rw [hG h₁] at ih₂; exact ih₂ hq
    | post hG hq => rw [hG h₂]; exact ih₁ hq
    | seq hq₁ hq₂ => exact .seq (ih₁ hq₁) (ih₂ hq₂)
  | condT hfc hcv _ ih =>
    intro p hg
    cases hg with
    | refl => exact .condT ((hf _ _).mp hfc) hcv (ih .refl)
    | cond hq₁ _ => exact .condT ((hf _ _).mp hfc) hcv (ih hq₁)
  | condF hfc hcv _ ih =>
    intro p hg
    cases hg with
    | refl => exact .condF ((hf _ _).mp hfc) hcv (ih .refl)
    | cond _ hq₂ => exact .condF ((hf _ _).mp hfc) hcv (ih hq₂)
  | loopT hfc hcv _ _ ih₁ ih₂ =>
    intro p hg
    cases hg with
    | refl => exact .loopT ((hf _ _).mp hfc) hcv (ih₁ .refl) (ih₂ .refl)
    | loop hq => exact .loopT ((hf _ _).mp hfc) hcv (ih₁ hq) (ih₂ (.loop hq))
  | loopF hfc hcv =>
    intro p hg
    cases hg with
    | refl => exact .loopF ((hf _ _).mp hfc) hcv
    | loop _ => exact .loopF ((hf _ _).mp hfc) hcv
  | @call _ k _ _ hkk hd _ ih =>
    intro p hg; cases hg
    exact .call (by rw [← hk]; exact hkk) hd (ih (hdefs k))
  | scope hx hax hfe hd _ ih =>
    intro p hg
    have hx' := hx; have hax' := hax
    rw [hn] at hx'; rw [ha] at hax'
    cases hg with
    | refl => exact .scope hx' hax' ((hf _ _).mp hfe) hd (ih .refl)
    | scope hq => exact .scope hx' hax' ((hf _ _).mp hfe) hd (ih hq)
  | store hfi hfe =>
    intro p hg; cases hg
    exact .store ((hf _ _).mp hfi) ((hf _ _).mp hfe)
  | fill hx hvs hl hfe =>
    intro p hg; cases hg
    exact .fill (by rw [← ha]; exact hx) hvs hl fun e he => (hf _ _).mp (hfe e he)
  | guard hfc hcv =>
    intro p hg; cases hg
    exact .guard ((hf _ _).mp hfc) hcv

/-- **The checked program computes the program**: what the checked version does
in 32 bits, the program does. -/
theorem guarded_sound {L L' : Layout} {cap : ℕ → Option ℕ} (hc : Checked L L' cap) {d : ℕ}
    {p : Stmt} {s t : St} (h : SEval L' d (p.guarded cap) s t) : SEval L d p s t :=
  gd_sound hc.n hc.arrayAt hc.keys hc.fits (fun k => by rw [hc.defs]; exact gd_guarded L' cap _) h
    (gd_guarded L' cap p)

end LaPToP.ProgramTheory.CompileB4
