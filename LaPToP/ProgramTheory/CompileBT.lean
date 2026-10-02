import LaPToP.ProgramTheory.CompileNet
import LaPToP.ProgramTheory.Alloc

/-!
# Backtracking on b4

`P or Q` and `ensure c` (Section 5.4.0), compiled for a lone program: a choice
keeps a choice point — where the other choice's code is, and a copy of every
cell — above the cells, and a failed `ensure` takes the last one back, or, with
none left, sets a flag and halts. The code that keeps choice points is written
in the language itself, over one array of the memory's words (`Layout.rt`), so
it is proved here as a program (`copy_runs`, `save_runs`, `pop_runs`) and run
by `CompileB4.stmt_runs`.

The language's backtracking is an abstract machine (`BStep`): what is left to
run, its state, and the choice points, each what is left and the state to go
back to. The compiled program simulates it (`bt_simulates`), and what it finds
is what the language allows (`bt_sound`), and when it fails, the language has
no poststate (`bt_fail`).
-/

namespace LaPToP.ProgramTheory.CompileBT

open B4
open LaPToP.ProgramTheory.Interpreter
open LaPToP.ProgramTheory.Interpreter.Lang
open LaPToP.ProgramTheory.CompileB4
open LaPToP.ProgramTheory.CompileNet
open LaPToP.ProgramTheory.Interpreter.Network
open LaPToP.ProgramTheory.Alloc (rd rd_set fits_lt fits_add fits_sub inR)

/-! ### The runtime, as a program over memory's words -/

/-- How many words the runtime's array has. -/
def _root_.LaPToP.ProgramTheory.CompileB4.Layout.cap (L : Layout) : ℕ := L.W + 5 + L.choices * (L.W + 1)

/-- A state of the runtime: its array holds `ms`. -/
def MS (ms : List ℤ) (σ : St) : St := Function.update σ 0 (.list (ms.map .int))

@[simp] theorem MS_zero (ms : List ℤ) (σ : St) : MS ms σ 0 = .list (ms.map .int) := by simp [MS]

@[simp] theorem eval_mem (ms : List ℤ) (σ : St) (e : Exp) :
    (RT.mem e).eval (MS ms σ) = .int (rd ms (e.eval (MS ms σ)).toInt) := by
  simp only [Exp.eval, MS_zero, Value.index, Value.toList_list, rd]
  split
  · rw [show (default : Value) = .int 0 from rfl, List.getD_map]
  · rfl

@[simp] theorem eval_rlit {st : St} {k : ℤ} : (RT.lit k).eval st = .int k := rfl
@[simp] theorem eval_radd {st : St} {a b : Exp} : (RT.add a b).eval st =
    BinOp.apply .add (a.eval st) (b.eval st) := rfl
@[simp] theorem eval_rsub {st : St} {a b : Exp} : (RT.sub a b).eval st =
    BinOp.apply .sub (a.eval st) (b.eval st) := rfl
@[simp] theorem eval_rmul {st : St} {a b : Exp} : (Exp.bin .mul a b).eval st =
    BinOp.apply .mul (a.eval st) (b.eval st) := rfl
@[simp] theorem eval_rlt {st : St} {a b : Exp} : (Exp.bin .lt a b).eval st =
    BinOp.apply .lt (a.eval st) (b.eval st) := rfl

theorem fits_mul {L : Layout} {st : St} {a b : Exp} {x y : ℤ} (fa : Fits L st a) (fb : Fits L st b)
    (ea : a.eval st = .int x) (eb : b.eval st = .int y) (rx : InRange x) (ry : InRange y)
    (r : InRange (x * y)) : Fits L st (.bin .mul a b) :=
  ⟨fa, fb, ⟨x, ea, rx⟩, ⟨y, eb, ry⟩, by rw [ea, eb]; exact r⟩

theorem fits_rlit {L : Layout} {st : St} {k : ℤ} (hk : InRange k) : Fits L st (RT.lit k) :=
  Or.inl ⟨k, rfl, hk⟩

theorem fits_mem {L : Layout} {ms : List ℤ} {σ : St} {e : Exp} {j : ℤ} (fe : Fits L.rt (MS ms σ) e)
    (he : e.eval (MS ms σ) = .int j) (h0 : 0 ≤ j) (hj : j < ms.length) (hl : ms.length = L.cap) :
    Fits L.rt (MS ms σ) (RT.mem e) :=
  ⟨fe, _, _, _, j, L.rt_arrayAt0, MS_zero ms σ, he, h0, by unfold Layout.cap at hl; omega,
    by simp; omega⟩

theorem upd_MS (ms : List ℤ) (σ : St) {j k : ℤ} (h0 : 0 ≤ j) (hj : j < ms.length) :
    Function.update (MS ms σ) 0 ((MS ms σ 0).update [j] (.int k)) = MS (ms.set j.toNat k) σ := by
  rw [MS_zero, Value.update_single ⟨h0, by simp; omega⟩, ← List.map_set]
  simp [MS]

theorem sev_rstore {L : Layout} {d : ℕ} {ms : List ℤ} {σ : St} {i e : Exp} {j k : ℤ}
    (fi : Fits L.rt (MS ms σ) i) (fe : Fits L.rt (MS ms σ) e) (hi : i.eval (MS ms σ) = .int j)
    (he : e.eval (MS ms σ) = .int k) (h0 : 0 ≤ j) (hj : j < ms.length) (hl : ms.length = L.cap) :
    SEval L.rt d (.store 0 i e) (MS ms σ) (MS (ms.set j.toNat k) σ) := by
  have := SEval.store (L := L.rt) (d := d) (x := 0) (i := i) (e := e) (s := MS ms σ)
    (fits_mem fi hi h0 hj hl) fe
  rwa [hi, he, Value.toInt_int, upd_MS ms σ h0 hj] at this


/-- **The copy loop** copies `c` words from `src` on to `dst` on, the two ranges
apart from each other and from the loop's own cells, and changes nothing else
but its own cells. -/
theorem copy_runs {L : Layout} {d : ℕ} {σ : St} (hcap : L.cap < 2 ^ 20) :
    ∀ (c : ℕ) (ms : List ℤ) (src dst : ℤ),
    ms.length = L.cap → rd ms (L.W + 1) = src → rd ms (L.W + 2) = dst → rd ms (L.W + 3) = c →
    0 ≤ src → 0 ≤ dst → src + c ≤ ms.length → dst + c ≤ ms.length →
    (dst + c ≤ src ∨ src + c ≤ dst) →
    (src + c ≤ L.W + 1 ∨ L.W + 4 ≤ src) → (dst + c ≤ L.W + 1 ∨ L.W + 4 ≤ dst) →
    ∃ ms' : List ℤ, SEval L.rt d (RT.copy L.W) (MS ms σ) (MS ms' σ) ∧ ms'.length = ms.length ∧
      (∀ i : ℤ, 0 ≤ i → i < c → rd ms' (dst + i) = rd ms (src + i)) ∧
      (∀ j : ℤ, (j < dst ∨ dst + c ≤ j) → j ≠ L.W + 1 → j ≠ L.W + 2 → j ≠ L.W + 3 →
        rd ms' j = rd ms j) := by
  have hcw : L.W + 5 ≤ L.cap := by unfold Layout.cap; omega
  intro c
  induction c with
  | zero =>
    intro ms src dst hl hs hd hc _ _ _ _ _ _ _
    refine ⟨ms, .loopF (fits_lt (x := 0) (y := 0) (fits_rlit rng) (fits_mem (j := L.W + 3) (fits_rlit rng) rfl
      (by omega) (by omega) hl) rfl (by simp [hc]) rng rng) (by simp [BinOp.apply, hc]),
      rfl, fun i _ hi => by omega, fun _ _ _ _ _ => rfl⟩
  | succ c ih =>
    intro ms src dst hl hs hd hc s0 d0 sl dl dj ts td
    push_cast at sl dl dj ts td
    have fW : ∀ k : ℕ, k ≤ 4 → Fits L.rt (MS ms σ) (RT.mem (RT.lit (L.W + k))) := fun k hk =>
      fits_mem (j := L.W + k) (fits_rlit rng) rfl (by omega) (by omega) hl
    -- M dst := M src
    let ms₁ := ms.set dst.toNat (rd ms src)
    have l₁ : ms₁.length = ms.length := by simp [ms₁]
    have r₁ := rd_set (ms := ms) (k := rd ms src) d0 (by omega)
    have s₁ := sev_rstore (d := d) (σ := σ) (j := dst) (k := rd ms src) (fW 2 (by omega))
      (fits_mem (j := src) (fW 1 (by omega)) (by simp [hs]) s0 (by omega) hl)
      (by simp [hd]) (by simp [hs]) d0 (by omega) hl
    -- src := src + 1
    let ms₂ := ms₁.set (L.W + 1 : ℤ).toNat (src + 1)
    have l₂ : ms₂.length = ms.length := by simp [ms₂, l₁]
    have r₂ := rd_set (ms := ms₁) (k := src + 1) (j := L.W + 1) (by omega) (by omega)
    have e₁₁ : rd ms₁ (L.W + 1) = src := by rw [r₁, ite_eq_right (by omega), hs]
    have e₁₂ : rd ms₁ (L.W + 2) = dst := by rw [r₁, ite_eq_right (by omega), hd]
    have e₁₃ : rd ms₁ (L.W + 3) = c + 1 := by rw [r₁, ite_eq_right (by omega), hc]; push_cast; omega
    have s₂ := sev_rstore (d := d) (σ := σ) (ms := ms₁) (j := L.W + 1) (k := src + 1) (fits_rlit rng)
      (fits_add (x := src) (y := 1) (fits_mem (j := L.W + 1) (fits_rlit rng) rfl (by omega) (by omega)
        (by rw [l₁, hl])) (fits_rlit rng) (by simp [e₁₁]) rfl rng rng rng)
      rfl (by simp [BinOp.apply, e₁₁]) (by omega) (by omega)
      (by rw [l₁, hl])
    -- dst := dst + 1
    let ms₃ := ms₂.set (L.W + 2 : ℤ).toNat (dst + 1)
    have l₃ : ms₃.length = ms.length := by simp [ms₃, l₂]
    have r₃ := rd_set (ms := ms₂) (k := dst + 1) (j := L.W + 2) (by omega) (by omega)
    have e₂ : rd ms₂ (L.W + 2) = dst := by
      rw [r₂, ite_eq_right (by omega), e₁₂]
    have s₃ := sev_rstore (d := d) (σ := σ) (ms := ms₂) (j := L.W + 2) (k := dst + 1) (fits_rlit rng)
      (fits_add (x := dst) (y := 1) (fits_mem (j := L.W + 2) (fits_rlit rng) rfl (by omega) (by omega)
        (by rw [l₂, hl])) (fits_rlit rng) (by simp [e₂]) rfl rng rng rng)
      rfl (by simp [BinOp.apply, e₂]) (by omega) (by omega) (by rw [l₂, hl])
    -- c := c - 1
    let ms₄ := ms₃.set (L.W + 3 : ℤ).toNat c
    have l₄ : ms₄.length = ms.length := by simp [ms₄, l₃]
    have r₄ := rd_set (ms := ms₃) (k := c) (j := L.W + 3) (by omega) (by omega)
    have e₃ : rd ms₃ (L.W + 3) = c + 1 := by
      rw [r₃, ite_eq_right (by omega), r₂, ite_eq_right (by omega), e₁₃]
    have s₄ := sev_rstore (d := d) (σ := σ) (ms := ms₃) (j := L.W + 3) (k := c) (fits_rlit rng)
      (fits_sub (x := c + 1) (y := 1) (fits_mem (j := L.W + 3) (fits_rlit rng) rfl (by omega) (by omega)
        (by rw [l₃, hl])) (fits_rlit rng) (by simp [e₃]) rfl rng rng rng)
      rfl (by simp [BinOp.apply, e₃]) (by omega) (by omega) (by rw [l₃, hl])
    have rd₄ : ∀ i : ℤ, rd ms₄ i = if i = L.W + 3 then (c : ℤ) else if i = L.W + 2 then dst + 1 else
        if i = L.W + 1 then src + 1 else if i = dst then rd ms src else rd ms i := fun i => by
      rw [r₄, r₃, r₂, r₁]
    obtain ⟨ms', run', l', cp', fr'⟩ := ih ms₄ (src + 1) (dst + 1) (by rw [l₄, hl])
      (by rw [rd₄]; simp) (by rw [rd₄]; simp)
      (by rw [rd₄]; simp) (by omega) (by omega) (by rw [l₄]; omega) (by rw [l₄]; omega) (by omega)
      (by omega) (by omega)
    refine ⟨ms', .loopT (fits_lt (x := 0) (y := c + 1) (fits_rlit rng) (fW 3 (by omega)) rfl
      (by simp [hc]) rng rng)
      (by simp [BinOp.apply, hc]) (.seq s₁ (.seq s₂ (.seq s₃ s₄))) run', by rw [l', l₄], ?_, ?_⟩
    · intro i hi0 hic
      rcases hi0.eq_or_lt with h | h
      · subst h
        rw [fr' _ (by omega) (by omega) (by omega) (by omega), rd₄]
        simp only [add_zero]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]; simp
      · have := cp' (i - 1) (by omega) (by omega)
        rw [show dst + 1 + (i - 1) = dst + i by omega, show src + 1 + (i - 1) = src + i by omega,
          rd₄] at this
        rw [this, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
    · intro j hj h1 h2 h3
      rw [fr' j (by omega) h1 h2 h3, rd₄, ite_eq_right h3, ite_eq_right h2, ite_eq_right h1,
        ite_eq_right (by omega)]

/-- Where choice point `k` starts. -/
def recIdx (L : Layout) (k : ℕ) : ℤ := L.W + 5 + k * (L.W + 1)

theorem eval_recAt {L : Layout} {ms : List ℤ} {σ : St} {k : ℕ} (hk : rd ms L.W = k) :
    (RT.recAt L.W).eval (MS ms σ) = .int (recIdx L k) := by
  simp [RT.recAt, BinOp.apply, hk, recIdx]

theorem fits_recAt {L : Layout} {ms : List ℤ} {σ : St} {k : ℕ} (hl : ms.length = L.cap)
    (hcap : L.cap < 2 ^ 20) (hk : rd ms L.W = k) (hkc : k ≤ L.choices) :
    Fits L.rt (MS ms σ) (RT.recAt L.W) := by
  have hcw : L.W + 5 ≤ L.cap := by unfold Layout.cap; omega
  have hkw : k * (L.W + 1) ≤ L.cap := by
    unfold Layout.cap; nlinarith
  have hP1 : (k : ℤ) * ((L.W : ℤ) + 1) ≤ L.cap := by exact_mod_cast hkw
  have hP0 : 0 ≤ (k : ℤ) * ((L.W : ℤ) + 1) := by positivity
  have hkcap : k ≤ L.cap := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hkw
  exact fits_add (x := L.W + 5) (y := k * (L.W + 1)) (fits_rlit rng)
    (fits_mul (x := k) (y := L.W + 1) (fits_mem (j := L.W) (fits_rlit rng) rfl (by omega) (by omega) hl)
      (fits_rlit rng) (by simp [hk]) rfl rng rng rng)
    rfl (by simp [BinOp.apply, hk]) rng rng rng

/-- **Keeping a choice point**: the `k`-th, with the other choice at `alt` and a
copy of the cells; the count goes up by one. -/
theorem save_runs {L : Layout} {d : ℕ} {σ : St} (hcap : L.cap < 2 ^ 20) {ms : List ℤ} {k : ℕ}
    {alt : ℕ} (hl : ms.length = L.cap) (hk : rd ms L.W = k) (hkc : k < L.choices)
    (halt : alt < 2 ^ 20) :
    ∃ ms' : List ℤ, SEval L.rt d (RT.save L.W alt) (MS ms σ) (MS ms' σ) ∧ ms'.length = ms.length ∧
      rd ms' L.W = k + 1 ∧ rd ms' (recIdx L k) = alt ∧
      (∀ i : ℤ, 0 ≤ i → i < L.W → rd ms' (recIdx L k + 1 + i) = rd ms i) ∧
      (∀ j : ℤ, (j < recIdx L k ∨ recIdx L k + L.W + 1 ≤ j) → j ≠ L.W → j ≠ L.W + 1 →
        j ≠ L.W + 2 → j ≠ L.W + 3 → rd ms' j = rd ms j) := by
  have hcw : L.W + 5 ≤ L.cap := by unfold Layout.cap; omega
  have hR : recIdx L k + L.W + 1 ≤ L.cap := by
    unfold recIdx Layout.cap
    have : (k + 1) * (L.W + 1) ≤ L.choices * (L.W + 1) := Nat.mul_le_mul_right _ hkc
    have h2 : ((k : ℤ) + 1) * ((L.W : ℤ) + 1) ≤ (L.choices : ℤ) * ((L.W : ℤ) + 1) := by exact_mod_cast this
    push_cast; nlinarith
  have hch : L.choices ≤ L.cap :=
    le_trans (Nat.le_mul_of_pos_right L.choices (by omega : 0 < L.W + 1)) (by unfold Layout.cap; omega)
  have hR0 : (L.W : ℤ) + 5 ≤ recIdx L k := by
    unfold recIdx; have : (0 : ℤ) ≤ k * (L.W + 1) := by positivity
    omega
  set R := recIdx L k with hRdef
  have fW : ∀ (ms₀ : List ℤ) (k : ℕ), ms₀.length = L.cap → k ≤ 4 →
      Fits L.rt (MS ms₀ σ) (RT.mem (RT.lit (L.W + k))) := fun ms₀ k h hk =>
    fits_mem (j := L.W + k) (fits_rlit rng) rfl (by omega) (by omega) h
  -- M R := alt
  let ms₁ := ms.set R.toNat alt
  have l₁ : ms₁.length = ms.length := by simp [ms₁]
  have r₁ := rd_set (ms := ms) (k := alt) (j := R) (by omega) (by omega)
  have s₁ := sev_rstore (d := d) (σ := σ) (j := R) (k := alt) (fits_recAt hl hcap hk hkc.le)
    (fits_rlit rng) (eval_recAt hk) rfl (by omega) (by omega) hl
  -- M (W+1) := 0; M (W+2) := R + 1; M (W+3) := W
  let ms₂ := ms₁.set (L.W + 1 : ℤ).toNat 0
  have l₂ : ms₂.length = ms.length := by simp [ms₂, l₁]
  have r₂ := rd_set (ms := ms₁) (k := 0) (j := L.W + 1) (by omega) (by omega)
  have s₂ := sev_rstore (d := d) (σ := σ) (ms := ms₁) (j := L.W + 1) (k := 0) (fits_rlit rng)
    (fits_rlit rng) rfl rfl (by omega) (by omega) (by rw [l₁, hl])
  have hk₂ : rd ms₂ L.W = k := by rw [r₂, ite_eq_right (by omega), r₁, ite_eq_right (by omega), hk]
  let ms₃ := ms₂.set (L.W + 2 : ℤ).toNat (R + 1)
  have l₃ : ms₃.length = ms.length := by simp [ms₃, l₂]
  have r₃ := rd_set (ms := ms₂) (k := R + 1) (j := L.W + 2) (by omega) (by omega)
  have s₃ := sev_rstore (d := d) (σ := σ) (ms := ms₂) (j := L.W + 2) (k := R + 1) (fits_rlit rng)
    (fits_add (y := 1) (fits_recAt (by rw [l₂, hl]) hcap hk₂ hkc.le) (fits_rlit rng) (eval_recAt hk₂) rfl
      rng rng rng) rfl (by simp only [eval_radd, eval_recAt hk₂]; simp [BinOp.apply]; rfl) (by omega)
      (by omega) (by rw [l₂, hl])
  let ms₄ := ms₃.set (L.W + 3 : ℤ).toNat L.W
  have l₄ : ms₄.length = ms.length := by simp [ms₄, l₃]
  have r₄ := rd_set (ms := ms₃) (k := L.W) (j := L.W + 3) (by omega) (by omega)
  have s₄ := sev_rstore (d := d) (σ := σ) (ms := ms₃) (j := L.W + 3) (k := L.W) (fits_rlit rng)
    (fits_rlit rng) rfl rfl (by omega) (by omega) (by rw [l₃, hl])
  have rd₄ : ∀ i : ℤ, rd ms₄ i = if i = L.W + 3 then (L.W : ℤ) else if i = L.W + 2 then R + 1 else
      if i = L.W + 1 then 0 else if i = R then (alt : ℤ) else rd ms i := fun i => by
    rw [r₄, r₃, r₂, r₁]
  -- copy the cells
  obtain ⟨ms₅, run₅, l₅, cp₅, fr₅⟩ := copy_runs (d := d) (σ := σ) hcap L.W ms₄ 0 (R + 1)
    (by rw [l₄, hl]) (by rw [rd₄]; simp) (by rw [rd₄]; simp) (by rw [rd₄]; simp) le_rfl (by omega)
    (by rw [l₄]; omega) (by rw [l₄]; omega) (by omega) (by omega) (by omega)
  -- the count goes up
  have hk₅ : rd ms₅ L.W = k := by
    rw [fr₅ _ (by omega) (by omega) (by omega) (by omega), rd₄]; simp only [ite_eq_right (by omega : ((L.W : ℤ) ≠ L.W + 3)), ite_eq_right (by omega : ((L.W : ℤ) ≠ L.W + 2)), ite_eq_right (by omega : ((L.W : ℤ) ≠ L.W + 1)), ite_eq_right (by omega : ((L.W : ℤ) ≠ R)), hk]
  let ms₆ := ms₅.set (L.W : ℤ).toNat (k + 1)
  have l₆ : ms₆.length = ms.length := by simp [ms₆, l₅, l₄]
  have r₆ := rd_set (ms := ms₅) (k := k + 1) (j := L.W) (by omega) (by rw [l₅, l₄]; omega)
  have s₆ := sev_rstore (d := d) (σ := σ) (ms := ms₅) (j := L.W) (k := k + 1) (fits_rlit rng)
    (fits_add (x := k) (y := 1) (fits_mem (j := L.W) (fits_rlit rng) rfl (by omega)
      (by rw [l₅, l₄]; omega) (by rw [l₅, l₄, hl])) (fits_rlit rng) (by simp [hk₅]) rfl rng rng rng)
    rfl (by simp [BinOp.apply, hk₅]) (by omega) (by rw [l₅, l₄]; omega) (by rw [l₅, l₄, hl])
  refine ⟨ms₆, .seq s₁ (.seq s₂ (.seq s₃ (.seq s₄ (.seq run₅ s₆)))), l₆,
    by rw [r₆, ite_eq_left rfl], ?_, ?_, ?_⟩
  · rw [r₆, ite_eq_right (by omega), fr₅ _ (by omega) (by omega) (by omega) (by omega), rd₄]
    simp only [ite_eq_right (by omega : R ≠ L.W + 3), ite_eq_right (by omega : R ≠ L.W + 2),
      ite_eq_right (by omega : R ≠ L.W + 1), ite_true]
  · intro i h0 hi
    rw [r₆, ite_eq_right (by omega), show R + 1 + i = R + 1 + i from rfl, cp₅ i h0 hi, zero_add, rd₄]
    simp only [ite_eq_right (by omega : i ≠ L.W + 3), ite_eq_right (by omega : i ≠ L.W + 2),
      ite_eq_right (by omega : i ≠ L.W + 1), ite_eq_right (by omega : i ≠ R)]
  · intro j hj h0 h1 h2 h3
    rw [r₆, ite_eq_right h0, fr₅ j (by omega) h1 h2 h3, rd₄, ite_eq_right h3, ite_eq_right h2,
      ite_eq_right h1, ite_eq_right (by omega)]

/-- **Taking a choice point back**: the last, the `k`-th; its copy goes back into
the cells, and the count goes down by one. -/
theorem pop_runs {L : Layout} {d : ℕ} {σ : St} (hcap : L.cap < 2 ^ 20) {ms : List ℤ} {k : ℕ}
    (hl : ms.length = L.cap) (hk : rd ms L.W = k + 1) (hkc : k < L.choices) :
    ∃ ms' : List ℤ, SEval L.rt d (RT.pop L.W) (MS ms σ) (MS ms' σ) ∧ ms'.length = ms.length ∧
      rd ms' L.W = k ∧ (∀ i : ℤ, 0 ≤ i → i < L.W → rd ms' i = rd ms (recIdx L k + 1 + i)) ∧
      (∀ j : ℤ, L.W + 4 ≤ j → rd ms' j = rd ms j) := by
  have hcw : L.W + 5 ≤ L.cap := by unfold Layout.cap; omega
  have hch : L.choices ≤ L.cap :=
    le_trans (Nat.le_mul_of_pos_right L.choices (by omega : 0 < L.W + 1)) (by unfold Layout.cap; omega)
  have hR : recIdx L k + L.W + 1 ≤ L.cap := by
    unfold recIdx Layout.cap
    have : (k + 1) * (L.W + 1) ≤ L.choices * (L.W + 1) := Nat.mul_le_mul_right _ hkc
    have h2 : ((k : ℤ) + 1) * ((L.W : ℤ) + 1) ≤ (L.choices : ℤ) * ((L.W : ℤ) + 1) := by exact_mod_cast this
    push_cast; nlinarith
  have hR0 : (L.W : ℤ) + 5 ≤ recIdx L k := by
    unfold recIdx; have : (0 : ℤ) ≤ k * (L.W + 1) := by positivity
    omega
  set R := recIdx L k with hRdef
  -- the count goes down
  let ms₁ := ms.set (L.W : ℤ).toNat k
  have l₁ : ms₁.length = ms.length := by simp [ms₁]
  have r₁ := rd_set (ms := ms) (k := k) (j := L.W) (by omega) (by omega)
  have s₁ := sev_rstore (d := d) (σ := σ) (j := L.W) (k := k) (fits_rlit rng)
    (fits_sub (x := k + 1) (y := 1) (fits_mem (j := L.W) (fits_rlit rng) rfl (by omega) (by omega) hl)
      (fits_rlit rng) (by simp [hk]) rfl rng rng rng) rfl (by simp [BinOp.apply, hk]) (by omega)
    (by omega) hl
  have hk₁ : rd ms₁ L.W = k := by rw [r₁, ite_eq_left rfl]
  -- src := R + 1; dst := 0; c := W
  let ms₂ := ms₁.set (L.W + 1 : ℤ).toNat (R + 1)
  have l₂ : ms₂.length = ms.length := by simp [ms₂, l₁]
  have r₂ := rd_set (ms := ms₁) (k := R + 1) (j := L.W + 1) (by omega) (by omega)
  have s₂ := sev_rstore (d := d) (σ := σ) (ms := ms₁) (j := L.W + 1) (k := R + 1) (fits_rlit rng)
    (fits_add (y := 1) (fits_recAt (by rw [l₁, hl]) hcap hk₁ hkc.le) (fits_rlit rng) (eval_recAt hk₁) rfl
      rng rng rng) rfl (by simp only [eval_radd, eval_recAt hk₁]; simp [BinOp.apply]; rfl) (by omega)
      (by omega) (by rw [l₁, hl])
  let ms₃ := ms₂.set (L.W + 2 : ℤ).toNat 0
  have l₃ : ms₃.length = ms.length := by simp [ms₃, l₂]
  have r₃ := rd_set (ms := ms₂) (k := 0) (j := L.W + 2) (by omega) (by omega)
  have s₃ := sev_rstore (d := d) (σ := σ) (ms := ms₂) (j := L.W + 2) (k := 0) (fits_rlit rng)
    (fits_rlit rng) rfl rfl (by omega) (by omega) (by rw [l₂, hl])
  let ms₄ := ms₃.set (L.W + 3 : ℤ).toNat L.W
  have l₄ : ms₄.length = ms.length := by simp [ms₄, l₃]
  have r₄ := rd_set (ms := ms₃) (k := L.W) (j := L.W + 3) (by omega) (by omega)
  have s₄ := sev_rstore (d := d) (σ := σ) (ms := ms₃) (j := L.W + 3) (k := L.W) (fits_rlit rng)
    (fits_rlit rng) rfl rfl (by omega) (by omega) (by rw [l₃, hl])
  have rd₄ : ∀ i : ℤ, rd ms₄ i = if i = L.W + 3 then (L.W : ℤ) else if i = L.W + 2 then 0 else
      if i = L.W + 1 then R + 1 else if i = L.W then (k : ℤ) else rd ms i := fun i => by
    rw [r₄, r₃, r₂, r₁]
  obtain ⟨ms₅, run₅, l₅, cp₅, fr₅⟩ := copy_runs (d := d) (σ := σ) hcap L.W ms₄ (R + 1) 0
    (by rw [l₄, hl]) (by rw [rd₄]; simp) (by rw [rd₄]; simp) (by rw [rd₄]; simp) (by omega) le_rfl
    (by rw [l₄]; omega) (by rw [l₄]; omega) (by omega) (by omega) (by omega)
  refine ⟨ms₅, .seq s₁ (.seq s₂ (.seq s₃ (.seq s₄ run₅))), by rw [l₅, l₄], ?_, ?_, ?_⟩
  · rw [fr₅ _ (by omega) (by omega) (by omega) (by omega), rd₄]
    simp only [ite_eq_right (by omega : ((L.W : ℤ) ≠ L.W + 3)), ite_eq_right (by omega : ((L.W : ℤ) ≠ L.W + 2)),
      ite_eq_right (by omega : ((L.W : ℤ) ≠ L.W + 1)), ite_true]
  · intro i h0 hi
    have := cp₅ i h0 hi
    rw [zero_add] at this
    rw [this, rd₄]
    simp only [ite_eq_right (by omega : R + 1 + i ≠ L.W + 3), ite_eq_right (by omega : R + 1 + i ≠ L.W + 2),
      ite_eq_right (by omega : R + 1 + i ≠ L.W + 1), ite_eq_right (by omega : R + 1 + i ≠ L.W)]
  · intro j hj
    rw [fr₅ j (by omega) (by omega) (by omega) (by omega), rd₄, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ### Memory as words -/

/-- Word `j` from the first cell. -/
def Wd (L : Layout) (m : ℕ → UInt8) (j : ℕ) : UInt32 := word m (L.base + 4 * j)

theorem fromInt32_toInt32 (w : UInt32) : fromInt32 (toInt32 w) = w := by
  apply UInt32.toNat_inj.mp
  have := w.toNat_lt
  unfold fromInt32 toInt32
  simp only
  split_ifs <;> simp [UInt32.toNat_ofNat'] <;> omega

/-- Memory's words from the first cell, as the runtime's array holds them. -/
def words (L : Layout) (m : ℕ → UInt8) : List ℤ :=
  (List.range L.cap).map fun j => toInt32 (Wd L m j)

@[simp] theorem length_words (L : Layout) (m : ℕ → UInt8) : (words L m).length = L.cap := by
  simp [words]

theorem rd_words {L : Layout} {m : ℕ → UInt8} {j : ℕ} (hj : j < L.cap) :
    rd (words L m) j = toInt32 (Wd L m j) := by
  simp [rd, words, List.getD_eq_getElem?_getD, hj]

theorem varsOk_words (L : Layout) (m : ℕ → UInt8) (σ : St) : VarsOk L.rt m (MS (words L m) σ) := by
  refine ⟨fun x hx => by simp [Layout.rt] at hx, fun x a₀ cap hx vs hvs j hj hjl => ?_⟩
  have hx0 : x = 0 := by
    by_contra h; simp [Layout.rt, Layout.arrayAt, arrFrom, Ne.symm h] at hx
  subst hx0
  rw [L.rt_arrayAt0] at hx; cases hx
  simp only [MS_zero, Value.list.injEq] at hvs; subst hvs
  simp only [List.length_map, length_words] at hjl
  rw [List.getD_eq_getElem _ _ (by simpa using hjl), List.getElem_map]
  simp only [words, List.getElem_map, List.getElem_range, enc, fromInt32_toInt32]
  rfl

theorem wd_of_varsOk {L : Layout} {m : ℕ → UInt8} {ms : List ℤ} {σ : St}
    (h : VarsOk L.rt m (MS ms σ)) (hl : ms.length = L.cap) {j : ℕ} (hj : j < L.cap) :
    Wd L m j = fromInt32 (rd ms j) := by
  have := h.2 0 _ _ L.rt_arrayAt0 _ (MS_zero ms σ) j (by unfold Layout.cap at hj; omega)
    (by simp; omega)
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map] at this
  unfold Wd; rw [this]
  simp [enc, rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < ms.length by omega)]

theorem arrFrom_off : ∀ (l : List (ℕ × ℕ)) (a x a₀ c : ℕ), arrFrom a l x = some (a₀, c) →
    ∃ o, a₀ = a + 4 * o ∧ o + c ≤ cellsOf l
  | [], _, _, _, _, h => by simp [arrFrom] at h
  | (y, c') :: rest, a, x, a₀, c, h => by
    simp only [arrFrom] at h
    simp only [cellsOf, List.map_cons, List.sum_cons]
    split_ifs at h
    · cases h; exact ⟨0, by omega, by omega⟩
    · obtain ⟨o, h₁, h₂⟩ := arrFrom_off rest _ x a₀ c h
      simp only [cellsOf] at h₂
      exact ⟨c' + o, by omega, by omega⟩

/-- The cells hold a state by their words alone. -/
theorem varsOk_congr {L : Layout} {m m' : ℕ → UInt8} {st : St} (h : VarsOk L m st)
    (hw : ∀ k < L.W, Wd L m' k = Wd L m k) : VarsOk L m' st := by
  refine ⟨fun x hx => ?_, fun x a₀ c hx vs hvs j hj hjl => ?_⟩
  · have := hw x (by unfold Layout.W; omega)
    unfold Wd at this; unfold Layout.addr; rw [this]; exact h.1 x hx
  · obtain ⟨o, h₁, h₂⟩ := arrFrom_off _ _ _ _ _ hx
    have := hw (L.n + o + j) (by unfold Layout.W; omega)
    unfold Wd at this
    rw [show a₀ + 4 * j = L.base + 4 * (L.n + o + j) by omega, this,
      show L.base + 4 * (L.n + o + j) = a₀ + 4 * j by omega]
    exact h.2 x a₀ c hx vs hvs j hj hjl

/-- Memory seen from word `o` on. -/
def Shift (m : ℕ → UInt8) (o : ℕ) : ℕ → UInt8 := fun a => m (a + 4 * o)

theorem wd_shift (L : Layout) (m : ℕ → UInt8) (o k : ℕ) : Wd L (Shift m o) k = Wd L m (o + k) := by
  unfold Wd Shift word
  simp only []
  rw [show L.base + 4 * k + 4 * o = L.base + 4 * (o + k) by omega,
    show L.base + 4 * k + 1 + 4 * o = L.base + 4 * (o + k) + 1 by omega,
    show L.base + 4 * k + 2 + 4 * o = L.base + 4 * (o + k) + 2 by omega,
    show L.base + 4 * k + 3 + 4 * o = L.base + 4 * (o + k) + 3 by omega]

/-! ### Backtracking, as an abstract machine -/

/-- What backtracking holds: what is left to run and its state, and the choice
points, the last first, each what is left and the state to go back to. -/
structure BCfg where
  /-- What is left to run, and its state. -/
  cur : List Stmt × PSt ℕ Value
  /-- The choice points. -/
  cps : List (List Stmt × PSt ℕ Value)

/-- A lone program, as a process with no channels. -/
def lone : SProc := ⟨.ok, [], []⟩

/-- No scripts. -/
def noScripts : Scripts Value := fun _ => []

/-- **A step of backtracking, in 32 bits**: a step of the program, other than
time; a choice, which keeps the other choice as a choice point; or an `ensure`,
which goes on, or goes back to the last choice point. Choices and failures are
outside calls and scopes. -/
inductive BStep (L : Layout) : BCfg → BCfg → Prop
  /-- A step of the program. -/
  | act {a b : List Stmt × PSt ℕ Value} {cps : List (List Stmt × PSt ℕ Value)} {Λ : Scripts Value} :
      SAct L lone noScripts a b Λ → (∀ ks, a.1 ≠ .tick :: ks) → BStep L ⟨a, cps⟩ ⟨b, cps⟩
  /-- `P or Q`: `P`, keeping `Q`. -/
  | choice {ks : List Stmt} {st : PSt ℕ Value} {p q : Stmt} {cps : List (List Stmt × PSt ℕ Value)} :
      frames ks = 0 → cps.length < L.choices →
      BStep L ⟨(.choice p q :: ks, st), cps⟩ ⟨(p :: ks, st), (q :: ks, st) :: cps⟩
  /-- `ensure c` with `c` true. -/
  | ensureT {ks : List Stmt} {st : PSt ℕ Value} {c : Exp} {cps : List (List Stmt × PSt ℕ Value)} :
      Fits L st.mem c → c.eval st.mem = .bool true →
      BStep L ⟨(.ensure c :: ks, st), cps⟩ ⟨(ks, st), cps⟩
  /-- `ensure c` with `c` false: back to the last choice point. -/
  | ensureF {ks : List Stmt} {st : PSt ℕ Value} {c : Exp} {cp : List Stmt × PSt ℕ Value}
      {cps : List (List Stmt × PSt ℕ Value)} :
      Fits L st.mem c → c.eval st.mem = .bool false → frames ks = 0 →
      BStep L ⟨(.ensure c :: ks, st), cp :: cps⟩ ⟨cp, cps⟩

/-- **Backtracking fails**: an `ensure` is false, and no choice point is left. -/
def BFails (L : Layout) (c : BCfg) : Prop :=
  ∃ (ks : List Stmt) (st : PSt ℕ Value) (e : Exp), c = ⟨(.ensure e :: ks, st), []⟩ ∧
    Fits L st.mem e ∧ e.eval st.mem = .bool false ∧ frames ks = 0

/-! ### The machine holds backtracking's configuration -/

/-- Where choice point `i` starts, in words. -/
def recN (L : Layout) (i : ℕ) : ℕ := L.W + 5 + i * (L.W + 1)

/-- Choice point `i`: the address of its code, which runs what is left, and a
copy of the cells holding its state. -/
def RecOk (L : Layout) (m : ℕ → UInt8) (i : ℕ) (cp : List Stmt × PSt ℕ Value) : Prop :=
  ∃ alt : ℕ, alt < 2 ^ 16 ∧ Wd L m (recN L i) = fromInt32 alt ∧ Cont L m [] cp.1 alt ∧
    VarsOk L (Shift m (recN L i + 1)) cp.2.mem

/-- **The machine holds a configuration of backtracking.** -/
structure BRel (L : Layout) (c : BCfg) (s : State) : Prop where
  /-- It runs what is left, with the cells holding the state. -/
  p : PRel L c.cur.1 c.cur.2 s c.cur.2.r
  /-- The count of choice points. -/
  cnt : Wd L (high s) L.W = fromInt32 c.cps.length
  /-- The flag is clear. -/
  flag : Wd L (high s) (L.W + 4) = 0
  /-- Not too many. -/
  len : c.cps.length ≤ L.choices
  /-- The choice points, the first kept first. -/
  recs : ∀ i (h : i < c.cps.length), RecOk L (high s) i (c.cps.reverse[i]'(by simpa))
  /-- Time and cursors stay put. -/
  same : ∀ cp ∈ c.cps, cp.2.t = c.cur.2.t ∧ cp.2.r = c.cur.2.r

theorem _root_.LaPToP.ProgramTheory.CompileB4.Layout.top_eq (L : Layout) :
    L.top = L.base + 4 * L.W := by
  unfold Layout.top Layout.W; omega

theorem recN_ge (L : Layout) (i : ℕ) : L.W + 5 ≤ recN L i := by unfold recN; omega

theorem RecOk.mono {L : Layout} {m m' : ℕ → UInt8} {i : ℕ} {cp : List Stmt × PSt ℕ Value}
    (h : RecOk L m i cp) (hlo : ∀ j < L.base, m' j = m j)
    (hw : ∀ j, L.W ≤ j → Wd L m' j = Wd L m j) : RecOk L m' i cp := by
  obtain ⟨alt, h₀, h₁, h₂, h₃⟩ := h
  refine ⟨alt, h₀, by rw [hw _ (by unfold recN; omega)]; exact h₁, h₂.mono hlo,
    varsOk_congr h₃ fun k _ => ?_⟩
  rw [wd_shift, wd_shift, hw _ (by unfold recN; omega)]

/-- Memory from `L.top` up gives the words from `W` up. -/
theorem wd_of_top {L : Layout} {m m' : ℕ → UInt8} (h : ∀ i, L.top ≤ i → m' i = m i) {j : ℕ}
    (hj : L.W ≤ j) : Wd L m' j = Wd L m j := by
  unfold Wd word
  rw [h _ (by rw [L.top_eq]; omega), h _ (by rw [L.top_eq]; omega), h _ (by rw [L.top_eq]; omega),
    h _ (by rw [L.top_eq]; omega)]

/-! ### Simulation: a step of the program -/

theorem sact_tr {L : Layout} {Λ : Scripts Value} {a b : List Stmt × PSt ℕ Value} (h : SAct L lone noScripts a b Λ)
    (ht : ∀ ks, a.1 ≠ .tick :: ks) : b.2.t = a.2.t ∧ b.2.r = a.2.r := by
  cases h <;> simp_all [lone]

theorem sact_not_send {L : Layout} {Λ : Scripts Value} {a b : List Stmt × PSt ℕ Value}
    (h : SAct L lone noScripts a b Λ) : ∀ ch e ks, a.1 ≠ .send ch e :: ks := by
  intro ch e ks he; cases h <;> simp_all [lone]

theorem sact_not_recv {L : Layout} {Λ : Scripts Value} {a b : List Stmt × PSt ℕ Value}
    (h : SAct L lone noScripts a b Λ) : ∀ ch x ks, a.1 ≠ .recv ch x :: ks := by
  intro ch x ks he; cases h <;> simp_all [lone]

/-- The machine at what is left, after its jumps. -/
theorem BRel.follow {L : Layout} (hL : L.Ok) {c : BCfg} {s : State} (hr : BRel L c s) :
    ∃ s₁, Steps s s₁ ∧ BRel L c s₁ ∧ Direct L (high s₁) (cstack s₁) c.cur.1 (getIP s₁) ∧
      high s₁ = high s := by
  obtain ⟨s₁, r₁, sm₁, w₁, d₁, hd₁⟩ := CompileNet.follow L hL hr.p.cont s rfl rfl hr.p.wf hr.p.run rfl
  refine ⟨s₁, r₁, ⟨⟨w₁, sm₁.running hr.p.run, by rw [d₁]; exact hr.p.stack,
    by rw [sm₁.high, sm₁.cs]; exact hd₁.cont, by rw [sm₁.high]; exact hr.p.vars,
    by rw [sm₁.clk]; exact hr.p.clk, hr.p.tfit, hr.p.rd, by rw [sm₁.high]; exact hr.p.image⟩,
    by rw [sm₁.high]; exact hr.cnt, by rw [sm₁.high]; exact hr.flag, hr.len,
    fun i h => by rw [sm₁.high]; exact hr.recs i h, hr.same⟩,
    by rw [sm₁.high, sm₁.cs]; exact hd₁, sm₁.high⟩

/-- **A step of the program is steps of the machine.** -/
theorem sim_act {L : Layout} (hL : L.Ok) {Λ : Scripts Value} {a b : List Stmt × PSt ℕ Value}
    {cps : List (List Stmt × PSt ℕ Value)} (h : SAct L lone noScripts a b Λ)
    (ht : ∀ ks, a.1 ≠ .tick :: ks) {s : State} (hr : BRel L ⟨a, cps⟩ s) :
    ∃ s', Steps s s' ∧ BRel L ⟨b, cps⟩ s' := by
  obtain ⟨s₁, r₁, hr₁, hd₁, -⟩ := hr.follow hL
  obtain ⟨s₂, r₂, hp₂, lo₂, top₂⟩ := machine_sim L hL h (sact_not_send h) (sact_not_recv h) hr₁.p hd₁
  obtain ⟨et, er⟩ := sact_tr h ht
  have hw : ∀ j, L.W ≤ j → Wd L (high s₂) j = Wd L (high s₁) j := fun j hj => wd_of_top top₂ hj
  refine ⟨s₂, r₁.trans r₂, ⟨by rw [er]; exact hp₂, by rw [hw _ le_rfl]; exact hr₁.cnt,
    by rw [hw _ (by omega)]; exact hr₁.flag, hr₁.len, fun i hi => (hr₁.recs i hi).mono lo₂ hw,
    fun cp hcp => by rw [et, er]; exact hr₁.same cp hcp⟩⟩

end LaPToP.ProgramTheory.CompileBT
