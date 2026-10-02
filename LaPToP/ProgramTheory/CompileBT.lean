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

/-! ### Running the runtime on the machine -/

theorem scodeR_save (L : Layout) (a w alt : ℕ) :
    scodeR L.rt a (RT.save w alt) = scode L.rt a (RT.save w alt) := by
  simp [RT.save, RT.copy, scodeR, scode]

theorem scodeR_pop (L : Layout) (a w : ℕ) : scodeR L.rt a (RT.pop w) = scode L.rt a (RT.pop w) := by
  simp [RT.pop, RT.copy, scodeR, scode]

theorem scodeR_halt (L : Layout) (a w : ℕ) : scodeR L.rt a (RT.halt w) = scode L.rt a (RT.halt w) := by
  simp [RT.halt, scodeR, scode]

/-- **The runtime's code runs as the runtime's program**: from the machine's
words to the words the program leaves. -/
theorem rt_runs {L : Layout} (hrt : L.rt.Ok) {P : Stmt} {σ : St} {ms' : List ℤ} {s : State} {a : ℕ}
    (hsev : SEval L.rt 0 P (MS (words L (high s)) σ) (MS ms' σ)) (hl' : ms'.length = L.cap)
    (hw : WF s) (hr : Running s) (hip : getIP s = a) (hlo : 256 ≤ a) (hhi : a + slen L.rt P ≤ L.base)
    (hc : CodeAt (high s) a (scode L.rt a P)) (hd : dstack s = []) (hcs : cstack s = [])
    (hdep : sdepth P ≤ STACKSZ) :
    ∃ s', Steps s s' ∧ WF s' ∧ Running s' ∧ getIP s' = a + slen L.rt P ∧ dstack s' = [] ∧
      (∀ j < L.cap, Wd L (high s') j = fromInt32 (rd ms' j)) ∧ Keeps L.rt s s' := by
  obtain ⟨s', r', w', run', i', d', v', k'⟩ := stmt_runs L.rt hrt hsev s a
    ⟨hw, hr, hip, hlo, hhi, hc, varsOk_words L _ σ, hd, hdep, by rw [hcs]; rfl,
      fun k hk => by simp [Layout.rt] at hk⟩
  exact ⟨s', r', w', run', i', d', fun j hj => wd_of_varsOk v' hl' hj, k'⟩

theorem rt_top (L : Layout) : L.rt.top = L.base + 4 * L.cap := by
  simp [Layout.top, Layout.rt, cellsOf, Layout.cap]

theorem slen_save (L : Layout) (w alt : ℕ) : slen L.rt (RT.save w alt) = 415 := by
  rw [← length_scode L.rt _ 0, ← scodeR_save, length_scodeR_save]

theorem slen_pop (L : Layout) (w : ℕ) : slen L.rt (RT.pop w) = 367 := by
  rw [← length_scode L.rt _ 0, ← scodeR_pop, length_scodeR_pop]

theorem slen_halt (L : Layout) (w : ℕ) : slen L.rt (RT.halt w) = 23 := by
  rw [← length_scode L.rt _ 0, ← scodeR_halt, length_scodeR_halt]

/-! ### Simulation: a choice -/

/-- What backtracking asks of the layout: the program's, and the runtime's. -/
structure BTOk (L : Layout) : Prop where
  ok : L.Ok
  rt : L.rt.Ok
  cap : L.cap < 2 ^ 20

theorem recIdx_eq (L : Layout) (k : ℕ) : recIdx L k = (recN L k : ℤ) := by
  unfold recIdx recN; push_cast; rfl

theorem RecOk.mono' {L : Layout} {m m' : ℕ → UInt8} {i : ℕ} {cp : List Stmt × PSt ℕ Value}
    (h : RecOk L m i cp) (hlo : ∀ j < L.base, m' j = m j)
    (hw : ∀ j, recN L i ≤ j → j ≤ recN L i + L.W → Wd L m' j = Wd L m j) : RecOk L m' i cp := by
  obtain ⟨alt, h₀, h₁, h₂, h₃⟩ := h
  refine ⟨alt, h₀, by rw [hw _ le_rfl (by omega)]; exact h₁, h₂.mono hlo,
    varsOk_congr h₃ fun k hk => ?_⟩
  rw [wd_shift, wd_shift, hw _ (by omega) (by omega)]

theorem recN_mono (L : Layout) {i k : ℕ} (h : i < k) : recN L i + L.W + 1 ≤ recN L k := by
  unfold recN
  have : (i + 1) * (L.W + 1) ≤ k * (L.W + 1) := Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at this; omega

theorem recN_end (L : Layout) {k : ℕ} (h : k < L.choices) : recN L k + L.W + 1 ≤ L.cap := by
  unfold recN Layout.cap
  have : (k + 1) * (L.W + 1) ≤ L.choices * (L.W + 1) := Nat.mul_le_mul_right _ h
  rw [Nat.succ_mul] at this; omega

theorem rd_words_toInt {L : Layout} {m : ℕ → UInt8} {j : ℕ} (hj : j < L.cap) :
    fromInt32 (rd (words L m) j) = Wd L m j := by
  rw [rd_words hj, fromInt32_toInt32]

/-- **A choice is steps of the machine**: keep the choice point, go on with the
first choice. -/
theorem sim_choice {L : Layout} (hB : BTOk L) {ks : List Stmt} {st : PSt ℕ Value} {p q : Stmt}
    {cps : List (List Stmt × PSt ℕ Value)} (hfr : frames ks = 0) (hlen : cps.length < L.choices)
    {s : State} (hr : BRel L ⟨(.choice p q :: ks, st), cps⟩ s) :
    ∃ s', Steps s s' ∧ BRel L ⟨(p :: ks, st), (q :: ks, st) :: cps⟩ s' := by
  have hL := hB.ok
  have hb : L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ 65536 := hL.2
  have hcap := hB.cap
  obtain ⟨s₁, r₁, hr₁, hd₁, -⟩ := hr.follow hL
  obtain ⟨h₁, h₂, h₃, h₄, hk, hcl⟩ := hd₁.cons_inv (by simp) (by simp)
  simp only [Stmt.clean, Bool.and_eq_true] at hcl
  have hcs : cstack s₁ = [] := by
    have := hr₁.p.cont.frames
    rw [frames_cons_clean (by simp [Stmt.clean, hcl.1, hcl.2]), hfr] at this
    exact List.eq_nil_of_length_eq_zero this
  obtain ⟨a, ha⟩ : ∃ a, getIP s₁ = a := ⟨_, rfl⟩
  rw [ha] at h₁ h₂ h₄ hk
  obtain ⟨k, hkdef⟩ : ∃ k, cps.length = k := ⟨_, rfl⟩
  rw [hkdef] at hlen
  simp only [slen, sdepth] at h₂ h₃ hk
  simp only [scode] at h₄
  rw [CodeAt.append, CodeAt.append, CodeAt.append] at h₄
  obtain ⟨⟨⟨hS, hP⟩, hJ⟩, hQ⟩ := h₄
  simp only [List.length_append, length_scodeR_save, length_scode, length_jmTo] at hP hJ hQ
  rw [scodeR_save] at hS
  obtain ⟨alt, haltdef⟩ : ∃ alt, alt = a + 415 + slen L p + 5 := ⟨_, rfl⟩
  rw [← haltdef] at hQ hJ hS
  have hcw : L.W + 5 ≤ L.cap := by unfold Layout.cap; omega
  have hkc : k < L.cap := by
    have := recN_end L hlen; unfold recN at this; nlinarith
  have hcnt0 := hr₁.cnt
  rw [hkdef] at hcnt0
  have hcnt : rd (words L (high s₁)) L.W = k := by
    rw [rd_words (by omega), hcnt0, toInt32_fromInt32 ⟨by omega, by omega⟩]
  obtain ⟨ms', sv, l', c', a', cp', fr'⟩ := save_runs (d := 0) (σ := fun _ => .int 0) (alt := alt)
    hB.cap (length_words L _) hcnt hlen (by omega)
  obtain ⟨s₂, r₂, w₂, run₂, i₂, d₂, wd₂, k₂⟩ := rt_runs hB.rt sv (by rw [l', length_words]) hr₁.p.wf
    hr₁.p.run ha h₁ (by rw [slen_save]; omega) hS hr₁.p.stack hcs
    (by simp [RT.save, RT.copy, RT.recAt, sdepth, depth, STACKSZ])
  rw [slen_save] at i₂
  have lo₂ : ∀ j < L.base, high s₂ j = high s₁ j := k₂.low
  have hW : ∀ j < L.cap, Wd L (high s₂) j = fromInt32 (rd ms' j) := wd₂
  have hR := recN_end L hlen
  have hRi := recIdx_eq L k
  -- the cells, untouched
  have hcells : ∀ j < L.W, Wd L (high s₂) j = Wd L (high s₁) j := fun j hj => by
    rw [hW j (by omega), fr' j (by left; rw [hRi]; unfold recN; omega) (by omega) (by omega) (by omega)
      (by omega), rd_words_toInt (by omega)]
  refine ⟨s₂, r₁.trans r₂, ⟨⟨w₂, run₂, d₂, ?_, varsOk_congr hr₁.p.vars hcells,
    by rw [k₂.clk]; exact hr₁.p.clk, hr₁.p.tfit, hr₁.p.rd, hr₁.p.image.mono lo₂⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [i₂, k₂.cs, hcs]
    rw [hcs] at hk
    exact .cons (by omega) (by omega) (by omega) hcl.1 (hP.mono lo₂ (by rw [length_scode]; omega))
      (.jump (by omega) (by omega) ((hJ.mono lo₂ (by simp; omega)).cast (by omega))
        ((hk.mono lo₂).cast (by omega)))
  · simp only [List.length_cons, hkdef]
    rw [hW _ (by omega), c']; push_cast; rfl
  · rw [hW _ (by omega), fr' _ (by left; rw [hRi]; unfold recN; omega) (by omega) (by omega)
      (by omega) (by omega), rd_words_toInt (by omega), hr₁.flag]
  · simp; omega
  · intro i hi
    simp only [List.reverse_cons, List.length_cons] at hi ⊢
    rw [hkdef] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · rw [List.getElem_append_left (by simpa [hkdef] using hi)]
      refine (hr₁.recs i (by rw [hkdef]; exact hi)).mono' lo₂ fun j h₁ h₂ => ?_
      have := recN_mono L hi
      have := recN_end L hlen
      rw [hW j (by omega), fr' j (by left; rw [hRi]; omega) (by unfold recN at h₁; omega)
        (by unfold recN at h₁; omega) (by unfold recN at h₁; omega) (by unfold recN at h₁; omega),
        rd_words_toInt (by omega)]
    · subst hi
      rw [List.getElem_append_right (by simp [hkdef])]
      simp only [List.length_reverse, hkdef, Nat.sub_self, List.getElem_cons_zero]
      refine ⟨alt, by omega, by rw [hW _ (by omega), ← hRi, a'], ?_, varsOk_congr hr₁.p.vars ?_⟩
      · rw [hcs] at hk
        exact .cons (by omega) (by omega) (by omega) hcl.2 ((hQ.mono lo₂ (by rw [length_scode]; omega)).cast (by omega))
          ((hk.mono lo₂).cast (by omega))
      · intro j hj
        rw [wd_shift, hW _ (by omega)]
        have := cp' j (by omega) (by omega)
        rw [hRi] at this; push_cast at this
        rw [show ((recN L i + 1 + j : ℕ) : ℤ) = (recN L i : ℤ) + 1 + j by push_cast; rfl, this,
          rd_words_toInt (by omega)]
  · intro cp hcp
    simp only [List.mem_cons] at hcp
    rcases hcp with rfl | hcp
    · exact ⟨rfl, rfl⟩
    · exact hr₁.same cp hcp

/-! ### Simulation: `ensure` -/

theorem length_ensure_rest (L : Layout) (f : ℕ) :
    (jmTo f ++ jmTo (f + 461) ++ failCode L f).length = 471 := by
  rw [List.length_append, List.length_append, length_failCode]; rfl

/-- The pieces of an `ensure`'s code. -/
theorem ensure_code {L : Layout} {m : ℕ → UInt8} {a : ℕ} {c : Exp}
    (h : CodeAt m a (scode L a (.ensure c))) :
    CodeAt m a (ecode L c ++ test ++ (jmTo (a + (ecode L c).length + 13) ++
        jmTo (a + (ecode L c).length + 13 + 461) ++ failCode L (a + (ecode L c).length + 13))) ∧
      CodeAt m (a + (ecode L c).length + 3) (jmTo (a + (ecode L c).length + 13)) ∧
      CodeAt m (a + (ecode L c).length + 8) (jmTo (a + (ecode L c).length + 13 + 461)) ∧
      CodeAt m (a + (ecode L c).length + 13) (failCode L (a + (ecode L c).length + 13)) := by
  simp only [scode] at h
  refine ⟨by simpa only [List.append_assoc] using h, ?_⟩
  rw [CodeAt.append, CodeAt.append, CodeAt.append, CodeAt.append] at h
  obtain ⟨⟨⟨⟨-, -⟩, hJ⟩, hJ'⟩, hF⟩ := h
  simp only [List.length_append, length_test, length_jmTo] at hJ hJ' hF
  exact ⟨hJ.cast (by omega), hJ'.cast (by omega), hF.cast (by omega)⟩

/-- The pieces of the failure code. -/
theorem fail_code {L : Layout} {m : ℕ → UInt8} {f : ℕ} (h : CodeAt m f (failCode L f)) :
    CodeAt m f (ecode L.rt (RT.mem (RT.lit L.W))) ∧ m (f + 18) = 0x9C ∧ m (f + 19) = 7 ∧
      CodeAt m (f + 20) (jmTo (f + 49)) ∧ CodeAt m (f + 25) (scode L.rt (f + 25) (RT.halt L.W)) ∧
      m (f + 48) = 0xFF ∧ CodeAt m (f + 49) (scode L.rt (f + 49) (RT.pop L.W)) ∧
      CodeAt m (f + 416) (ecode L.rt (RT.mem (RT.recAt L.W))) ∧ m (f + 459) = 0x90 ∧
      m (f + 460) = 0x9E := by
  unfold failCode at h
  simp only [CodeAt.append] at h
  obtain ⟨⟨⟨⟨hC, hH⟩, hJ⟩, ⟨hHa, hHl⟩⟩, ⟨⟨hP, hA⟩, hD⟩⟩ := h
  simp only [List.length_append, length_ecode_cnt, length_ecode_alt, length_jmTo, length_scodeR_halt,
    length_scodeR_pop, List.length_cons, List.length_nil] at hH hJ hHa hHl hP hA hD
  rw [scodeR_halt] at hHa; rw [scodeR_pop] at hP
  refine ⟨hC, by simpa using hH 0 (by simp), by simpa using hH 1 (by simp), hJ.cast (by omega),
    hHa.cast (by omega), by simpa using hHl 0 (by simp), hP.cast (by omega), hA.cast (by omega),
    by simpa using hD 0 (by simp), by simpa using hD 1 (by simp)⟩

set_option maxRecDepth 20000 in
/-- **`ensure c`, `c` true, is steps of the machine**: test, and jump past the
failure code. -/
theorem sim_ensureT {L : Layout} (hL : L.Ok) {ks : List Stmt} {st : PSt ℕ Value} {c : Exp}
    {cps : List (List Stmt × PSt ℕ Value)} (hf : Fits L st.mem c) (hc : c.eval st.mem = .bool true)
    {s : State} (hr : BRel L ⟨(.ensure c :: ks, st), cps⟩ s) :
    ∃ s', Steps s s' ∧ BRel L ⟨(ks, st), cps⟩ s' := by
  have hb : L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ 65536 := hL.2
  obtain ⟨s₁, r₁, hr₁, hd₁, -⟩ := hr.follow hL
  obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd₁.cons_inv (by simp) (by simp)
  obtain ⟨a, ha⟩ : ∃ a, getIP s₁ = a := ⟨_, rfl⟩
  rw [ha] at h₁ h₂ h₄ hk
  simp only [slen, sdepth] at h₂ h₃ hk
  obtain ⟨hA, -, hJ', -⟩ := ensure_code h₄
  obtain ⟨s₂, r₂, w₂, run₂, i₂, d₂, sm₂⟩ := run_cond (b := true)
    (rest := jmTo (a + (ecode L c).length + 13) ++ jmTo (a + (ecode L c).length + 13 + 461) ++
      failCode L (a + (ecode L c).length + 13)) hL hf hc hr₁.p.wf hr₁.p.run ha h₁
    (by rw [length_ensure_rest]; omega) hA hr₁.p.vars hr₁.p.stack (by omega)
  simp only [ite_true] at i₂
  have hJ₂ : CodeAt (high s₂) (getIP s₂) (jmTo (a + (ecode L c).length + 13 + 461)) := by
    rw [i₂, sm₂.high]; exact hJ'
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_jm' hL w₂ (by rw [i₂]; omega) (by rw [i₂]; omega) hJ₂ (by omega)
    (by omega)
  have sm := sm₂.trans sm₃
  refine ⟨step s₂, r₁.trans (r₂.tail ⟨run₂, notIo_jm (by rw [i₂]; omega) hJ₂, rfl⟩),
    ⟨⟨w₃, sm₃.running run₂, by rw [d₃, d₂], ?_, by rw [sm.high]; exact hr₁.p.vars,
      by rw [sm.clk]; exact hr₁.p.clk, hr₁.p.tfit, hr₁.p.rd, by rw [sm.high]; exact hr₁.p.image⟩,
    by rw [sm.high]; exact hr₁.cnt, by rw [sm.high]; exact hr₁.flag, hr₁.len,
    fun i h => by rw [sm.high]; exact hr₁.recs i h, hr₁.same⟩⟩
  rw [i₃, sm.high, sm.cs]
  exact hk.cast (by omega)

set_option maxRecDepth 20000 in
/-- **`ensure c`, `c` false, reaches the failure code**, with nothing changed
but the pointer, and the control stack empty. -/
theorem to_fail {L : Layout} (hL : L.Ok) {ks : List Stmt} {st : PSt ℕ Value} {c : Exp}
    {cps : List (List Stmt × PSt ℕ Value)} (hf : Fits L st.mem c) (hc : c.eval st.mem = .bool false)
    (hfr : frames ks = 0) {s : State} (hr : BRel L ⟨(.ensure c :: ks, st), cps⟩ s) :
    ∃ s' f, Steps s s' ∧ BRel L ⟨(.ensure c :: ks, st), cps⟩ s ∧ WF s' ∧ Running s' ∧
      getIP s' = f ∧ 256 ≤ f ∧ f + 461 ≤ L.base ∧ dstack s' = [] ∧ cstack s' = [] ∧
      high s' = high s ∧ getClk s' = getClk s ∧ CodeAt (high s') f (failCode L f) := by
  have hb : L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ 65536 := hL.2
  obtain ⟨s₁, r₁, hr₁, hd₁, hh₁⟩ := hr.follow hL
  have hcs : cstack s₁ = [] := by
    have := hr₁.p.cont.frames
    rw [frames_cons_clean (by simp [Stmt.clean]), hfr] at this
    exact List.eq_nil_of_length_eq_zero this
  obtain ⟨h₁, h₂, h₃, h₄, hk, -⟩ := hd₁.cons_inv (by simp) (by simp)
  obtain ⟨a, ha⟩ : ∃ a, getIP s₁ = a := ⟨_, rfl⟩
  rw [ha] at h₁ h₂ h₄ hk
  simp only [slen, sdepth] at h₂ h₃ hk
  obtain ⟨hA, hJ, -, hF⟩ := ensure_code h₄
  obtain ⟨s₂, r₂, w₂, run₂, i₂, d₂, sm₂⟩ := run_cond (b := false)
    (rest := jmTo (a + (ecode L c).length + 13) ++ jmTo (a + (ecode L c).length + 13 + 461) ++
      failCode L (a + (ecode L c).length + 13)) hL hf hc hr₁.p.wf hr₁.p.run ha h₁
    (by rw [length_ensure_rest]; omega) hA hr₁.p.vars hr₁.p.stack (by omega)
  simp only [Bool.false_eq_true, ite_false] at i₂
  have hJ₂ : CodeAt (high s₂) (getIP s₂) (jmTo (a + (ecode L c).length + 13)) := by
    rw [i₂, sm₂.high]; exact hJ
  obtain ⟨w₃, i₃, d₃, sm₃⟩ := run_jm' hL w₂ (by rw [i₂]; omega) (by rw [i₂]; omega) hJ₂ (by omega)
    (by omega)
  have sm := sm₂.trans sm₃
  refine ⟨step s₂, a + (ecode L c).length + 13, r₁.trans (r₂.tail ⟨run₂, notIo_jm (by rw [i₂]; omega) hJ₂, rfl⟩),
    hr, w₃, sm₃.running run₂, i₃, by omega, by omega, by rw [d₃, d₂], by rw [sm.cs, hcs],
    by rw [sm.high, hh₁], by rw [sm.clk, hr₁.p.clk, hr.p.clk], by rw [sm.high]; exact hF⟩

/-- An expression of the runtime, on the machine's words. -/
theorem rt_exp {L : Layout} (hrt : L.rt.Ok) {e : Exp} {σ : St} {s : State}
    (hf : Fits L.rt (MS (words L (high s)) σ) e) (hw : WF s) (hr : Running s) (hlo : 256 ≤ getIP s)
    (hhi : getIP s + (ecode L.rt e).length + 8 < MAXBYTE) (hc : CodeAt (high s) (getIP s) (ecode L.rt e))
    (hd : dstack s = []) (hdep : depth e ≤ STACKSZ) :
    ∃ s', Steps s s' ∧ WF s' ∧ getIP s' = getIP s + (ecode L.rt e).length ∧
      dstack s' = [enc (e.eval (MS (words L (high s)) σ))] ∧ Same s s' := by
  obtain ⟨s', r', w', i', d', sm'⟩ := exp_runs L.rt hrt _ e s hf
    ⟨hw, hr, hlo, hhi, hc, varsOk_words L _ σ, by rw [hd]; simpa using hdep⟩
  exact ⟨s', r', w', i', by rw [d', hd]; rfl, sm'⟩

theorem Steps.of_step {s : State} (hr : Running s) (hn : NotIo s) : Steps s (step s) := Steps.one hr hn

set_option maxRecDepth 20000 in
/-- **A failed `ensure` with a choice point left is steps of the machine**: take
the choice point back, and go to its other choice. -/
theorem sim_ensureF {L : Layout} (hB : BTOk L) {ks : List Stmt} {st : PSt ℕ Value} {c : Exp}
    {cp : List Stmt × PSt ℕ Value} {cps : List (List Stmt × PSt ℕ Value)}
    (hf : Fits L st.mem c) (hc : c.eval st.mem = .bool false) (hfr : frames ks = 0)
    {s : State} (hr : BRel L ⟨(.ensure c :: ks, st), cp :: cps⟩ s) :
    ∃ s', Steps s s' ∧ BRel L ⟨cp, cps⟩ s' := by
  have hL := hB.ok
  have hb : L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ 65536 := hL.2
  have hcap := hB.cap
  have hcw : L.W + 5 ≤ L.cap := by unfold Layout.cap; omega
  obtain ⟨s₃, f, r₃, -, w₃, run₃, i₃, f0, f1, d₃, c₃, hh₃, ck₃, hF⟩ := to_fail hL hf hc hfr hr
  obtain ⟨hC, hH0, hH1, hJ, -, -, hP, hAlt, hDc, hRt⟩ := fail_code hF
  obtain ⟨k, hkdef⟩ : ∃ k, cps.length = k := ⟨_, rfl⟩
  have hlen : k < L.choices := by have := hr.len; simp [hkdef] at this; omega
  have hch : L.choices ≤ L.cap :=
    le_trans (Nat.le_mul_of_pos_right L.choices (by omega : 0 < L.W + 1)) (by unfold Layout.cap; omega)
  have hcnt : rd (words L (high s₃)) L.W = k + 1 := by
    rw [rd_words (by omega), hh₃, hr.cnt, toInt32_fromInt32 ⟨by simp; omega, by simp; omega⟩]
    simp [hkdef]
  -- the count
  obtain ⟨s₄, r₄, w₄, i₄, d₄, sm₄⟩ := rt_exp (σ := fun _ => .int 0) hB.rt
    (fits_mem (j := L.W) (fits_rlit (Alloc.inR (by norm_num) (by omega))) rfl (by omega)
      (by simp; omega) (length_words L _)) w₃ run₃ (by omega) (by rw [i₃, length_ecode_cnt]; unfold MAXBYTE; omega)
    (by rw [i₃]; exact hC) d₃ (by simp [depth, STACKSZ])
  rw [i₃, length_ecode_cnt] at i₄
  simp only [eval_mem, eval_rlit, Value.toInt_int, hcnt] at d₄
  -- h0: not zero, go on
  have hop₄ : high s₄ (getIP s₄) = 0x9C := by rw [i₄, sm₄.high]; exact hH0
  have hd₄ : high s₄ (getIP s₄ + 1) = 7 := by rw [i₄, sm₄.high]; exact hH1
  have h7 : sbyte 7 = 7 := by decide
  obtain ⟨w₅, i₅, d₅, sm₅⟩ := step_h0 s₄ [] _ w₄ (by rw [i₄]; omega) (by rw [i₄]; unfold MAXBYTE; omega)
    hop₄ (by simpa using d₄) (by rw [hd₄, h7, i₄]; simp only [Int.ofNat_eq_natCast]; omega)
    (by rw [hd₄, h7, i₄]; simp only [Int.ofNat_eq_natCast]; unfold MAXBYTE; omega)
  have hne : enc (.int ((k : ℤ) + 1)) ≠ 0 := by
    simp only [enc]; exact fromInt32_ne_zero ⟨by omega, by omega⟩ (by omega)
  rw [if_neg hne, i₄] at i₅
  -- jm to the pop
  have hJ₅ : CodeAt (high (step s₄)) (getIP (step s₄)) (jmTo (f + 49)) := by
    rw [i₅, sm₅.high, sm₄.high]; exact hJ.cast (by omega)
  obtain ⟨w₆, i₆, d₆, sm₆⟩ := run_jm' hL w₅ (by rw [i₅]; omega) (by rw [i₅]; omega) hJ₅ (by omega)
    (by omega)
  set s₆ := step (step s₄) with hs₆
  have run₆ : Running s₆ := sm₆.running (sm₅.running (sm₄.running run₃))
  have hh₆ : high s₆ = high s := by rw [sm₆.high, sm₅.high, sm₄.high, hh₃]
  have c₆ : cstack s₆ = [] := by rw [sm₆.cs, sm₅.cs, sm₄.cs, c₃]
  have r₆ : Steps s₃ s₆ := (r₄.tail ⟨sm₄.running run₃, notIo_of_hop (by rw [i₄]; omega) hop₄, rfl⟩).tail
    ⟨sm₅.running (sm₄.running run₃), notIo_jm (by rw [i₅]; omega) hJ₅, rfl⟩
  -- take the choice point back
  have hcnt₆ : rd (words L (high s₆)) L.W = k + 1 := by rw [hh₆, ← hh₃]; exact hcnt
  obtain ⟨ms', sv, l', cW, cpy, fr⟩ := pop_runs (d := 0) (σ := fun _ => .int 0) hB.cap
    (length_words L _) hcnt₆ hlen
  obtain ⟨s₇, r₇, w₇, run₇, i₇, d₇, wd₇, k₇⟩ := rt_runs hB.rt sv (by rw [l', length_words]) w₆ run₆
    i₆ (by omega) (by rw [slen_pop]; omega) (by rw [hh₆, ← hh₃]; exact hP) (by rw [d₆, d₅]) c₆
    (by simp [RT.pop, RT.copy, RT.recAt, sdepth, depth, STACKSZ])
  rw [slen_pop] at i₇
  have hR := recN_end L hlen
  have hRi := recIdx_eq L k
  have hk₇ : rd (words L (high s₇)) L.W = k := by
    rw [rd_words (by omega), wd₇ _ (by omega), cW, toInt32_fromInt32 ⟨by omega, by omega⟩]
  -- the other choice's address
  obtain ⟨s₈, r₈, w₈, i₈, d₈, sm₈⟩ := rt_exp (σ := fun _ => .int 0) (e := RT.mem (RT.recAt L.W)) hB.rt
    (fits_mem (j := recIdx L k) (fits_recAt (length_words L _) hB.cap hk₇ hlen.le) (eval_recAt hk₇)
      (by rw [hRi]; omega) (by rw [hRi, length_words]; omega) (length_words L _)) w₇ run₇
    (by rw [i₇]; omega) (by rw [i₇, length_ecode_alt]; unfold MAXBYTE; omega)
    (by rw [i₇]; exact (hAlt.mono (fun i hi => by rw [k₇.low i hi, hh₆, ← hh₃])
      (by rw [length_ecode_alt]; simp only [Layout.rt]; omega)).cast (by omega)) d₇ (by simp [depth, RT.recAt, STACKSZ])
  rw [i₇, length_ecode_alt] at i₈
  -- the choice point
  have hrec : RecOk L (high s) k cp := by
    have := hr.recs k (by simp [hkdef])
    simpa [List.getElem_append_right, hkdef] using this
  obtain ⟨alt, halt, hWa, hCont, hVar⟩ := hrec
  have hlo₇ : ∀ i < L.base, high s₇ i = high s i := fun i hi => by rw [k₇.low i hi, hh₆]
  have hW₇ : ∀ j, L.W + 4 ≤ j → j < L.cap → Wd L (high s₇) j = Wd L (high s) j := fun j h₁ h₂ => by
    rw [wd₇ j h₂, fr j (by omega), rd_words_toInt h₂, hh₆]
  have hv : enc ((RT.mem (RT.recAt L.W)).eval (MS (words L (high s₇)) (fun _ => .int 0))) =
      fromInt32 alt := by
    rw [eval_mem, eval_recAt hk₇, Value.toInt_int, hRi]
    simp only [enc]
    rw [show ((recN L k : ℕ) : ℤ) = ((recN L k : ℕ) : ℤ) from rfl, rd_words (by omega),
      fromInt32_toInt32, hW₇ _ (by unfold recN; omega) (by omega), hWa]
  rw [hv] at d₈
  -- dc
  have hop₈ : high s₈ (getIP s₈) = 0x90 := by
    rw [i₈, sm₈.high, hlo₇ _ (by omega), ← hh₃]; exact hDc
  have c₈ : cstack s₈ = [] := by rw [sm₈.cs, k₇.cs, c₆]
  obtain ⟨w₉, i₉, d₉, c₉, f₉⟩ := step_dc s₈ [] (fromInt32 alt) w₈ (by rw [i₈]; omega)
    (by rw [i₈]; omega) hop₈ (by simpa using d₈) (by rw [c₈]; decide)
  -- rt, to the other choice
  have hop₉ : high (step s₈) (getIP (step s₈)) = 0x9E := by
    rw [i₉, i₈, f₉.high, sm₈.high, hlo₇ _ (by omega), ← hh₃]; exact hRt
  have halt' : (fromInt32 (alt : ℤ)).toNat = alt := by
    rw [fromInt32_natCast (by omega)]; exact toNat_ofNat_addr (by unfold MAXBYTE; omega)
  have halo : 256 ≤ alt := hCont.bounds.1
  obtain ⟨w₁₀, i₁₀, d₁₀, c₁₀, f₁₀⟩ := step_rt (step s₈) [] (fromInt32 alt) w₉ (by rw [i₉, i₈]; omega)
    hop₉ (by rw [c₉, c₈]) (by rw [halt']; exact halo)
  rw [halt'] at i₁₀
  have run₉ : Running (step s₈) := ⟨f₉.st.trans (sm₈.running run₇).1, f₉.db.trans (sm₈.running run₇).2⟩
  have hh : high (step (step s₈)) = high s₇ := by rw [f₁₀.high, f₉.high, sm₈.high]
  have hlo : ∀ i < L.base, high (step (step s₈)) i = high s i := fun i hi => by rw [hh, hlo₇ i hi]
  have ck : getClk (step (step s₈)) = getClk s := by
    rw [f₁₀.clk, f₉.clk, sm₈.clk, k₇.clk, sm₆.clk, sm₅.clk, sm₄.clk, ck₃]
  obtain ⟨et, er⟩ := hr.same cp (by simp)
  refine ⟨step (step s₈), r₃.trans (r₆.trans (r₇.trans ((r₈.tail ⟨sm₈.running run₇,
    notIo_of_hop (by rw [i₈]; omega) hop₈, rfl⟩).tail ⟨run₉, notIo_of_hop (by rw [i₉, i₈]; omega) hop₉,
    rfl⟩))), ⟨⟨w₁₀, ⟨f₁₀.st.trans run₉.1, f₁₀.db.trans run₉.2⟩, by rw [d₁₀, d₉], ?_, ?_,
    by rw [ck, hr.p.clk, et], by rw [et]; exact hr.p.tfit, fun _ => rfl, hr.p.image.mono hlo⟩,
    ?_, ?_, by simp [hkdef]; omega, ?_, ?_⟩⟩
  · rw [i₁₀, c₁₀]; exact hCont.mono hlo
  · refine varsOk_congr hVar fun j hj => ?_
    rw [wd_shift]
    unfold Wd; rw [hh]; change Wd L (high s₇) j = _
    rw [wd₇ j (by omega), cpy j (by omega) (by omega), hRi]
    rw [show (recN L k : ℤ) + 1 + j = ((recN L k + 1 + j : ℕ) : ℤ) by push_cast; rfl,
      rd_words_toInt (by omega), hh₆]
    rfl
  · unfold Wd; rw [hh]; change Wd L (high s₇) L.W = _
    rw [wd₇ _ (by omega), cW, ← hkdef]
  · unfold Wd; rw [hh]; change Wd L (high s₇) (L.W + 4) = _
    rw [hW₇ _ le_rfl (by omega)]
    have := hr.flag; unfold Wd at this ⊢; exact this
  · intro i hi
    have hi' : i < k := by simpa [hkdef] using hi
    have : RecOk L (high s) i (cps.reverse[i]'(by simp; omega)) := by
      have h := hr.recs i (by simp; omega)
      simpa [List.getElem_append_left, hkdef, hi'] using h
    refine this.mono' hlo fun j h₁ h₂ => ?_
    have := recN_mono L hi'
    unfold Wd; rw [hh]; change Wd L (high s₇) j = Wd L (high s) j
    exact hW₇ j (by unfold recN at h₁; omega) (by omega)
  · intro cp' hcp'
    obtain ⟨e₁, e₂⟩ := hr.same cp' (by simp [hcp'])
    exact ⟨e₁.trans et.symm, e₂.trans er.symm⟩

/-! ### The ends -/

theorem high_hl {s : State} (hip : 256 ≤ getIP s) (hop : high s (getIP s) = 0xFF) :
    high (step s) = high s := by
  rw [step_of s _ hip hop, runOp_hl]; simp

set_option maxRecDepth 20000 in
/-- **Failure**: a false `ensure` with no choice point left sets the flag and
halts. -/
theorem sim_fail {L : Layout} (hB : BTOk L) {ks : List Stmt} {st : PSt ℕ Value} {c : Exp}
    (hf : Fits L st.mem c) (hc : c.eval st.mem = .bool false) (hfr : frames ks = 0)
    {s : State} (hr : BRel L ⟨(.ensure c :: ks, st), []⟩ s) :
    ∃ s', Steps s s' ∧ getRST s' = 0 ∧ Wd L (high s') (L.W + 4) = fromInt32 (-1) := by
  have hL := hB.ok
  have hb : L.base + 4 * L.n + 4 * cellsOf L.arrays + 16 ≤ 65536 := hL.2
  have hcap := hB.cap
  have hcw : L.W + 5 ≤ L.cap := by unfold Layout.cap; omega
  obtain ⟨s₃, f, r₃, -, w₃, run₃, i₃, f0, f1, d₃, c₃, hh₃, -, hF⟩ := to_fail hL hf hc hfr hr
  obtain ⟨hC, hH0, hH1, -, hHa, hHl, -, -, -, -⟩ := fail_code hF
  have hcnt : rd (words L (high s₃)) L.W = 0 := by
    rw [rd_words (by omega), hh₃, hr.cnt]; rfl
  obtain ⟨s₄, r₄, w₄, i₄, d₄, sm₄⟩ := rt_exp (σ := fun _ => .int 0) hB.rt
    (fits_mem (j := L.W) (fits_rlit (Alloc.inR (by norm_num) (by omega))) rfl (by omega)
      (by simp; omega) (length_words L _)) w₃ run₃ (by omega)
    (by rw [i₃, length_ecode_cnt]; unfold MAXBYTE; omega) (by rw [i₃]; exact hC) d₃
    (by simp [depth, STACKSZ])
  rw [i₃, length_ecode_cnt] at i₄
  simp only [eval_mem, eval_rlit, Value.toInt_int, hcnt] at d₄
  have hop₄ : high s₄ (getIP s₄) = 0x9C := by rw [i₄, sm₄.high]; exact hH0
  have hd₄ : high s₄ (getIP s₄ + 1) = 7 := by rw [i₄, sm₄.high]; exact hH1
  have h7 : sbyte 7 = 7 := by decide
  obtain ⟨w₅, i₅, d₅, sm₅⟩ := step_h0 s₄ [] _ w₄ (by rw [i₄]; omega) (by rw [i₄]; unfold MAXBYTE; omega)
    hop₄ (by simpa using d₄) (by rw [hd₄, h7, i₄]; simp only [Int.ofNat_eq_natCast]; omega)
    (by rw [hd₄, h7, i₄]; simp only [Int.ofNat_eq_natCast]; unfold MAXBYTE; omega)
  rw [ite_eq_left (by decide), hd₄, h7, i₄] at i₅
  have i₅' : getIP (step s₄) = f + 25 := by rw [i₅]; simp only [Int.ofNat_eq_natCast]; omega
  have run₅ : Running (step s₄) := sm₅.running (sm₄.running run₃)
  have hh₅ : high (step s₄) = high s₃ := by rw [sm₅.high, sm₄.high]
  -- set the flag
  have sv := sev_rstore (L := L) (d := 0) (σ := fun _ => .int 0) (ms := words L (high (step s₄)))
    (i := RT.lit (L.W + 4)) (e := RT.lit (-1)) (j := L.W + 4) (k := -1)
    (fits_rlit (Alloc.inR (by omega) (by omega))) (fits_rlit (Alloc.inR (by norm_num) (by norm_num)))
    rfl rfl (by omega) (by simp; omega) (length_words L _)
  obtain ⟨s₆, r₆, w₆, run₆, i₆, d₆, wd₆, k₆⟩ := rt_runs (P := RT.halt L.W) hB.rt sv (by simp)
    w₅ run₅ i₅' (by omega) (by rw [slen_halt]; omega) (by rw [hh₅]; exact hHa)
    (by rw [d₅]) (by rw [sm₅.cs, sm₄.cs, c₃]) (by simp [RT.halt, sdepth, depth, STACKSZ])
  rw [slen_halt] at i₆
  have hop₆ : high s₆ (getIP s₆) = 0xFF := by rw [i₆, k₆.low _ (by simp only [Layout.rt]; omega), hh₅]; exact hHl
  refine ⟨step s₆, (r₃.trans ((r₄.tail ⟨sm₄.running run₃, notIo_of_hop (by rw [i₄]; omega) hop₄, rfl⟩).trans
    r₆)).tail ⟨run₆, notIo_of_hop (by omega) hop₆, rfl⟩, step_hl s₆ w₆ (by omega) hop₆, ?_⟩
  rw [high_hl (by omega) hop₆, wd₆ _ (by omega)]
  have := rd_set (ms := words L (high (step s₄))) (k := -1) (j := L.W + 4) (by omega) (by simp; omega)
    (L.W + 4)
  rw [ite_eq_left rfl] at this
  rw [show ((L.W + 4 : ℕ) : ℤ) = (L.W : ℤ) + 4 by push_cast; rfl, this]

/-- **Success**: nothing is left; the machine halts with the cells holding the
state, and the flag clear. -/
theorem sim_done {L : Layout} (hL : L.Ok) {st : PSt ℕ Value} {cps : List (List Stmt × PSt ℕ Value)}
    {s : State} (hr : BRel L ⟨([], st), cps⟩ s) :
    ∃ s', Steps s s' ∧ getRST s' = 0 ∧ VarsOk L (high s') st.mem ∧
      Wd L (high s') (L.W + 4) = 0 := by
  obtain ⟨s₁, r₁, hr₁, hd₁, -⟩ := hr.follow hL
  obtain ⟨h₁, h₂, h₃⟩ := hd₁.nil_inv
  refine ⟨step s₁, r₁.tail ⟨hr₁.p.run, notIo_of_hop h₁ h₃, rfl⟩, step_hl s₁ hr₁.p.wf h₁ h₃, ?_, ?_⟩
  · rw [high_hl h₁ h₃]; exact hr₁.p.vars
  · rw [high_hl h₁ h₃]; exact hr₁.flag

/-! ### Runs -/

/-- **A step of backtracking is steps of the machine.** -/
theorem bt_step {L : Layout} (hB : BTOk L) {c c' : BCfg} (h : BStep L c c') {s : State}
    (hr : BRel L c s) : ∃ s', Steps s s' ∧ BRel L c' s' := by
  cases h with
  | act ha ht => exact sim_act hB.ok ha ht hr
  | choice hfr hlen => exact sim_choice hB hfr hlen hr
  | ensureT hf hc => exact sim_ensureT hB.ok hf hc hr
  | ensureF hf hc hfr => exact sim_ensureF hB hf hc hfr hr

/-- **A run of backtracking is a run of the machine.** -/
theorem bt_steps {L : Layout} (hB : BTOk L) {c c' : BCfg} (h : Relation.ReflTransGen (BStep L) c c')
    {s : State} (hr : BRel L c s) : ∃ s', Steps s s' ∧ BRel L c' s' := by
  induction h with
  | refl => exact ⟨s, .refl, hr⟩
  | tail _ hs ih =>
    obtain ⟨s₁, r₁, h₁⟩ := ih
    obtain ⟨s₂, r₂, h₂⟩ := bt_step hB hs h₁
    exact ⟨s₂, r₁.trans r₂, h₂⟩

/-- Where backtracking starts: the program, the state, time `0`, no choice point. -/
def BCfg.init (p : Stmt) (st : St) : BCfg := ⟨([p], ⟨st, 0, fun _ => 0, fun _ => 0⟩), []⟩

theorem high_load (L : Layout) (p : Stmt) (st : St) {a : ℕ} (ha : 256 ≤ a) :
    high (load L p st) a = (loadMem L p st).get! a := by
  let s₀ : State := ⟨loadMem L p st, Array.replicate STACKSZ 0, Array.replicate STACKSZ 0, ""⟩
  have hload : load L p st = setRST (setIP s₀ L.start) 1 := rfl
  have : high (load L p st) = high s₀ := by rw [hload]; simp
  rw [this]; simp [high, s₀, ha]

/-- Memory above the cells starts as zeros. -/
theorem load_top (L : Layout) (hL : L.Ok) (p : Stmt) (st : St) (hfit : L.start + slen L p + 1 ≤ L.base)
    {i : ℕ} (hi : L.top ≤ i) : high (load L p st) i = 0 := by
  have h1 := hL.1
  rw [L.top_eq] at hi
  rw [high_load L p st (by omega), loadMem, get!_writeVars_out _ _ _ _ _ (Or.inr (by unfold Layout.W at hi; omega)),
    get!_writeArrs_out _ _ _ _ _ (Or.inr (by unfold Layout.W at hi; omega))]
  by_cases hm : i < MAXBYTE
  · rw [get!_writeBytes _ _ _ (by simp; unfold Layout.start at hfit; have := hL.2; omega),
      ite_eq_right (by unfold Layout.start at hfit; simp; omega), get!_zeros]
  · simp only [ByteArray.get!]
    rw [getElem!_neg _ i (by simp [writeBytes] at *; simpa using hm)]; rfl

theorem wd_load (L : Layout) (hL : L.Ok) (p : Stmt) (st : St) (hfit : L.start + slen L p + 1 ≤ L.base)
    {j : ℕ} (hj : L.W ≤ j) : Wd L (high (load L p st)) j = 0 := by
  unfold Wd word
  rw [load_top L hL p st hfit (by rw [L.top_eq]; omega), load_top L hL p st hfit (by rw [L.top_eq]; omega),
    load_top L hL p st hfit (by rw [L.top_eq]; omega), load_top L hL p st hfit (by rw [L.top_eq]; omega)]
  rfl

/-- **The loaded machine holds backtracking's start.** -/
theorem bt_init {L : Layout} (hL : L.Ok) {p : Stmt} (hF : L.Fit p) (hcl : p.clean = true) (st : St) :
    BRel L (BCfg.init p st) (load L p st) := by
  have hf₁ := hF.hi
  obtain ⟨hw, hrun, hip, hc, hv, hd, hcs⟩ := load_ready L hL p st hf₁
  obtain ⟨hc₁, hc₂⟩ := L.main_of_compile hc
  have hs : 256 ≤ L.start := by unfold Layout.start; omega
  refine ⟨⟨hw, hrun, hd, ?_, hv, by rw [getClk_load L hL _ _ hf₁]; rfl, by simp [TFits, BCfg.init],
    fun _ => rfl, L.image_of_compile hF hc⟩, by rw [wd_load L hL p st hf₁ le_rfl]; rfl,
    wd_load L hL p st hf₁ (by omega), by simp [BCfg.init], fun i h => by simp [BCfg.init] at h,
    fun cp h => by simp [BCfg.init] at h⟩
  rw [hip, hcs]
  exact .cons hs (by omega) hF.depth hcl hc₁ (.nil (by omega) (by omega) hc₂)

/-- **What backtracking finds, the machine finds**: when backtracking runs to the
end, the loaded machine halts, the flag clear, with the cells holding the state
it ends in. -/
theorem bt_success {L : Layout} (hB : BTOk L) {p : Stmt} (hF : L.Fit p) (hcl : p.clean = true)
    {st : St} {t : PSt ℕ Value} {cps : List (List Stmt × PSt ℕ Value)}
    (h : Relation.ReflTransGen (BStep L) (BCfg.init p st) ⟨([], t), cps⟩) :
    ∃ n, getRST (runN n (load L p st)) = 0 ∧ VarsOk L (high (runN n (load L p st))) t.mem ∧
      Wd L (high (runN n (load L p st))) (L.W + 4) = 0 := by
  obtain ⟨s₁, r₁, h₁⟩ := bt_steps hB h (bt_init hB.ok hF hcl st)
  obtain ⟨s₂, r₂, h₂, v₂, f₂⟩ := sim_done hB.ok h₁
  obtain ⟨n, hn⟩ := runN_of_steps (r₁.trans r₂)
  exact ⟨n, by rw [hn]; exact h₂, by rw [hn]; exact v₂, by rw [hn]; exact f₂⟩

/-- **When backtracking fails, the machine says so**: it halts with the flag set. -/
theorem bt_failure {L : Layout} (hB : BTOk L) {p : Stmt} (hF : L.Fit p) (hcl : p.clean = true)
    {st : St} {c : BCfg} (h : Relation.ReflTransGen (BStep L) (BCfg.init p st) c) (hfail : BFails L c) :
    ∃ n, getRST (runN n (load L p st)) = 0 ∧
      Wd L (high (runN n (load L p st))) (L.W + 4) = fromInt32 (-1) := by
  obtain ⟨ks, st', e, rfl, hf, hc, hfr⟩ := hfail
  obtain ⟨s₁, r₁, h₁⟩ := bt_steps hB h (bt_init hB.ok hF hcl st)
  obtain ⟨s₂, r₂, h₂, f₂⟩ := sim_fail hB hf hc hfr h₁
  obtain ⟨n, hn⟩ := runN_of_steps (r₁.trans r₂)
  exact ⟨n, by rw [hn]; exact h₂, by rw [hn]; exact f₂⟩

/-! ### What backtracking finds is what the language allows -/

/-- What is left takes `s` to `t`, by the language's semantics. -/
def EvalK (L : Layout) : List Stmt → St → St → Prop
  | [], s, t => s = t
  | p :: ks, s, t => ∃ u, @Eval ℕ Value L.env _ p.toProg s u ∧ EvalK L ks u t

/-- A solution: from what is left, or from a choice point. -/
def Sol (L : Layout) (c : BCfg) (t : St) : Prop :=
  EvalK L c.cur.1 c.cur.2.mem t ∨ ∃ cp ∈ c.cps, EvalK L cp.1 cp.2.mem t

/-- A step of the program: what is left after it reaches what it reached
before, and back. -/
theorem sact_evalK {L : Layout} {Λ : Scripts Value} {a b : List Stmt × PSt ℕ Value}
    (h : SAct L lone noScripts a b Λ) (t : St) :
    EvalK L b.1 b.2.mem t ↔ EvalK L a.1 a.2.mem t := by
  let _ := L.env
  cases h with
  | ok => exact ⟨fun h => ⟨_, .ok, h⟩, fun ⟨u, hu, h⟩ => by cases hu; exact h⟩
  | assign =>
    exact ⟨fun h => ⟨_, .assign, h⟩, fun ⟨u, hu, h⟩ => by cases hu; exact h⟩
  | tick => exact ⟨fun h => ⟨_, .tick, h⟩, fun ⟨u, hu, h⟩ => by cases hu; exact h⟩
  | seq =>
    exact ⟨fun ⟨u, hu, v, hv, h⟩ => ⟨v, .seq hu hv, h⟩,
      fun ⟨v, hv, h⟩ => by cases hv with | seq hu hv => exact ⟨_, hu, _, hv, h⟩⟩
  | condT _ hc =>
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, .condTrue (by simp [Exp.test, hc]) hu, h⟩, fun ⟨u, hu, h⟩ => by
      cases hu with
      | condTrue _ hu => exact ⟨u, hu, h⟩
      | condFalse hf _ => simp_all [Exp.test]⟩
  | condF _ hc =>
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, .condFalse (by simp [Exp.test, hc]) hu, h⟩, fun ⟨u, hu, h⟩ => by
      cases hu with
      | condTrue ht _ => simp_all [Exp.test]
      | condFalse _ hu => exact ⟨u, hu, h⟩⟩
  | loopT _ hc =>
    exact ⟨fun ⟨u, hu, v, hv, h⟩ => ⟨v, .whileTrue (by simp [Exp.test, hc]) hu hv, h⟩, fun ⟨v, hv, h⟩ => by
      cases hv with
      | whileTrue _ hu hv => exact ⟨_, hu, _, hv, h⟩
      | whileFalse hf => simp_all [Exp.test]⟩
  | loopF _ hc =>
    exact ⟨fun h => ⟨_, .whileFalse (by simp [Exp.test, hc]), h⟩, fun ⟨v, hv, h⟩ => by
      cases hv with
      | whileTrue ht _ _ => simp_all [Exp.test]
      | whileFalse _ => exact h⟩
  | send hch => simp [lone] at hch
  | recv hch => simp [lone] at hch
  | call =>
    exact ⟨fun ⟨u, hu, v, hv, h⟩ => by cases hv; exact ⟨u, .call hu, h⟩,
      fun ⟨u, hu, h⟩ => by cases hu with | call hu => exact ⟨u, hu, _, .ok, h⟩⟩
  | ret => exact ⟨fun h => ⟨_, .ok, h⟩, fun ⟨u, hu, h⟩ => by cases hu; exact h⟩
  | scope =>
    exact ⟨fun ⟨u, hu, v, hv, h⟩ => by cases hv; exact ⟨_, .newLocal hu, h⟩,
      fun ⟨v, hv, h⟩ => by cases hv with | newLocal hu => exact ⟨_, hu, _, .assign, h⟩⟩
  | restore => exact ⟨fun h => ⟨_, .assign, h⟩, fun ⟨u, hu, h⟩ => by cases hu; exact h⟩
  | store => exact ⟨fun h => ⟨_, .assign, h⟩, fun ⟨u, hu, h⟩ => by cases hu; exact h⟩

/-- **A step of backtracking keeps the solutions**: the same, before and after. -/
theorem bstep_sol {L : Layout} {c c' : BCfg} (h : BStep L c c') (t : St) : Sol L c' t ↔ Sol L c t := by
  let _ := L.env
  cases h with
  | act ha _ =>
    simp only [Sol]; rw [sact_evalK ha]
  | @choice ks st p q cps _ _ =>
    simp only [Sol, EvalK, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (⟨u, hu, h⟩ | ⟨u, hu, h⟩ | h)
      · exact .inl ⟨u, .orLeft hu, h⟩
      · exact .inl ⟨u, .orRight hu, h⟩
      · exact .inr h
    · rintro (⟨u, hu, h⟩ | h)
      · cases hu with
        | orLeft hu => exact .inl ⟨u, hu, h⟩
        | orRight hu => exact .inr (.inl ⟨u, hu, h⟩)
      · exact .inr (.inr h)
  | ensureT _ hc =>
    simp only [Sol, EvalK]
    constructor
    · rintro (h | h)
      · exact .inl ⟨_, .ensure (by simp [Exp.test, hc]), h⟩
      · exact .inr h
    · rintro (⟨u, hu, h⟩ | h)
      · cases hu; exact .inl h
      · exact .inr h
  | ensureF _ hc _ =>
    simp only [Sol, EvalK, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    · rintro (⟨u, hu, h⟩ | h | h)
      · cases hu; simp_all [Exp.test]
      · exact .inl h
      · exact .inr h

theorem bsteps_sol {L : Layout} {c c' : BCfg} (h : Relation.ReflTransGen (BStep L) c c') (t : St) :
    Sol L c' t ↔ Sol L c t := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (bstep_sol hs t).trans ih

/-- **Sound**: what backtracking ends with is a poststate of the program. -/
theorem bt_sound {L : Layout} {p : Stmt} {st : St} {t : PSt ℕ Value} {cps : List (List Stmt × PSt ℕ Value)}
    (h : Relation.ReflTransGen (BStep L) (BCfg.init p st) ⟨([], t), cps⟩) :
    @Eval ℕ Value L.env _ p.toProg st t.mem := by
  have := (bsteps_sol h t.mem).mp (.inl rfl)
  simp only [Sol, BCfg.init, EvalK, List.not_mem_nil, false_and, exists_false, or_false] at this
  obtain ⟨u, hu, rfl⟩ := this
  exact hu

/-- **Complete about failure**: when backtracking fails, the program has no
poststate at all. -/
theorem bt_fail_sound {L : Layout} {p : Stmt} {st : St} {c : BCfg}
    (h : Relation.ReflTransGen (BStep L) (BCfg.init p st) c) (hfail : BFails L c) (t : St) :
    ¬ @Eval ℕ Value L.env _ p.toProg st t := by
  intro he
  have hs : Sol L (BCfg.init p st) t := .inl ⟨t, he, rfl⟩
  have := (bsteps_sol h t).mpr hs
  obtain ⟨ks, st', e, rfl, -, hc, -⟩ := hfail
  have hb : Exp.test e st'.mem = false := by simp [Exp.test, hc]
  rcases this with ⟨u, hu, -⟩ | ⟨cp, hcp, -⟩
  · cases hu; simp_all
  · simp at hcp

end LaPToP.ProgramTheory.CompileBT
