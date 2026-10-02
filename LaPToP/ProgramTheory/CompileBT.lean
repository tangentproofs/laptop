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

end LaPToP.ProgramTheory.CompileBT
