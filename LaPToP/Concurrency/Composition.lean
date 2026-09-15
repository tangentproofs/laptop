import LaPToP.ProgramTheory.Time
import LaPToP.ProgramTheory.Scope

/-!
# Concurrent composition

This module formalizes Section 8.0 (Concurrent Composition) and Section 8.0.0
(Laws of Concurrent Composition) of Eric Hehner's *A Practical Theory of
Programming* (aPToP).

## The model

"We define the concurrent composition of specifications `P` and `Q` so that
`P||Q` is satisfied by a computer that behaves according to `P` and, at the
same time, concurrently, according to `Q`. ... For concurrent composition
`P||Q`, we require that `P` and `Q` have completely different state
variables, and the state variables of the composition `P||Q` are those of
both `P` and `Q`. If we ignore time and space, concurrent composition is
conjunction: `P||Q = P∧Q`."

The partition of the variables is made explicit by a product: a process on
the variables `σ₁` and a process on the variables `σ₂` compose to a
specification on `σ₁ × σ₂`, `Spec.par P Q = P ∧ Q` (each conjunct on its own
component). A process may mention the other process's variables "but only as
constants (mathematical variables, not state variables)": `Spec.parWith`
lets each process read the *initial* values of the other's variables. This is
the book's "both occurrences of `x` in the left process refer to the initial
value of variable `x`". Since sequential composition hides intermediate
states, "if one process is a sequential composition, the other cannot see its
intermediate values".

"The time variable is not subject to partitioning; it belongs to both
processes. ... Execution of the composition `P||Q` finishes when both `P` and
`Q` are finished. With time, `P||Q = ∃tP, tQ· ⟨t′· P⟩ tP ∧ ⟨t′· Q⟩ tQ ∧ t′ = tP↑tQ`":
`Spec.parT`, on a state `(σ₁ × σ₂) × ℕ∞`.

The laws of Section 8.0.0 are proved: concurrent substitution, symmetry and
associativity (up to the evident reshuffling of the product state — these are
equalities of specifications only after transport along `Prod.swap`, resp.
reassociation, which is the honest form of "the same specification on the
same variables"), the three distributive laws, and Refinement by Steps and
by Parts for `||`.
-/

namespace LaPToP.Concurrency

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

universe u v w

variable {σ₁ : Type u} {σ₂ : Type v} {σ₃ : Type w}

/-- `P||Q = P ∧ Q`: the processes `P` and `Q` on disjoint variables `σ₁`, `σ₂`. -/
def par (P : Spec σ₁) (Q : Spec σ₂) : Spec (σ₁ × σ₂) := fun s s' => P s.1 s'.1 ∧ Q s.2 s'.2

/-- `P||Q` where each process may read the initial values of the other's
variables as constants. -/
def parWith (P : σ₂ → Spec σ₁) (Q : σ₁ → Spec σ₂) : Spec (σ₁ × σ₂) :=
  fun s s' => P s.2 s.1 s'.1 ∧ Q s.1 s.2 s'.2

/-- `par` is the special case of `parWith` in which neither process reads the other. -/
theorem par_eq_parWith (P : Spec σ₁) (Q : Spec σ₂) : par P Q = parWith (fun _ => P) fun _ => Q := rfl

/-- A whole-state assignment `σ:= e σ` (for one process's variables). -/
def assignF {σ : Type u} (e : σ → σ) : Spec σ := fun s s' => s' = e s

/-- Substitution Law for a whole-state assignment. -/
theorem assignF_seq {σ : Type u} (e : σ → σ) (P : Spec σ) : seq (assignF e) P = fun s s' => P (e s) s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-! ### Laws of concurrent composition (aPToP §8.0.0) -/

section Laws

variable (P P' : Spec σ₁) (Q Q' R : Spec σ₂)

/-- `P || Q = Q || P` (symmetry), up to swapping the two components of the state. -/
theorem par_comm (s s' : σ₁ × σ₂) : par P Q s s' ↔ par Q P s.swap s'.swap := And.comm

/-- Reassociation of a three-process state. -/
def assoc (s : σ₁ × (σ₂ × σ₃)) : (σ₁ × σ₂) × σ₃ := ((s.1, s.2.1), s.2.2)

/-- `P || (Q || R) = (P || Q) || R` (associativity), up to reassociating the state:
"we can compose any number of processes without worrying how they are grouped". -/
theorem par_assoc (R : Spec σ₃) (s s' : σ₁ × (σ₂ × σ₃)) :
    par P (par Q R) s s' ↔ par (par P Q) R (assoc s) (assoc s') := and_assoc.symm

/-- `P || Q∨R = (P || Q) ∨ (P || R)` (distributivity). -/
theorem par_or : par P (or Q R) = or (par P Q) (par P R) :=
  Spec.ext fun _ _ => and_or_left

/-- `P || if b then Q else R = if b then P || Q else P || R` (distributivity), `b`
an expression of the right process's prestate. -/
theorem par_cond (b : σ₂ → Prop) : par P (cond b Q R) = cond (fun s => b s.2) (par P Q) (par P R) :=
  Spec.ext fun s _ => by
    simp only [par, Spec.cond]
    by_cases hb : b s.2 <;> simp [hb]

/-- `if b then P||Q else R||S = (if b then P else R) || (if b then Q else S)`
(distributivity), for `b` an expression of the whole prestate: each process
reads the other's initial variables to evaluate `b`. -/
theorem cond_par (b : σ₁ × σ₂ → Prop) (R' : Spec σ₁) (S : Spec σ₂) :
    cond b (par P Q) (par R' S) =
      parWith (fun s₂ => cond (fun s₁ => b (s₁, s₂)) P R') fun s₁ => cond (fun s₂ => b (s₁, s₂)) Q S :=
  Spec.ext fun s _ => by
    simp only [par, parWith, Spec.cond]
    by_cases hb : b s <;> simp [hb]

/-- Concurrent substitution: `(x:= e || y:= f). P` is `P` with `e` substituted for
`x` and concurrently `f` for `y`, "each substitution replaces all and only the
original occurrences of its variable". -/
theorem par_assignF_seq (e : σ₁ → σ₁) (f : σ₂ → σ₂) (P : Spec (σ₁ × σ₂)) :
    seq (par (assignF e) (assignF f)) P = fun s s' => P (e s.1, f s.2) s' :=
  Spec.ext fun s s' =>
    ⟨fun ⟨u, ⟨h1, h2⟩, hP⟩ => by
      simp only [assignF] at h1 h2
      have : u = (e s.1, f s.2) := Prod.ext h1 h2
      exact this ▸ hP,
     fun hP => ⟨(e s.1, f s.2), ⟨rfl, rfl⟩, hP⟩⟩

/-- Concurrent substitution when each assignment reads the other's initial variables. -/
theorem parWith_assignF_seq (e : σ₁ → σ₂ → σ₁) (f : σ₁ → σ₂ → σ₂) (P : Spec (σ₁ × σ₂)) :
    seq (parWith (fun s₂ => assignF fun s₁ => e s₁ s₂) fun s₁ => assignF fun s₂ => f s₁ s₂) P =
      fun s s' => P (e s.1 s.2, f s.1 s.2) s' :=
  Spec.ext fun s s' =>
    ⟨fun ⟨u, ⟨h1, h2⟩, hP⟩ => by
      simp only [assignF] at h1 h2
      have : u = (e s.1 s.2, f s.1 s.2) := Prod.ext h1 h2
      exact this ▸ hP,
     fun hP => ⟨(e s.1 s.2, f s.1 s.2), ⟨rfl, rfl⟩, hP⟩⟩

/-- Concurrent composition is monotonic in both processes. -/
theorem par_mono (h₁ : Refines P P') (h₂ : Refines Q Q') : Refines (par P Q) (par P' Q') :=
  fun _ _ ⟨hP, hQ⟩ => ⟨h₁ _ _ hP, h₂ _ _ hQ⟩

/-- Refinement by Steps for `||`: "if `A ⇐ B||C` and `B ⇐ D` and `C ⇐ E` are
theorems, then `A ⇐ D||E` is a theorem". -/
theorem steps_par {A : Spec (σ₁ × σ₂)} {B D : Spec σ₁} {C E : Spec σ₂}
    (hA : Refines A (par B C)) (hB : Refines B D) (hC : Refines C E) : Refines A (par D E) :=
  refines_trans _ _ _ hA (par_mono B D C E hB hC)

/-- Refinement by Parts for `||`: "if `A ⇐ B||C` and `D ⇐ E||F` are theorems,
then `A∧D ⇐ (B∧E) || (C∧F)` is a theorem". -/
theorem parts_par {A D : Spec (σ₁ × σ₂)} {B E : Spec σ₁} {C F : Spec σ₂}
    (hA : Refines A (par B C)) (hD : Refines D (par E F)) :
    Refines (and A D) (par (and B E) (and C F)) :=
  fun s s' ⟨⟨hB, hE⟩, hC, hF⟩ => ⟨hA s s' ⟨hB, hC⟩, hD s s' ⟨hE, hF⟩⟩

end Laws

/-! ### The book's examples (aPToP §8.0), in integer variables `x`, `y` -/

namespace Examples

/-- `x:= x+1 || y:= y+2 = x′=x+1 ∧ y′=y+2`: "for the assignments to make sense,
`x` has to belong to the left process and `y` to the right process". -/
theorem incr_par : par (assignF fun x : ℤ => x + 1) (assignF fun y : ℤ => y + 2) =
    fun s s' : ℤ × ℤ => s'.1 = s.1 + 1 ∧ s'.2 = s.2 + 2 := rfl

/-- `x:= y || y:= x = x′=y ∧ y′=x`: "variables `x` and `y` swap values,
apparently without a temporary variable" — each process reads the other's
initial value. -/
theorem swap_par : parWith (fun y₀ : ℤ => assignF fun _ : ℤ => y₀) (fun x₀ : ℤ => assignF fun _ : ℤ => x₀) =
    fun s s' : ℤ × ℤ => s'.1 = s.2 ∧ s'.2 = s.1 := rfl

/-- `b:= x=x || x:= x+1 = b:= ⊤ || x:= x+1`: "both occurrences of `x` in the left
process refer to the initial value of variable `x`", so `x=x` may be replaced
by `⊤`. -/
theorem beq_par : parWith (fun x₀ : ℤ => assignF fun _ : Bool => decide (x₀ = x₀)) (fun _ => assignF fun x : ℤ => x + 1) =
    par (assignF fun _ : Bool => true) (assignF fun x : ℤ => x + 1) := by
  refine Spec.ext fun s s' => ?_
  simp [parWith, par, assignF]

/-- `x:= x+1. x:= x–1 = ok`. -/
theorem incr_decr : seq (assignF fun x : ℤ => x + 1) (assignF fun x : ℤ => x - 1) = ok := by
  rw [assignF_seq]
  refine Spec.ext fun s s' => ?_
  simp only [assignF, Spec.ok]
  omega

/-- `(x:= x+1. x:= x–1) || y:= x = ok || y:= x = y:= x`: "the intermediate values
of variables are local to the sequential composition; ... the occurrence of `x`
in the right process refers to the initial value of variable `x`". On the
composed state, `y:= x` is `x′=x ∧ y′=x`. -/
theorem seq_par : parWith (fun _ : ℤ => seq (assignF fun x : ℤ => x + 1) (assignF fun x : ℤ => x - 1))
      (fun x₀ : ℤ => assignF fun _ : ℤ => x₀) =
    fun s s' : ℤ × ℤ => s'.1 = s.1 ∧ s'.2 = s.1 := by
  rw [incr_decr]
  rfl

/-- The Substitution Law example `(x:= x+y || y:= x×y). z′ = x–y = (z′ = (x+y) – (x×y))`,
with `z` a variable of the right process. -/
theorem subst_example :
    seq (parWith (fun s₂ : ℤ × ℤ => assignF fun x : ℤ => x + s₂.1)
        (fun x : ℤ => assignF fun s₂ : ℤ × ℤ => (x * s₂.1, s₂.2)))
      (fun s s' : ℤ × (ℤ × ℤ) => s'.2.2 = s.1 - s.2.1) =
    fun s s' : ℤ × (ℤ × ℤ) => s'.2.2 = (s.1 + s.2.1) - s.1 * s.2.1 := by
  rw [parWith_assignF_seq]

/-- "Synchronization is sequencing": the two-stage composition
`(x:= x+y || y:= x–y). (x:= x×y || y:= x/y)` needs neither shared memory nor
synchronization devices — it is a sequential composition of two concurrent
compositions, computed by concurrent substitution. -/
theorem two_stage :
    seq (parWith (fun y : ℤ => assignF fun x : ℤ => x + y) (fun x : ℤ => assignF fun y : ℤ => x - y))
      (parWith (fun y : ℤ => assignF fun x : ℤ => x * y) (fun x : ℤ => assignF fun y : ℤ => x / y)) =
    fun s s' : ℤ × ℤ => s'.1 = (s.1 + s.2) * (s.1 - s.2) ∧ s'.2 = (s.1 + s.2) / (s.1 - s.2) := by
  rw [parWith_assignF_seq]
  rfl

end Examples

/-! ### Concurrent composition with time (aPToP §8.0) -/

/-- `P||Q = ∃tP, tQ· ⟨t′· P⟩ tP ∧ ⟨t′· Q⟩ tQ ∧ t′ = tP↑tQ`: "both `P` and `Q` begin
execution at time `t`, but their executions may finish at different times.
Execution of the composition `P||Q` finishes when both `P` and `Q` are finished." -/
def parT (P : Spec (σ₁ × ℕ∞)) (Q : Spec (σ₂ × ℕ∞)) : Spec ((σ₁ × σ₂) × ℕ∞) :=
  fun s s' => ∃ tP tQ, P (s.1.1, s.2) (s'.1.1, tP) ∧ Q (s.1.2, s.2) (s'.1.2, tQ) ∧ s'.2 = max tP tQ

variable (P : Spec (σ₁ × ℕ∞)) (Q : Spec (σ₂ × ℕ∞))

/-- Symmetry of the timed composition, up to swapping the processes' variables. -/
theorem parT_comm (s s' : (σ₁ × σ₂) × ℕ∞) : parT P Q s s' ↔ parT Q P (s.1.swap, s.2) (s'.1.swap, s'.2) := by
  simp only [parT, Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨tP, tQ, hP, hQ, ht⟩; exact ⟨tQ, tP, hQ, hP, ht.trans (max_comm _ _)⟩
  · rintro ⟨tQ, tP, hQ, hP, ht⟩; exact ⟨tP, tQ, hP, hQ, ht.trans (max_comm _ _)⟩

/-- If the left process does not decrease time, neither does the composition
(and symmetrically, by `parT_comm`). -/
theorem parT_time_nondecreasing (hP : ∀ s s', P s s' → s.2 ≤ s'.2)
    (s s' : (σ₁ × σ₂) × ℕ∞) (h : parT P Q s s') : s.2 ≤ s'.2 := by
  obtain ⟨tP, tQ, hP', -, ht⟩ := h
  rw [ht]
  exact (hP _ _ hP').trans (le_max_left _ _)

/-- The composition finishes no earlier than either process. -/
theorem parT_finish (s s' : (σ₁ × σ₂) × ℕ∞) (h : parT P Q s s') :
    ∃ tP tQ, P (s.1.1, s.2) (s'.1.1, tP) ∧ Q (s.1.2, s.2) (s'.1.2, tQ) ∧ tP ≤ s'.2 ∧ tQ ≤ s'.2 := by
  obtain ⟨tP, tQ, hP, hQ, ht⟩ := h
  exact ⟨tP, tQ, hP, hQ, ht ▸ le_max_left _ _, ht ▸ le_max_right _ _⟩

end LaPToP.Concurrency
