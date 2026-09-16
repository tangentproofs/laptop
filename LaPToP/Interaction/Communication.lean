import LaPToP.Interaction.InteractiveVariables
import Mathlib.Algebra.Group.Nat.Even

/-!
# Communication

This module formalizes Section 9.1 (Communication), Subsection 9.1.0
(Implementability) and Subsection 9.1.1 (Input and Output) of Eric Hehner's
*A Practical Theory of Programming* (aPToP).

"Communication on channel `c` is described by two infinite strings `Mc` and
`Tc` called the message script and the time script, and two extended natural
variables `rc` and `wc` called the read cursor and the write cursor. The
message script is the string of all messages, past, present, and future, that
pass along the channel. The time script is the corresponding string of times
that the messages were or are or will be sent. The scripts are state
constants, not state variables. The read cursor is a state variable saying
how many messages have been read, or input, from the channel. The write
cursor is a state variable saying how many messages have been written, or
output, to the channel."

"`c! e = Mw=e ∧ Tw = t ∧ (w:= w+1)` “c output e”; `c? = r:= r+1` “c input”;
`c = M r–1`; `√c = T r ≤ t` “check c”."

## The model

The scripts of a channel are a pair of functions `M : ℕ → α`, `T : ℕ → ℕ∞`
(infinite strings), constants of the specification: a specification with a
channel is a function of the scripts, `CSpec α := Scripts α → Spec CS`, where
the state `CS` has the time, the two cursors and a memory variable. Cursors
are naturals (the book: extended naturals; a cursor is never `∞` in a finite
computation). `c! e` is literally `Mw = e ∧ Tw = t ∧ (w:= w+1)` — a constraint
on the (constant) scripts together with the increment of the write cursor —
with `e` an expression of the state. "Every computation satisfies
`t′≥t ∧ r′≥r ∧ w′≥w`": proved for the primitives and closed under sequential
composition and conditional. Implementability with a channel is the book's
definition, literally, with the scripts re-chosen only on the segment `w;..w′`
written by the computation; `c! e` and `c?` are implementable.

The two examples of Subsection 9.1.1 use two channels `c`, `d` and are proved
as the book calculates them: `Md wd = even (Mc rc) ⇐ c?. d! even c`, and
`S = ∀n: nat· Md wd+n = 2 × Mc rc+n`, `S ⇐ c?. d! 2×c. S` with the recursive
call as a specification (Section 6.1).
-/

namespace LaPToP.Interaction

open LaPToP.ProgramTheory LaPToP.ProgramTheory.Spec

universe u v

/-- The scripts of a channel: "two infinite strings `M` and `T` called the message
script and the time script". -/
structure Scripts (α : Type u) where
  /-- The message script `M`. -/
  M : ℕ → α
  /-- The time script `T`. -/
  T : ℕ → ℕ∞

/-- The state of a computation with one channel: the time, the read and write
cursors, and a memory variable. -/
structure CS where
  /-- The time. -/
  t : ℕ∞
  /-- The read cursor `r`, "how many messages have been read". -/
  r : ℕ
  /-- The write cursor `w`, "how many messages have been written". -/
  w : ℕ
  /-- A memory variable. -/
  x : ℤ

/-- A specification with a channel: a function of the (constant) scripts. -/
abbrev CSpec (α : Type u) := Scripts α → Spec CS

namespace Channel

variable {α : Type u}

/-- `c! e = Mw=e ∧ Tw = t ∧ (w:= w+1)`, "c output e". -/
def output (e : CS → α) : CSpec α := fun sc s s' =>
  sc.M s.w = e s ∧ sc.T s.w = s.t ∧ s' = { s with w := s.w + 1 }

/-- `c? = r:= r+1`, "c input". -/
def input : Spec CS := fun s s' => s' = { s with r := s.r + 1 }

/-- `c = M r–1`, "the message that was last previously read on the channel". -/
def lastRead (sc : Scripts α) (s : CS) : α := sc.M (s.r - 1)

/-- `√c = T r ≤ t`, "there is unread input available on channel c". -/
def check (sc : Scripts α) (s : CS) : Prop := sc.T s.r ≤ s.t

/-- The Substitution Law for `c?`. -/
theorem input_seq (P : Spec CS) : seq input P = fun s s' => P { s with r := s.r + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

/-- The Substitution Law for `c! e`. -/
theorem output_seq (e : CS → α) (sc : Scripts α) (P : Spec CS) :
    seq (output e sc) P = fun s s' => sc.M s.w = e s ∧ sc.T s.w = s.t ∧ P { s with w := s.w + 1 } s' :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨_, ⟨hM, hT, h⟩, hP⟩ => ⟨hM, hT, h ▸ hP⟩, fun ⟨hM, hT, hP⟩ => ⟨_, ⟨hM, hT, rfl⟩, hP⟩⟩

/-! ### "Every computation satisfies `t′≥t ∧ r′≥r ∧ w′≥w`" (aPToP §9.1.0) -/

/-- "Time and the cursors can only increase. Once an input has been read, it
cannot be unread; once an output has been written, it cannot be unwritten." -/
def Increasing (S : Spec CS) : Prop := ∀ s s', S s s' → s.t ≤ s'.t ∧ s.r ≤ s'.r ∧ s.w ≤ s'.w

theorem increasing_ok : Increasing ok := by
  rintro s _ rfl
  exact ⟨le_rfl, le_rfl, le_rfl⟩

theorem increasing_input : Increasing input := by
  rintro s _ rfl
  exact ⟨le_rfl, Nat.le_succ _, le_rfl⟩

theorem increasing_output (e : CS → α) (sc : Scripts α) : Increasing (output e sc) := by
  rintro s _ ⟨-, -, rfl⟩
  exact ⟨le_rfl, le_rfl, Nat.le_succ _⟩

theorem increasing_seq {S R : Spec CS} (hS : Increasing S) (hR : Increasing R) : Increasing (seq S R) :=
  fun s s' ⟨u, h₁, h₂⟩ =>
    let ⟨a₁, b₁, c₁⟩ := hS s u h₁
    let ⟨a₂, b₂, c₂⟩ := hR u s' h₂
    ⟨le_trans a₁ a₂, le_trans b₁ b₂, le_trans c₁ c₂⟩

theorem increasing_cond (b : CS → Prop) {S R : Spec CS} (hS : Increasing S) (hR : Increasing R) :
    Increasing (cond b S R) := by
  rintro s s' (⟨-, h⟩ | ⟨-, h⟩)
  · exact hS s s' h
  · exact hR s s' h

/-! ### Implementability with a channel (aPToP §9.1.0) -/

/-- "A specification `S` (in initial state `σ`, final state `σ′`, message script `M`,
and time script `T`) is implementable if and only if
`∀σ, M, T· ∃σ′, M, T· S ∧ t′≥t ∧ r′≥r ∧ w′≥w ∧ M(0;..w); (w′;..∞) = M(0;..w); (w′;..∞)
∧ T(0;..w); (w′;..∞) = T(0;..w); (w′;..∞) ∧ ∀i, j: w,..w′· i≤j ⇒ t ≤ Ti ≤ Tj ≤ t′`":
the scripts may be chosen only on the segment `w;..w′` written by the
computation, where the time script is monotonic and within `t;..t′`. -/
def ImplementableC (S : CSpec α) : Prop :=
  ∀ (s : CS) (M : ℕ → α) (T : ℕ → ℕ∞), ∃ (s' : CS) (M' : ℕ → α) (T' : ℕ → ℕ∞),
    S ⟨M', T'⟩ s s' ∧ s.t ≤ s'.t ∧ s.r ≤ s'.r ∧ s.w ≤ s'.w ∧
    (∀ i, (i < s.w ∨ s'.w ≤ i) → M' i = M i ∧ T' i = T i) ∧
    (∀ i j, s.w ≤ i → i ≤ j → j < s'.w → s.t ≤ T' i ∧ T' i ≤ T' j ∧ T' j ≤ s'.t)

/-- `c! e` is implementable: the scripts are chosen at index `w` only. -/
theorem implementableC_output (e : CS → α) : ImplementableC (output e) := by
  intro s M T
  refine ⟨{ s with w := s.w + 1 }, Function.update M s.w (e s), Function.update T s.w s.t,
    ⟨Function.update_self .., Function.update_self .., rfl⟩, le_rfl, le_rfl, Nat.le_succ _,
    fun i hi => ?_, fun i j hi hij hj => ?_⟩
  · have : i ≠ s.w := by simp only at hi; omega
    exact ⟨Function.update_of_ne this .., Function.update_of_ne this ..⟩
  · simp only at hj
    have hi' : i = s.w := by omega
    have hj' : j = s.w := by omega
    subst hi' hj'
    simp

/-- `c?` is implementable: the scripts are unchanged. -/
theorem implementableC_input : ImplementableC (fun _ : Scripts α => input) := by
  intro s M T
  refine ⟨{ s with r := s.r + 1 }, M, T, rfl, le_rfl, Nat.le_succ _, le_rfl, fun _ _ => ⟨rfl, rfl⟩,
    fun i j hi _ hj => ?_⟩
  simp only at hj
  omega

end Channel

/-! ### Two channels: the examples of aPToP §9.1.1 -/

/-- The state with two channels `c` and `d`: the time and the four cursors. -/
structure CS2 where
  /-- The time. -/
  t : ℕ∞
  /-- The read cursor of channel `c`. -/
  rc : ℕ
  /-- The write cursor of channel `c`. -/
  wc : ℕ
  /-- The read cursor of channel `d`. -/
  rd : ℕ
  /-- The write cursor of channel `d`. -/
  wd : ℕ

namespace TwoChannels

variable {α : Type u} {β : Type v}

/-- `c? = rc:= rc+1`. -/
def inputC : Spec CS2 := fun s s' => s' = { s with rc := s.rc + 1 }

/-- `d! e = Md wd = e ∧ Td wd = t ∧ (wd:= wd+1)`, where `e` may mention the last
message read on `c`. -/
def outputD (e : CS2 → Scripts α → β) (c : Scripts α) (d : Scripts β) : Spec CS2 := fun s s' =>
  d.M s.wd = e s c ∧ d.T s.wd = s.t ∧ s' = { s with wd := s.wd + 1 }

/-- `c = Mc rc–1`. -/
def lastReadC (c : Scripts α) (s : CS2) : α := c.M (s.rc - 1)

theorem inputC_seq (P : Spec CS2) : seq inputC P = fun s s' => P { s with rc := s.rc + 1 } s' :=
  Spec.ext fun _ _ => ⟨fun ⟨_, h, hP⟩ => h ▸ hP, fun hP => ⟨_, rfl, hP⟩⟩

theorem outputD_seq (e : CS2 → Scripts α → β) (c : Scripts α) (d : Scripts β) (P : Spec CS2) :
    seq (outputD e c d) P = fun s s' => d.M s.wd = e s c ∧ d.T s.wd = s.t ∧ P { s with wd := s.wd + 1 } s' :=
  Spec.ext fun _ _ =>
    ⟨fun ⟨_, ⟨hM, hT, h⟩, hP⟩ => ⟨hM, hT, h ▸ hP⟩, fun ⟨hM, hT, hP⟩ => ⟨_, ⟨hM, hT, rfl⟩, hP⟩⟩

/-- "If the next input on channel `c` is even, then the next output on channel `d`
will be `⊤`, and otherwise it will be `⊥`": `Md wd = even (Mc rc)`. -/
def evenSpec (c : Scripts ℤ) (d : Scripts Bool) : Spec CS2 := fun s _ => d.M s.wd = decide (Even (c.M s.rc))

/-- The two forms of the example specification agree:
`if even (Mc rc) then Md wd = ⊤ else Md wd = ⊥` is `Md wd = even (Mc rc)`. -/
theorem evenSpec_iff (c : Scripts ℤ) (d : Scripts Bool) (s s' : CS2) :
    evenSpec c d s s' ↔ (if Even (c.M s.rc) then d.M s.wd = true else d.M s.wd = false) := by
  simp only [evenSpec]
  split_ifs with h <;> simp [h]

/-- `Md wd = even (Mc rc) ⇐ c?. d! even c`, the book's calculation:
`c?. d! even c = rc:= rc+1. Md wd = even (Mc rc–1) ∧ Td wd = t ∧ (wd:= wd+1)
= Md wd = even (Mc rc) ∧ … ⇒ Md wd = even (Mc rc)`. -/
theorem evenSpec_refines (c : Scripts ℤ) (d : Scripts Bool) :
    Refines (evenSpec c d) (seq inputC (outputD (fun s c => decide (Even (lastReadC c s))) c d)) := by
  intro s s' h
  rw [inputC_seq] at h
  obtain ⟨hM, -, -⟩ := h
  simpa [evenSpec, lastReadC] using hM

/-- "Read numbers from channel `c`, and write their doubles on channel `d`":
`S = ∀n: nat· Md wd+n = 2 × Mc rc+n`. -/
def doubling (c d : Scripts ℤ) : Spec CS2 := fun s _ => ∀ n : ℕ, d.M (s.wd + n) = 2 * c.M (s.rc + n)

/-- `S ⇐ c?. d! 2×c. S`, with the recursive call as a specification: "`c?. d! 2×c. S
= rc:= rc+1. Md wd = 2 × Mc rc–1 ∧ (wd:= wd+1). ∀n· Md wd+n = 2 × Mc rc+n
= Md wd = 2 × Mc rc ∧ ∀n· Md wd+1+n = 2 × Mc rc+1+n = ∀n· Md wd+n = 2 × Mc rc+n = S`". -/
theorem doubling_refines (c d : Scripts ℤ) :
    Refines (doubling c d) (seq inputC (seq (outputD (fun s c => 2 * lastReadC c s) c d) (doubling c d))) := by
  intro s s' h
  rw [inputC_seq, outputD_seq] at h
  obtain ⟨hM, -, hS⟩ := h
  simp only [lastReadC, Nat.add_sub_cancel] at hM
  intro n
  cases n with
  | zero => simpa using hM
  | succ n =>
    have := hS n
    simp only at this
    rw [show s.wd + (n + 1) = s.wd + 1 + n by omega, show s.rc + (n + 1) = s.rc + 1 + n by omega]
    exact this

end TwoChannels

end LaPToP.Interaction
