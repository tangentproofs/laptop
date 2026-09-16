import LaPToP.Interaction.InteractiveVariables
import LaPToP.RecursiveDefinition.Nat

/-!
# Thermostat

This module formalizes Subsection 9.0.0 (Thermostat) of Eric Hehner's
*A Practical Theory of Programming* (aPToP), Exercise 502, as a definition.

"The inputs to the thermostat are: real `temperature`, which comes from the
thermometer ...; real `desired`, which comes from the control ...; binary
`flame`, which comes from a flame sensor in the burner ... These three
variables must be interactive variables because their values may be changed
at any time by another process and the thermostat must react to their
current values. ... The outputs of the thermostat are: binary `gas`; ...
binary `spark` ... They must also be interactive variables; the burner needs
their current values. Heat is wanted when the actual temperature falls `ε`
below the desired temperature, and not wanted when the actual temperature
rises `ε` above the desired temperature ... To obtain heat, the spark should
be applied to the gas for at least 1 second to give it a chance to ignite and
to allow the flame to become stable. But a safety regulation states that the
gas must not remain on and unlit for more than 3 seconds. Another regulation
says that when the gas is shut off, it must not be turned on again for at
least 20 seconds to allow any accumulated gas to clear. And finally, the gas
burner must respond to its inputs within 1 second. Here is a specification:

    thermostat = (gas:= ⊥ || spark:= ⊥). GasIsOff
    GasIsOff = if temperature < desired – ε
               then (gas:= ⊤ || spark:= ⊤ || t′ ≥ t+1) ∧ t′ ≤ t+3. spark:= ⊥. GasIsOn
               else ((frame gas, spark· ok) || t′ ≥ t) ∧ t′ ≤ t+1. GasIsOff
    GasIsOn  = if temperature < desired + ε ∧ flame
               then ((frame gas, spark· ok) || t′ ≥ t) ∧ t′ ≤ t+1. GasIsOn
               else (gas:= ⊥ || (frame spark· ok) || t′ ≥ t+20) ∧ t′ ≤ t+21. GasIsOff

We are using the time variable to represent real time in seconds. ... One can
always argue about whether a formal specification captures the intent of an
informal specification. For example, if the gas is off, and heat becomes
wanted, and the ignition sequence begins, and then heat is no longer wanted,
this last input may not be noticed for up to 3 seconds. ... At least the
formal specification is unambiguous."

## The model

Time is `ℕ∞` (the book: real seconds). The interactive variables are
functions of time as in `LaPToP.Interaction.InteractiveVariables`; the
inputs `temperature`, `desired`, `flame` are read at the current time, the
outputs `gas`, `spark` are assigned by the thermostat. A specification is a
relation on times, parameterized by the five interactive variables. The
book's compound `(gas:= ⊤ || spark:= ⊤ || t′ ≥ t+1) ∧ t′ ≤ t+3` is read as: at
the final time both hold, and `t+1 ≤ t′ ≤ t+3`; `frame gas, spark· ok` as: both
unchanged throughout `[t, t′]`. Assignment to an interactive variable "cannot
be instantaneous": the book gives `spark:= ⊥` (and the initial
`gas:= ⊥ || spark:= ⊥`) no explicit duration; one time unit is used and
recorded. `GasIsOff` and `GasIsOn` are mutually recursive specifications:
they are defined as the two components of a fixed point of the pair of
bodies (Section 6.1); nothing further is claimed about them beyond the
step-time bounds read off the bodies, which are proved.
-/

namespace LaPToP.Interaction

open LaPToP.RecursiveDefinition

namespace Thermostat

/-- A specification of the thermostat: a relation on the initial and final times,
depending on the interactive variables `temperature`, `desired`, `flame` (inputs)
and `gas`, `spark` (outputs). -/
abbrev TSpec := (ℕ∞ → ℚ) → (ℕ∞ → ℚ) → (ℕ∞ → Bool) → (ℕ∞ → Bool) → (ℕ∞ → Bool) → ℕ∞ → ℕ∞ → Prop

variable (ε : ℚ)

/-- `frame gas, spark· ok` over `[t, t′]`: both outputs unchanged. -/
def frameOk (gas spark : ℕ∞ → Bool) (t t' : ℕ∞) : Prop :=
  ∀ t'', t ≤ t'' → t'' ≤ t' → gas t'' = gas t ∧ spark t'' = spark t

/-- `(gas:= ⊤ || spark:= ⊤ || t′ ≥ t+1) ∧ t′ ≤ t+3`: the ignition. -/
def ignite (gas spark : ℕ∞ → Bool) (t t' : ℕ∞) : Prop :=
  gas t' = true ∧ spark t' = true ∧ t + 1 ≤ t' ∧ t' ≤ t + 3

/-- `spark:= ⊥`, taking one time unit. -/
def sparkOff (spark : ℕ∞ → Bool) (t t' : ℕ∞) : Prop := spark t' = false ∧ t' = t + 1

/-- `((frame gas, spark· ok) || t′ ≥ t) ∧ t′ ≤ t+1`: an idle step of at most one second. -/
def idle (gas spark : ℕ∞ → Bool) (t t' : ℕ∞) : Prop := frameOk gas spark t t' ∧ t ≤ t' ∧ t' ≤ t + 1

/-- `(gas:= ⊥ || (frame spark· ok) || t′ ≥ t+20) ∧ t′ ≤ t+21`: shutting the gas off and
letting it clear. -/
def shutOff (gas spark : ℕ∞ → Bool) (t t' : ℕ∞) : Prop :=
  gas t' = false ∧ (∀ t'', t ≤ t'' → t'' ≤ t' → spark t'' = spark t) ∧ t + 20 ≤ t' ∧ t' ≤ t + 21

/-- The body of `GasIsOff`, as a function of the unknowns `(GasIsOff, GasIsOn)`. -/
def gasIsOffBody (Off On : TSpec) : TSpec := fun temperature desired flame gas spark t t' =>
  if temperature t < desired t - ε then
    ∃ t₁ t₂, ignite gas spark t t₁ ∧ sparkOff spark t₁ t₂ ∧ On temperature desired flame gas spark t₂ t'
  else
    ∃ t₁, idle gas spark t t₁ ∧ Off temperature desired flame gas spark t₁ t'

/-- The body of `GasIsOn`. -/
def gasIsOnBody (Off On : TSpec) : TSpec := fun temperature desired flame gas spark t t' =>
  if temperature t < desired t + ε ∧ flame t = true then
    ∃ t₁, idle gas spark t t₁ ∧ On temperature desired flame gas spark t₁ t'
  else
    ∃ t₁, shutOff gas spark t t₁ ∧ Off temperature desired flame gas spark t₁ t'

/-- The pair of bodies: `(GasIsOff, GasIsOn)` is a fixed point. -/
def body (p : TSpec × TSpec) : TSpec × TSpec := (gasIsOffBody ε p.1 p.2, gasIsOnBody ε p.1 p.2)

/-- `thermostat = (gas:= ⊥ || spark:= ⊥). GasIsOff`, for a solution `Off` of the
fixed-point equations; the initial assignments take one time unit. -/
def thermostat (Off : TSpec) : TSpec := fun temperature desired flame gas spark t t' =>
  ∃ t₁, gas t₁ = false ∧ spark t₁ = false ∧ t₁ = t + 1 ∧ Off temperature desired flame gas spark t₁ t'

/-- The ignition sequence takes between 1 and 3 seconds ("the gas must not remain on
and unlit for more than 3 seconds"), then the spark is turned off; so a
`GasIsOff` step reaches its continuation within 4 seconds, and an idle step
within 1 ("the gas burner must respond to its inputs within 1 second"). -/
theorem gasIsOffBody_time (Off On : TSpec) (temperature desired : ℕ∞ → ℚ) (flame gas spark : ℕ∞ → Bool)
    (t t' : ℕ∞) (h : gasIsOffBody ε Off On temperature desired flame gas spark t t') :
    ∃ t₁, t ≤ t₁ ∧ t₁ ≤ t + 4 ∧
      (On temperature desired flame gas spark t₁ t' ∨ Off temperature desired flame gas spark t₁ t') := by
  unfold gasIsOffBody at h
  split_ifs at h with hc
  · obtain ⟨t₁, t₂, ⟨-, -, h1, h3⟩, ⟨-, rfl⟩, hOn⟩ := h
    refine ⟨t₁ + 1, le_trans (le_trans le_self_add h1) le_self_add, ?_, Or.inl hOn⟩
    calc t₁ + 1 ≤ t + 3 + 1 := by gcongr
      _ = t + 4 := by rw [add_assoc]; norm_num
  · obtain ⟨t₁, ⟨-, h0, h1⟩, hOff⟩ := h
    exact ⟨t₁, h0, le_trans h1 (by gcongr; norm_num), Or.inr hOff⟩

/-- A `GasIsOn` step reaches its continuation within 21 seconds: idling takes at most
1, and shutting off waits "at least 20 seconds to allow any accumulated gas to
clear" and at most 21. -/
theorem gasIsOnBody_time (Off On : TSpec) (temperature desired : ℕ∞ → ℚ) (flame gas spark : ℕ∞ → Bool)
    (t t' : ℕ∞) (h : gasIsOnBody ε Off On temperature desired flame gas spark t t') :
    ∃ t₁, t ≤ t₁ ∧ t₁ ≤ t + 21 ∧
      (On temperature desired flame gas spark t₁ t' ∨ Off temperature desired flame gas spark t₁ t') := by
  unfold gasIsOnBody at h
  split_ifs at h with hc
  · obtain ⟨t₁, ⟨-, h0, h1⟩, hOn⟩ := h
    exact ⟨t₁, h0, le_trans h1 (by gcongr; norm_num), Or.inl hOn⟩
  · obtain ⟨t₁, ⟨-, -, h20, h21⟩, hOff⟩ := h
    exact ⟨t₁, le_trans le_self_add h20, h21, Or.inr hOff⟩

/-- After shutting off, the gas stays off for at least 20 seconds before the
continuation: the shut-off step of `GasIsOn` ends with `gas = ⊥` at a time `≥ t+20`. -/
theorem gasIsOnBody_shutOff (Off On : TSpec) (temperature desired : ℕ∞ → ℚ) (flame gas spark : ℕ∞ → Bool)
    (t t' : ℕ∞) (h : gasIsOnBody ε Off On temperature desired flame gas spark t t')
    (hc : ¬ (temperature t < desired t + ε ∧ flame t = true)) :
    ∃ t₁, gas t₁ = false ∧ t + 20 ≤ t₁ ∧ Off temperature desired flame gas spark t₁ t' := by
  unfold gasIsOnBody at h
  rw [if_neg hc] at h
  obtain ⟨t₁, ⟨hg, -, h20, -⟩, hOff⟩ := h
  exact ⟨t₁, hg, h20, hOff⟩

/-- `⊥` for both is a fixed point of the bodies: the equations have solutions. -/
theorem bot_fixedPoint : IsFixedPoint (body ε) (fun _ _ _ _ _ _ _ => False, fun _ _ _ _ _ _ _ => False) := by
  unfold IsFixedPoint body gasIsOffBody gasIsOnBody
  refine Prod.ext ?_ ?_ <;> (funext temperature desired flame gas spark t t'; simp)

end Thermostat

end LaPToP.Interaction
