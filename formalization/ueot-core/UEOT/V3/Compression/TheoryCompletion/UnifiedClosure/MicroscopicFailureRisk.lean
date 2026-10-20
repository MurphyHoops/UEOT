import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteHorizonRisk

/-!
# Physical failure events and observable conservative envelopes

A path-TV certificate controls events in the represented history. To control
an actual microscopic failure event, the caller must prove that every such
failure lies in the preimage of an observable failure envelope. This file
derives the microscopic probability bound from that inclusion and the actual
source pushforward theorem. Exact measurability of failure through the
quotient is sufficient but is not required: a conservative envelope suffices.

The final endpoint includes failure at the initial state and at every state
up to the declared finite horizon. It is a finite-horizon risk statement,
not a claim of probability-one persistence at all times.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

noncomputable section

universe u

/-- A genuine microscopic event is bounded by any measurable envelope of
its image. No equality between the event and a quotient preimage is assumed. -/
theorem risk_microscopic_event_le_envelope
    {U V : Type u} [MeasurableSpace U] [MeasurableSpace V]
    (p : PMF U) (f : U → V) (hf : Measurable f)
    (E : Set U) (F : Set V) (hF : MeasurableSet F)
    (hEF : E ⊆ f ⁻¹' F) :
    p.toMeasure.real E ≤ (p.map f).toMeasure.real F := by
  calc
    p.toMeasure.real E ≤ p.toMeasure.real (f ⁻¹' F) := measureReal_mono hEF
    _ = (p.map f).toMeasure.real F := by
      rw [← PMF.toMeasure_map f p hf]
      simp only [Measure.real, Measure.map_apply hf hF]

/-- Failure has occurred at the initial state or after one of the recorded
transitions. The horizon counts transitions, so horizon zero is meaningful. -/
def riskEverFailure {X A : Type u} (bad : X → Prop) :
    ∀ n, CausalHistory X (A × X) n → Prop
  | 0, h => bad h
  | n + 1, h => riskEverFailure bad n h.1 ∨ bad h.2.2

/-- A state-level conservative observation rule controls the entire finite
history event, including an initially failed state. -/
theorem risk_ever_failure_envelope
    {X Y A : Type u} (q : X → Y) (badX : X → Prop) (badY : Y → Prop)
    (hbad : ∀ x, badX x → badY (q x)) (n : ℕ)
    (h : CausalHistory X (A × X) n) :
    riskEverFailure badX n h →
      riskEverFailure badY n
        (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) := by
  induction n with
  | zero => exact hbad h
  | succ n ih =>
    intro hh
    rcases hh with hh | hh
    · exact Or.inl (ih h.1 hh)
    · exact Or.inr (hbad h.2.2 hh)

/-- The smallest conservative unsafe label available at this resolution.
Every coarse state containing at least one failed microstate is marked. -/
def riskFailureEnvelope {X Y : Type u} (q : X → Y) (bad : X → Prop) : Y → Prop :=
  fun y => ∃ x, q x = y ∧ bad x

theorem risk_failure_envelope_covers
    {X Y : Type u} (q : X → Y) (bad : X → Prop) (x : X) :
    bad x → riskFailureEnvelope q bad (q x) :=
  fun hx => ⟨x, rfl, hx⟩

/-- Any sound coarse unsafe label must contain the canonical envelope.
Its conservatism cannot be removed while keeping the same observation map. -/
theorem risk_failure_envelope_minimal
    {X Y : Type u} (q : X → Y) (bad : X → Prop) (envelope : Y → Prop)
    (hcover : ∀ x, bad x → envelope (q x)) (y : Y) :
    riskFailureEnvelope q bad y → envelope y := by
  rintro ⟨x, rfl, hx⟩
  exact hcover x hx

section ControlledRisk

variable {X Y A : Type u} [Fintype X] [Fintype Y] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (p₀ : PMF X) (q : X → Y)
variable (P : ℕ → X → A → PMF X) (Q : ℕ → Y → A → PMF Y)
variable (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
variable (ε : ℕ → ℝ) (T : ℕ)
variable (hε0 : ∀ n, n < T → 0 ≤ ε n)
variable (hε1 : ∀ n, n < T → ε n ≤ 1)
variable (hrow : ∀ n, n < T → ∀ x a,
  tvDist ((P n x a).map q).toMeasure (Q n (q x) a).toMeasure ≤ ε n)

include hε0 hε1 hrow in
/-- Same-source, same-policy path control transfers an observable conservative
envelope into an upper bound on actual microscopic failure probability. -/
theorem same_policy_microscopic_failure_risk
    (E : Set (CausalHistory X (A × X) T))
    (F : Set (CausalHistory Y (A × Y) T))
    (hEF : E ⊆ (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T) ⁻¹' F) :
    (causalLaw p₀ (riskMicroControlKernel q P π) T).toMeasure.real E
      ≤ min 1
        ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real F +
          (1 - (∏ i ∈ Finset.range T, (1 - ε i)))) := by
  have hF : MeasurableSet F := Set.to_countable F |>.measurableSet
  exact (risk_microscopic_event_le_envelope _ _ (measurable_of_countable _)
    E F hF hEF).trans
      (same_policy_projected_failure_risk p₀ q P Q π ε T hε0 hε1 hrow F hF)

include hε0 hε1 hrow in
/-- A pointwise conservative unsafe-state label, uniform transition-row
calibration, and the common causal policy bound actual finite-time exit risk.
The microscopic failure label may depend on hidden state within a fibre. -/
theorem same_policy_microscopic_exit_risk
    (badX : X → Prop) (badY : Y → Prop)
    (hbad : ∀ x, badX x → badY (q x)) :
    (causalLaw p₀ (riskMicroControlKernel q P π) T).toMeasure.real
        {h | riskEverFailure badX T h}
      ≤ min 1
        ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real
            {h | riskEverFailure badY T h} +
          (1 - (∏ i ∈ Finset.range T, (1 - ε i)))) := by
  apply same_policy_microscopic_failure_risk p₀ q P Q π ε T hε0 hε1 hrow
  intro h hh
  exact risk_ever_failure_envelope q badX badY hbad T h hh

include hε0 hε1 hrow in
/-- The canonical envelope discharges the observation-safety implication.
The bound may become uninformative when compression hides unsafe states. -/
theorem same_policy_canonical_exit_risk (bad : X → Prop) :
    (causalLaw p₀ (riskMicroControlKernel q P π) T).toMeasure.real
        {h | riskEverFailure bad T h}
      ≤ min 1
        ((causalLaw (p₀.map q) (riskMacroControlKernel Q π) T).toMeasure.real
            {h | riskEverFailure (riskFailureEnvelope q bad) T h} +
          (1 - (∏ i ∈ Finset.range T, (1 - ε i)))) :=
  same_policy_microscopic_exit_risk p₀ q P Q π ε T hε0 hε1 hrow
    bad (riskFailureEnvelope q bad) (risk_failure_envelope_covers q bad)

end ControlledRisk

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
