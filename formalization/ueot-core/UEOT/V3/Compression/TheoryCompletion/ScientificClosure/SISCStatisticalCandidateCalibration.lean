import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCRegisteredCausalCandidates
import UEOT.V3.BoundedLossTwoSided
import UEOT.V3.FiniteCandidatePStat08
import Mathlib.Tactic

/-!
# SISC N4: finite-sample statistical certification of candidate calibration

Reuses the *existing proven* two-sided Hoeffding/finite-candidate
union-bound theorem (P-STAT-08 supporting lemma). No concentration
inequality is reproved here. Instead we prove that a calibrated
simultaneous risk-estimation event implies N3's scientific good-event,
then transport the bound to an erroneous unique resolution.

CRUCIAL: the bridge from sampled loss trueRisk to N3's post-action
absolute *mean response mismatch* is a named, external hRiskMatch
assumption, NOT a definitional identity: E|Y-r| and |E Y-r| differ.
It must be discharged by a dedicated estimator/measurement model.

This module uses IID bounded [0,1] losses. Correlated block samples
cannot be silently passed through the IID proof.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open UEOT.V3.BoundedLossTwoSided

universe uX uA uC uO uΩ uZ

/-- Replace only the previously admitted C2 estimates with *actual finite
validation empirical risk* and a registered nonnegative radius. All prior
causal registrations, K, readouts and candidate responses are retained. -/
noncomputable def empiricalCandidateProtocol
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    {Z : Type uZ} {Ω : Type uΩ}
    {N : ℕ}
    (P : RegisteredCausalCandidateProtocol X A C O)
    (loss : C → Z → ℝ)
    (sample : Fin N → Ω → Z)
    (ω : Ω) (u : ℝ) (hu : 0 ≤ u) :
    RegisteredCausalCandidateProtocol X A C O :=
  { P with interval := fun c => {
      estimate := empiricalRisk (loss c) sample ω
      statisticalRadius := u
      driftRadius := 0
      statisticalRadius_nonneg := hu
      driftRadius_nonneg := le_refl 0
    } }

/-- True candidate risk matching is an explicit interface obligation. The
random empirical loss is not automatically an unbiased estimator of the
absolute mean mismatch which was defined in N3. -/
def SampleLossMatchesRegisteredRisk
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    {Z : Type uZ} [MeasurableSpace Z]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (dataLaw : Measure Z) (loss : C → Z → ℝ) : Prop :=
  ∀ c ∈ P.registered,
    trueRisk dataLaw (loss c) = registeredCandidateRisk P c

/-- Uniform finite validation is sufficient for *all* registered C2
certificates simultaneously, including the causal candidates selected only
after looking at the data. -/
theorem empiricalCandidateProtocol_calibrated_of_uniform
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    {Z : Type uZ} [MeasurableSpace Z] {Ω : Type uΩ}
    {N : ℕ}
    (P : RegisteredCausalCandidateProtocol X A C O)
    (dataLaw : Measure Z) (loss : C → Z → ℝ)
    (sample : Fin N → Ω → Z)
    (ω : Ω) (u : ℝ) (hu : 0 ≤ u)
    (hRiskMatch : SampleLossMatchesRegisteredRisk P dataLaw loss)
    (hUniform : ∀ c,
      |empiricalRisk (loss c) sample ω - trueRisk dataLaw (loss c)| ≤ u) :
    (empiricalCandidateProtocol P loss sample ω u hu).Calibrated := by
  intro c hc
  have hmatch := hRiskMatch c hc
  change |empiricalRisk (loss c) sample ω - registeredCandidateRisk P c| ≤ u + 0
  simpa [hmatch] using hUniform c

/-- Reuse the exact frozen finite-class union bound to certify N3 calibration
with *actual probability*, rather than merely assuming that the good-event
holds. The statistical meaning still relies on the explicit model-matching
contract above. -/
theorem measure_bad_empirical_calibration_le
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [Fintype C]
    {Z : Type uZ} {Ω : Type uΩ}
    [MeasurableSpace Z] [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N)
    (P : RegisteredCausalCandidateProtocol X A C O)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure Z)
    (loss : C → Z → ℝ)
    (hloss : ∀ c, Measurable (loss c))
    (hloss01 : ∀ c z, loss c z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Ω → Z)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = dataLaw)
    (u : ℝ) (hu : 0 ≤ u)
    (hRiskMatch : SampleLossMatchesRegisteredRisk P dataLaw loss) :
    μ.real {ω | ¬ (empiricalCandidateProtocol P loss sample ω u hu).Calibrated} ≤
      (Fintype.card C : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω | ¬ (empiricalCandidateProtocol P loss sample ω u hu).Calibrated} ⊆
      {ω | ∃ c : C,
        u < |empiricalRisk (loss c) sample ω - trueRisk dataLaw (loss c)|} := by
    intro ω hbad
    by_contra hn
    have hUniform : ∀ c,
        |empiricalRisk (loss c) sample ω - trueRisk dataLaw (loss c)| ≤ u := by
      intro c
      by_contra hc
      exact hn ⟨c, lt_of_not_ge hc⟩
    exact hbad (empiricalCandidateProtocol_calibrated_of_uniform
      P dataLaw loss sample ω u hu hRiskMatch hUniform)
  exact (measureReal_mono hsubset).trans
    (measure_exists_candidate_bad_le hN μ dataLaw loss hloss hloss01
      sample hmeas hindep hlaw hu)

/-- A wrong unique operational successor within the registered causal family
is contained in the calibrated-good-event failure. Consequently its
probability is at most the *existing* finite-class Hoeffding bound.

No physical-token class or unregistered causal lineage is asserted. -/
theorem measure_wrong_unique_registered_candidate_le
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [Fintype C] [DecidableEq C]
    {Z : Type uZ} {Ω : Type uΩ}
    [MeasurableSpace Z] [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N)
    (P : RegisteredCausalCandidateProtocol X A C O)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure Z)
    (loss : C → Z → ℝ)
    (hloss : ∀ c, Measurable (loss c))
    (hloss01 : ∀ c z, loss c z ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin N → Ω → Z)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = dataLaw)
    (u : ℝ) (hu : 0 ≤ u)
    (hRiskMatch : SampleLossMatchesRegisteredRisk P dataLaw loss) :
    μ.real {ω | ∃ c d : C,
      resolveRegisteredCandidates
        (empiricalCandidateProtocol P loss sample ω u hu) = .unique c ∧
      (empiricalCandidateProtocol P loss sample ω u hu).TrulyCompatible d ∧
      d ≠ c} ≤
      (Fintype.card C : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω | ∃ c d : C,
        resolveRegisteredCandidates
          (empiricalCandidateProtocol P loss sample ω u hu) = .unique c ∧
        (empiricalCandidateProtocol P loss sample ω u hu).TrulyCompatible d ∧
        d ≠ c} ⊆
      {ω | ¬ (empiricalCandidateProtocol P loss sample ω u hu).Calibrated} := by
    intro ω ⟨c, d, hunique, hd, hne⟩
    exact wrong_unique_implies_calibration_failure
      (empiricalCandidateProtocol P loss sample ω u hu) hunique hd hne
  exact (measureReal_mono hsubset).trans
    (measure_bad_empirical_calibration_le hN P μ dataLaw loss hloss
      hloss01 sample hmeas hindep hlaw u hu hRiskMatch)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
