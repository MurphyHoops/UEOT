import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCSeparationPower
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCInterventionTransferAudit

/-!
# SISC rowwise experiments: actual intervals, identification, and source audit

Different probes use separate fixed-allocation samples. Their actual means
must independently match the declared N3 kernel/source/action/read, or the
declared N6 parent response. These are distinct scientific obligations.
One scalar coordinate-good event controls every candidate, so no additional
candidate-count penalty is paid. N3 retains its nonempty-observation field;
N6 retains the existing gap against every parent in its full type.

The true candidate or parent is absent from both data constructors. It only
appears in correctness statements together with external model matching.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling
open scoped BigOperators Classical

noncomputable section

universe uX uA uC uJ uΩ uZ uChild

/-- Coordinate-level model matching, stated before any candidate is selected.
Different treatment laws do not automatically match one source/action row. -/
def RowwiseCoordinateLawMatchesKernel
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] [MeasurableSpace X]
    (P : RegisteredCausalCandidateProtocol X A C J) (row : J → PMF X) : Prop :=
  ∀ j, trueRisk (row j).toMeasure (fun y => P.read y j) =
    ∑ y : X, P.kernel.mass P.source P.action y * P.read y j

/-- Kernel risk equality is derived from actual coordinate means, not supplied
as the final target equation. Predictions are exactly the old protocol's table. -/
theorem rowwise_population_risk_eq_registered
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] [MeasurableSpace X]
    (P : RegisteredCausalCandidateProtocol X A C J) (row : J → PMF X)
    (hMean : RowwiseCoordinateLawMatchesKernel P row) (c : C) :
    (∑ j : J, |trueRisk (row j).toMeasure (fun y => P.read y j) -
      P.prediction c j|) = registeredCandidateRisk P c := by
  unfold registeredCandidateRisk
  apply Finset.sum_congr rfl
  intro j _
  rw [hMean j]

/-- Estimate the mean of each actual group first, then its L1 mismatch. -/
def rowwiseCoordinateRisk
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] {Ω : Type uΩ} {N : J → ℕ}
    (P : RegisteredCausalCandidateProtocol X A C J)
    (sample : ∀ j, Fin (N j) → Ω → X) (ω : Ω) (c : C) : ℝ :=
  ∑ j : J, |empiricalRisk (fun y => P.read y j) (sample j) ω - P.prediction c j|

/-- Only the interval is replaced. The original kernel, source, action,
predictions, registration, causal gate, threshold and nonempty field persist. -/
def rowwiseCoordinateProtocol
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] {Ω : Type uΩ} {N : J → ℕ}
    (P : RegisteredCausalCandidateProtocol X A C J)
    (sample : ∀ j, Fin (N j) → Ω → X) (ω : Ω) (u : ℝ) (hu : 0 ≤ u) :
    RegisteredCausalCandidateProtocol X A C J :=
  { P with interval := fun c => {
      estimate := rowwiseCoordinateRisk P sample ω c
      statisticalRadius := (Fintype.card J : ℝ) * u
      driftRadius := 0
      statisticalRadius_nonneg := mul_nonneg (Nat.cast_nonneg _) hu
      driftRadius_nonneg := le_refl 0
    } }

theorem rowwise_protocol_same_risk
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] {Ω : Type uΩ} {N : J → ℕ}
    (P : RegisteredCausalCandidateProtocol X A C J)
    (sample : ∀ j, Fin (N j) → Ω → X) (ω : Ω) (u : ℝ) (hu : 0 ≤ u) (c : C) :
    registeredCandidateRisk (rowwiseCoordinateProtocol P sample ω u hu) c =
      registeredCandidateRisk P c := rfl

/-- The common mean event simultaneously calibrates all candidates, even
when the candidate type itself is infinite. -/
theorem rowwise_protocol_calibrated_on_good
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] [MeasurableSpace X] {Ω : Type uΩ} {N : J → ℕ}
    (P : RegisteredCausalCandidateProtocol X A C J) (row : J → PMF X)
    (sample : ∀ j, Fin (N j) → Ω → X) (ω : Ω) (u : ℝ) (hu : 0 ≤ u)
    (hMean : RowwiseCoordinateLawMatchesKernel P row)
    (hgood : ω ∈ coordinateGood row (fun j y => P.read y j) sample u) :
    (rowwiseCoordinateProtocol P sample ω u hu).Calibrated := by
  intro c _hc
  change |rowwiseCoordinateRisk P sample ω c - registeredCandidateRisk P c| ≤
    (Fintype.card J : ℝ) * u + 0
  rw [← rowwise_population_risk_eq_registered P row hMean c]
  calc
    |rowwiseCoordinateRisk P sample ω c -
        (∑ j : J, |trueRisk (row j).toMeasure (fun y => P.read y j) - P.prediction c j|)|
      ≤ ∑ j : J, |empiricalRisk (fun y => P.read y j) (sample j) ω -
          trueRisk (row j).toMeasure (fun y => P.read y j)| :=
        finite_absolute_response_risk_lipschitz
          (fun j => empiricalRisk (fun y => P.read y j) (sample j) ω)
          (fun j => trueRisk (row j).toMeasure (fun y => P.read y j))
          (fun j => P.prediction c j)
    _ ≤ ∑ _j : J, u := Finset.sum_le_sum (fun j _ => hgood j)
    _ = (Fintype.card J : ℝ) * u + 0 := by simp [Finset.sum_const, nsmul_eq_mul]

/-- Existing N4 margins are consumed by the actual newly constructed interval. -/
theorem rowwise_unique_of_good_and_margin
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] [MeasurableSpace X] [DecidableEq C]
    {Ω : Type uΩ} {N : J → ℕ}
    (P : RegisteredCausalCandidateProtocol X A C J) (row : J → PMF X)
    (sample : ∀ j, Fin (N j) → Ω → X) (ω : Ω) (u : ℝ) (hu : 0 ≤ u)
    (hMean : RowwiseCoordinateLawMatchesKernel P row) (c : C)
    (hreg : c ∈ P.registered) (hcausal : P.causal c)
    (hinside : registeredCandidateRisk P c + 2 * ((Fintype.card J : ℝ) * u) ≤
      P.tolerance)
    (houtside : ∀ d ∈ P.registered, P.causal d → d ≠ c →
      P.tolerance + 2 * ((Fintype.card J : ℝ) * u) < registeredCandidateRisk P d)
    (hgood : ω ∈ coordinateGood row (fun j y => P.read y j) sample u) :
    resolveRegisteredCandidates (rowwiseCoordinateProtocol P sample ω u hu) =
      .unique c := by
  apply registered_unique_identified_of_calibrated_margin
    (rowwiseCoordinateProtocol P sample ω u hu) c ((Fintype.card J : ℝ) * u)
  · exact hreg
  · exact hcausal
  · exact hinside
  · exact houtside
  · intro d _hd
    simp [rowwiseCoordinateProtocol, IntervalCertificate.totalRadius]
  · exact rowwise_protocol_calibrated_on_good P row sample ω u hu hMean hgood

/-- Identification power under the independently stated coordinate/model match.
The correct label is absent from the interval constructor and the resolver. -/
theorem measure_rowwise_failure_to_identify_le
    {X : Type uX} {A : Type uA} {C : Type uC} {J : Type uJ}
    [Fintype X] [Fintype J] [MeasurableSpace X] [DecidableEq C]
    {Ω : Type uΩ} [MeasurableSpace Ω]
    (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (P : RegisteredCausalCandidateProtocol X A C J)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (row : J → PMF X)
    (sample : ∀ j, Fin (N j) → Ω → X)
    (hRead : ∀ j, Measurable (fun y => P.read y j))
    (hRead01 : ∀ j y, P.read y j ∈ Set.Icc (0 : ℝ) 1)
    (hSample : ∀ j k, Measurable (sample j k))
    (hIndependent : ∀ j, iIndepFun (sample j) μ)
    (hLaw : ∀ j k, μ.map (sample j k) = (row j).toMeasure)
    (u : ℝ) (hu : 0 ≤ u) (hMean : RowwiseCoordinateLawMatchesKernel P row)
    (c : C) (hreg : c ∈ P.registered) (hcausal : P.causal c)
    (hinside : registeredCandidateRisk P c + 2 * ((Fintype.card J : ℝ) * u) ≤
      P.tolerance)
    (houtside : ∀ d ∈ P.registered, P.causal d → d ≠ c →
      P.tolerance + 2 * ((Fintype.card J : ℝ) * u) < registeredCandidateRisk P d) :
    μ.real {ω | resolveRegisteredCandidates
      (rowwiseCoordinateProtocol P sample ω u hu) ≠ .unique c} ≤
      min 1 (scalarBudget N u) := by
  have hsubset : {ω | resolveRegisteredCandidates
      (rowwiseCoordinateProtocol P sample ω u hu) ≠ .unique c} ⊆
      (coordinateGood row (fun j y => P.read y j) sample u)ᶜ := by
    intro ω hfail hgood
    exact hfail (rowwise_unique_of_good_and_margin P row sample ω u hu
      hMean c hreg hcausal hinside houtside hgood)
  exact (measureReal_mono hsubset).trans
    (measure_coordinateGood_compl_le N hN μ row (fun j y => P.read y j) sample
      hRead hRead01 hSample hIndependent hLaw u hu)

/-- Separate N6 constructor. The observations are for the child considered
in the theorem; this does not infer that other children share the experiment. -/
def rowwiseInterventionAudit
    {C : Type uC} {Child : Type uChild} {J : Type uJ}
    [Fintype C] {Z : Type uZ} {Ω : Type uΩ} {N : J → ℕ}
    (audit : FiniteInterventionTransferAudit C Child J)
    (outcome : J → Z → ℝ) (sample : ∀ j, Fin (N j) → Ω → Z)
    (ω : Ω) (u : ℝ) : FiniteInterventionTransferAudit C Child J :=
  { audit with
    observedResponse := fun _ j => empiricalRisk (outcome j) (sample j) ω
    tolerance := u }

/-- Actual population means must match this parent's registered responses.
`LocalResponseGap` quantifies over the entire parent type, as in the old API. -/
theorem rowwise_audited_source_unique_on_good
    {C : Type uC} {Child : Type uChild} {J : Type uJ}
    [Fintype C] [DecidableEq C] {Z : Type uZ} [MeasurableSpace Z]
    {Ω : Type uΩ} {N : J → ℕ}
    (audit : FiniteInterventionTransferAudit C Child J)
    (row : J → PMF Z) (outcome : J → Z → ℝ)
    (sample : ∀ j, Fin (N j) → Ω → Z) (ω : Ω) (u : ℝ)
    (parent : C) (child : Child)
    (hreg : parent ∈ audit.registered)
    (htransfer : audit.authenticatedTransfer parent child)
    (hModel : ∀ j, trueRisk (row j).toMeasure (outcome j) =
      audit.referenceResponse parent j)
    (hgap : LocalResponseGap audit.referenceResponse u parent)
    (hgood : ω ∈ coordinateGood row outcome sample u) :
    auditedSourceCandidates (rowwiseInterventionAudit audit outcome sample ω u) child =
      {parent} := by
  apply audited_source_candidates_eq_singleton_of_gap
    (rowwiseInterventionAudit audit outcome sample ω u) child parent
  · exact hreg
  · exact htransfer
  · intro j
    change |empiricalRisk (outcome j) (sample j) ω -
      audit.referenceResponse parent j| ≤ u
    rw [← hModel j]
    exact hgood j
  · exact hgap

/-- The N6 probability bound consumes the same scalar good event once.
Transfer authentication and model matching remain independent premises. -/
theorem measure_rowwise_audited_source_failure_le
    {C : Type uC} {Child : Type uChild} {J : Type uJ}
    [Fintype C] [DecidableEq C] [Fintype J]
    {Z : Type uZ} [MeasurableSpace Z] {Ω : Type uΩ} [MeasurableSpace Ω]
    (N : J → ℕ) (hN : ∀ j, 0 < N j)
    (audit : FiniteInterventionTransferAudit C Child J)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (row : J → PMF Z)
    (outcome : J → Z → ℝ) (sample : ∀ j, Fin (N j) → Ω → Z)
    (hOutcome : ∀ j, Measurable (outcome j))
    (hOutcome01 : ∀ j z, outcome j z ∈ Set.Icc (0 : ℝ) 1)
    (hSample : ∀ j k, Measurable (sample j k))
    (hIndependent : ∀ j, iIndepFun (sample j) μ)
    (hLaw : ∀ j k, μ.map (sample j k) = (row j).toMeasure)
    (u : ℝ) (hu : 0 ≤ u) (parent : C) (child : Child)
    (hreg : parent ∈ audit.registered)
    (htransfer : audit.authenticatedTransfer parent child)
    (hModel : ∀ j, trueRisk (row j).toMeasure (outcome j) =
      audit.referenceResponse parent j)
    (hgap : LocalResponseGap audit.referenceResponse u parent) :
    μ.real {ω | auditedSourceCandidates
      (rowwiseInterventionAudit audit outcome sample ω u) child ≠ {parent}} ≤
      min 1 (scalarBudget N u) := by
  have hsubset : {ω | auditedSourceCandidates
      (rowwiseInterventionAudit audit outcome sample ω u) child ≠ {parent}} ⊆
      (coordinateGood row outcome sample u)ᶜ := by
    intro ω hfail hgood
    exact hfail (rowwise_audited_source_unique_on_good audit row outcome sample ω u
      parent child hreg htransfer hModel hgap hgood)
  exact (measureReal_mono hsubset).trans
    (measure_coordinateGood_compl_le N hN μ row outcome sample hOutcome hOutcome01
      hSample hIndependent hLaw u hu)

end
end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
