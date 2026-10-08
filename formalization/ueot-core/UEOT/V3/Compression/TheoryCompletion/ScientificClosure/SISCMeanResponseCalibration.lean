import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCStatisticalCandidateCalibration
import Mathlib.Tactic

/-!
# SISC N4-B — genuine sampled coordinate means calibrate N3's L1 risk

The N3 target is a SUM of absolute discrepancies between *expected*
post-action responses and candidate response vectors. E|Y-r| is NOT that
target. Here we estimate the observation-coordinate means first, then
apply the reverse triangle inequality to prove the candidate-risk
estimator's uniform error bound.

One simultaneous Hoeffding good event indexed only by the registered
observation coordinates O suffices for ALL candidates C, even with a large
or non-Fintype registered candidate universe. The required law-matching
hypothesis identifies the observed post-action microstate sample law
with the declared transition kernel's coordinate expectations; this is
an independent scientific modeling assumption, not a free consequence
of the process-level candidate decision.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open MeasureTheory ProbabilityTheory Real
open UEOT.V3.BoundedLossSampling
open UEOT.V3.BoundedLossTwoSided

universe uX uA uC uO uΩ

/-- The L1 discrepancy of candidate response vectors is 1-Lipschitz in
each measured coordinate, independently of the candidate predictions. -/
theorem finite_absolute_response_risk_lipschitz
    {O : Type uO} [Fintype O]
    (p q target : O → ℝ) :
    |(∑ j : O, |p j - target j|) -
      (∑ j : O, |q j - target j|)| ≤
        ∑ j : O, |p j - q j| := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j : O, (|p j - target j| - |q j - target j|)| ≤
        ∑ j : O, abs (|p j - target j| - |q j - target j|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : O, |p j - q j| := by
      apply Finset.sum_le_sum
      intro j _
      calc
        abs (|p j - target j| - |q j - target j|) ≤
            |(p j - target j) - (q j - target j)| :=
          abs_abs_sub_abs_le_abs_sub _ _
        _ = |p j - q j| := by congr 1; ring

/-- From IID samples of the *next microscopic state*, first estimate each
registered observable coordinate mean. Only then form the candidate
L1 response risk, avoiding the false identity E|Y-r| = |EY-r|. -/
noncomputable def empiricalCoordinateRisk
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    {Ω : Type uΩ} {N : ℕ}
    (P : RegisteredCausalCandidateProtocol X A C O)
    (sample : Fin N → Ω → X) (ω : Ω) (c : C) : ℝ :=
  ∑ j : O, |empiricalRisk (fun y => P.read y j) sample ω -
    P.prediction c j|

/-- The actual C2 radius scales with the number of observed coordinates,
not with the number of candidate labels, and retains the independent
statistical versus drift-radius distinction. -/
noncomputable def empiricalCoordinateProtocol
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    {Ω : Type uΩ} {N : ℕ}
    (P : RegisteredCausalCandidateProtocol X A C O)
    (sample : Fin N → Ω → X) (ω : Ω)
    (u : ℝ) (hu : 0 ≤ u) :
    RegisteredCausalCandidateProtocol X A C O :=
  { P with interval := fun c => {
      estimate := empiricalCoordinateRisk P sample ω c
      statisticalRadius := (Fintype.card O : ℝ) * u
      driftRadius := 0
      statisticalRadius_nonneg := mul_nonneg (Nat.cast_nonneg _) hu
      driftRadius_nonneg := le_refl 0
    } }

/-- A correctly specified observation-law contract: each expected
coordinate under the *actual* IID data law equals the corresponding
one-step microkernel predicted response. This does not assume that the
sampled absolute loss estimates the absolute-mean loss. -/
def PostActionCoordinateLawMatchesKernel
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [MeasurableSpace X]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (dataLaw : Measure X) : Prop :=
  ∀ j : O, trueRisk dataLaw (fun y => P.read y j) =
    ∑ y : X, P.kernel.mass P.source P.action y * P.read y j

/-- Simultaneous coordinate-wise mean accuracy is sufficient to calibrate
all N3 registered causal candidate risk intervals, with no candidate-loss
model matching assumption and no union bound over candidate count. -/
theorem empirical_coordinate_protocol_calibrated_of_uniform
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [MeasurableSpace X]
    {Ω : Type uΩ} {N : ℕ}
    (P : RegisteredCausalCandidateProtocol X A C O)
    (dataLaw : Measure X) (sample : Fin N → Ω → X)
    (ω : Ω) (u : ℝ) (hu : 0 ≤ u)
    (hLaw : PostActionCoordinateLawMatchesKernel P dataLaw)
    (hUniform : ∀ j : O,
       |empiricalRisk (fun y => P.read y j) sample ω -
          trueRisk dataLaw (fun y => P.read y j)| ≤ u) :
    (empiricalCoordinateProtocol P sample ω u hu).Calibrated := by
  intro c hc
  change |empiricalCoordinateRisk P sample ω c -
      registeredCandidateRisk P c| ≤ (Fintype.card O : ℝ) * u + 0
  have hlip := finite_absolute_response_risk_lipschitz
    (fun j => empiricalRisk (fun y => P.read y j) sample ω)
    (fun j => trueRisk dataLaw (fun y => P.read y j))
    (fun j => P.prediction c j)
  have hpoint : ∀ j : O, |empiricalRisk
      (fun y => P.read y j) sample ω -
      trueRisk dataLaw (fun y => P.read y j)| ≤ u := hUniform
  calc
    |empiricalCoordinateRisk P sample ω c -
      registeredCandidateRisk P c| =
      |(∑ j : O, |empiricalRisk (fun y => P.read y j) sample ω -
         P.prediction c j|) -
       (∑ j : O, |trueRisk dataLaw (fun y => P.read y j) -
         P.prediction c j|)| := by
           have heq : (∑ j : O, |(∑ y : X,
               P.kernel.mass P.source P.action y * P.read y j) -
               P.prediction c j|) =
             (∑ j : O, |trueRisk dataLaw (fun y => P.read y j) -
               P.prediction c j|) := by
             apply Finset.sum_congr rfl
             intro j _
             rw [hLaw j]
           simp only [empiricalCoordinateRisk, registeredCandidateRisk]
           rw [heq]
    _ ≤ ∑ j : O, |empiricalRisk (fun y => P.read y j) sample ω -
         trueRisk dataLaw (fun y => P.read y j)| := hlip
    _ ≤ ∑ _j : O, u := by
      apply Finset.sum_le_sum
      intro j _
      exact hpoint j
    _ = (Fintype.card O : ℝ) * u + 0 := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The frozen bounded-loss union-bound theorem is applied ONCE to the
coordinates (rather than individually to data-dependent candidate
decisions). This bound holds simultaneously for the entire declared
finite candidate registry, independently of its size. -/
theorem measure_bad_coordinate_calibration_le
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [MeasurableSpace X]
    {Ω : Type uΩ} [MeasurableSpace Ω]
    {N : ℕ} (hN : 0 < N)
    (P : RegisteredCausalCandidateProtocol X A C O)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure X)
    (sample : Fin N → Ω → X)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = dataLaw)
    (hReadMeas : ∀ j, Measurable (fun y => P.read y j))
    (hRead01 : ∀ j y, P.read y j ∈ Set.Icc (0 : ℝ) 1)
    (hModel : PostActionCoordinateLawMatchesKernel P dataLaw)
    (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω | ¬ (empiricalCoordinateProtocol P sample ω u hu).Calibrated} ≤
      (Fintype.card O : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω | ¬ (empiricalCoordinateProtocol P sample ω u hu).Calibrated} ⊆
      {ω | ∃ j : O,
       u < |empiricalRisk (fun y => P.read y j) sample ω -
          trueRisk dataLaw (fun y => P.read y j)|} := by
    intro ω hbad
    by_contra hn
    have hUniform : ∀ j : O,
        |empiricalRisk (fun y => P.read y j) sample ω -
          trueRisk dataLaw (fun y => P.read y j)| ≤ u := by
      intro j
      by_contra hj
      exact hn ⟨j, lt_of_not_ge hj⟩
    exact hbad (empirical_coordinate_protocol_calibrated_of_uniform
      P dataLaw sample ω u hu hModel hUniform)
  exact (measureReal_mono hsubset).trans
    (measure_exists_candidate_bad_le hN μ dataLaw
      (fun j y => P.read y j) hReadMeas hRead01
      sample hmeas hindep hlaw hu)

/-- Quantitative probability of false *unique* operational succession,
relative to genuinely compatible registered causal candidates, controlled
by ONLY the number of measured response coordinates O. -/
theorem measure_wrong_unique_coordinate_protocol_le
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [MeasurableSpace X]
    {Ω : Type uΩ} [MeasurableSpace Ω] [DecidableEq C]
    {N : ℕ} (hN : 0 < N)
    (P : RegisteredCausalCandidateProtocol X A C O)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure X)
    (sample : Fin N → Ω → X)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = dataLaw)
    (hReadMeas : ∀ j, Measurable (fun y => P.read y j))
    (hRead01 : ∀ j y, P.read y j ∈ Set.Icc (0 : ℝ) 1)
    (hModel : PostActionCoordinateLawMatchesKernel P dataLaw)
    (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω | ∃ c d : C,
      resolveRegisteredCandidates (empiricalCoordinateProtocol P sample ω u hu) = .unique c ∧
      (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible d ∧
      d ≠ c} ≤
      (Fintype.card O : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω | ∃ c d : C,
        resolveRegisteredCandidates (empiricalCoordinateProtocol P sample ω u hu) = .unique c ∧
        (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible d ∧
        d ≠ c} ⊆
      {ω | ¬ (empiricalCoordinateProtocol P sample ω u hu).Calibrated} := by
    intro ω ⟨c, d, hunique, hd, hne⟩
    exact wrong_unique_implies_calibration_failure
      (empiricalCoordinateProtocol P sample ω u hu) hunique hd hne
  exact (measureReal_mono hsubset).trans
    (measure_bad_coordinate_calibration_le hN P μ dataLaw sample
      hmeas hindep hlaw hReadMeas hRead01 hModel u hu)

/-- Negative control against the invalid assumption E|Y-r| = |EY-r|:
with a uniformly random Boolean response and target 1/2, absolute loss
has expectation 1/2 while mismatch of expected response is exactly zero. -/
theorem expected_abs_loss_is_not_abs_mean_mismatch :
    ((1 / 2 : ℝ) * |(0 : ℝ) - 1/2| +
      (1 / 2 : ℝ) * |(1 : ℝ) - 1/2|) ≠
      |((1 / 2 : ℝ) * 0 + (1 / 2 : ℝ) * 1) - 1/2| := by
  norm_num

/-- A FALSE unique certificate means the returned candidate is genuinely
incompatible OR some other genuinely compatible registered causal candidate
was wrongly excluded. On a simultaneous good event neither is possible. -/
theorem unsound_registered_unique_implies_bad_calibration
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O) (c : C)
    (hout : resolveRegisteredCandidates P = .unique c)
    (hbad : ¬ P.TrulyCompatible c ∨
      ∃ d : C, P.TrulyCompatible d ∧ d ≠ c) :
    ¬ P.Calibrated := by
  intro hcal
  obtain ⟨hc, huniq⟩ := unique_resolution_sound P hcal c hout
  rcases hbad with hn | ⟨d, hd, hne⟩
  · exact hn hc
  · exact hne (huniq d hd)

/-- Probability of ANY incorrect unique claim (including certifying an
incompatible label when there is no valid candidate at all), bounded by the
same coordinate-based P-STAT union bound. -/
theorem measure_unsound_unique_coordinate_protocol_le
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [MeasurableSpace X]
    {Ω : Type uΩ} [MeasurableSpace Ω] [DecidableEq C]
    {N : ℕ} (hN : 0 < N)
    (P : RegisteredCausalCandidateProtocol X A C O)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure X)
    (sample : Fin N → Ω → X)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = dataLaw)
    (hReadMeas : ∀ j, Measurable (fun y => P.read y j))
    (hRead01 : ∀ j y, P.read y j ∈ Set.Icc (0 : ℝ) 1)
    (hModel : PostActionCoordinateLawMatchesKernel P dataLaw)
    (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω | ∃ c : C,
      resolveRegisteredCandidates (empiricalCoordinateProtocol P sample ω u hu) = .unique c ∧
      (¬ (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible c ∨
        ∃ d : C, (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible d ∧ d ≠ c)} ≤
      (Fintype.card O : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω | ∃ c : C,
        resolveRegisteredCandidates (empiricalCoordinateProtocol P sample ω u hu) = .unique c ∧
        (¬ (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible c ∨
          ∃ d : C, (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible d ∧ d ≠ c)} ⊆
      {ω | ¬ (empiricalCoordinateProtocol P sample ω u hu).Calibrated} := by
    intro ω ⟨c, hselected, hunsound⟩
    exact unsound_registered_unique_implies_bad_calibration
      (empiricalCoordinateProtocol P sample ω u hu) c hselected hunsound
  exact (measureReal_mono hsubset).trans
    (measure_bad_coordinate_calibration_le hN P μ dataLaw sample
      hmeas hindep hlaw hReadMeas hRead01 hModel u hu)

/-- Similarly, reporting no compatible registered candidate when one does
exist is a statistically unsound 'uncovered' decision. The same Hoeffding
calibration event controls this failure; it says nothing about candidates
outside the scientific registration universe. -/
theorem measure_false_uncovered_coordinate_protocol_le
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [MeasurableSpace X]
    {Ω : Type uΩ} [MeasurableSpace Ω] [DecidableEq C]
    {N : ℕ} (hN : 0 < N)
    (P : RegisteredCausalCandidateProtocol X A C O)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (dataLaw : Measure X)
    (sample : Fin N → Ω → X)
    (hmeas : ∀ n, Measurable (sample n))
    (hindep : iIndepFun sample μ)
    (hlaw : ∀ n, μ.map (sample n) = dataLaw)
    (hReadMeas : ∀ j, Measurable (fun y => P.read y j))
    (hRead01 : ∀ j y, P.read y j ∈ Set.Icc (0 : ℝ) 1)
    (hModel : PostActionCoordinateLawMatchesKernel P dataLaw)
    (u : ℝ) (hu : 0 ≤ u) :
    μ.real {ω |
      resolveRegisteredCandidates (empiricalCoordinateProtocol P sample ω u hu) = .uncovered ∧
      ∃ d : C, (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible d} ≤
      (Fintype.card O : ℝ) * (2 * exp (-2 * (N : ℝ) * u ^ 2)) := by
  have hsubset :
      {ω | resolveRegisteredCandidates (empiricalCoordinateProtocol P sample ω u hu) = .uncovered ∧
        ∃ d : C, (empiricalCoordinateProtocol P sample ω u hu).TrulyCompatible d} ⊆
      {ω | ¬ (empiricalCoordinateProtocol P sample ω u hu).Calibrated} := by
    intro ω ⟨houtput, hexists⟩ hcal
    exact (uncovered_excludes_registered_truth
      (empiricalCoordinateProtocol P sample ω u hu) hcal houtput) hexists
  exact (measureReal_mono hsubset).trans
    (measure_bad_coordinate_calibration_le hN P μ dataLaw sample
      hmeas hindep hlaw hReadMeas hRead01 hModel u hu)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
