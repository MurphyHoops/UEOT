import UEOT.V3.Compression.CrossTrack.InteractionBindingIsolation
import UEOT.V3.Compression.CrossTrack.ParentBindingDynamic

/-!
# Dynamic interaction-generated semantic exactification

If a finite separating interaction family remains fixed while observational
fingerprint error tends to zero, common-Markov parent realization plus a
uniform positive Track-S semantic-isolation floor forces the corresponding
parent invariant semantics to converge in total variation.
-/

namespace UEOT.V3.Compression.CrossTrack

open Filter
open MeasureTheory
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uA uI uY uX uS

noncomputable section

variable {A : Type uA} {I : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]
variable [Fintype A] [Nontrivial A] [MetricSpace A]
variable {X : Type uX} [MeasurableSpace X]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance interactionDynamicDecidableEqS : DecidableEq S :=
  Classical.decEq S

/-- Time-slice semantic bound generated directly by interaction-fingerprint
error. -/
theorem interactionGenerated_timeSliceSemanticBound
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes)
    (observed : ℕ → I → Measure Y)
    (hobserved : ∀ n i, IsProbabilityMeasure (observed n i))
    (eta : ℕ → ℝ)
    (thetaBar theta : ℕ → A)
    (hobs : ∀ n,
      interactionObservationError F probes hprobes (observed n) (thetaBar n) ≤ eta n ∧
      interactionObservationError F probes hprobes (observed n) (theta n) ≤ eta n)
    (K : A → Matrix S S ℝ)
    (hK : ∀ a, K a ∈ Matrix.rowStochastic ℝ S)
    (real : CommonMarkovParentRealization X (fun a : A => a) K hK)
    (mu : A → stdSimplex ℝ S)
    (hmu : ∀ a, mu a ∈ invariantLawSet (K a) (hK a))
    (kappaMin : ℝ) (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hisolationFloor : ∀ n,
      kappaMin ≤ l1ResidualConorm (K (thetaBar n)))
    (n : ℕ) :
    lawTV (mu (thetaBar n)) (mu (theta n)) ≤
      (2 * eta n / interactionIsolationConorm F probes hprobes) / kappaMin := by
  have hbeta : 0 < interactionIsolationConorm F probes hprobes :=
    (interactionIsolationConorm_pos_iff_pairwiseSeparating F probes hprobes).2 hsep
  have hassembly := assemblyDist_le_two_observationError_div_interactionConorm
    F probes hprobes hsep (observed n) (hobserved n) (eta n)
    (hobs n).1 (hobs n).2
  have hrow : ∀ x,
      crossRowTV (K (thetaBar n)) (hK (thetaBar n))
        (K (theta n)) (hK (theta n)) x ≤
          2 * eta n / interactionIsolationConorm F probes hprobes := by
    intro x
    exact (real.rowTV_le_assemblyDist
      (fun a : A => a) K hK (thetaBar n) (theta n) x).trans hassembly
  have hsource : 0 < l1ResidualConorm (K (thetaBar n)) :=
    lt_of_lt_of_le hkappaMin (hisolationFloor n)
  have htrack := suppliedInvariant_tracking
    (K (thetaBar n)) (hK (thetaBar n))
    (K (theta n)) (hK (theta n))
    (mu (thetaBar n)) (mu (theta n))
    (hmu (thetaBar n)) (hmu (theta n))
    (2 * eta n / interactionIsolationConorm F probes hprobes)
    hcard hsource hrow
  have heta0 : 0 ≤ eta n := by
    have hnonneg : 0 ≤ interactionObservationError
        F probes hprobes (observed n) (thetaBar n) := by
      rcases hprobes with ⟨i, hi⟩
      let _ : IsProbabilityMeasure (F.response (thetaBar n) i) :=
        F.probability (thetaBar n) i
      let _ : IsProbabilityMeasure (observed n i) := hobserved n i
      exact (UEOT.V3.TotalVariation.tvDist_nonneg _ _).trans (by
        unfold interactionObservationError
        exact Finset.le_sup'
          (fun j : I => (UEOT.V3.TotalVariation.tvDist
            (F.response (thetaBar n) j) (observed n j) : ℝ)) hi)
    exact hnonneg.trans (hobs n).1
  have hnum0 : 0 ≤ 2 * eta n / interactionIsolationConorm F probes hprobes :=
    div_nonneg (mul_nonneg (by norm_num) heta0) hbeta.le
  exact htrack.trans
    (div_le_div_of_nonneg_left hnum0 hkappaMin (hisolationFloor n))

/-- **Dynamic interaction exactification.**

Vanishing observational fingerprint radius implies vanishing long-run semantic
TV error when both isolation mechanisms remain uniformly nondegenerate. -/
theorem interactionGenerated_semanticTracking_tendsto_zero
    (F : InteractionResponseFamily A I Y)
    (probes : Finset I) (hprobes : probes.Nonempty)
    (hsep : PairwiseInteractionSeparating F probes)
    (observed : ℕ → I → Measure Y)
    (hobserved : ∀ n i, IsProbabilityMeasure (observed n i))
    (eta : ℕ → ℝ)
    (heta : Tendsto eta atTop (nhds 0))
    (thetaBar theta : ℕ → A)
    (hobs : ∀ n,
      interactionObservationError F probes hprobes (observed n) (thetaBar n) ≤ eta n ∧
      interactionObservationError F probes hprobes (observed n) (theta n) ≤ eta n)
    (K : A → Matrix S S ℝ)
    (hK : ∀ a, K a ∈ Matrix.rowStochastic ℝ S)
    (real : CommonMarkovParentRealization X (fun a : A => a) K hK)
    (mu : A → stdSimplex ℝ S)
    (hmu : ∀ a, mu a ∈ invariantLawSet (K a) (hK a))
    (kappaMin : ℝ) (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hisolationFloor : ∀ n,
      kappaMin ≤ l1ResidualConorm (K (thetaBar n))) :
    Tendsto (fun n => lawTV (mu (thetaBar n)) (mu (theta n)))
      atTop (nhds 0) := by
  have hbeta : 0 < interactionIsolationConorm F probes hprobes :=
    (interactionIsolationConorm_pos_iff_pairwiseSeparating F probes hprobes).2 hsep
  have hdelta : Tendsto
      (fun n => 2 * eta n / interactionIsolationConorm F probes hprobes)
      atTop (nhds 0) := by
    have htwo : Tendsto (fun n => 2 * eta n) atTop (nhds (2 * 0)) :=
      heta.const_mul 2
    simpa using htwo.div_const (interactionIsolationConorm F probes hprobes)
  apply parentSemanticTracking_tendsto_zero
    (fun n => mu (thetaBar n)) (fun n => mu (theta n))
    (fun n => 2 * eta n / interactionIsolationConorm F probes hprobes)
    1 kappaMin hdelta
  intro n
  simpa using interactionGenerated_timeSliceSemanticBound
    F probes hprobes hsep observed hobserved eta thetaBar theta hobs
    K hK real mu hmu kappaMin hkappaMin hcard hisolationFloor n

end

end UEOT.V3.Compression.CrossTrack
