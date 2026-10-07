import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.CarrierConsistency
import UEOT.V3.Compression.CrossTrack.EndogenousCandidateFormation

/-!
# P4.2 — candidate-universe consistency

P3 already proves that one finite response estimator with vanishing uniform TV
error eventually recovers, from the **same** response table,

* the true predictive equivalence relation;
* the exact minimal physical carrier family; and
* its blocker.

Track X already proves that exact carrier-family recovery pushes through the
P-COMP-06 child-coalition construction to recover the response-generated formed
candidate family.  P4 therefore adds only the missing thin composition: the
finite inverse-object candidate universe is eventually exact with no second
coalition-matching hypothesis and no external predictive/carrier gap.

This theorem recovers a candidate universe, not yet one unique Objecthood
candidate.  Interaction evidence, validity gates and object-class semantics are
separate P4 obligations.
-/

namespace UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

open Filter Topology MeasureTheory
open UEOT.V3
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.StatisticalDefect
open UEOT.V3.TotalVariation
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

universe uV uH uI uR uY uChild

/-- P3 response consistency plus the existing Track-X formation map eventually
recovers the predictive relation, the full response-generated formed-candidate
universe, and the exact blocker simultaneously. -/
theorem eventually_canonical_candidateUniverse_recovery
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Fintype H] [Nonempty H]
    {I : Type uI} [Fintype I] [Nonempty I]
    {Rout : Type uR}
    {Y : Type uY} [MeasurableSpace Y]
    {Child : Type uChild}
    (readout : Finset V → H → Rout)
    (p : H → I → Measure Y)
    (pHat : ℕ → H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ n h i, IsProbabilityMeasure (pHat n h i))
    (regions : Child → Finset V)
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (hresp : ∀ n h i, tvDist (p h i) (pHat n h i) ≤ eta n) :
    let gamma := canonicalPredictiveGap p
    let Delta := canonicalPositiveDefectGap (responseDefect readout p)
    ∀ᶠ n in atTop,
      (∀ h h',
        UEOT.V3.PredictiveClassRecovery.protocolDistance (pHat n) h h' ≤ gamma / 2 ↔
          UEOT.V3.PredictiveClassRecovery.trueEquivalent p h h') ∧
      estimatedResponseFormedCandidateFamily
          readout (pHat n) (Delta / 2) regions =
        responseFormedCandidateFamily readout p regions ∧
      UEOT.Blocker.blocker
          (estimatedCarrierFamily readout (pHat n) (Delta / 2)) =
        UEOT.Blocker.blocker (exactCarrierFamily readout p) := by
  dsimp only
  let gamma := canonicalPredictiveGap p
  let Delta := canonicalPositiveDefectGap (responseDefect readout p)
  have hrec := eventually_canonical_response_recovery
    readout p pHat hp hpHat eta heta hresp
  filter_upwards [hrec] with n hn
  refine ⟨hn.1, ?_, hn.2.2⟩
  exact estimatedResponseFormedCandidateFamily_eq_true
    readout p (pHat n) regions (Delta / 2) hn.2.1

/-- Candidate-universe exactification alone, exposed as a smaller endpoint for
later inverse-selection theorems. -/
theorem eventually_exact_responseFormedCandidateFamily
    {V : Type uV} [Fintype V] [DecidableEq V]
    {H : Type uH} [Fintype H] [Nonempty H]
    {I : Type uI} [Fintype I] [Nonempty I]
    {Rout : Type uR}
    {Y : Type uY} [MeasurableSpace Y]
    {Child : Type uChild}
    (readout : Finset V → H → Rout)
    (p : H → I → Measure Y)
    (pHat : ℕ → H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ n h i, IsProbabilityMeasure (pHat n h i))
    (regions : Child → Finset V)
    (eta : ℕ → ℝ) (heta : Tendsto eta atTop (𝓝 0))
    (hresp : ∀ n h i, tvDist (p h i) (pHat n h i) ≤ eta n) :
    let Delta := canonicalPositiveDefectGap (responseDefect readout p)
    ∀ᶠ n in atTop,
      estimatedResponseFormedCandidateFamily
          readout (pHat n) (Delta / 2) regions =
        responseFormedCandidateFamily readout p regions := by
  dsimp only
  let Delta := canonicalPositiveDefectGap (responseDefect readout p)
  have hall := eventually_canonical_candidateUniverse_recovery
    readout p pHat hp hpHat regions eta heta hresp
  filter_upwards [hall] with n hn
  exact hn.2.1

end UEOT.V3.Compression.TheoryCompletion.InverseObjecthood
