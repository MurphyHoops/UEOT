import UEOT.V3.Compression.CrossTrack.EndogenousCandidateFormation
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C2IntervalDecision
import Mathlib.Tactic.Ring

/-!
# Scientific Closure C2 — certified formation recovery

The canonical response-defect estimator already has deterministic `2η`
stability.  C2 separates that sampling/estimation radius from a possible drift
radius and feeds the combined interval into the abstaining decision layer.

Exact formed-family recovery is exposed only under the already required explicit
finite separation conditions.  Unknown separation never receives an invented
stopping rule.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.StatisticalDefect
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.Compression.CrossTrack

universe uV uH uI uR uY uChild

variable {V : Type uV} {H : Type uH} {I : Type uI}
variable {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
variable {Child : Type uChild}

/-- Carrier-defect interval with the statistical and drift budgets kept
separate for auditability. -/
noncomputable def carrierDefectCertificate
    (readout : Finset V → H → Rout)
    (pHat : H → I → Measure Y)
    (S : Finset V)
    (eta drift : ℝ)
    (heta : 0 ≤ eta) (hdrift : 0 ≤ drift) : IntervalCertificate where
  estimate := responseDefect readout pHat S
  statisticalRadius := 2 * eta
  driftRadius := drift
  statisticalRadius_nonneg := mul_nonneg (by norm_num) heta
  driftRadius_nonneg := hdrift

/-- Response estimation around a registered reference law plus a separate
reference→deployment drift budget gives the declared C2 interval guarantee. -/
theorem carrierDefect_within_certificate
    [Nonempty H] [Nonempty I]
    (readout : Finset V → H → Rout)
    (pRef pNow pHat : H → I → Measure Y)
    (hpRef : ∀ h i, IsProbabilityMeasure (pRef h i))
    (hpHat : ∀ h i, IsProbabilityMeasure (pHat h i))
    (eta drift : ℝ) (heta : 0 ≤ eta) (hdrift0 : 0 ≤ drift)
    (hresp : ∀ h i, tvDist (pRef h i) (pHat h i) ≤ eta)
    (hdrift : ∀ S,
      |responseDefect readout pRef S - responseDefect readout pNow S| ≤ drift)
    (S : Finset V) :
    |(carrierDefectCertificate readout pHat S eta drift heta hdrift0).estimate -
        responseDefect readout pNow S| ≤
      (carrierDefectCertificate readout pHat S eta drift heta hdrift0).totalRadius := by
  have hest := responseDefect_error
    readout pRef pHat hpRef hpHat eta hresp S
  have htri :
      |responseDefect readout pHat S - responseDefect readout pNow S| ≤
        |responseDefect readout pHat S - responseDefect readout pRef S| +
        |responseDefect readout pRef S - responseDefect readout pNow S| :=
    abs_sub_le _ _ _
  exact htri.trans (add_le_add hest (hdrift S))

/-- Certified-carrier soundness: if the upper endpoint is below the registered
carrier tolerance, then the deployed true defect is below that tolerance on the
good event. -/
theorem carrier_certified_sound
    (C : IntervalCertificate) (truth tolerance : ℝ)
    (hgood : |C.estimate - truth| ≤ C.totalRadius)
    (hdecision : decideAt C tolerance = CertificationDecision.certified) :
    truth ≤ tolerance :=
  decideAt_certified_sound C tolerance truth hgood hdecision

/-- Rejection is equally one-sided sound. -/
theorem carrier_rejected_sound
    (C : IntervalCertificate) (truth tolerance : ℝ)
    (hgood : |C.estimate - truth| ≤ C.totalRadius)
    (hdecision : decideAt C tolerance = CertificationDecision.rejected) :
    tolerance < truth :=
  decideAt_rejected_sound C tolerance truth hgood hdecision

/-- **C2-05 exact endpoint under explicit known margins.**

When the stronger known-gap hypotheses of the existing response-recovery theorem
are actually supplied, exact carrier recovery transports exactly to the formed
candidate family.  This theorem is intentionally separate from the abstaining
unknown-gap path above. -/
theorem formedFamily_exact_of_registeredGap
    [Fintype V] [DecidableEq V]
    [Fintype H] [Nonempty H]
    [Fintype I] [Nonempty I]
    [Fintype Child]
    (readout : Finset V → H → Rout)
    (p pHat : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ h i, IsProbabilityMeasure (pHat h i))
    (regions : Child → Finset V)
    (eta gamma Delta tau : ℝ)
    (hresp : ∀ h i, tvDist (p h i) (pHat h i) ≤ eta)
    (hsep : ∀ h h',
      ¬UEOT.V3.PredictiveClassRecovery.trueEquivalent p h h' →
        gamma ≤ UEOT.V3.PredictiveClassRecovery.protocolDistance p h h')
    (hpredGap : 2 * eta < gamma / 2)
    (hcarrierGap : ∀ S,
      0 < responseDefect readout p S → Delta ≤ responseDefect readout p S)
    (hlower : 2 * eta < tau)
    (hupper : tau < Delta - 2 * eta) :
    estimatedResponseFormedCandidateFamily readout pHat tau regions =
      responseFormedCandidateFamily readout p regions := by
  exact responseFormedCandidateFamily_recovery_on_good_event
    readout p pHat hp hpHat regions eta gamma Delta tau hresp hsep
    hpredGap hcarrierGap hlower hupper

/-- Unknown-gap C2 never derives exact formed-family equality merely from an
interval estimate.  Instead every registered carrier receives a ternary
certificate decision. -/
noncomputable def carrierDecision
    (readout : Finset V → H → Rout)
    (pHat : H → I → Measure Y)
    (S : Finset V)
    (eta drift tolerance : ℝ)
    (heta : 0 ≤ eta) (hdrift : 0 ≤ drift) : CertificationDecision :=
  decideAt (carrierDefectCertificate readout pHat S eta drift heta hdrift)
    tolerance

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure
