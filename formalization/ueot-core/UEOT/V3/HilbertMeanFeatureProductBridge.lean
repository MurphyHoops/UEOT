import Mathlib.MeasureTheory.Constructions.Pi

/-!
# P-STAT-06 — common-sample feature product bridge

This module isolates the measure-transport step needed for simultaneous RKHS
control on one raw sample space. A measurable feature map is applied coordinatewise
to an `N`-sample product law; the resulting map is measure preserving onto the
product of the pushed-forward coordinate laws.
-/

namespace UEOT.V3.HilbertMeanFeatureProductBridge

open MeasureTheory

universe uY uH

variable {Y : Type uY} {H : Type uH}
variable [MeasurableSpace Y] [MeasurableSpace H]

/-- Applying one measurable feature map coordinatewise to a finite product sample
is measure preserving onto the product of the pushed-forward marginals. -/
theorem measurePreserving_featureProduct
    {N : ℕ}
    (ν : Fin N → Measure Y)
    (φ : Y → H)
    (hφ : Measurable φ)
    [∀ i, SigmaFinite ((ν i).map φ)] :
    MeasurePreserving
      (fun y : Fin N → Y => fun i => φ (y i))
      (Measure.pi ν)
      (Measure.pi (fun i => (ν i).map φ)) := by
  exact measurePreserving_pi ν (fun i => (ν i).map φ)
    (fun i => hφ.measurePreserving (ν i))

end UEOT.V3.HilbertMeanFeatureProductBridge
