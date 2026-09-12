import UEOT.V3.InformationCore
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Right-coordinate deterministic data processing

P-INFO-04 applies a decoder to the observation coordinate of a joint law
`(J,Y)`.  This module is the right-coordinate counterpart of
`InformationStatistic`: the measurable map `(j,y) ↦ (j,d y)` cannot increase
mutual information.
-/

namespace UEOT.V3.InformationRightStatistic

open MeasureTheory InformationTheory
open UEOT.V3.InformationCore

universe uJ uY uD

variable {J : Type uJ} {Y : Type uY} {D : Type uD}
variable [MeasurableSpace J] [MeasurableSpace Y] [MeasurableSpace D]

noncomputable def rightStatisticJoint
    (μ : Measure (J × Y)) (d : Y → D) (hd : Measurable d) :
    Measure (J × D) :=
  μ.map (fun z : J × Y => (z.1, d z.2))

theorem rightStatisticJoint_fst
    (μ : Measure (J × Y)) (d : Y → D) (hd : Measurable d) :
    (rightStatisticJoint μ d hd).fst = μ.fst := by
  unfold rightStatisticJoint
  rw [Measure.fst_map_prodMk₀
    (μ := μ)
    (X := fun z : J × Y => z.1)
    (Y := fun z : J × Y => d z.2)
    (hd.comp measurable_snd).aemeasurable]
  unfold Measure.fst
  rfl

theorem rightStatisticJoint_snd
    (μ : Measure (J × Y)) (d : Y → D) (hd : Measurable d) :
    (rightStatisticJoint μ d hd).snd = μ.snd.map d := by
  unfold rightStatisticJoint
  rw [Measure.snd_map_prodMk₀
    (μ := μ)
    (X := fun z : J × Y => z.1)
    (Y := fun z : J × Y => d z.2)
    measurable_fst.aemeasurable]
  unfold Measure.snd
  rw [Measure.map_map hd measurable_snd]
  rfl

theorem productMarginals_rightStatisticJoint
    (μ : Measure (J × Y)) [SFinite μ]
    (d : Y → D) (hd : Measurable d) :
    (rightStatisticJoint μ d hd).fst.prod
        (rightStatisticJoint μ d hd).snd =
      (μ.fst.prod μ.snd).map (Prod.map id d) := by
  rw [rightStatisticJoint_fst μ d hd, rightStatisticJoint_snd μ d hd]
  simpa using Measure.map_prod_map μ.fst μ.snd measurable_id hd

/-- Deterministic post-processing of the observation coordinate cannot
increase mutual information.  This is the decoder-DPI step of P-INFO-04. -/
theorem mutualInfo_rightStatistic_le
    (μ : Measure (J × Y)) [IsProbabilityMeasure μ]
    (d : Y → D) (hd : Measurable d) :
    mutualInfo (rightStatisticJoint μ d hd) ≤ mutualInfo μ := by
  unfold mutualInfo
  rw [productMarginals_rightStatisticJoint μ d hd]
  exact InformationTheory.klDiv_map_le
    μ (μ.fst.prod μ.snd) (measurable_id.prodMap hd)

end UEOT.V3.InformationRightStatistic
