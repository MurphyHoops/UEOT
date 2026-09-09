import UEOT.V3.InformationCore
import Mathlib.MeasureTheory.Measure.Prod

/-!
# P-INFO-01 foundation — deterministic statistic data processing

For a joint law of (H,Y), a measurable deterministic statistic M=f(H)
pushes the joint law through (f,id). Mutual information is the KL divergence
from the joint law to the product of its marginals, so Mathlib's KL data
processing gives I(M;Y) <= I(H;Y) once the pushed product-marginal law is
identified exactly.

This is a general measurable-space theorem. The P-INFO-01 chain-rule equality
and conditional-information residual are separate next-layer obligations.
-/

namespace UEOT.V3.InformationStatistic

open MeasureTheory InformationTheory
open UEOT.V3.InformationCore

universe uH uM uY

variable {H : Type uH} {M : Type uM} {Y : Type uY}
variable [MeasurableSpace H] [MeasurableSpace M] [MeasurableSpace Y]

noncomputable def statisticJoint
    (μ : Measure (H × Y)) (f : H → M) (hf : Measurable f) :
    Measure (M × Y) :=
  μ.map (fun z : H × Y => (f z.1, z.2))

theorem statisticJoint_fst
    (μ : Measure (H × Y)) (f : H → M) (hf : Measurable f) :
    (statisticJoint μ f hf).fst = μ.fst.map f := by
  unfold statisticJoint
  rw [Measure.fst_map_prodMk₀
    (μ := μ)
    (X := fun z : H × Y => f z.1)
    (Y := fun z : H × Y => z.2)
    (hf.comp measurable_fst).aemeasurable
    measurable_snd.aemeasurable]
  rw [Measure.map_map hf measurable_fst]

theorem statisticJoint_snd
    (μ : Measure (H × Y)) (f : H → M) (hf : Measurable f) :
    (statisticJoint μ f hf).snd = μ.snd := by
  unfold statisticJoint
  rw [Measure.snd_map_prodMk₀
    (μ := μ)
    (X := fun z : H × Y => f z.1)
    (Y := fun z : H × Y => z.2)
    (hf.comp measurable_fst).aemeasurable
    measurable_snd.aemeasurable]
  simp

theorem productMarginals_statisticJoint
    (μ : Measure (H × Y)) [SFinite μ]
    (f : H → M) (hf : Measurable f) :
    (statisticJoint μ f hf).fst.prod (statisticJoint μ f hf).snd =
      (μ.fst.prod μ.snd).map (Prod.map f id) := by
  rw [statisticJoint_fst μ f hf, statisticJoint_snd μ f hf]
  simpa using Measure.map_prod_map μ.fst μ.snd hf measurable_id

/-- Deterministic statistics cannot increase mutual information with Y. -/
theorem mutualInfo_statistic_le
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → M) (hf : Measurable f) :
    mutualInfo (statisticJoint μ f hf) ≤ mutualInfo μ := by
  unfold mutualInfo
  rw [productMarginals_statisticJoint μ f hf]
  exact InformationTheory.klDiv_map_le
    μ (μ.fst.prod μ.snd) (hf.prodMap measurable_id)

end UEOT.V3.InformationStatistic
