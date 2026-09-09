import UEOT.V3.InformationCore
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
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
    measurable_snd.aemeasurable]
  unfold Measure.fst
  rw [Measure.map_map hf measurable_fst]
  rfl

theorem statisticJoint_snd
    (μ : Measure (H × Y)) (f : H → M) (hf : Measurable f) :
    (statisticJoint μ f hf).snd = μ.snd := by
  unfold statisticJoint
  rw [Measure.snd_map_prodMk₀
    (μ := μ)
    (X := fun z : H × Y => f z.1)
    (Y := fun z : H × Y => z.2)
    (hf.comp measurable_fst).aemeasurable]
  unfold Measure.snd
  rfl

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


/-- KL divergence is preserved by a measurable map that admits a measurable
left inverse.  This is the exact reversible-embedding bridge used below to
carry the deterministic statistic M=f(H) as an explicit coordinate without
changing information. -/
theorem klDiv_map_eq_of_measurable_leftInverse
    {A : Type*} {B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : A → B) (g : B → A)
    (hf : Measurable f) (hg : Measurable g)
    (hleft : Function.LeftInverse g f) :
    InformationTheory.klDiv (μ.map f) (ν.map f) =
      InformationTheory.klDiv μ ν := by
  apply le_antisymm
  · exact InformationTheory.klDiv_map_le μ ν hf
  · have hback :=
      InformationTheory.klDiv_map_le (μ.map f) (ν.map f) hg
    have hμ :
        (μ.map f).map g = μ := by
      rw [Measure.map_map hg hf]
      have hgf : g ∘ f = id := by
        funext x
        exact hleft x
      rw [hgf, Measure.map_id]
    have hν :
        (ν.map f).map g = ν := by
      rw [Measure.map_map hg hf]
      have hgf : g ∘ f = id := by
        funext x
        exact hleft x
      rw [hgf, Measure.map_id]
    simpa [hμ, hν] using hback

/-- Lift a sample (H,Y) to ((M,Y),H), retaining the original history while
making the deterministic statistic M=f(H) part of the leading coordinate. -/
def statisticLift {H : Type*} {Y : Type*} {M : Type*}
    (f : H → M) : H × Y → (M × Y) × H :=
  fun p => ((f p.1, p.2), p.1)

/-- Measurable left inverse of statisticLift: forget the redundant statistic
coordinate. -/
def statisticForget {H : Type*} {Y : Type*} {M : Type*} :
    (M × Y) × H → H × Y :=
  fun p => (p.2, p.1.2)

theorem measurable_statisticLift
    {H : Type*} {Y : Type*} {M : Type*}
    [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace M]
    (f : H → M) (hf : Measurable f) :
    Measurable (statisticLift (Y := Y) f) := by
  unfold statisticLift
  exact ((hf.comp measurable_fst).prodMk measurable_snd).prodMk measurable_fst

theorem measurable_statisticForget
    {H : Type*} {Y : Type*} {M : Type*}
    [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace M] :
    Measurable (statisticForget (H := H) (Y := Y) (M := M)) := by
  unfold statisticForget
  exact measurable_snd.prodMk (measurable_snd.comp measurable_fst)

theorem statisticForget_leftInverse
    {H : Type*} {Y : Type*} {M : Type*}
    (f : H → M) :
    Function.LeftInverse
      (statisticForget (H := H) (Y := Y) (M := M))
      (statisticLift (Y := Y) f) := by
  intro p
  rfl

/-- Adding the deterministic statistic coordinate to a joint law preserves
its KL information against any finite reference law. -/
theorem klDiv_statisticLift_eq
    {H : Type*} {Y : Type*} {M : Type*}
    [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace M]
    (μ ν : Measure (H × Y))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : H → M) (hf : Measurable f) :
    InformationTheory.klDiv
        (μ.map (statisticLift (Y := Y) f))
        (ν.map (statisticLift (Y := Y) f)) =
      InformationTheory.klDiv μ ν :=
  klDiv_map_eq_of_measurable_leftInverse μ ν
    (statisticLift (Y := Y) f)
    (statisticForget (H := H) (Y := Y) (M := M))
    (measurable_statisticLift f hf)
    measurable_statisticForget
    (statisticForget_leftInverse f)

end UEOT.V3.InformationStatistic
