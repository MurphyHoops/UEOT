import UEOT.V3.InformationPredictiveFactorization

/-!
# P-INT-01 — canonical predictive-factorization witness

An arbitrary factorization witness `q : Kernel Z Y` is only defined up to the
`P_Z`-almost-sure ambiguity of regular conditional probabilities.  For the
factorization/conditional-independence equivalence it is cleaner to replace it
by the canonical Mathlib version `condDistrib Y Z` and prove that the original
history-conditional kernel still factors through that canonical version.
-/

namespace UEOT.V3.InformationPredictiveFactorization

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe uH uY uZ

variable {H : Type uH} {Y : Type uY} {Z : Type uZ}
variable [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
variable [StandardBorelSpace H] [StandardBorelSpace Y]
variable [Nonempty Y]

/-- The law of `z(H)` obtained from the joint law equals the pushforward of the
history marginal. -/
theorem statisticVar_map_eq_fst_map
    (μ : Measure (H × Y))
    (z : H → Z) (hz : Measurable z) :
    μ.map (statisticVar (Y := Y) z) = μ.fst.map z := by
  unfold statisticVar Measure.fst
  exact (Measure.map_map hz measurable_fst).symm

/-- Every predictive-factorization witness can be replaced by the actual
regular conditional kernel `P(Y|z(H))` without losing the factorization of
`P(Y|H)`.  This removes all arbitrary-version choices before proving the final
conditional-independence equivalence. -/
theorem canonicalFactorization_of_factorization
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (z : H → Z) (hz : Measurable z)
    (hfac : PredictiveFactorization μ z hz) :
    μ.condKernel =ᵐ[μ.fst]
      (condDistrib
        (futureVar (H := H) (Y := Y))
        (statisticVar (Y := Y) z) μ).comap z hz := by
  rcases hfac with ⟨q, hqMarkov, hfacq⟩
  letI : IsMarkovKernel q := hqMarkov
  have hq :
      condDistrib
          (futureVar (H := H) (Y := Y))
          (statisticVar (Y := Y) z) μ
        =ᵐ[μ.map (statisticVar (Y := Y) z)] q :=
    condDistrib_future_statistic_ae_eq_of_factorization μ z hz q hfacq
  have hmap := statisticVar_map_eq_fst_map (Y := Y) μ z hz
  rw [hmap] at hq
  have hpull :
      ∀ᵐ h ∂μ.fst,
        condDistrib
            (futureVar (H := H) (Y := Y))
            (statisticVar (Y := Y) z) μ (z h) = q (z h) :=
    ae_of_ae_map hz.aemeasurable hq
  filter_upwards [hfacq, hpull] with h hh hpull_h
  have hh' : μ.condKernel h = q (z h) := by
    simpa [Kernel.comap_apply] using hh
  exact hh'.trans hpull_h.symm

end

end UEOT.V3.InformationPredictiveFactorization
