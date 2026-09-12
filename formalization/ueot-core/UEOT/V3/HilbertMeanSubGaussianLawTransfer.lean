import UEOT.V3.HilbertMeanPastActiveIndependence
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# P-STAT-06 — transport of sub-Gaussianity through an exact law

If a random variable `X` has law `ν` under `P`, then every scalar statistic
`g ∘ X` has exactly the same MGF under `P` as `g` has under `ν`.  Hence
ordinary sub-Gaussianity transports without any loss in the proxy constant.
-/

namespace UEOT.V3.HilbertMeanSubGaussianLawTransfer

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

universe uΩ uX

variable {Ω : Type uΩ} {𝓧 : Type uX}
variable [MeasurableSpace Ω] [MeasurableSpace 𝓧]
variable {P : Measure Ω} {ν : Measure 𝓧}
variable {X : Ω → 𝓧} {g : 𝓧 → ℝ} {c : ℝ≥0}

/-- Ordinary sub-Gaussianity is invariant under exact transport of law. -/
theorem HasSubgaussianMGF.comp_hasLaw
    (hsg : HasSubgaussianMGF g c ν)
    (hX : HasLaw X ν P) :
    HasSubgaussianMGF (fun ω => g (X ω)) c P := by
  constructor
  · intro t
    have hν := hsg.integrable_exp_mul t
    have hmap : Integrable (fun x => exp (t * g x)) (Measure.map X P) := by
      simpa [hX.map_eq] using hν
    exact (integrable_map_measure hmap.1 hX.aemeasurable).1 hmap
  · intro t
    have hν := hsg.integrable_exp_mul t
    have hint := hX.integral_comp hν.1
    have hmgf :
        mgf (fun ω => g (X ω)) P t = mgf g ν t := by
      simpa [mgf, Function.comp_def] using hint
    rw [hmgf]
    exact hsg.mgf_le t

/-- Ordinary sub-Gaussianity is invariant under almost-everywhere equality. -/
theorem HasSubgaussianMGF.congr_ae
    {Y Z : Ω → ℝ}
    (hsg : HasSubgaussianMGF Y c P)
    (hYZ : Y =ᵐ[P] Z) :
    HasSubgaussianMGF Z c P := by
  constructor
  · intro t
    refine (integrable_congr ?_).mpr (hsg.integrable_exp_mul t)
    filter_upwards [hYZ] with ω hω
    rw [hω]
  · intro t
    rw [mgf_congr (Filter.EventuallyEq.symm hYZ)]
    exact hsg.mgf_le t

end UEOT.V3.HilbertMeanSubGaussianLawTransfer
