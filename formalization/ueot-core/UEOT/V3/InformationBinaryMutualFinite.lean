import UEOT.V3.InformationBinaryMutualEntropy

/-!
# Finiteness of binary-output mutual information

For any probability law on `X × Fin 2`, the mutual information is finite.
This avoids any need to assume measurability of a parameterized kernel-KL
function in the later conditional lift.  Boundary binary marginals force
independence; an interior marginal reduces the posterior KL to the explicit
integrable nonnegative real binary-KL integrand.
-/

namespace UEOT.V3.InformationBinaryMutualFinite

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationBinaryPosterior
open UEOT.V3.InformationFin2KL
open UEOT.V3.InformationBinaryMutualEntropy

universe uX

variable {X : Type uX} [MeasurableSpace X]
variable [StandardBorelSpace X] [Nonempty X]

/-- Mutual information with a binary second coordinate is always finite. -/
theorem mutualInfo_ne_top_binary
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    mutualInfo ρ ≠ ⊤ := by
  by_cases hq0 : binaryMarginalOneProb ρ = 0
  · have heq : ρ.condKernel =ᵐ[ρ.fst] Kernel.const X ρ.snd := by
      filter_upwards [condKernel_ac_snd_ae ρ] with x hx
      apply (InformationTheory.klDiv_eq_zero_iff).mp
      exact fin2_klDiv_eq_zero_of_reference_zero
        (ρ.condKernel x) ρ.snd hx hq0
    have hprod : ρ = ρ.fst.prod ρ.snd := by
      calc
        ρ = ρ.fst ⊗ₘ ρ.condKernel :=
          (Measure.disintegrate ρ ρ.condKernel).symm
        _ = ρ.fst ⊗ₘ Kernel.const X ρ.snd := Measure.compProd_congr heq
        _ = ρ.fst.prod ρ.snd := Measure.compProd_const
    have hmi : mutualInfo ρ = 0 := by
      unfold mutualInfo
      exact (InformationTheory.klDiv_eq_zero_iff).2 hprod
    rw [hmi]
    simp
  · by_cases hq1 : binaryMarginalOneProb ρ = 1
    · have heq : ρ.condKernel =ᵐ[ρ.fst] Kernel.const X ρ.snd := by
        filter_upwards [condKernel_ac_snd_ae ρ] with x hx
        apply (InformationTheory.klDiv_eq_zero_iff).mp
        exact fin2_klDiv_eq_zero_of_reference_one
          (ρ.condKernel x) ρ.snd hx hq1
      have hprod : ρ = ρ.fst.prod ρ.snd := by
        calc
          ρ = ρ.fst ⊗ₘ ρ.condKernel :=
            (Measure.disintegrate ρ ρ.condKernel).symm
          _ = ρ.fst ⊗ₘ Kernel.const X ρ.snd := Measure.compProd_congr heq
          _ = ρ.fst.prod ρ.snd := Measure.compProd_const
      have hmi : mutualInfo ρ = 0 := by
        unfold mutualInfo
        exact (InformationTheory.klDiv_eq_zero_iff).2 hprod
      rw [hmi]
      simp
    · have hq0' : 0 < binaryMarginalOneProb ρ :=
        lt_of_le_of_ne measureReal_nonneg (Ne.symm hq0)
      have hq1' : binaryMarginalOneProb ρ < 1 :=
        lt_of_le_of_ne measureReal_le_one hq1
      have hac := condKernel_ac_snd_ae ρ
      have hkl_ofReal :
          (fun x => klDiv (ρ.condKernel x) ρ.snd) =ᵐ[ρ.fst]
            fun x => ENNReal.ofReal (binaryKLEntropyIntegrand ρ x) := by
        filter_upwards
          [hac, binaryPosteriorKL_toReal_ae_eq_integrand ρ hq0' hq1']
          with x hx hreal
        have hfinite := fin2_klDiv_ne_top_of_ac (ρ.condKernel x) ρ.snd hx
        calc
          klDiv (ρ.condKernel x) ρ.snd =
              ENNReal.ofReal (klDiv (ρ.condKernel x) ρ.snd).toReal := by
            exact (ENNReal.ofReal_toReal hfinite).symm
          _ = ENNReal.ofReal (binaryKLEntropyIntegrand ρ x) := by
            rw [hreal]
      have hg_int := integrable_binaryKLEntropyIntegrand ρ
      have hg_nonneg := binaryKLEntropyIntegrand_nonneg_ae ρ hq0' hq1'
      have hmi_ofReal :
          mutualInfo ρ =
            ENNReal.ofReal
              (∫ x, binaryKLEntropyIntegrand ρ x ∂ρ.fst) := by
        rw [mutualInfo_eq_lintegral_binaryPosteriorKL ρ,
          lintegral_congr_ae hkl_ofReal]
        exact (ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg).symm
      rw [hmi_ofReal]
      exact ENNReal.ofReal_ne_top

end UEOT.V3.InformationBinaryMutualFinite
