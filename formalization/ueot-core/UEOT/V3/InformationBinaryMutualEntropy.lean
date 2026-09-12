import UEOT.V3.InformationCore
import UEOT.V3.InformationKernelKL
import UEOT.V3.InformationBinaryPosterior
import UEOT.V3.InformationFin2KL
import UEOT.V3.InformationBinaryConditionalMean
import UEOT.V3.InformationBinaryEntropy
import UEOT.V3.InformationBinaryKLEntropy
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary mutual information = entropy drop

For a probability law on `X × Fin 2`, this module proves the exact identity

`I(X;B) = H(B) - H(B|X)`

in the repository's KL semantics.  The proof is measure-theoretic: disintegrate
the joint law, use posterior absolute continuity, evaluate each two-point KL,
and use the posterior-mean identity to cancel the cross-entropy terms.
-/

namespace UEOT.V3.InformationBinaryMutualEntropy

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationCore
open UEOT.V3.InformationKernelKL
open UEOT.V3.InformationBinaryPosterior
open UEOT.V3.InformationFin2KL
open UEOT.V3.InformationBinaryConditionalMean
open UEOT.V3.InformationBinaryEntropy
open UEOT.V3.InformationBinaryKLEntropy

universe uX

variable {X : Type uX} [MeasurableSpace X]
variable [StandardBorelSpace X] [Nonempty X]

/-- Marginal success probability `P(B=1)`. -/
noncomputable def binaryMarginalOneProb
    (ρ : Measure (X × Fin 2)) : ℝ :=
  ρ.snd.real ({1} : Set (Fin 2))

/-- Real integrand obtained from a binary posterior KL against the fixed
marginal in the interior case. -/
noncomputable def binaryKLEntropyIntegrand
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ]
    (x : X) : ℝ :=
  -Real.binEntropy (posteriorBitOneProb ρ x) -
    posteriorBitOneProb ρ x * Real.log (binaryMarginalOneProb ρ) -
    (1 - posteriorBitOneProb ρ x) *
      Real.log (1 - binaryMarginalOneProb ρ)

/-- Mutual information is the average KL from the binary posterior to the
binary marginal. -/
theorem mutualInfo_eq_lintegral_binaryPosteriorKL
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    mutualInfo ρ =
      ∫⁻ x, klDiv (ρ.condKernel x) ρ.snd ∂ρ.fst := by
  have hdis : ρ.fst ⊗ₘ ρ.condKernel = ρ :=
    Measure.disintegrate ρ ρ.condKernel
  have hconst :
      ρ.fst ⊗ₘ Kernel.const X ρ.snd = ρ.fst.prod ρ.snd :=
    Measure.compProd_const
  have hac :
      ∀ᵐ x ∂ρ.fst, ρ.condKernel x ≪ (Kernel.const X ρ.snd) x := by
    simpa using condKernel_ac_snd_ae ρ
  unfold mutualInfo
  calc
    klDiv ρ (ρ.fst.prod ρ.snd) =
        klDiv (ρ.fst ⊗ₘ ρ.condKernel)
          (ρ.fst ⊗ₘ Kernel.const X ρ.snd) := by
      rw [hdis, hconst]
    _ = ∫⁻ x, klDiv (ρ.condKernel x) ((Kernel.const X ρ.snd) x) ∂ρ.fst :=
      klDiv_compProd_right_eq_lintegral
        (μ := ρ.fst) (κ := ρ.condKernel)
        (η := Kernel.const X ρ.snd) hac
    _ = ∫⁻ x, klDiv (ρ.condKernel x) ρ.snd ∂ρ.fst := by
      simp

/-- In the interior marginal case, each fiber KL has the explicit
entropy/cross-entropy real form. -/
theorem binaryPosteriorKL_toReal_ae_eq_integrand
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ]
    (hq0 : 0 < binaryMarginalOneProb ρ)
    (hq1 : binaryMarginalOneProb ρ < 1) :
    (fun x => (klDiv (ρ.condKernel x) ρ.snd).toReal) =ᵐ[ρ.fst]
      binaryKLEntropyIntegrand ρ := by
  filter_upwards [condKernel_ac_snd_ae ρ] with x hx
  have hscalar := fin2_klDiv_toReal_of_ac (ρ.condKernel x) ρ.snd hx
  have halg := binaryKLScalar_eq_negEntropy_cross
    (posteriorBitOneProb ρ x) (binaryMarginalOneProb ρ)
    measureReal_nonneg measureReal_le_one hq0 hq1
  calc
    (klDiv (ρ.condKernel x) ρ.snd).toReal =
        (ρ.condKernel x).real ({1} : Set (Fin 2)) *
            Real.log ((ρ.condKernel x).real ({1} : Set (Fin 2)) /
              ρ.snd.real ({1} : Set (Fin 2))) +
          (1 - (ρ.condKernel x).real ({1} : Set (Fin 2))) *
            Real.log ((1 - (ρ.condKernel x).real ({1} : Set (Fin 2))) /
              (1 - ρ.snd.real ({1} : Set (Fin 2)))) := hscalar
    _ = binaryKLEntropyIntegrand ρ x := by
      simpa [posteriorBitOneProb, binaryMarginalOneProb,
        binaryKLEntropyIntegrand] using halg

/-- The explicit interior KL integrand is integrable. -/
theorem integrable_binaryKLEntropyIntegrand
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    Integrable (binaryKLEntropyIntegrand ρ) ρ.fst := by
  have hp_meas : Measurable (posteriorBitOneProb ρ) :=
    measurable_posteriorBitOneProb ρ
  have hp_int : Integrable (posteriorBitOneProb ρ) ρ.fst := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hp_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have hp0 : 0 ≤ posteriorBitOneProb ρ x := measureReal_nonneg
    have hp1 : posteriorBitOneProb ρ x ≤ 1 := measureReal_le_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hp0] using hp1
  have h1p_int : Integrable (fun x => 1 - posteriorBitOneProb ρ x) ρ.fst :=
    (integrable_const (1 : ℝ)).sub hp_int
  have hH_int := integrable_binEntropy_posteriorBitOneProb ρ
  unfold binaryKLEntropyIntegrand
  exact (hH_int.neg.sub (hp_int.mul_const _)).sub (h1p_int.mul_const _)

/-- The interior KL integrand is nonnegative almost everywhere because it is
the real value of an actual KL divergence. -/
theorem binaryKLEntropyIntegrand_nonneg_ae
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ]
    (hq0 : 0 < binaryMarginalOneProb ρ)
    (hq1 : binaryMarginalOneProb ρ < 1) :
    0 ≤ᵐ[ρ.fst] binaryKLEntropyIntegrand ρ := by
  filter_upwards [binaryPosteriorKL_toReal_ae_eq_integrand ρ hq0 hq1] with x hx
  rw [← hx]
  exact ENNReal.toReal_nonneg

/-- Integrating the explicit binary KL formula cancels the cross-entropy terms
through `E[P(B=1|X)] = P(B=1)`. -/
theorem integral_binaryKLEntropyIntegrand_eq_entropy_drop
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    ∫ x, binaryKLEntropyIntegrand ρ x ∂ρ.fst =
      Real.binEntropy (binaryMarginalOneProb ρ) -
        ∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst := by
  have hp_meas : Measurable (posteriorBitOneProb ρ) :=
    measurable_posteriorBitOneProb ρ
  have hp_int : Integrable (posteriorBitOneProb ρ) ρ.fst := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hp_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    have hp0 : 0 ≤ posteriorBitOneProb ρ x := measureReal_nonneg
    have hp1 : posteriorBitOneProb ρ x ≤ 1 := measureReal_le_one
    simpa [Real.norm_eq_abs, abs_of_nonneg hp0] using hp1
  have h1p_int : Integrable (fun x => 1 - posteriorBitOneProb ρ x) ρ.fst :=
    (integrable_const (1 : ℝ)).sub hp_int
  have hH_int := integrable_binEntropy_posteriorBitOneProb ρ
  have hpmean' :
      (∫ x, posteriorBitOneProb ρ x ∂ρ.fst) =
        binaryMarginalOneProb ρ := by
    simpa [binaryMarginalOneProb] using
      (integral_posteriorBitOneProb_eq_marginal ρ)
  have h1pmean :
      (∫ x, (1 - posteriorBitOneProb ρ x) ∂ρ.fst) =
        1 - binaryMarginalOneProb ρ := by
    rw [integral_sub (integrable_const (1 : ℝ)) hp_int]
    simp [hpmean']
  have hinner :
      (∫ x,
          -Real.binEntropy (posteriorBitOneProb ρ x) -
            posteriorBitOneProb ρ x * Real.log (binaryMarginalOneProb ρ)
          ∂ρ.fst) =
        (∫ x, -Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst) -
          ∫ x, posteriorBitOneProb ρ x *
            Real.log (binaryMarginalOneProb ρ) ∂ρ.fst := by
    exact integral_sub hH_int.neg (hp_int.mul_const _)
  unfold binaryKLEntropyIntegrand
  calc
    (∫ x,
        (-Real.binEntropy (posteriorBitOneProb ρ x) -
          posteriorBitOneProb ρ x * Real.log (binaryMarginalOneProb ρ)) -
          (1 - posteriorBitOneProb ρ x) *
            Real.log (1 - binaryMarginalOneProb ρ) ∂ρ.fst) =
        (∫ x,
            -Real.binEntropy (posteriorBitOneProb ρ x) -
              posteriorBitOneProb ρ x * Real.log (binaryMarginalOneProb ρ) ∂ρ.fst) -
          ∫ x,
            (1 - posteriorBitOneProb ρ x) *
              Real.log (1 - binaryMarginalOneProb ρ) ∂ρ.fst := by
      exact integral_sub
        (hH_int.neg.sub (hp_int.mul_const _)) (h1p_int.mul_const _)
    _ =
        ((∫ x, -Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst) -
          ∫ x, posteriorBitOneProb ρ x *
            Real.log (binaryMarginalOneProb ρ) ∂ρ.fst) -
          ∫ x, (1 - posteriorBitOneProb ρ x) *
            Real.log (1 - binaryMarginalOneProb ρ) ∂ρ.fst := by
      exact congrArg
        (fun t : ℝ => t -
          ∫ x, (1 - posteriorBitOneProb ρ x) *
            Real.log (1 - binaryMarginalOneProb ρ) ∂ρ.fst) hinner
    _ =
        (-(∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst) -
          binaryMarginalOneProb ρ * Real.log (binaryMarginalOneProb ρ)) -
          (1 - binaryMarginalOneProb ρ) *
            Real.log (1 - binaryMarginalOneProb ρ) := by
      rw [integral_neg, integral_mul_const, integral_mul_const, hpmean', h1pmean]
    _ = Real.binEntropy (binaryMarginalOneProb ρ) -
          ∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst := by
      unfold binaryMarginalOneProb
      rw [Real.binEntropy, Real.log_inv, Real.log_inv]
      ring

/-- Interior-marginal binary mutual information is exactly the binary entropy
drop from the marginal to the posterior. -/
theorem mutualInfo_toReal_eq_entropy_drop_of_interior
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ]
    (hq0 : 0 < binaryMarginalOneProb ρ)
    (hq1 : binaryMarginalOneProb ρ < 1) :
    (mutualInfo ρ).toReal =
      Real.binEntropy (binaryMarginalOneProb ρ) -
        ∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst := by
  have hac := condKernel_ac_snd_ae ρ
  have hkl_ofReal :
      (fun x => klDiv (ρ.condKernel x) ρ.snd) =ᵐ[ρ.fst]
        fun x => ENNReal.ofReal (binaryKLEntropyIntegrand ρ x) := by
    filter_upwards [hac, binaryPosteriorKL_toReal_ae_eq_integrand ρ hq0 hq1]
      with x hx hreal
    have hfinite := fin2_klDiv_ne_top_of_ac (ρ.condKernel x) ρ.snd hx
    calc
      klDiv (ρ.condKernel x) ρ.snd =
          ENNReal.ofReal (klDiv (ρ.condKernel x) ρ.snd).toReal := by
            exact (ENNReal.ofReal_toReal hfinite).symm
      _ = ENNReal.ofReal (binaryKLEntropyIntegrand ρ x) := by rw [hreal]
  have hg_int := integrable_binaryKLEntropyIntegrand ρ
  have hg_nonneg := binaryKLEntropyIntegrand_nonneg_ae ρ hq0 hq1
  rw [mutualInfo_eq_lintegral_binaryPosteriorKL ρ,
    lintegral_congr_ae hkl_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg]
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hg_nonneg)]
  exact integral_binaryKLEntropyIntegrand_eq_entropy_drop ρ

/-- Degenerate marginal `P(B=1)=0` forces independence and zero posterior
binary entropy. -/
theorem mutualInfo_toReal_eq_entropy_drop_of_marginal_zero
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ]
    (hq0 : binaryMarginalOneProb ρ = 0) :
    (mutualInfo ρ).toReal =
      Real.binEntropy (binaryMarginalOneProb ρ) -
        ∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst := by
  have hp0 : posteriorBitOneProb ρ =ᵐ[ρ.fst] fun _ => (0 : ℝ) := by
    filter_upwards [condKernel_ac_snd_ae ρ] with x hx
    exact fin2_successProb_eq_zero_of_ac (ρ.condKernel x) ρ.snd hx hq0
  have heq : ρ.condKernel =ᵐ[ρ.fst] Kernel.const X ρ.snd := by
    filter_upwards [condKernel_ac_snd_ae ρ] with x hx
    apply (InformationTheory.klDiv_eq_zero_iff).mp
    exact fin2_klDiv_eq_zero_of_reference_zero (ρ.condKernel x) ρ.snd hx hq0
  have hprod : ρ = ρ.fst.prod ρ.snd := by
    calc
      ρ = ρ.fst ⊗ₘ ρ.condKernel := (Measure.disintegrate ρ ρ.condKernel).symm
      _ = ρ.fst ⊗ₘ Kernel.const X ρ.snd := Measure.compProd_congr heq
      _ = ρ.fst.prod ρ.snd := Measure.compProd_const
  have hmi : mutualInfo ρ = 0 := by
    unfold mutualInfo
    exact (InformationTheory.klDiv_eq_zero_iff).2 hprod
  have hH0 :
      (∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst) = 0 := by
    calc
      (∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst) =
          ∫ _x : X, (0 : ℝ) ∂ρ.fst := by
        apply integral_congr_ae
        filter_upwards [hp0] with x hx
        simp [hx]
      _ = 0 := by simp
  rw [hmi, hq0, hH0]
  simp

/-- Degenerate marginal `P(B=1)=1` is the symmetric boundary case. -/
theorem mutualInfo_toReal_eq_entropy_drop_of_marginal_one
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ]
    (hq1 : binaryMarginalOneProb ρ = 1) :
    (mutualInfo ρ).toReal =
      Real.binEntropy (binaryMarginalOneProb ρ) -
        ∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst := by
  have hp1 : posteriorBitOneProb ρ =ᵐ[ρ.fst] fun _ => (1 : ℝ) := by
    filter_upwards [condKernel_ac_snd_ae ρ] with x hx
    exact fin2_successProb_eq_one_of_ac (ρ.condKernel x) ρ.snd hx hq1
  have heq : ρ.condKernel =ᵐ[ρ.fst] Kernel.const X ρ.snd := by
    filter_upwards [condKernel_ac_snd_ae ρ] with x hx
    apply (InformationTheory.klDiv_eq_zero_iff).mp
    exact fin2_klDiv_eq_zero_of_reference_one (ρ.condKernel x) ρ.snd hx hq1
  have hprod : ρ = ρ.fst.prod ρ.snd := by
    calc
      ρ = ρ.fst ⊗ₘ ρ.condKernel := (Measure.disintegrate ρ ρ.condKernel).symm
      _ = ρ.fst ⊗ₘ Kernel.const X ρ.snd := Measure.compProd_congr heq
      _ = ρ.fst.prod ρ.snd := Measure.compProd_const
  have hmi : mutualInfo ρ = 0 := by
    unfold mutualInfo
    exact (InformationTheory.klDiv_eq_zero_iff).2 hprod
  have hH1 :
      (∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst) = 0 := by
    calc
      (∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst) =
          ∫ _x : X, (0 : ℝ) ∂ρ.fst := by
        apply integral_congr_ae
        filter_upwards [hp1] with x hx
        simp [hx]
      _ = 0 := by simp
  rw [hmi, hq1, hH1]
  simp

/-- **Exact binary mutual-information identity, all boundary cases included.** -/
theorem mutualInfo_toReal_eq_binaryEntropy_sub_posteriorEntropy
    (ρ : Measure (X × Fin 2)) [IsProbabilityMeasure ρ] :
    (mutualInfo ρ).toReal =
      Real.binEntropy (binaryMarginalOneProb ρ) -
        ∫ x, Real.binEntropy (posteriorBitOneProb ρ x) ∂ρ.fst := by
  by_cases hq0 : binaryMarginalOneProb ρ = 0
  · exact mutualInfo_toReal_eq_entropy_drop_of_marginal_zero ρ hq0
  by_cases hq1 : binaryMarginalOneProb ρ = 1
  · exact mutualInfo_toReal_eq_entropy_drop_of_marginal_one ρ hq1
  have hq0' : 0 < binaryMarginalOneProb ρ :=
    lt_of_le_of_ne measureReal_nonneg (Ne.symm hq0)
  have hq1' : binaryMarginalOneProb ρ < 1 :=
    lt_of_le_of_ne measureReal_le_one hq1
  exact mutualInfo_toReal_eq_entropy_drop_of_interior ρ hq0' hq1'

end UEOT.V3.InformationBinaryMutualEntropy
