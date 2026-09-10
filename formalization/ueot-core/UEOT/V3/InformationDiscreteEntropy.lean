import UEOT.V3.InformationEntropyBound
import UEOT.V3.InformationEntropy
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# P-INFO-01 discrete copy-KL / Shannon bridge

The frozen source states the entropy corollary for a **discrete** macrostate,
not merely a finite one.  This module therefore treats countable discrete state
spaces at the source-facing layer.  Shannon entropy is extended-real valued:
it is the expectation of discrete self-information when integrable and `∞`
otherwise.  This matches Mathlib's `klDiv : ℝ≥0∞` semantics and avoids losing
an infinite entropy through `ENNReal.toReal`.

For finite state spaces we additionally recover the ordinary real-valued PMF
Shannon sum already used elsewhere in the UEOT library.
-/

namespace UEOT.V3.InformationDiscreteEntropy

noncomputable section

open MeasureTheory InformationTheory
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationEntropy
open scoped ENNReal

universe uM

variable {M : Type uM}
variable [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]

local instance : DecidableEq M := Classical.decEq M
local instance classicalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Radon--Nikodym density of the diagonal copy law relative to two independent
copies, on a countable discrete state space. -/
def copyDensity (μ : Measure M) : M × M → ℝ≥0∞ :=
  fun z => if z.1 = z.2 then (μ {z.1})⁻¹ else 0

lemma measurable_copyDensity (μ : Measure M) : Measurable (copyDensity μ) := by
  exact measurable_of_countable _

/-- The diagonal law is exactly the independent product law tilted by the
copy density. -/
theorem prod_withDensity_copyDensity_eq_copyJoint
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (μ.prod μ).withDensity (copyDensity μ) = copyJoint μ := by
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  rw [withDensity_apply _ (measurableSet_singleton (a, b))]
  rw [lintegral_singleton]
  have hprod : (μ.prod μ) ({(a, b)} : Set (M × M)) = μ {a} * μ {b} := by
    rw [show ({(a, b)} : Set (M × M)) = ({a} : Set M) ×ˢ ({b} : Set M) by ext z; simp]
    exact Measure.prod_prod _ _
  rw [hprod]
  unfold copyJoint
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (a, b))]
  by_cases hab : a = b
  · subst b
    rw [show ((fun m : M => (m, m)) ⁻¹' ({(a, a)} : Set (M × M))) = ({a} : Set M) by
      ext m
      simp]
    change (if a = a then (μ {a})⁻¹ else 0) * (μ {a} * μ {a}) = μ {a}
    rw [if_pos rfl]
    by_cases ha : μ {a} = 0
    · simp [ha]
    · rw [← mul_assoc, ENNReal.inv_mul_cancel ha (measure_ne_top μ {a})]
      simp
  · have hpre :
        ((fun m : M => (m, m)) ⁻¹' ({(a, b)} : Set (M × M))) = (∅ : Set M) := by
      ext m
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false]
      constructor
      · intro hpair
        have hma : m = a := congrArg Prod.fst hpair
        have hmb : m = b := congrArg Prod.snd hpair
        exact (hab (hma.symm.trans hmb)).elim
      · intro hfalse
        exact False.elim hfalse
    rw [hpre]
    simp [copyDensity, hab]

/-- Absolute continuity needed by the KL/Radon--Nikodym API follows from the
explicit density representation. -/
theorem copyJoint_absolutelyContinuous_prod
    (μ : Measure M) [IsProbabilityMeasure μ] :
    copyJoint μ ≪ μ.prod μ := by
  rw [← prod_withDensity_copyDensity_eq_copyJoint μ]
  exact withDensity_absolutelyContinuous _ _

/-- The abstract Mathlib Radon--Nikodym derivative agrees almost everywhere
with the explicit countable-discrete copy density. -/
theorem rnDeriv_copyJoint_prod
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (copyJoint μ).rnDeriv (μ.prod μ) =ᵐ[μ.prod μ] copyDensity μ := by
  rw [← prod_withDensity_copyDensity_eq_copyJoint μ]
  exact Measure.rnDeriv_withDensity (μ.prod μ) (measurable_copyDensity μ)

/-- Log-likelihood of the copied state against two independent copies, written
through the explicit copy density. -/
theorem llr_copyJoint_prod
    (μ : Measure M) [IsProbabilityMeasure μ] :
    llr (copyJoint μ) (μ.prod μ) =ᵐ[copyJoint μ]
      fun z => Real.log (copyDensity μ z).toReal := by
  have hAC : copyJoint μ ≪ μ.prod μ := copyJoint_absolutelyContinuous_prod μ
  have hrn :
      (copyJoint μ).rnDeriv (μ.prod μ) =ᵐ[copyJoint μ] copyDensity μ :=
    hAC.ae_le (rnDeriv_copyJoint_prod μ)
  filter_upwards [hrn] with z hz
  simp only [llr]
  rw [hz]

/-- Extended-real Shannon entropy of a countable discrete probability law.
The integrand is the usual self-information `log (1 / p_m)` evaluated on the
diagonal copy density.  If that expectation is not integrable, entropy is
`∞`, as required for a general discrete random variable. -/
noncomputable def discreteShannonEntropy (μ : Measure M) : ℝ≥0∞ :=
  let info : M → ℝ := fun m => Real.log (copyDensity μ (m, m)).toReal
  if Integrable info μ then ENNReal.ofReal (∫ m, info m ∂μ) else ∞

/-- The copied-state KL divergence is exactly extended Shannon entropy for a
countable discrete marginal.  This is the source-facing identity behind
`I(M;Y) ≤ H(M)` and remains valid when the entropy diverges. -/
theorem copy_kl_eq_discreteShannonEntropy
    (μ : Measure M) [IsProbabilityMeasure μ] :
    klDiv (copyJoint μ) (μ.prod μ) = discreteShannonEntropy μ := by
  let g : M × M → ℝ := fun z => Real.log (copyDensity μ z).toReal
  let info : M → ℝ := fun m => Real.log (copyDensity μ (m, m)).toReal
  have hAC : copyJoint μ ≪ μ.prod μ := copyJoint_absolutelyContinuous_prod μ
  have hllr : llr (copyJoint μ) (μ.prod μ) =ᵐ[copyJoint μ] g := by
    simpa [g] using llr_copyJoint_prod μ
  have hg : AEStronglyMeasurable g (copyJoint μ) := by
    exact (measurable_of_countable g).aestronglyMeasurable
  have hdiag : AEMeasurable (fun m : M => (m, m)) μ :=
    (measurable_of_countable _).aemeasurable
  have hmapInt : Integrable g (copyJoint μ) ↔ Integrable info μ := by
    unfold copyJoint
    have h := integrable_map_measure hg hdiag
    simpa [g, info, Function.comp_def] using h
  have hint :
      Integrable (llr (copyJoint μ) (μ.prod μ)) (copyJoint μ) ↔
        Integrable info μ := by
    exact (integrable_congr hllr).trans hmapInt
  have hintegral :
      (∫ z, llr (copyJoint μ) (μ.prod μ) z ∂(copyJoint μ)) =
        ∫ m, info m ∂μ := by
    rw [integral_congr_ae hllr]
    unfold copyJoint
    rw [integral_map]
    · exact hdiag
    · exact hg
  have hmass : copyJoint μ Set.univ = (μ.prod μ) Set.univ := by
    unfold copyJoint
    rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp
  have hmassReal : (μ.prod μ).real Set.univ = (copyJoint μ).real Set.univ := by
    simp only [measureReal_def]
    rw [hmass]
  by_cases hinfo : Integrable info μ
  · have hllrInt : Integrable (llr (copyJoint μ) (μ.prod μ)) (copyJoint μ) :=
      hint.mpr hinfo
    rw [InformationTheory.klDiv_of_ac_of_integrable hAC hllrInt]
    simp only [discreteShannonEntropy, info, hinfo, ↓reduceIte]
    rw [hintegral, hmassReal, add_sub_cancel_right]
  · have hllrNot : ¬ Integrable (llr (copyJoint μ) (μ.prod μ)) (copyJoint μ) := by
      intro h
      exact hinfo (hint.mp h)
    rw [InformationTheory.klDiv_of_not_integrable hllrNot]
    simp [discreteShannonEntropy, info, hinfo]

/-- Finite-state specialization: the extended Shannon entropy bridge recovers
the ordinary real-valued PMF Shannon sum already used by P-INFO-05. -/
theorem toReal_copy_kl_eq_shannon
    [Fintype M]
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (klDiv (copyJoint μ) (μ.prod μ)).toReal =
      pmfShannonEntropy μ.toPMF := by
  have hAC : copyJoint μ ≪ μ.prod μ := copyJoint_absolutelyContinuous_prod μ
  have hmass : copyJoint μ Set.univ = (μ.prod μ) Set.univ := by
    unfold copyJoint
    rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
    simp
  rw [InformationTheory.toReal_klDiv_of_measure_eq hAC hmass]
  have hllr := llr_copyJoint_prod μ
  rw [integral_congr_ae hllr]
  unfold copyJoint
  rw [integral_map]
  · calc
      (∫ (x : M), Real.log (copyDensity μ (x, x)).toReal ∂μ) =
          ∑ x, (μ.toPMF x).toReal * Real.log (copyDensity μ (x, x)).toReal := by
        simpa only [Measure.toPMF_toMeasure, smul_eq_mul] using
          (PMF.integral_eq_sum (p := μ.toPMF)
            (f := fun x : M => Real.log (copyDensity μ (x, x)).toReal))
      _ = pmfShannonEntropy μ.toPMF := by
        unfold pmfShannonEntropy
        rw [tsum_fintype]
        apply Finset.sum_congr rfl
        intro m hm
        simp [copyDensity, Measure.toPMF_apply, ENNReal.toReal_inv,
          Real.log_inv, Real.negMulLog]
  · exact (measurable_of_countable _).aemeasurable
  · exact (measurable_of_countable _).aestronglyMeasurable

end

end UEOT.V3.InformationDiscreteEntropy