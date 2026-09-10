import UEOT.V3.InformationEntropyBound
import UEOT.V3.InformationEntropy
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# P-INFO-01 finite discrete copy-KL / Shannon bridge

This module isolates the genuinely discrete step in the P-INFO-01 entropy
bound. For a finite measurable state space, the diagonal/copy law is written
as a density with respect to the independent product law, and its KL divergence
is reduced to the ordinary Shannon entropy of the marginal PMF.
-/

namespace UEOT.V3.InformationDiscreteEntropy

noncomputable section

open MeasureTheory InformationTheory
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationEntropy
open scoped ENNReal

universe uM

variable {M : Type uM}
variable [Fintype M] [MeasurableSpace M] [MeasurableSingletonClass M]

local instance : DecidableEq M := Classical.decEq M

/-- Radon--Nikodym density of the diagonal copy law relative to two independent
copies, on a finite discrete state space. -/
def copyDensity (μ : Measure M) : M × M → ℝ≥0∞ :=
  fun z => if z.1 = z.2 then (μ {z.1})⁻¹ else 0

lemma measurable_copyDensity (μ : Measure M) : Measurable (copyDensity μ) := by
  exact measurable_of_finite _

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
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton (a, b))]
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
with the explicit finite-discrete copy density. -/
theorem rnDeriv_copyJoint_prod
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (copyJoint μ).rnDeriv (μ.prod μ) =ᵐ[μ.prod μ] copyDensity μ := by
  rw [← prod_withDensity_copyDensity_eq_copyJoint μ]
  exact Measure.rnDeriv_withDensity (μ.prod μ) (measurable_copyDensity μ)

/-- The copied-state KL divergence is exactly the Shannon entropy of the
finite discrete marginal. This is the missing scalar identity behind
`I(M;Y) ≤ H(M)` in P-INFO-01. -/
theorem toReal_copy_kl_eq_shannon
    (μ : Measure M) [IsProbabilityMeasure μ] :
    (klDiv (copyJoint μ) (μ.prod μ)).toReal =
      pmfShannonEntropy μ.toPMF := by
  have hAC : copyJoint μ ≪ μ.prod μ := copyJoint_absolutelyContinuous_prod μ
  have hmass : copyJoint μ Set.univ = (μ.prod μ) Set.univ := by
    unfold copyJoint
    rw [Measure.map_apply (measurable_of_finite _) MeasurableSet.univ]
    simp
  rw [InformationTheory.toReal_klDiv_of_measure_eq hAC hmass]
  have hrn :
      (copyJoint μ).rnDeriv (μ.prod μ) =ᵐ[copyJoint μ] copyDensity μ :=
    hAC.ae_le (rnDeriv_copyJoint_prod μ)
  have hllr :
      llr (copyJoint μ) (μ.prod μ) =ᵐ[copyJoint μ]
        fun z => Real.log (copyDensity μ z).toReal := by
    filter_upwards [hrn] with z hz
    simp only [llr]
    rw [hz]
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
  · exact (measurable_of_finite _).aemeasurable
  · exact (measurable_of_finite _).aestronglyMeasurable

end

end UEOT.V3.InformationDiscreteEntropy