import Mathlib.Probability.BrownianMotion.Basic
import UEOT.V3.DynamicsKernel

/-!
Original commitment: continuous stochastic recovery needs an actually realized noise source.
Existing facts: finite Brownian Gaussian laws are projective; conditional kernels and trajectory measures exist.
Premise reduced: construct a countable-time source, without assuming a Brownian process or projective limit.
Model/witness: any nonnegative real time sequence, including duplicates; positive-time variance is nonzero.
Consumer: actual finite Gaussian coordinate laws and their mean/covariance; all-real and continuous paths remain open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianCountableSource
open MeasureTheory ProbabilityTheory
open UEOT.V3.DynamicsKernel
open scoped ENNReal NNReal
noncomputable section

private abbrev Prefix (n : ℕ) := (i : Finset.Iic n) → ℝ

/-- The original history append is the existing measurable gluing equivalence. -/
private def appendEquiv (n : ℕ) : Prefix n × ℝ ≃ᵐ Prefix (n+1) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Prefix n))
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => ℝ) n)).trans
    (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ => ℝ) (Nat.le_succ n))

private theorem appendEquiv_coe (n : ℕ) :
    (appendEquiv n : Prefix n × ℝ → Prefix (n+1)) = appendHistory n := rfl

private theorem split_fst (n : ℕ) :
    Prod.fst ∘ (appendEquiv n).symm =
      Finset.restrict₂ (π := fun _ : ℕ => ℝ) (Finset.Iic_subset_Iic.mpr (Nat.le_succ n)) := rfl

private def splitLaw (μ : (n : ℕ) → Measure (Prefix n)) (n : ℕ) :
    Measure (Prefix n × ℝ) := (μ (n+1)).map (appendEquiv n).symm

private instance splitLaw_probability (μ : (n : ℕ) → Measure (Prefix n))
    [∀ n, IsProbabilityMeasure (μ n)] (n : ℕ) : IsProbabilityMeasure (splitLaw μ n) :=
  Measure.isProbabilityMeasure_map (appendEquiv n).symm.measurable.aemeasurable

private def nextKernel (μ : (n : ℕ) → Measure (Prefix n))
    [∀ n, IsProbabilityMeasure (μ n)] (n : ℕ) : Kernel (Prefix n) ℝ :=
  (splitLaw μ n).condKernel

private instance nextKernel_isMarkov (μ : (n : ℕ) → Measure (Prefix n))
    [∀ n, IsProbabilityMeasure (μ n)] (n : ℕ) : IsMarkovKernel (nextKernel μ n) := by
  unfold nextKernel
  infer_instance

private def initialLaw (μ : (n : ℕ) → Measure (Prefix n)) : Measure ℝ :=
  (μ 0).map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ))

private instance initialLaw_probability (μ : (n : ℕ) → Measure (Prefix n))
    [∀ n, IsProbabilityMeasure (μ n)] : IsProbabilityMeasure (initialLaw μ) :=
  Measure.isProbabilityMeasure_map (MeasurableEquiv.piUnique _).measurable.aemeasurable

/-- Constructed by the original Ionescu--Tulcea kernel iteration, not selected
from a premise asserting the desired finite laws. -/
private def prefixRealization (μ : (n : ℕ) → Measure (Prefix n))
    [∀ n, IsProbabilityMeasure (μ n)] : Measure (ℕ → ℝ) :=
  Kernel.trajMeasure (initialLaw μ) (nextKernel μ)

private instance prefixRealization_probability (μ : (n : ℕ) → Measure (Prefix n))
    [∀ n, IsProbabilityMeasure (μ n)] : IsProbabilityMeasure (prefixRealization μ) := by
  unfold prefixRealization
  infer_instance

private theorem prefixRealization_law (μ : (n : ℕ) → Measure (Prefix n))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ n, (μ (n+1)).map
      (Finset.restrict₂ (π := fun _ : ℕ => ℝ) (Finset.Iic_subset_Iic.mpr (Nat.le_succ n))) = μ n) :
    ∀ n, (prefixRealization μ).map (Preorder.frestrictLe n) = μ n := by
  intro n
  induction n with
  | zero =>
      rw [prefixRealization, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp,
        initialLaw, Measure.map_map (MeasurableEquiv.piUnique _).symm.measurable
          (MeasurableEquiv.piUnique _).measurable]
      have hcomp : (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm ∘
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)) = id := by
        funext x
        exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => ℝ)).symm_apply_apply x
      rw [hcomp, Measure.map_id]
  | succ n ih =>
      have hfst : (splitLaw μ n).fst = μ n := by
        change ((μ (n+1)).map (appendEquiv n).symm).map Prod.fst = μ n
        rw [Measure.map_map measurable_fst (appendEquiv n).symm.measurable, split_fst]
        exact hμ n
      have hstep := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ : ℕ => ℝ) (μ₀ := initialLaw μ) (κ := nextKernel μ) (a := n)
      change (prefixRealization μ).map (Preorder.frestrictLe n) ⊗ₘ nextKernel μ n =
        (prefixRealization μ).map (fun x => (Preorder.frestrictLe n x,x (n+1))) at hstep
      have hpack := congrArg (fun ν : Measure (Prefix n × ℝ) => ν.map (appendEquiv n)) hstep
      rw [ih, ← hfst] at hpack
      change ((splitLaw μ n).fst ⊗ₘ (splitLaw μ n).condKernel).map (appendEquiv n) = _ at hpack
      rw [Measure.IsCondKernel.disintegrate, splitLaw,
        Measure.map_map (appendEquiv n).measurable (appendEquiv n).symm.measurable] at hpack
      have hid : (appendEquiv n) ∘ (appendEquiv n).symm = id := by
        funext x
        exact (appendEquiv n).apply_symm_apply x
      rw [hid, Measure.map_id] at hpack
      rw [Measure.map_map (appendEquiv n).measurable (by fun_prop)] at hpack
      have heq : (appendEquiv n) ∘ (fun x : ℕ → ℝ => (Preorder.frestrictLe n x,x (n+1))) =
          Preorder.frestrictLe (n+1) := by
        funext x
        rw [Function.comp_apply, appendEquiv_coe]
        exact appendHistory_prefix_next n x
      rw [heq] at hpack
      exact hpack.symm

private def selectTimes (τ : ℕ → ℝ≥0) (I : Finset ℕ)
    (x : I.image τ → ℝ) : I → ℝ :=
  fun i => x ⟨τ i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩

private theorem measurable_selectTimes (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    Measurable (selectTimes τ I) := by
  unfold selectTimes
  fun_prop

/-- A finite coordinate sample uses the original Gaussian law on the finite
IMAGE of the requested times. Repeated times therefore share one coordinate. -/
def finiteLaw (τ : ℕ → ℝ≥0) (I : Finset ℕ) : Measure (I → ℝ) :=
  (BrownianReal.projectiveFamily (I.image τ)).map (selectTimes τ I)

instance finiteLaw_isProbability (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    IsProbabilityMeasure (finiteLaw τ I) :=
  Measure.isProbabilityMeasure_map (measurable_selectTimes τ I).aemeasurable

/-- Prefix consistency is derived from Brownian's actual finite Gaussian
projective family, including when the time sequence has duplicates. -/
theorem finiteLaw_restrict (τ : ℕ → ℝ≥0) {I J : Finset ℕ} (hIJ : I ⊆ J) :
    (finiteLaw τ J).map (Finset.restrict₂ (π := fun _ : ℕ => ℝ) hIJ) = finiteLaw τ I := by
  have htimes : I.image τ ⊆ J.image τ := Finset.image_subset_image hIJ
  have hp := BrownianReal.isProjectiveMeasureFamily_projectiveFamily (J.image τ) (I.image τ) htimes
  unfold finiteLaw
  rw [Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℕ => ℝ) hIJ) (measurable_selectTimes τ J), hp,
    Measure.map_map (measurable_selectTimes τ I) (Finset.measurable_restrict₂ (X := fun _ : ℝ≥0 => ℝ) htimes)]
  rfl

/-- An actual countable-coordinate probability space, constructed from
conditional kernels of finite Gaussian laws. No `hB` or limit certificate is input. -/
def countableLaw (τ : ℕ → ℝ≥0) : Measure (ℕ → ℝ) :=
  prefixRealization (fun n => finiteLaw τ (Finset.Iic n))

instance countableLaw_isProbability (τ : ℕ → ℝ≥0) : IsProbabilityMeasure (countableLaw τ) := by
  unfold countableLaw
  infer_instance

theorem countableLaw_prefix (τ : ℕ → ℝ≥0) (n : ℕ) :
    (countableLaw τ).map (Preorder.frestrictLe n) = finiteLaw τ (Finset.Iic n) := by
  apply prefixRealization_law
  intro n
  exact finiteLaw_restrict τ (Finset.Iic_subset_Iic.mpr (Nat.le_succ n))

/-- Every finite set of coordinates, not just an initial block, has the actual
Brownian finite law sampled at those requested times. -/
theorem countableLaw_finite (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    (countableLaw τ).map (I.restrict (π := fun _ : ℕ => ℝ)) = finiteLaw τ I := by
  have hI : I ⊆ Finset.Iic (I.sup id) := I.subset_Iic_sup_id
  rw [← finiteLaw_restrict τ hI, ← countableLaw_prefix τ (I.sup id),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℕ => ℝ) hI) (Preorder.measurable_frestrictLe _)]
  rfl

/-- Requested finite coordinates are Gaussian even when times repeat: the
selection is an actual continuous linear image of the original Gaussian law. -/
instance finiteLaw_isGaussian (τ : ℕ → ℝ≥0) (I : Finset ℕ) :
    IsGaussian (finiteLaw τ I) := by
  let L : (I.image τ → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj
      (⟨τ i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩ : I.image τ))
  change IsGaussian ((BrownianReal.projectiveFamily (I.image τ)).map L)
  infer_instance

/-- The realized coordinate process has all finite Gaussian laws, rather than
assuming an abstract Gaussian process as input. -/
theorem countable_isGaussianProcess (τ : ℕ → ℝ≥0) :
    IsGaussianProcess (fun k (ω : ℕ → ℝ) => ω k) (countableLaw τ) where
  hasGaussianLaw I := by
    have h : HasLaw (I.restrict (π := fun _ : ℕ => ℝ)) (finiteLaw τ I) (countableLaw τ) :=
      ⟨(Finset.measurable_restrict I).aemeasurable,countableLaw_finite τ I⟩
    exact h.hasGaussianLaw

private theorem finiteLaw_eval (τ : ℕ → ℝ≥0) (I : Finset ℕ) (i : I) :
    HasLaw (fun x : I → ℝ => x i) (gaussianReal 0 (τ i)) (finiteLaw τ I) := by
  refine ⟨(measurable_pi_apply i).aemeasurable,?_⟩
  rw [finiteLaw,Measure.map_map (measurable_pi_apply i) (measurable_selectTimes τ I)]
  exact (BrownianReal.measurePreserving_eval_projectiveFamily
    (⟨τ i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩ : I.image τ)).map_eq

/-- Each actual sampled coordinate has the centered Gaussian Brownian law. -/
theorem countable_eval_hasLaw (τ : ℕ → ℝ≥0) (k : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω k) (gaussianReal 0 (τ k)) (countableLaw τ) := by
  have h : HasLaw (({k} : Finset ℕ).restrict (π := fun _ : ℕ => ℝ))
      (finiteLaw τ {k}) (countableLaw τ) :=
    ⟨(Finset.measurable_restrict _).aemeasurable,countableLaw_finite τ {k}⟩
  exact (finiteLaw_eval τ {k} ⟨k,by simp⟩).comp h

/-- Actual coordinate means, with integrability supplied by their Gaussian laws. -/
theorem countable_mean (τ : ℕ → ℝ≥0) (k : ℕ) :
    (∫ ω, ω k ∂countableLaw τ) = 0 := by
  rw [(countable_eval_hasLaw τ k).integral_eq,integral_id_gaussianReal]

private theorem finiteLaw_covariance (τ : ℕ → ℝ≥0) (I : Finset ℕ) (i j : I) :
    cov[fun x : I → ℝ => x i,fun x => x j;finiteLaw τ I] = min (τ i : ℝ) (τ j : ℝ) := by
  rw [finiteLaw,covariance_map (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable (measurable_selectTimes τ I).aemeasurable]
  exact BrownianReal.covariance_eval_projectiveFamily _ _ _

/-- Covariance of the realized countable process is min of the actual requested
times. In particular, repeated times have the same Brownian covariance. -/
theorem countable_covariance (τ : ℕ → ℝ≥0) (k l : ℕ) :
    cov[fun ω : ℕ → ℝ => ω k,fun ω => ω l;countableLaw τ] = min (τ k : ℝ) (τ l : ℝ) := by
  have h : HasLaw (({k,l} : Finset ℕ).restrict (π := fun _ : ℕ => ℝ))
      (finiteLaw τ {k,l}) (countableLaw τ) :=
    ⟨(Finset.measurable_restrict _).aemeasurable,countableLaw_finite τ {k,l}⟩
  have hc := h.covariance_fun_comp
    (f := fun x : ({k,l} : Finset ℕ) → ℝ => x ⟨k,by simp⟩)
    (g := fun x => x ⟨l,by simp⟩)
    (measurable_pi_apply (⟨k,by simp⟩ : ({k,l} : Finset ℕ))).aemeasurable
    (measurable_pi_apply (⟨l,by simp⟩ : ({k,l} : Finset ℕ))).aemeasurable
  exact hc.trans (finiteLaw_covariance τ {k,l} ⟨k,by simp⟩ ⟨l,by simp⟩)

theorem countable_variance (τ : ℕ → ℝ≥0) (k : ℕ) :
    variance (fun ω : ℕ → ℝ => ω k) (countableLaw τ) = (τ k : ℝ) := by
  rw [← covariance_self, countable_covariance, min_self]
  exact (measurable_pi_apply k).aemeasurable

private theorem finiteLaw_increment (τ : ℕ → ℝ≥0) (I : Finset ℕ) (i j : I) :
    HasLaw (fun x : I → ℝ => x i - x j) (gaussianReal 0 (nndist (τ i) (τ j))) (finiteLaw τ I) := by
  have hm : Measurable (fun x : I → ℝ => x i - x j) :=
    (measurable_pi_apply i).sub (measurable_pi_apply j)
  refine ⟨hm.aemeasurable,?_⟩
  rw [finiteLaw,Measure.map_map hm (measurable_selectTimes τ I)]
  exact (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily (I.image τ)
    (⟨τ i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩ : I.image τ)
    (⟨τ j,Finset.mem_image.mpr ⟨j,j.2,rfl⟩⟩ : I.image τ)).map_eq

/-- Actual increment laws supply the L2 control needed by the next all-time
completion step, with no monotonicity or injectivity restriction on τ. -/
theorem countable_increment_hasLaw (τ : ℕ → ℝ≥0) (k l : ℕ) :
    HasLaw (fun ω : ℕ → ℝ => ω k - ω l) (gaussianReal 0 (nndist (τ k) (τ l))) (countableLaw τ) := by
  have h : HasLaw (({k,l} : Finset ℕ).restrict (π := fun _ : ℕ => ℝ))
      (finiteLaw τ {k,l}) (countableLaw τ) :=
    ⟨(Finset.measurable_restrict _).aemeasurable,countableLaw_finite τ {k,l}⟩
  exact (finiteLaw_increment τ {k,l} ⟨k,by simp⟩ ⟨l,by simp⟩).comp h

/-- The exact increment second moment is its requested time distance. This is
a proved source bound, not an assumed Kolmogorov-continuity certificate. -/
theorem countable_increment_second_moment (τ : ℕ → ℝ≥0) (k l : ℕ) :
    (∫ ω, (ω k - ω l)^2 ∂countableLaw τ) = (nndist (τ k) (τ l) : ℝ) := by
  have h := countable_increment_hasLaw τ k l
  have hm := h.integral_eq
  rw [integral_id_gaussianReal] at hm
  have hv := h.variance_eq
  rw [variance_id_gaussianReal,variance_eq_integral h.aemeasurable,hm] at hv
  simpa only [sub_zero] using hv

/-- A concrete dense nonnegative time sequence with explicit zero and unit
coordinates. Density does not require the sequence to be injective. -/
def denseTimes : ℕ → ℝ≥0
  | 0 => 0
  | 1 => 1
  | n+2 => TopologicalSpace.denseSeq ℝ≥0 n

theorem denseTimes_dense : DenseRange denseTimes := by
  apply (TopologicalSpace.denseRange_denseSeq ℝ≥0).mono
  rintro x ⟨n,rfl⟩
  exact ⟨n+2,rfl⟩

/-- The actual constructed dense-time source starts at zero almost surely. -/
theorem dense_source_zero : ∀ᵐ ω ∂countableLaw denseTimes, ω 0 = 0 := by
  have h := countable_eval_hasLaw denseTimes 0
  rw [denseTimes,gaussianReal_zero_var] at h
  exact h.ae_eq_of_dirac

/-- Genuine positive noise in the SAME dense-time source, independent of any
supplied Brownian process or randomized initial seed. -/
theorem dense_source_unit_variance :
    variance (fun ω : ℕ → ℝ => ω 1) (countableLaw denseTimes) = 1 := by
  rw [countable_variance]
  rfl

/-- Nonempty countable-time source consumer: one actual law has Gaussian finite
coordinates, exact Brownian covariance, zero start and positive unit variance.
This does not assert an all-real-time or continuous Brownian process. -/
theorem dense_source_realized :
    ∃ μ : Measure (ℕ → ℝ), IsProbabilityMeasure μ ∧
      IsGaussianProcess (fun k (ω : ℕ → ℝ) => ω k) μ ∧
      (∀ k l, cov[fun ω : ℕ → ℝ => ω k,fun ω => ω l;μ] =
        min (denseTimes k : ℝ) (denseTimes l : ℝ)) ∧
      (∀ᵐ ω ∂μ, ω 0 = 0) ∧ variance (fun ω : ℕ → ℝ => ω 1) μ = 1 :=
  ⟨countableLaw denseTimes,inferInstance,countable_isGaussianProcess denseTimes,
    countable_covariance denseTimes,dense_source_zero,dense_source_unit_variance⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianCountableSource
