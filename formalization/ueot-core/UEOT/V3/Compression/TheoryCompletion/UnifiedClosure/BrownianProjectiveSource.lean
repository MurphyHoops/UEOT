import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianCountableSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUQuadraticDynkinSource
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-!
Original commitment: continuous stochastic recovery requires an actual all-time noise source.
Existing facts: actual countable Brownian coordinates and finite Gaussian projective laws.
Premise reduced: prove cylinder content sigma-subadditivity and construct its all-real-time measure.
Model/witness: canonical nonnegative-time real coordinate process, zero start and unit variance.
Consumer: actual IsPreBrownianReal feeds the original OU quadratic Dynkin/recovery source; continuity remains open.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianProjectiveSource
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section

private def timeIndex (τ : ℕ → ℝ≥0) (t : ℝ≥0) : ℕ := by
  classical
  exact if h : t ∈ range τ then h.choose else 0

private theorem timeIndex_spec (τ : ℕ → ℝ≥0) (t : ℝ≥0) (ht : t ∈ range τ) :
    τ (timeIndex τ t) = t := by
  classical
  simp only [timeIndex,dif_pos ht]
  exact ht.choose_spec

/-- Local readout into all time coordinates; unsupported coordinates are zero.
This local law is used only for one countable cylinder family, not as Brownian globally. -/
private def fill (τ : ℕ → ℝ≥0) (ω : ℕ → ℝ) (t : ℝ≥0) : ℝ := by
  classical
  exact if t ∈ range τ then ω (timeIndex τ t) else 0

private theorem measurable_fill (τ : ℕ → ℝ≥0) : Measurable (fill τ) := by
  classical
  apply measurable_pi_iff.mpr
  intro t
  by_cases ht : t ∈ range τ
  · simp only [fill,if_pos ht]
    exact measurable_pi_apply _
  · simp only [fill,if_neg ht]
    exact measurable_const

/-- Every finite set supported by the countable enumeration has exactly its
original Brownian law under the literal local readout. -/
private theorem local_finite_law (τ : ℕ → ℝ≥0) (I : Finset ℝ≥0)
    (hI : ∀ t ∈ I, t ∈ range τ) :
    (BrownianCountableSource.countableLaw τ).map
      (I.restrict (π := fun _ : ℝ≥0 => ℝ) ∘ fill τ) = BrownianReal.projectiveFamily I := by
  classical
  let J : Finset ℕ := I.image (timeIndex τ)
  let read : (J → ℝ) → (I → ℝ) := fun x i =>
    x ⟨timeIndex τ i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩
  let select : (J.image τ → ℝ) → (J → ℝ) := fun x j =>
    x ⟨τ j,Finset.mem_image.mpr ⟨j,j.2,rfl⟩⟩
  have hr : Measurable read := by unfold read; fun_prop
  have hs : Measurable select := by unfold select; fun_prop
  have hread : I.restrict (π := fun _ : ℝ≥0 => ℝ) ∘ fill τ =
      read ∘ J.restrict (π := fun _ : ℕ => ℝ) := by
    funext ω i
    simp only [Function.comp_apply,Finset.restrict,fill,if_pos (hI i i.2),read]
  calc
    _ = ((BrownianCountableSource.countableLaw τ).map
        (J.restrict (π := fun _ : ℕ => ℝ))).map read := by
      rw [Measure.map_map hr (Finset.measurable_restrict J),hread]
    _ = (BrownianCountableSource.finiteLaw τ J).map read := by
      rw [BrownianCountableSource.countableLaw_finite]
    _ = (BrownianReal.projectiveFamily (J.image τ)).map (read ∘ select) := by
      change ((BrownianReal.projectiveFamily (J.image τ)).map select).map read = _
      exact Measure.map_map hr hs
    _ = _ := by
      ext A hA
      rw [Measure.map_apply (hr.comp hs) hA]
      have hc : cylinder (α := fun _ : ℝ≥0 => ℝ) (J.image τ) ((read ∘ select) ⁻¹' A) = cylinder (α := fun _ : ℝ≥0 => ℝ) I A := by
        ext x
        change (fun i : I => x (τ (timeIndex τ i))) ∈ A ↔ (fun i : I => x i) ∈ A
        have heq : (fun i : I => x (τ (timeIndex τ i))) = fun i : I => x i := by
          funext i
          rw [timeIndex_spec τ i (hI i i.2)]
        rw [heq]
      exact BrownianReal.isProjectiveMeasureFamily_projectiveFamily.congr_cylinder
        ((hr.comp hs) hA) hA hc

private theorem local_cylinder (τ : ℕ → ℝ≥0) (I : Finset ℝ≥0)
    (hI : ∀ t ∈ I, t ∈ range τ) (A : Set (I → ℝ)) (hA : MeasurableSet A) :
    ((BrownianCountableSource.countableLaw τ).map (fill τ)) (cylinder I A) =
      BrownianReal.projectiveFamily I A := by
  have h := congrArg (fun ν : Measure (I → ℝ) => ν A) (local_finite_law τ I hI)
  rw [Measure.map_apply ((Finset.measurable_restrict I).comp (measurable_fill τ)) hA] at h
  rw [Measure.map_apply (measurable_fill τ) hA.cylinder]
  exact h

/-- The missing sigma-subadditivity follows by realizing ALL cylinder supports
of one countable cover on one actual countable Brownian probability space. -/
theorem brownianContent_sigmaSubadditive :
    (projectiveFamilyContent BrownianReal.isProjectiveMeasureFamily_projectiveFamily).IsSigmaSubadditive := by
  classical
  intro f hf hU
  let I (n : ℕ) : Finset ℝ≥0 := measurableCylinders.finset (hf n)
  let J : Finset ℝ≥0 := measurableCylinders.finset hU
  let S : Set ℝ≥0 := ({0} ∪ (J : Set ℝ≥0)) ∪ ⋃ n, (I n : Set ℝ≥0)
  have hS : S.Countable := ((countable_singleton 0).union J.countable_toSet).union
    (countable_iUnion (fun n => (I n).countable_toSet))
  obtain ⟨τ,hτ⟩ := hS.exists_eq_range ⟨0,Or.inl (Or.inl rfl)⟩
  have hI (n : ℕ) : ∀ t ∈ I n, t ∈ range τ := by
    intro t ht
    rw [← hτ]
    exact Or.inr (mem_iUnion.mpr ⟨n,ht⟩)
  have hJ : ∀ t ∈ J, t ∈ range τ := by
    intro t ht
    rw [← hτ]
    exact Or.inl (Or.inr ht)
  let ν := (BrownianCountableSource.countableLaw τ).map (fill τ)
  have hfn (n : ℕ) : ν (f n) =
      projectiveFamilyContent BrownianReal.isProjectiveMeasureFamily_projectiveFamily (f n) := by
    rw [measurableCylinders.eq_cylinder (hf n),projectiveFamilyContent_cylinder _
      (measurableCylinders.measurableSet (hf n))]
    exact local_cylinder τ (I n) (hI n) _ (measurableCylinders.measurableSet (hf n))
  have hUn : ν (⋃ n, f n) =
      projectiveFamilyContent BrownianReal.isProjectiveMeasureFamily_projectiveFamily (⋃ n, f n) := by
    rw [measurableCylinders.eq_cylinder hU,projectiveFamilyContent_cylinder _
      (measurableCylinders.measurableSet hU)]
    exact local_cylinder τ J hJ _ (measurableCylinders.measurableSet hU)
  rw [← hUn]
  calc
    _ ≤ ∑' n, ν (f n) := measure_iUnion_le f
    _ = _ := tsum_congr hfn

/-- Canonical all-nonnegative-real-time source measure, constructed by the
original Caratheodory extension of its now-proved sigma-subadditive content. -/
def sourceLaw : Measure (ℝ≥0 → ℝ) :=
  (projectiveFamilyContent BrownianReal.isProjectiveMeasureFamily_projectiveFamily).measure
    isSetSemiring_measurableCylinders generateFrom_measurableCylinders.ge
    brownianContent_sigmaSubadditive

/-- Every finite coordinate law is literally the original Brownian Gaussian
projective family; no projective-limit or Brownian-source certificate is input. -/
theorem sourceLaw_finite (I : Finset ℝ≥0) :
    sourceLaw.map (I.restrict (π := fun _ : ℝ≥0 => ℝ)) = BrownianReal.projectiveFamily I := by
  ext A hA
  rw [Measure.map_apply (Finset.measurable_restrict I) hA]
  change sourceLaw (cylinder I A) = _
  rw [sourceLaw,AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm]
  · exact projectiveFamilyContent_cylinder _ hA
  · exact cylinder_mem_measurableCylinders (α := fun _ : ℝ≥0 => ℝ) I A hA

instance sourceLaw_isProbability : IsProbabilityMeasure sourceLaw := by
  constructor
  have h := congrArg (fun ν : Measure ((∅ : Finset ℝ≥0) → ℝ) => ν univ) (sourceLaw_finite ∅)
  rw [Measure.map_apply (Finset.measurable_restrict _) MeasurableSet.univ] at h
  simpa using h

/-- The supplied-source premise of the OU recovery bridge is now realized by
one actual canonical process, on ALL nonnegative real times. -/
theorem source_isPreBrownian :
    IsPreBrownianReal (fun t (ω : ℝ≥0 → ℝ) => ω t) sourceLaw where
  hasLaw I := ⟨(Finset.measurable_restrict I).aemeasurable,sourceLaw_finite I⟩

theorem source_zero : ∀ᵐ ω ∂sourceLaw, ω 0 = 0 := source_isPreBrownian.eval_zero_ae_eq_zero

theorem source_unit_variance : variance (fun ω : ℝ≥0 → ℝ => ω 1) sourceLaw = 1 := by
  rw [← covariance_self,source_isPreBrownian.covariance_eval,min_self]
  · rfl
  · exact source_isPreBrownian.aemeasurable 1

/-- Actual downstream consumer: source-derived quadratic Dynkin recovery with
NO externally supplied Brownian-source premise. Continuous paths, general Ito,
SDE/control and Girsanov still require their own remaining proofs. -/
theorem actual_ou_recovery (k s x0 T : ℝ) (hk : 0 < k) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T,
      (∫ x, x^2 ∂OUQuadraticDynkinSource.ouLaw sourceLaw (fun t ω => ω t) k s x0 t) ≤
        Real.exp (-(2*k)*t)*x0^2+s^2/(2*k)*(1-Real.exp (-(2*k)*t)) :=
  OUQuadraticDynkinSource.actual_source_p_rec_02 source_isPreBrownian k s x0 T hk hT

/-- The very SAME realized all-time source gives genuinely nonzero OU execution
variance from every deterministic initial state, without an external hB. -/
theorem actual_ou_positive_variance (k s x0 : ℝ) (hk : 0 < k) (hs : s ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) :
    0 < variance (OUQuadraticDynkinSource.ouSource (fun t (ω : ℝ≥0 → ℝ) => ω t) k s x0 t) sourceLaw :=
  OUQuadraticDynkinSource.nonzero_noise_positive_variance source_isPreBrownian k s x0 hk hs t ht

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianProjectiveSource
