import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianMartingaleSource
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Independence.Integration

/-!
Original commitment: P11 finite-dimensional consumers need a realized finite-dimensional noise source.
Existing result: one actual scalar Brownian source with continuous paths and natural-past independence.
Premise reduced: derive coordinate independence and covariance from the actual finite product, not fields.
Model/witness: arbitrary finite d, including 0 and 2; original sourceLaw factors and EuclideanSpace real L2 norm.
Consumer: later vector stochastic integral/Ito/Girsanov; those consumers are not asserted here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteProductSource
open MeasureTheory ProbabilityTheory Set
open BrownianProjectiveSource BrownianContinuousSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

abbrev Sample (d : ℕ) := Fin d → (ℝ≥0 → ℝ)

/-- The actual finite product of the already constructed scalar source. -/
def productLaw (d : ℕ) : Measure (Sample d) := Measure.pi (fun _ => sourceLaw)

instance productLaw_isProbability (d : ℕ) : IsProbabilityMeasure (productLaw d) := by
  unfold productLaw
  infer_instance

theorem eval_preserving (d : ℕ) (i : Fin d) :
    MeasurePreserving (fun ω : Sample d => ω i) (productLaw d) sourceLaw :=
  measurePreserving_eval (fun _ : Fin d => sourceLaw) i

/-- Coordinate readout runs the SAME original continuous process on its own source factor. -/
def coordinate (d : ℕ) (i : Fin d) (t : ℝ≥0) (ω : Sample d) : ℝ := process t (ω i)

theorem coordinate_measurable (d : ℕ) (i : Fin d) (t : ℝ≥0) :
    Measurable (coordinate d i t) :=
  (measurable_process t).comp (measurable_pi_apply i)

theorem coordinate_joint_measurable (d : ℕ) (i : Fin d) :
    Measurable (Function.uncurry (coordinate d i)) :=
  measurable_joint_process.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem coordinate_continuous (d : ℕ) (i : Fin d) (ω : Sample d) :
    Continuous (fun t => coordinate d i t ω) := process_continuous (ω i)

/-- Finite-dimensional Gaussian laws are transported by the actual product evaluation map. -/
theorem coordinate_preBrownian (d : ℕ) (i : Fin d) :
    IsPreBrownianReal (coordinate d i) (productLaw d) where
  hasLaw I := (process_isPreBrownian.hasLaw I).comp (eval_preserving d i).hasLaw

theorem coordinate_isBrownian (d : ℕ) (i : Fin d) :
    IsBrownianReal (coordinate d i) (productLaw d) where
  toIsPreBrownianReal := coordinate_preBrownian d i
  cont := ae_of_all _ (coordinate_continuous d i)

/-- Independence holds for the entire coordinate processes, not merely one time slice. -/
theorem coordinateProcesses_independent (d : ℕ) :
    iIndepFun (fun i : Fin d => fun ω : Sample d => fun t => coordinate d i t ω) (productLaw d) :=
  iIndepFun_pi (fun _ : Fin d =>
    (measurable_pi_lambda _ (fun t => measurable_process t)).aemeasurable)

/-- Actual coordinate increments, without an independent noise parameter. -/
def coordinateIncrement (d : ℕ) (i : Fin d) (s t : ℝ≥0) (ω : Sample d) : ℝ :=
  coordinate d i t ω - coordinate d i s ω

theorem coordinateIncrement_measurable (d : ℕ) (i : Fin d) (s t : ℝ≥0) :
    Measurable (coordinateIncrement d i s t) :=
  (coordinate_measurable d i t).sub (coordinate_measurable d i s)

theorem coordinateIncrement_memLp_two (d : ℕ) (i : Fin d) (s t : ℝ≥0) :
    MemLp (coordinateIncrement d i s t) 2 (productLaw d) :=
  ((coordinate_preBrownian d i).hasLaw_sub t s).hasGaussianLaw.memLp_two

theorem coordinateIncrement_mean (d : ℕ) (i : Fin d) (s t : ℝ≥0) :
    (∫ ω, coordinateIncrement d i s t ω ∂productLaw d) = 0 := by
  have h := (eval_preserving d i).hasLaw.integral_comp
    (f := BrownianMartingaleSource.increment s t)
    (BrownianMartingaleSource.measurable_increment s t).aestronglyMeasurable
  exact h.trans (BrownianMartingaleSource.increment_mean s t)

theorem coordinateIncrement_square_mean (d : ℕ) (i : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, coordinateIncrement d i s t ω ^ 2 ∂productLaw d) = (t : ℝ) - (s : ℝ) := by
  have h := (eval_preserving d i).hasLaw.integral_comp
    (f := fun ω => BrownianMartingaleSource.increment s t ω ^ 2)
    ((BrownianMartingaleSource.measurable_increment s t).pow_const 2).aestronglyMeasurable
  exact h.trans (BrownianMartingaleSource.increment_square_mean s t hst)

/-- Native product independence is derived for every finite family, including dimension zero. -/
theorem coordinateIncrements_independent (d : ℕ) (s t : ℝ≥0) :
    iIndepFun (fun i : Fin d => coordinateIncrement d i s t) (productLaw d) :=
  iIndepFun_pi (fun _ : Fin d => (BrownianMartingaleSource.measurable_increment s t).aemeasurable)

theorem coordinateIncrement_cross_mean (d : ℕ) (i j : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, coordinateIncrement d i s t ω * coordinateIncrement d j s t ω ∂productLaw d) =
      if i = j then (t : ℝ) - (s : ℝ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    simpa only [pow_two] using coordinateIncrement_square_mean d i s t hst
  · rw [if_neg hij]
    have h := ((coordinateIncrements_independent d s t).indepFun hij).integral_mul_eq_mul_integral
      (coordinateIncrement_measurable d i s t).aestronglyMeasurable
      (coordinateIncrement_measurable d j s t).aestronglyMeasurable
    change (∫ ω, coordinateIncrement d i s t ω * coordinateIncrement d j s t ω ∂productLaw d) = _ at h
    rw [coordinateIncrement_mean,coordinateIncrement_mean,mul_zero] at h
    exact h

/-- This is the actual Euclidean (PiLp 2) readout, not the finite-pi sup norm. -/
def vectorProcess (d : ℕ) (t : ℝ≥0) (ω : Sample d) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => coordinate d i t ω)

@[simp] theorem vectorProcess_apply (d : ℕ) (t : ℝ≥0) (ω : Sample d) (i : Fin d) :
    vectorProcess d t ω i = coordinate d i t ω := rfl

theorem vectorProcess_continuous (d : ℕ) (ω : Sample d) :
    Continuous (fun t => vectorProcess d t ω) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp (continuous_pi (fun i => coordinate_continuous d i ω))

theorem vectorProcess_measurable (d : ℕ) (t : ℝ≥0) : Measurable (vectorProcess d t) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp
    (measurable_pi_lambda _ (fun i => coordinate_measurable d i t))

theorem vectorProcess_joint_measurable (d : ℕ) : Measurable (Function.uncurry (vectorProcess d)) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.comp
    (measurable_pi_lambda _ (fun i => coordinate_joint_measurable d i))

def vectorIncrement (d : ℕ) (s t : ℝ≥0) (ω : Sample d) : EuclideanSpace ℝ (Fin d) :=
  vectorProcess d t ω - vectorProcess d s ω

@[simp] theorem vectorIncrement_apply (d : ℕ) (s t : ℝ≥0) (ω : Sample d) (i : Fin d) :
    vectorIncrement d s t ω i = coordinateIncrement d i s t ω := rfl

/-- Euclidean second energy is the sum of the actual coordinate second energies. -/
theorem vectorIncrement_energy (d : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, ‖vectorIncrement d s t ω‖ ^ 2 ∂productLaw d) = (d : ℝ) * ((t : ℝ) - (s : ℝ)) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq,vectorIncrement_apply]
  rw [integral_finsetSum _ (fun i _ => (coordinateIncrement_memLp_two d i s t).integrable_sq)]
  simp_rw [coordinateIncrement_square_mean d _ s t hst]
  simp [mul_sub]


/-- The explicit Gaussian law is derived from the SAME original coordinate source. -/
theorem coordinateIncrement_hasLaw (d : ℕ) (i : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (coordinateIncrement d i s t) (gaussianReal 0 (t-s)) (productLaw d) :=
  (BrownianMartingaleSource.increment_hasLaw s t hst).comp (eval_preserving d i).hasLaw

/-- Actual covariance, not just a postulated cross-coordinate field. -/
theorem coordinateIncrement_covariance (d : ℕ) (i j : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    cov[coordinateIncrement d i s t,coordinateIncrement d j s t;productLaw d] =
      if i = j then (t : ℝ)-(s : ℝ) else 0 := by
  rw [covariance_eq_sub (coordinateIncrement_memLp_two d i s t) (coordinateIncrement_memLp_two d j s t)]
  simp only [Pi.mul_apply]
  rw [coordinateIncrement_cross_mean d i j s t hst,coordinateIncrement_mean,coordinateIncrement_mean]
  simp only [zero_mul,sub_zero]

private theorem vectorIncrement_eq_equiv (d : ℕ) (s t : ℝ≥0) (ω : Sample d) :
    vectorIncrement d s t ω = (EuclideanSpace.equiv (Fin d) ℝ).symm
      (fun i => coordinateIncrement d i s t ω) := by
  apply (EuclideanSpace.equiv (Fin d) ℝ).injective
  rfl

/-- Entire Euclidean increment law is the native pushforward of the derived
product of Gaussian increment laws, with the actual Euclidean readout. -/
theorem vectorIncrement_hasLaw (d : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (vectorIncrement d s t)
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 (t-s))).map (EuclideanSpace.equiv (Fin d) ℝ).symm)
      (productLaw d) := by
  have hPi : HasLaw (fun ω : Sample d => fun i => coordinateIncrement d i s t ω)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (t-s))) (productLaw d) := by
    refine ⟨(measurable_pi_lambda _ (fun i => coordinateIncrement_measurable d i s t)).aemeasurable,?_⟩
    change (Measure.pi (fun _ : Fin d => sourceLaw)).map
      (fun ω => fun i => BrownianMartingaleSource.increment s t (ω i)) = _
    rw [Measure.pi_map_pi (fun _ : Fin d => (BrownianMartingaleSource.measurable_increment s t).aemeasurable)]
    simp_rw [(BrownianMartingaleSource.increment_hasLaw s t hst).map_eq]
  have hE : HasLaw (EuclideanSpace.equiv (Fin d) ℝ).symm
      ((Measure.pi (fun _ : Fin d => gaussianReal 0 (t-s))).map (EuclideanSpace.equiv (Fin d) ℝ).symm)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (t-s))) :=
    ⟨(EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.measurable.aemeasurable,rfl⟩
  apply (hE.comp hPi).congr
  exact ae_of_all _ (fun ω => vectorIncrement_eq_equiv d s t ω)

private theorem piIncrementPast_independent (d : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (fun ω : Sample d => fun i => BrownianMartingaleSource.increment s t (ω i))
      (fun ω : Sample d => fun i => fun r : Iic s => process r (ω i)) (productLaw d) := by
  let X : (ℝ≥0 → ℝ) → ℝ := BrownianMartingaleSource.increment s t
  let Y : (ℝ≥0 → ℝ) → (Iic s → ℝ) := fun ω r => process r ω
  have hX : Measurable X := BrownianMartingaleSource.measurable_increment s t
  have hY : Measurable Y := measurable_pi_lambda _ (fun r => measurable_process r)
  let ν := sourceLaw.map X
  let ρ := sourceLaw.map Y
  have hp : sourceLaw.map (fun ω => (X ω,Y ω)) = ν.prod ρ :=
    (BrownianMartingaleSource.increment_indep_past s t hst).map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hPi : (productLaw d).map (fun ω => fun i => (X (ω i),Y (ω i))) =
      Measure.pi (fun _ : Fin d => ν.prod ρ) := by
    change (Measure.pi (fun _ : Fin d => sourceLaw)).map (fun ω => fun i => (X (ω i),Y (ω i))) = _
    rw [Measure.pi_map_pi (fun _ : Fin d => (hX.prodMk hY).aemeasurable)]
    simp_rw [hp]
  let E := MeasurableEquiv.arrowProdEquivProdArrow ℝ (Iic s → ℝ) (Fin d)
  have hmap : (productLaw d).map (fun ω => ((fun i => X (ω i)),(fun i => Y (ω i)))) =
      (Measure.pi (fun _ : Fin d => ν)).prod (Measure.pi (fun _ : Fin d => ρ)) := by
    calc
      _ = ((productLaw d).map (fun ω => fun i => (X (ω i),Y (ω i)))).map E := by
        have hf : Measurable (fun ω : Sample d => fun i => (X (ω i),Y (ω i))) :=
          measurable_pi_lambda _ (fun i => (hX.prodMk hY).comp (measurable_pi_apply i))
        exact (Measure.map_map E.measurable hf).symm
      _ = (Measure.pi (fun _ : Fin d => ν.prod ρ)).map E := by rw [hPi]
      _ = _ := (measurePreserving_arrowProdEquivProdArrow ℝ (Iic s → ℝ) (Fin d)
        (fun _ => ν) (fun _ => ρ)).map_eq
  change IndepFun (fun ω : Sample d => fun i => X (ω i))
    (fun ω : Sample d => fun i => Y (ω i)) (productLaw d)
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun i => hX.comp (measurable_pi_apply i))).aemeasurable
    (measurable_pi_lambda _ (fun i => hY.comp (measurable_pi_apply i))).aemeasurable).mpr
  change (productLaw d).map (fun ω => ((fun i => X (ω i)),(fun i => Y (ω i)))) =
    ((productLaw d).map (fun ω => fun i => X (ω i))).prod
      ((productLaw d).map (fun ω => fun i => Y (ω i)))
  have hmX : (productLaw d).map (fun ω => fun i => X (ω i)) = Measure.pi (fun _ : Fin d => ν) :=
    Measure.pi_map_pi (fun _ : Fin d => hX.aemeasurable)
  have hmY : (productLaw d).map (fun ω => fun i => Y (ω i)) = Measure.pi (fun _ : Fin d => ρ) :=
    Measure.pi_map_pi (fun _ : Fin d => hY.aemeasurable)
  rw [hmX,hmY]
  exact hmap

/-- ALL coordinates at ALL past times; this is the actual joint visible past. -/
def jointPast (d : ℕ) (s : ℝ≥0) (ω : Sample d) (r : Iic s) : EuclideanSpace ℝ (Fin d) :=
  vectorProcess d r ω

theorem jointPast_measurable (d : ℕ) (s : ℝ≥0) : Measurable (jointPast d s) :=
  measurable_pi_lambda _ (fun r => vectorProcess_measurable d r)

/-- The complete future vector increment is independent of the ENTIRE joint
natural past. Product-law pairing, not own-coordinate independence alone,
supplies the cross-coordinate past permission. -/
theorem vectorIncrement_indep_jointPast (d : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (vectorIncrement d s t) (jointPast d s) (productLaw d) := by
  let F := (EuclideanSpace.equiv (Fin d) ℝ).symm
  let G : (Fin d → Iic s → ℝ) → Iic s → EuclideanSpace ℝ (Fin d) :=
    fun h r => F (fun i => h i r)
  have hG : Measurable G := by
    apply measurable_pi_lambda
    intro r
    exact F.continuous.measurable.comp (measurable_pi_lambda _
      (fun i => (measurable_pi_apply r).comp (measurable_pi_apply i)))
  have hi := (piIncrementPast_independent d s t hst).comp F.continuous.measurable hG
  have he : (F ∘ (fun ω : Sample d => fun i => BrownianMartingaleSource.increment s t (ω i))) =
      vectorIncrement d s t := by
    funext ω
    exact (vectorIncrement_eq_equiv d s t ω).symm
  rw [he] at hi
  exact hi

/-- Each future coordinate increment is independent of ALL coordinates' actual past. -/
theorem coordinateIncrement_indep_jointPast (d : ℕ) (i : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (coordinateIncrement d i s t) (jointPast d s) (productLaw d) := by
  have h := (vectorIncrement_indep_jointPast d s t hst).comp
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.measurable measurable_id
  exact h

/-- Original natural filtration generated by the actual Euclidean process. -/
def jointNaturalFiltration (d : ℕ) : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Sample d)) :=
  Filtration.natural (vectorProcess d) (fun t => (vectorProcess_measurable d t).stronglyMeasurable)

theorem vectorProcess_stronglyAdapted (d : ℕ) :
    StronglyAdapted (jointNaturalFiltration d) (vectorProcess d) :=
  Filtration.stronglyAdapted_natural (fun t => (vectorProcess_measurable d t).stronglyMeasurable)

theorem coordinateIncrement_indep_jointNatural (d : ℕ) (i : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (coordinateIncrement d i s t) inferInstance)
      (jointNaturalFiltration d s) (productLaw d) := by
  rw [jointNaturalFiltration,Filtration.natural_eq_comap]
  exact coordinateIncrement_indep_jointPast d i s t hst


theorem vectorIncrement_measurable (d : ℕ) (s t : ℝ≥0) :
    Measurable (vectorIncrement d s t) :=
  (vectorProcess_measurable d t).sub (vectorProcess_measurable d s)

theorem vectorIncrement_indep_jointNatural (d : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (vectorIncrement d s t) inferInstance)
      (jointNaturalFiltration d s) (productLaw d) := by
  rw [jointNaturalFiltration,Filtration.natural_eq_comap]
  exact vectorIncrement_indep_jointPast d s t hst

/-- All conditional-moment consumers below are integrable under the SAME product law. -/
theorem coordinateIncrement_integrable (d : ℕ) (i : Fin d) (s t : ℝ≥0) :
    Integrable (coordinateIncrement d i s t) (productLaw d) :=
  (coordinateIncrement_memLp_two d i s t).integrable (by norm_num)

theorem coordinateIncrement_product_integrable (d : ℕ) (i j : Fin d) (s t : ℝ≥0) :
    Integrable (fun ω => coordinateIncrement d i s t ω * coordinateIncrement d j s t ω)
      (productLaw d) :=
  (coordinateIncrement_memLp_two d i s t).integrable_mul (coordinateIncrement_memLp_two d j s t)

/-- This zero mean is conditional on the ENTIRE joint natural past. -/
theorem coordinateIncrement_condExp (d : ℕ) (i : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    (productLaw d)[coordinateIncrement d i s t | jointNaturalFiltration d s] =ᵐ[productLaw d]
      fun _ => (0 : ℝ) := by
  have hm : @Measurable (Sample d) ℝ
      (MeasurableSpace.comap (coordinateIncrement d i s t) inferInstance) inferInstance
      (coordinateIncrement d i s t) := measurable_iff_comap_le.mpr le_rfl
  have h := condExp_indep_eq (coordinateIncrement_measurable d i s t).comap_le
    ((jointNaturalFiltration d).le s) hm.stronglyMeasurable
    (coordinateIncrement_indep_jointNatural d i s t hst)
  simpa only [coordinateIncrement_mean] using h

/-- The conditional covariance matrix is derived from actual vector independence;
no coordinate is allowed to condition on another coordinate's future. -/
theorem coordinateIncrement_condExp_product (d : ℕ) (i j : Fin d) (s t : ℝ≥0) (hst : s ≤ t) :
    (productLaw d)[fun ω => coordinateIncrement d i s t ω * coordinateIncrement d j s t ω |
      jointNaturalFiltration d s] =ᵐ[productLaw d]
      fun _ => if i = j then (t : ℝ)-(s : ℝ) else 0 := by
  let φ : EuclideanSpace ℝ (Fin d) → ℝ := fun z => z i * z j
  have hφ : Measurable φ :=
    (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.measurable.mul
      (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable
  have hm : @Measurable (Sample d) (EuclideanSpace ℝ (Fin d))
      (MeasurableSpace.comap (vectorIncrement d s t) inferInstance) inferInstance
      (vectorIncrement d s t) := measurable_iff_comap_le.mpr le_rfl
  have h := condExp_indep_eq (vectorIncrement_measurable d s t).comap_le
    ((jointNaturalFiltration d).le s) (hφ.comp hm).stronglyMeasurable
    (vectorIncrement_indep_jointNatural d s t hst)
  change (productLaw d)[fun ω => coordinateIncrement d i s t ω * coordinateIncrement d j s t ω |
    jointNaturalFiltration d s] =ᵐ[productLaw d] fun _ =>
    ∫ ω, coordinateIncrement d i s t ω * coordinateIncrement d j s t ω ∂productLaw d at h
  simpa only [coordinateIncrement_cross_mean d i j s t hst] using h

/-- Dimension zero is a legitimate product probability source with zero Euclidean output. -/
theorem vectorProcess_zero_dimension (t : ℝ≥0) (ω : Sample 0) : vectorProcess 0 t ω = 0 :=
  Subsingleton.elim _ _

theorem vectorIncrement_zero_dimension (s t : ℝ≥0) (ω : Sample 0) :
    vectorIncrement 0 s t ω = 0 := Subsingleton.elim _ _

/-- Two independent nondegenerate coordinates have Euclidean unit-time energy two. -/
theorem two_dimensional_unit_energy :
    (∫ ω, ‖vectorIncrement 2 0 1 ω‖ ^ 2 ∂productLaw 2) = 2 := by
  simpa using vectorIncrement_energy 2 0 1 (by norm_num)

theorem two_dimensional_unit_cross_covariance :
    cov[coordinateIncrement 2 0 0 1,coordinateIncrement 2 1 0 1;productLaw 2] = 0 := by
  simpa using coordinateIncrement_covariance 2 0 1 0 1 (by norm_num)

theorem two_dimensional_unit_variance :
    cov[coordinateIncrement 2 0 0 1,coordinateIncrement 2 0 0 1;productLaw 2] = 1 := by
  simpa using coordinateIncrement_covariance 2 0 0 0 1 (by norm_num)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteProductSource
