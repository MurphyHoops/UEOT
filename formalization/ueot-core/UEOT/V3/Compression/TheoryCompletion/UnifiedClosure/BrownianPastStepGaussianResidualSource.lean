import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepTiltKernelSource

/-!
Original commitment: full random-START Girsanov requires joint residual/past independence, not separate pairwise assertions.
Existing result: actual random-coefficient Gaussian fiber recentering, whole START conditional normalization and endpoint noise law.
Premise reduced: derive SAME finite Brownian residual vector jointly independent of the one-block increment together with arbitrary real START coefficient H.
Model/witness: original B/sourceLaw/Fa, a<b, arbitrary finite time set incl before/inside/after interval; H only originalFa measurable, need not be Gaussian.
Consumer: exact full finite law of B_t-H*(min(t,b)-min(t,a)) under same Q; path/filtration transport follows separately.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepGaussianResidualSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianPastStepExponentialSource BrownianPastStepTiltKernelSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def overlap (a b t : ℝ≥0) : ℝ := (min t b : ℝ≥0)-(min t a : ℝ≥0)

def coefficient (a b t : ℝ≥0) : ℝ := overlap a b t/((b : ℝ)-(a : ℝ))

def residual (a b t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ := process t ω-coefficient a b t*increment a b ω

def residualVector (a b : ℝ≥0) (I : Finset ℝ≥0) (ω : ℝ≥0 → ℝ) : I → ℝ := fun i => residual a b i ω

private theorem process_memLp_two (t : ℝ≥0) : MemLp (process t) 2 sourceLaw :=
  (process_isPreBrownian.hasLaw_eval t).hasGaussianLaw.memLp_two

private theorem increment_memLp_two (a b : ℝ≥0) : MemLp (increment a b) 2 sourceLaw :=
  (process_isPreBrownian.hasLaw_sub b a).hasGaussianLaw.memLp_two

theorem residual_measurable (a b t : ℝ≥0) : Measurable (residual a b t) :=
  (measurable_process t).sub (measurable_const.mul (measurable_increment a b))

theorem residualVector_measurable (a b : ℝ≥0) (I : Finset ℝ≥0) : Measurable (residualVector a b I) :=
  measurable_pi_lambda _ (fun i => residual_measurable a b i)

/-- Covariance of actual observations with the original one-block noise. -/
theorem observation_increment_covariance (a b t : ℝ≥0) :
    cov[process t,increment a b;sourceLaw]=overlap a b t := by
  change cov[process t,fun ω => process b ω-process a ω;sourceLaw]=overlap a b t
  rw [covariance_fun_sub_right (process_memLp_two t) (process_memLp_two b) (process_memLp_two a),
    process_isPreBrownian.covariance_eval,process_isPreBrownian.covariance_eval]
  rfl

theorem residual_increment_covariance (a b t : ℝ≥0) (hab : a < b) :
    cov[residual a b t,increment a b;sourceLaw]=0 := by
  have hv : cov[increment a b,increment a b;sourceLaw]=(b : ℝ)-(a : ℝ) := by
    rw [covariance_self (measurable_increment a b).aemeasurable,(increment_hasLaw a b hab.le).variance_eq,variance_id_gaussianReal,NNReal.coe_sub hab.le]
  change cov[fun ω => process t ω-coefficient a b t*increment a b ω,increment a b;sourceLaw]=0
  rw [covariance_fun_sub_left (process_memLp_two t) ((increment_memLp_two a b).const_mul _) (increment_memLp_two a b),
    observation_increment_covariance,covariance_const_mul_left,hv]
  have hd : (b : ℝ)-(a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (a : ℝ)<(b : ℝ) from hab))
  unfold coefficient
  field_simp [hd]
  ring

/-- Native Gaussian-process witness for the increment and the COMBINED
finite residual observations plus ENTIRE original START past. -/
private theorem jointGaussian (a b : ℝ≥0) (I : Finset ℝ≥0) :
    IsGaussianProcess (Sum.elim (fun _ : Unit => increment a b)
      (Sum.elim (fun i : I => residual a b i) (fun r : Iic a => process r))) sourceLaw := by
  classical
  apply process_isPreBrownian.isGaussianProcess.of_isGaussianProcess
  rintro (_ | (i | r))
  · exact ⟨{a,b},
      { toFun x := x ⟨b,by simp⟩-x ⟨a,by simp⟩
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring },fun _ => rfl⟩
  · exact ⟨{(i : ℝ≥0),a,b},
      { toFun x := x ⟨i,by simp⟩-coefficient a b i*(x ⟨b,by simp⟩-x ⟨a,by simp⟩)
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring },fun _ => rfl⟩
  · exact ⟨{(r : ℝ≥0)},
      { toFun x := x ⟨r,by simp⟩
        map_add' x y := rfl
        map_smul' c x := rfl },fun _ => rfl⟩

/-- The supplied H may be a nonlinear observable of the ENTIRE START past.
It is not assumed jointly Gaussian: Gaussian independence is proved first
for residual+past, then restricted through the actual measurable H. -/
theorem residual_coefficient_indep_increment (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a < b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (I : Finset ℝ≥0) :
    IndepFun (fun ω => (residualVector a b I ω,H ω)) (increment a b) sourceLaw := by
  let Z : Sum I (Iic a) → (ℝ≥0 → ℝ) → ℝ := Sum.elim (fun i : I => residual a b i) (fun r : Iic a => process r)
  have hG := jointGaussian a b I
  have hi := hG.indepFun_of_covariance_eq_zero
    (fun _ => (measurable_increment a b).aemeasurable)
    (fun q => by cases q with
      | inl i => exact (residual_measurable a b i).aemeasurable
      | inr r => exact (measurable_process r).aemeasurable) (fun _ q => by
        cases q with
        | inl i => exact (covariance_comm _ _).trans (residual_increment_covariance a b i hab)
        | inr r =>
          change cov[increment a b,process r;sourceLaw]=0
          rw [covariance_comm,observation_increment_covariance]
          unfold overlap
          rw [min_eq_left (r.property.trans hab.le),min_eq_left r.property]
          simp)
  have hzind : IndepFun (increment a b) (fun ω q => Z q ω) sourceLaw :=
    hi.comp (measurable_pi_apply ()) measurable_id
  let mZ := MeasurableSpace.comap (fun ω q => Z q ω) inferInstance
  have hmZ : @Measurable (ℝ≥0 → ℝ) (Sum I (Iic a) → ℝ) mZ inferInstance (fun ω q => Z q ω) :=
    measurable_iff_comap_le.mpr le_rfl
  have hR : @Measurable (ℝ≥0 → ℝ) (I → ℝ) mZ inferInstance (residualVector a b I) :=
    measurable_pi_lambda _ (fun i => (measurable_pi_apply (Sum.inl i)).comp hmZ)
  have hPast : @Measurable (ℝ≥0 → ℝ) (Iic a → ℝ) mZ inferInstance (fun ω r => process r ω) :=
    measurable_pi_lambda _ (fun r => (measurable_pi_apply (Sum.inr r)).comp hmZ)
  have hStart : naturalFiltration a ≤ mZ := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact hPast.comap_le
  have hX : @Measurable (ℝ≥0 → ℝ) ((I → ℝ) × ℝ) mZ inferInstance (fun ω => (residualVector a b I ω,H ω)) :=
    hR.prodMk (hH.measurable.mono hStart le_rfl)
  have hI : Indep (MeasurableSpace.comap (increment a b) inferInstance) mZ sourceLaw := hzind
  exact (indep_of_indep_of_le_right hI hX.comap_le).symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepGaussianResidualSource
