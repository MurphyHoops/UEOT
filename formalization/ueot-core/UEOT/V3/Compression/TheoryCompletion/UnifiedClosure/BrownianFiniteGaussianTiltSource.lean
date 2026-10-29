import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianGaussianTiltSource

/-!
Original commitment: one tilted endpoint does not establish a true shifted Brownian process under Q.
Existing result: SAME actual terminal exponential measure and exact centered Gaussian Esscher identity.
Premise reduced: derive all finite shifted path laws using actual finite Gaussian regression and independent residuals.
Model/witness: W_t=B_t-u*min(t,T) on SAME path space, actual tiltedLaw u T, every finite time set, including times after T.
Consumer: actual constant-control Girsanov source and originalFt transport; general predictable-control change of measure remains separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteGaussianTiltSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianGaussianTiltSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- The actual finite-horizon tilt shifts drift only through the horizon. -/
def shiftedProcess (u : ℝ) (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  process t ω-u*(min t T : ℝ≥0)

def regressionCoefficient (T t : ℝ≥0) : ℝ := (min t T : ℝ≥0)/(T : ℝ)

def regressionResidual (T t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  process t ω-regressionCoefficient T t*process T ω

def residualVector (T : ℝ≥0) (I : Finset ℝ≥0) (ω : ℝ≥0 → ℝ) : I → ℝ :=
  fun i => regressionResidual T i ω

theorem residualVector_measurable (T : ℝ≥0) (I : Finset ℝ≥0) : Measurable (residualVector T I) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_process i).sub (measurable_const.mul (measurable_process T))

/-- Actual jointly Gaussian residual vector and terminal coordinate. -/
theorem residual_terminal_jointGaussian (T : ℝ≥0) (I : Finset ℝ≥0) :
    HasGaussianLaw (fun ω => (residualVector T I ω,fun _ : Unit => process T ω)) sourceLaw := by
  classical
  let J := insert T I
  let ind (i : I) : J := ⟨i,by simp [J,i.property]⟩
  let last : J := ⟨T,by simp [J]⟩
  let L : (J → ℝ) →L[ℝ] ((I → ℝ) × (Unit → ℝ)) :=
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (ind i)-
      regressionCoefficient T i • ContinuousLinearMap.proj last)).prod
      (ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.proj last))
  have h := (process_isPreBrownian.isGaussianProcess.hasGaussianLaw J).map L
  exact h

/-- Gaussian regression is independent of the actual terminal Brownian
coordinate, for the ENTIRE supplied finite residual vector. -/
theorem residual_indep_terminal (T : ℝ≥0) (hT : T ≠ 0) (I : Finset ℝ≥0) :
    IndepFun (residualVector T I) (process T) sourceLaw := by
  have hcov (i : I) (j : Unit) : cov[regressionResidual T i,fun ω => process T ω;sourceLaw]=0 := by
    have hi : MemLp (process i) 2 sourceLaw := (process_isPreBrownian.hasLaw_eval i).hasGaussianLaw.memLp_two
    have ht : MemLp (process T) 2 sourceLaw := (process_isPreBrownian.hasLaw_eval T).hasGaussianLaw.memLp_two
    change cov[fun ω => process i ω-regressionCoefficient T i*process T ω,process T;sourceLaw]=0
    rw [covariance_fun_sub_left hi (ht.const_mul _) ht,covariance_const_mul_left,
      process_isPreBrownian.covariance_eval,process_isPreBrownian.covariance_eval,min_self]
    have hn : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    unfold regressionCoefficient
    field_simp [hn]
    ring
  have h := (residual_terminal_jointGaussian T I).indepFun_of_covariance_eval hcov
  exact h.comp measurable_id (measurable_pi_apply ())

/-- The actual tilted joint law is the original residual law times the
actual shifted Gaussian terminal law, by native product-withDensity. -/
theorem tilted_residual_terminal_map (u : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (I : Finset ℝ≥0) :
    (tiltedLaw u T).map (fun ω => (residualVector T I ω,process T ω)) =
      (sourceLaw.map (residualVector T I)).prod (gaussianReal (u*(T : ℝ)) T) := by
  change (sourceLaw.withDensity (fun ω => gaussianTiltWeight u T (process T ω))).map
    (fun ω => (residualVector T I ω,process T ω)) = _
  rw [map_readout_density sourceLaw _ ((residualVector_measurable T I).prodMk (measurable_process T))
    (fun p : (I → ℝ) × ℝ => gaussianTiltWeight u T p.2) (by unfold gaussianTiltWeight; fun_prop)]
  rw [(residual_indep_terminal T hT I).map_prod_eq_prod_map_map
    (residualVector_measurable T I).aemeasurable (measurable_process T).aemeasurable]
  rw [← prod_withDensity_right (by unfold gaussianTiltWeight; fun_prop),
    (process_isPreBrownian.hasLaw_eval T).map_eq,gaussian_exponential_tilt]

/-- Actual joint law after recentering the SAME terminal coordinate is the
original joint law, with the full residual vector retained. -/
theorem tilted_centered_joint_map (u : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (I : Finset ℝ≥0) :
    (tiltedLaw u T).map (fun ω => (residualVector T I ω,process T ω-u*(T : ℝ))) =
      sourceLaw.map (fun ω => (residualVector T I ω,process T ω)) := by
  have hm : (fun ω => (residualVector T I ω,process T ω-u*(T : ℝ))) =
      Prod.map id (fun y : ℝ => y-u*(T : ℝ)) ∘ (fun ω => (residualVector T I ω,process T ω)) := rfl
  rw [hm,← Measure.map_map (by fun_prop) ((residualVector_measurable T I).prodMk (measurable_process T)),
    tilted_residual_terminal_map u T hT I,
    ← Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id,
    gaussianReal_map_sub_const,sub_self]
  have h := (residual_indep_terminal T hT I).map_prod_eq_prod_map_map
    (residualVector_measurable T I).aemeasurable (measurable_process T).aemeasurable
  rw [(process_isPreBrownian.hasLaw_eval T).map_eq] at h
  exact h.symm

/-- The ENTIRE caller-supplied finite shifted-coordinate table has exactly
the original Brownian law under the actual changed measure. The set may
contain zero and times below or above the density horizon; arbitrary finite readouts follow by mapping. -/
theorem shifted_finite_map (u : ℝ) (T : ℝ≥0) (hT : T ≠ 0) (I : Finset ℝ≥0) :
    (tiltedLaw u T).map (fun ω => I.restrict (shiftedProcess u T · ω)) =
      sourceLaw.map (fun ω => I.restrict (process · ω)) := by
  let F : (I → ℝ) × ℝ → I → ℝ := fun p i => p.1 i+regressionCoefficient T i*p.2
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply i).comp measurable_fst).add (measurable_const.mul measurable_snd)
  have h := congrArg (fun μ : Measure ((I → ℝ) × ℝ) => μ.map F) (tilted_centered_joint_map u T hT I)
  have hmc : Measurable (fun ω => (residualVector T I ω,process T ω-u*(T : ℝ))) :=
    (residualVector_measurable T I).prodMk ((measurable_process T).sub measurable_const)
  have hmb : Measurable (fun ω => (residualVector T I ω,process T ω)) :=
    (residualVector_measurable T I).prodMk (measurable_process T)
  rw [Measure.map_map hF hmc,Measure.map_map hF hmb] at h
  have hleft : F ∘ (fun ω => (residualVector T I ω,process T ω-u*(T : ℝ))) =
      fun ω => I.restrict (shiftedProcess u T · ω) := by
    funext ω i
    change process i ω-regressionCoefficient T i*process T ω+
      regressionCoefficient T i*(process T ω-u*(T : ℝ)) = process i ω-u*(min (i : ℝ≥0) T : ℝ≥0)
    have hn : (T : ℝ) ≠ 0 := by exact_mod_cast hT
    unfold regressionCoefficient
    field_simp [hn]
    ring
  have hright : F ∘ (fun ω => (residualVector T I ω,process T ω)) =
      fun ω => I.restrict (process · ω) := by
    funext ω i
    change process i ω-regressionCoefficient T i*process T ω+regressionCoefficient T i*process T ω=process i ω
    ring
  rw [hleft,hright] at h
  exact h

theorem shiftedProcess_measurable (u : ℝ) (T t : ℝ≥0) : Measurable (shiftedProcess u T t) :=
  (measurable_process t).sub measurable_const

/-- Actual full pre-Brownian source under Q, for ALL nonnegative times,
including times beyond the original finite density horizon. -/
theorem shiftedProcess_isPreBrownian (u : ℝ) (T : ℝ≥0) :
    IsPreBrownianReal (shiftedProcess u T) (tiltedLaw u T) := by
  constructor
  intro I
  have hr : Measurable (fun ω => I.restrict (shiftedProcess u T · ω)) :=
    measurable_pi_lambda _ (fun (i : I) => shiftedProcess_measurable u T i)
  refine ⟨hr.aemeasurable,?_⟩
  by_cases hT : T=0
  · subst T
    rw [tiltedLaw_zero]
    simpa only [shiftedProcess,min_zero,NNReal.coe_zero,mul_zero,sub_zero] using (process_isPreBrownian.hasLaw I).map_eq
  · exact (shifted_finite_map u T hT I).trans (process_isPreBrownian.hasLaw I).map_eq

/-- Continuity is retained by the SAME actual process and deterministic
clipped drift, so finite laws upgrade to actual Brownian motion under Q. -/
theorem shiftedProcess_isBrownian (u : ℝ) (T : ℝ≥0) :
    IsBrownianReal (shiftedProcess u T) (tiltedLaw u T) := by
  refine ⟨shiftedProcess_isPreBrownian u T,Eventually.of_forall (fun ω => ?_)⟩
  exact (process_continuous ω).sub (continuous_const.mul (continuous_subtype_val.comp (continuous_id.min continuous_const)))

/-- Physical drift is u*t exactly through the density horizon, and then
stays u*T. This theorem makes the finite-horizon scope explicit. -/
theorem shiftedProcess_before (u : ℝ) (T t : ℝ≥0) (ht : t ≤ T) (ω : ℝ≥0 → ℝ) :
    shiftedProcess u T t ω=process t ω-u*(t : ℝ) := by rw [shiftedProcess,min_eq_left ht]

theorem shiftedProcess_after (u : ℝ) (T t : ℝ≥0) (ht : T ≤ t) (ω : ℝ≥0 → ℝ) :
    shiftedProcess u T t ω=process t ω-u*(T : ℝ) := by rw [shiftedProcess,min_eq_right ht]

/-- Shifted future noise is independent of the ENTIRE ORIGINAL natural
past, transported by the exact deterministic shift of every past coordinate. -/
theorem shifted_indep_original_past (u : ℝ) (T s : ℝ≥0) :
    IndepFun (fun ω r => shiftedProcess u T (s+r) ω-shiftedProcess u T s ω)
      (fun ω (r : Iic s) => process r ω) (tiltedLaw u T) := by
  have hm : Measurable (fun f : Iic s → ℝ => fun r => f r+u*(min (r : ℝ≥0) T : ℝ≥0)) := by
    apply measurable_pi_lambda
    intro r
    exact (measurable_pi_apply r).add measurable_const
  have h := ((shiftedProcess_isPreBrownian u T).indepFun_shift s).comp measurable_id hm
  simpa only [Function.comp_def,id_eq,shiftedProcess,sub_add_cancel] using h

def shiftedIncrement (u : ℝ) (T s t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  shiftedProcess u T t ω-shiftedProcess u T s ω

theorem shiftedIncrement_measurable (u : ℝ) (T s t : ℝ≥0) : Measurable (shiftedIncrement u T s t) :=
  (shiftedProcess_measurable u T t).sub (shiftedProcess_measurable u T s)

theorem shiftedIncrement_indep_original_past (u : ℝ) (T s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (shiftedIncrement u T s t) (fun ω (r : Iic s) => process r ω) (tiltedLaw u T) := by
  have h := (shifted_indep_original_past u T s).comp (measurable_pi_apply (t-s)) measurable_id
  have hs : s+(t-s)=t := add_tsub_cancel_of_le hst
  change IndepFun (fun ω => shiftedProcess u T (s+(t-s)) ω-shiftedProcess u T s ω)
    (fun ω (r : Iic s) => process r ω) (tiltedLaw u T) at h
  rw [hs] at h
  exact h

/-- Original F_t permissions are retained; there is no enlarged or
future-dependent filtration introduced by the change of measure. -/
theorem shiftedProcess_stronglyAdapted (u : ℝ) (T : ℝ≥0) :
    StronglyAdapted naturalFiltration (shiftedProcess u T) := by
  intro t
  exact (process_stronglyAdapted t).sub stronglyMeasurable_const

theorem condExp_shiftedIncrement (u : ℝ) (T s t : ℝ≥0) (hst : s ≤ t) :
    (tiltedLaw u T)[shiftedIncrement u T s t | naturalFiltration s] =ᵐ[tiltedLaw u T] fun _ => 0 := by
  have hi : Indep (MeasurableSpace.comap (shiftedIncrement u T s t) inferInstance)
      (naturalFiltration s) (tiltedLaw u T) := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact shiftedIncrement_indep_original_past u T s t hst
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ
      (MeasurableSpace.comap (shiftedIncrement u T s t) inferInstance) inferInstance (shiftedIncrement u T s t) :=
    measurable_iff_comap_le.mpr le_rfl
  have hc := condExp_indep_eq (shiftedIncrement_measurable u T s t).comap_le (naturalFiltration.le s)
    hm.stronglyMeasurable hi
  have hW := shiftedProcess_isPreBrownian u T
  have he : (∫ ω, shiftedIncrement u T s t ω ∂tiltedLaw u T)=0 := by
    change (∫ ω, shiftedProcess u T t ω-shiftedProcess u T s ω ∂tiltedLaw u T)=0
    rw [integral_sub (hW.integrable_eval t) (hW.integrable_eval s),hW.integral_eval,hW.integral_eval,sub_self]
  exact hc.trans (Eventually.of_forall (fun _ => he))

/-- Actual shifted Brownian is a martingale under the SAME original F_t
and the actual exponential changed measure. -/
theorem shiftedProcess_martingale (u : ℝ) (T : ℝ≥0) :
    Martingale (shiftedProcess u T) naturalFiltration (tiltedLaw u T) := by
  refine ⟨shiftedProcess_stronglyAdapted u T,fun s t hst => ?_⟩
  have hW := shiftedProcess_isPreBrownian u T
  have hi : Integrable (shiftedIncrement u T s t) (tiltedLaw u T) :=
    (hW.integrable_eval t).sub (hW.integrable_eval s)
  have he : shiftedProcess u T t = shiftedIncrement u T s t+shiftedProcess u T s := by
    funext ω
    simp only [shiftedIncrement,Pi.add_apply,sub_add_cancel]
  rw [he]
  have hc := condExp_add hi (hW.integrable_eval s) (naturalFiltration s)
  have hp := condExp_of_stronglyMeasurable (naturalFiltration.le s) (shiftedProcess_stronglyAdapted u T s) (hW.integrable_eval s)
  apply hc.trans
  rw [hp]
  filter_upwards [condExp_shiftedIncrement u T s t hst] with ω hω
  simp only [Pi.add_apply,hω,zero_add]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteGaussianTiltSource
