import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepGaussianResidualSource

/-!
Original commitment: random START feedback needs a true whole shifted Brownian source under its actual Q.
Existing result: actual conditional normalization and joint Gaussian residual-vector/START-coefficient independence with fiber Esscher recentering.
Premise reduced: derive complete finite shifted path laws and actual continuous Brownian source, with literal pre-START identity and clipped postinterval drift.
Model/witness: SAME B/sourceLaw/Q, H originalFa measurable, a<=b, W_t=B_t-H*(min(t,b)-min(t,a)), all nonnegative times.
Consumer: one-step actual originalFt Girsanov/TerminalGirsanovData; finite/simple/general predictable controls remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepShiftedSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianPastStepExponentialSource BrownianPastStepTiltKernelSource BrownianPastStepGaussianResidualSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

def shiftedProcess (H : (ℝ≥0 → ℝ) → ℝ) (a b t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  process t ω-H ω*overlap a b t

/-- Exact full finite-law transport uses the actual joint residual+H,
not separate pairwise independence and not a newly selected control. -/
theorem shifted_finite_map (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a < b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (I : Finset ℝ≥0) :
    (stepLaw H a b).map (fun ω => I.restrict (shiftedProcess H a b · ω)) =
      sourceLaw.map (fun ω => I.restrict (process · ω)) := by
  let X := fun ω => (residualVector a b I ω,H ω)
  have hX : Measurable X := (residualVector_measurable a b I).prodMk (hH.mono (naturalFiltration.le a)).measurable
  have h := independent_gaussian_random_tilt_joint sourceLaw X hX (increment a b) (measurable_increment a b) (b-a)
    (increment_hasLaw a b hab.le) (residual_coefficient_indep_increment H a b hab hH I) Prod.snd measurable_snd
  change (stepLaw H a b).map (fun ω => ((residualVector a b I ω,H ω),increment a b ω-H ω*((b-a : ℝ≥0) : ℝ))) =
    sourceLaw.map (fun ω => ((residualVector a b I ω,H ω),increment a b ω)) at h
  let F : ((I → ℝ) × ℝ) × ℝ → I → ℝ := fun p i => p.1.1 i+coefficient a b i*p.2
  have hF : Measurable F := by
    apply measurable_pi_lambda
    intro i
    exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).add (measurable_const.mul measurable_snd)
  have hmL : Measurable (fun ω => ((residualVector a b I ω,H ω),increment a b ω-H ω*((b-a : ℝ≥0) : ℝ))) :=
    hX.prodMk ((measurable_increment a b).sub ((hH.mono (naturalFiltration.le a)).measurable.mul_const _))
  have hmR : Measurable (fun ω => ((residualVector a b I ω,H ω),increment a b ω)) := hX.prodMk (measurable_increment a b)
  have hh := congrArg (fun μ : Measure (((I → ℝ) × ℝ) × ℝ) => μ.map F) h
  rw [Measure.map_map hF hmL,Measure.map_map hF hmR] at hh
  have hl : F ∘ (fun ω => ((residualVector a b I ω,H ω),increment a b ω-H ω*((b-a : ℝ≥0) : ℝ))) =
      fun ω => I.restrict (shiftedProcess H a b · ω) := by
    funext ω i
    change process i ω-coefficient a b i*increment a b ω+
      coefficient a b i*(increment a b ω-H ω*((b-a : ℝ≥0) : ℝ))=process i ω-H ω*overlap a b i
    rw [NNReal.coe_sub hab.le]
    have hd : (b : ℝ)-(a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (show (a : ℝ)<(b : ℝ) from hab))
    unfold coefficient
    field_simp [hd]
    ring
  have hr : F ∘ (fun ω => ((residualVector a b I ω,H ω),increment a b ω))=
      fun ω => I.restrict (process · ω) := by
    funext ω i
    change process i ω-coefficient a b i*increment a b ω+coefficient a b i*increment a b ω=process i ω
    ring
  rw [hl,hr] at hh
  exact hh

theorem shiftedProcess_measurable (H : (ℝ≥0 → ℝ) → ℝ) (a b t : ℝ≥0)
    (hH : StronglyMeasurable[naturalFiltration a] H) : Measurable (shiftedProcess H a b t) :=
  (measurable_process t).sub ((hH.mono (naturalFiltration.le a)).measurable.mul_const _)

/-- Actual full source finite laws, including times before START and after
END; same-time case uses the literal unchanged measure and drift. -/
theorem shiftedProcess_isPreBrownian (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    IsPreBrownianReal (shiftedProcess H a b) (stepLaw H a b) := by
  constructor
  intro I
  have hm : Measurable (fun ω => I.restrict (shiftedProcess H a b · ω)) :=
    measurable_pi_lambda _ (fun i => shiftedProcess_measurable H a b i hH)
  refine ⟨hm.aemeasurable,?_⟩
  rcases hab.eq_or_lt with h | h
  · subst b
    rw [stepLaw_same_time]
    simpa only [shiftedProcess,overlap,sub_self,mul_zero,sub_zero] using (process_isPreBrownian.hasLaw I).map_eq
  · exact (shifted_finite_map H a b h hH I).trans (process_isPreBrownian.hasLaw I).map_eq

theorem overlap_continuous (a b : ℝ≥0) : Continuous (overlap a b) :=
  (continuous_subtype_val.comp (continuous_id.min continuous_const)).sub
    (continuous_subtype_val.comp (continuous_id.min continuous_const))

/-- Genuinely continuous Brownian motion under the actual random-feedback Q. -/
theorem shiftedProcess_isBrownian (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    IsBrownianReal (shiftedProcess H a b) (stepLaw H a b) := by
  refine ⟨shiftedProcess_isPreBrownian H a b hab hH,Eventually.of_forall (fun ω => ?_)⟩
  exact (process_continuous ω).sub (continuous_const.mul (overlap_continuous a b))

/-- Before START the future coefficient term is LITERALLY zero: no access
to H is needed at these times, on any sample. -/
theorem shiftedProcess_before (H : (ℝ≥0 → ℝ) → ℝ) (a b t : ℝ≥0) (hab : a ≤ b) (ht : t ≤ a) (ω : ℝ≥0 → ℝ) :
    shiftedProcess H a b t ω=process t ω := by
  simp only [shiftedProcess,overlap,min_eq_left (ht.trans hab),min_eq_left ht,sub_self,mul_zero,sub_zero]

theorem shiftedProcess_after (H : (ℝ≥0 → ℝ) → ℝ) (a b t : ℝ≥0) (hab : a ≤ b) (ht : b ≤ t) (ω : ℝ≥0 → ℝ) :
    shiftedProcess H a b t ω=process t ω-H ω*((b : ℝ)-(a : ℝ)) := by
  simp only [shiftedProcess,overlap,min_eq_right ht,min_eq_right (hab.trans ht)]

/-- SAME original natural filtration permissions: H is used only at or
after its actual START, and is never granted a future observation permission. -/
theorem shiftedProcess_stronglyAdapted (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) : StronglyAdapted naturalFiltration (shiftedProcess H a b) := by
  intro t
  by_cases ht : t ≤ a
  · have he : shiftedProcess H a b t=process t := funext (shiftedProcess_before H a b t hab ht)
    rw [he]
    exact process_stronglyAdapted t
  · exact (process_stronglyAdapted t).sub ((hH.mono (naturalFiltration.mono (le_of_not_ge ht))).mul stronglyMeasurable_const)

/-- Actual natural filtration of the constructed shifted process. -/
def shiftedNatural (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
  Filtration.natural (shiftedProcess H a b) (fun t => (shiftedProcess_measurable H a b t hH).stronglyMeasurable)

private theorem shiftedNatural_adapted (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    StronglyAdapted (shiftedNatural H a b hH) (shiftedProcess H a b) :=
  Filtration.stronglyAdapted_natural (fun t => (shiftedProcess_measurable H a b t hH).stronglyMeasurable)

/-- START sigma is exactly unchanged, because the original readout is
literally unchanged at EVERY time through START. -/
theorem start_filtration_eq (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) : shiftedNatural H a b hH a=naturalFiltration a := by
  rw [shiftedNatural,Filtration.natural_eq_comap,naturalFiltration,Filtration.natural_eq_comap]
  congr 1
  funext ω r
  exact shiftedProcess_before H a b r hab r.property ω

private theorem originalProcess_adapted_shiftedNatural (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) : StronglyAdapted (shiftedNatural H a b hH) process := by
  have hs : StronglyMeasurable[shiftedNatural H a b hH a] H := by rw [start_filtration_eq H a b hab hH]; exact hH
  intro t
  by_cases ht : t ≤ a
  · have he : process t=shiftedProcess H a b t := funext (fun ω => (shiftedProcess_before H a b t hab ht ω).symm)
    rw [he]
    exact shiftedNatural_adapted H a b hH t
  · have hh := hs.mono ((shiftedNatural H a b hH).mono (le_of_not_ge ht))
    have he : process t=fun ω => shiftedProcess H a b t ω+H ω*overlap a b t := by
      funext ω
      unfold shiftedProcess
      ring
    rw [he]
    exact (shiftedNatural_adapted H a b hH t).add (hh.mul stronglyMeasurable_const)

/-- Exact ORIGINAL filtration identity, proved in both directions from
actual permissions. Adaptedness alone is not used to claim this equality. -/
theorem shiftedNatural_eq_original (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) : shiftedNatural H a b hH=naturalFiltration := by
  apply Filtration.ext
  funext t
  apply le_antisymm
  · change (⨆ (j : ℝ≥0) (_ : j ≤ t),MeasurableSpace.comap (shiftedProcess H a b j) inferInstance) ≤ naturalFiltration t
    refine iSup₂_le (fun j hj => ?_)
    exact ((shiftedProcess_stronglyAdapted H a b hab hH j).mono (naturalFiltration.mono hj)).measurable.comap_le
  · change (⨆ (j : ℝ≥0) (_ : j ≤ t),MeasurableSpace.comap (process j) inferInstance) ≤ shiftedNatural H a b hH t
    refine iSup₂_le (fun j hj => ?_)
    exact ((originalProcess_adapted_shiftedNatural H a b hab hH j).mono
      ((shiftedNatural H a b hH).mono hj)).measurable.comap_le

/-- Future shifted noise is independent of the ENTIRE ORIGINAL natural
past under actual Q, via the proved filtration identity. -/
theorem shifted_indep_original_past (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (s : ℝ≥0) :
    IndepFun (fun ω r => shiftedProcess H a b (s+r) ω-shiftedProcess H a b s ω)
      (fun ω (r : Iic s) => process r ω) (stepLaw H a b) := by
  have h := (shiftedProcess_isPreBrownian H a b hab hH).indepFun_shift s
  have hi : Indep (MeasurableSpace.comap
      (fun ω r => shiftedProcess H a b (s+r) ω-shiftedProcess H a b s ω) inferInstance)
      (shiftedNatural H a b hH s) (stepLaw H a b) := by
    rw [shiftedNatural,Filtration.natural_eq_comap]
    exact h
  rw [shiftedNatural_eq_original H a b hab hH,naturalFiltration,Filtration.natural_eq_comap] at hi
  exact hi

def shiftedIncrement (H : (ℝ≥0 → ℝ) → ℝ) (a b s t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  shiftedProcess H a b t ω-shiftedProcess H a b s ω

theorem shiftedIncrement_indep_original_past (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (s t : ℝ≥0) (hst : s ≤ t) :
    IndepFun (shiftedIncrement H a b s t) (fun ω (r : Iic s) => process r ω) (stepLaw H a b) := by
  have h := (shifted_indep_original_past H a b hab hH s).comp (measurable_pi_apply (t-s)) measurable_id
  have hs : s+(t-s)=t := add_tsub_cancel_of_le hst
  change IndepFun (fun ω => shiftedProcess H a b (s+(t-s)) ω-shiftedProcess H a b s ω)
    (fun ω (r : Iic s) => process r ω) (stepLaw H a b) at h
  rw [hs] at h
  exact h

theorem condExp_shiftedIncrement (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (s t : ℝ≥0) (hst : s ≤ t) :
    (stepLaw H a b)[shiftedIncrement H a b s t | naturalFiltration s] =ᵐ[stepLaw H a b] fun _ => 0 := by
  let _ := stepLaw_probability H a b hab hH
  have hg : Measurable (shiftedIncrement H a b s t) :=
    (shiftedProcess_measurable H a b t hH).sub (shiftedProcess_measurable H a b s hH)
  have hi : Indep (MeasurableSpace.comap (shiftedIncrement H a b s t) inferInstance)
      (naturalFiltration s) (stepLaw H a b) := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact shiftedIncrement_indep_original_past H a b hab hH s t hst
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ (MeasurableSpace.comap (shiftedIncrement H a b s t) inferInstance)
      inferInstance (shiftedIncrement H a b s t) := measurable_iff_comap_le.mpr le_rfl
  have hc := condExp_indep_eq hg.comap_le (naturalFiltration.le s) hm.stronglyMeasurable hi
  have hW := shiftedProcess_isPreBrownian H a b hab hH
  have he : (∫ ω, shiftedIncrement H a b s t ω ∂stepLaw H a b)=0 := by
    change (∫ ω, shiftedProcess H a b t ω-shiftedProcess H a b s ω ∂stepLaw H a b)=0
    rw [integral_sub (hW.integrable_eval t) (hW.integrable_eval s),hW.integral_eval,hW.integral_eval,sub_self]
  exact hc.trans (Eventually.of_forall (fun _ => he))

/-- Actual full shifted process martingale under the SAME original F_t. -/
theorem shiftedProcess_martingale (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    Martingale (shiftedProcess H a b) naturalFiltration (stepLaw H a b) := by
  let _ := stepLaw_probability H a b hab hH
  refine ⟨shiftedProcess_stronglyAdapted H a b hab hH,fun s t hst => ?_⟩
  have hW := shiftedProcess_isPreBrownian H a b hab hH
  have hi : Integrable (shiftedIncrement H a b s t) (stepLaw H a b) :=
    (hW.integrable_eval t).sub (hW.integrable_eval s)
  have he : shiftedProcess H a b t=shiftedIncrement H a b s t+shiftedProcess H a b s := by
    funext ω
    simp only [shiftedIncrement,Pi.add_apply,sub_add_cancel]
  rw [he]
  have hc := condExp_add hi (hW.integrable_eval s) (naturalFiltration s)
  have hp := condExp_of_stronglyMeasurable (naturalFiltration.le s) (shiftedProcess_stronglyAdapted H a b hab hH s) (hW.integrable_eval s)
  apply hc.trans
  rw [hp]
  filter_upwards [condExp_shiftedIncrement H a b hab hH s t hst] with ω hω
  simp only [Pi.add_apply,hω,zero_add]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepShiftedSource
