import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepConditionalSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepGirsanovSource

/-!
Original commitment: the original P-KL consumer must bind the returned finite policy table and actual integrator.
Existing result: SAME final tableQ has literal centered-row conditional Gaussian laws relative to the entire original START past.
Premise reduced: derive the actual finite controlled terminal integral, zero-start terminal martingale and original TerminalGirsanovData.
Model/witness: original ElementaryInput T, originalFs and sourceLaw, actual tableLaw, original dt energy; repeated/empty clocks included.
Consumer/boundary: original exact KL and every measurable readout bound; full arbitrary-time shifted Brownian and general predictable control remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepTerminalKLSource
open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianOneStepIntegral
open BrownianIntegralClosure BrownianPredictableDensity BrownianIntegralTimeEnergy BrownianLiteralGridBinding
open BrownianFiniteStepExponentialSource BrownianFiniteStepConditionalSource BrownianPastStepGirsanovSource
open UEOT.V3.GirsanovPathKL
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem cell_mono {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : r.clock i.castSucc ≤ r.clock i.succ :=
  r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))
private theorem cell_end_le {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : r.clock i.succ ≤ T := by
  simpa only [r.clock_end] using r.clock_mono (Fin.le_last i.succ)

/-- The finite actual time-dependent control, with literal zero before each row's START. -/
def tableControl {T : ℝ≥0} (r : ElementaryInput T) (t : ℝ) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, stepControl (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) t ω

theorem tableControl_progressive {T : ℝ≥0} (r : ElementaryInput T) :
    IsProgressive BrownianConstantGirsanovSource.controlFiltration (tableControl r) := by
  intro t
  exact Finset.measurable_sum _ (fun i _ => stepControl_progressive _ _ _ (r.coefficient_past i) t)

private theorem row_control_mul_zero {T : ℝ≥0} (r : ElementaryInput T) (i j : Fin r.n) (hij : i ≠ j)
    (t : ℝ) (ω : ℝ≥0 → ℝ) :
    stepControl (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) t ω *
      stepControl (r.coefficient j) (r.clock j.castSucc) (r.clock j.succ) t ω=0 := by
  have hd : ¬ (t ∈ Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ) ∧
      t ∈ Ioc (r.clock j.castSucc : ℝ) (r.clock j.succ : ℝ)) := by
    intro hp
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := r.clock_mono (show i.succ ≤ j.castSucc by exact_mod_cast Nat.succ_le_of_lt hij)
      have hc : (r.clock i.succ : ℝ)≤(r.clock j.castSucc : ℝ) := by exact_mod_cast h
      exact (not_lt_of_ge (hp.1.2.trans hc)) hp.2.1
    · have h := r.clock_mono (show j.succ ≤ i.castSucc by exact_mod_cast Nat.succ_le_of_lt hji)
      have hc : (r.clock j.succ : ℝ)≤(r.clock i.castSucc : ℝ) := by exact_mod_cast h
      exact (not_lt_of_ge (hp.2.2.trans hc)) hp.1.1
  by_cases hi : t ∈ Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)
  · have hj : t ∉ Ioc (r.clock j.castSucc : ℝ) (r.clock j.succ : ℝ) := fun hj => hd ⟨hi,hj⟩
    simp [stepControl,hj]
  · simp [stepControl,hi]

private theorem tableControl_square {T : ℝ≥0} (r : ElementaryInput T) (t : ℝ) (ω : ℝ≥0 → ℝ) :
    ‖tableControl r t ω‖^2=
      ∑ i : Fin r.n, (Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)).indicator
        (fun _ => ‖r.coefficient i ω‖^2) t := by
  rw [Real.norm_eq_abs,sq_abs,tableControl,pow_two,Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · by_cases ht : t ∈ Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)
    · simp [stepControl,ht,Real.norm_eq_abs,pow_two]
    · simp [stepControl,ht]
  · intro j _ hji
    exact row_control_mul_zero r i j hji.symm t ω
  · simp

theorem tableControl_energy_intervalIntegrable {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    IntervalIntegrable (fun t => ‖tableControl r t ω‖^2) volume 0 (T : ℝ) := by
  simp_rw [tableControl_square]
  have h : IntervalIntegrable (∑ i : Fin r.n, (Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)).indicator
      (fun _ => ‖r.coefficient i ω‖^2)) volume 0 (T : ℝ) := by
    apply IntervalIntegrable.sum
    intro i _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg]
    exact (integrable_const (μ := volume.restrict (Ioc 0 (T : ℝ))) (‖r.coefficient i ω‖^2)).indicator measurableSet_Ioc
  have he : (fun t => ∑ i : Fin r.n, (Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)).indicator
      (fun _ => ‖r.coefficient i ω‖^2) t)=∑ i : Fin r.n, (Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ)).indicator
      (fun _ => ‖r.coefficient i ω‖^2) := by
    funext t
    simp only [Finset.sum_apply]
  rw [he]
  exact h

/-- The original literal clock-time energy is the SAME table energy. -/
theorem tableControl_energy {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    controlEnergy T (tableControl r) ω=tableEnergy r ω := by
  rw [controlEnergy]
  simp_rw [tableControl_square]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have hs : Ioc (r.clock i.castSucc : ℝ) (r.clock i.succ : ℝ) ⊆ Ioc (0 : ℝ) (T : ℝ) := by
      intro t ht
      exact ⟨lt_of_le_of_lt (r.clock i.castSucc).coe_nonneg ht.1,ht.2.trans (by exact_mod_cast cell_end_le r i)⟩
    rw [intervalIntegral.integral_of_le T.coe_nonneg,integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr hs,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,ENNReal.toReal_ofReal,
      sub_nonneg.mpr (show (r.clock i.castSucc : ℝ)≤(r.clock i.succ : ℝ) from cell_mono r i),
      smul_eq_mul,Real.norm_eq_abs,sq_abs]
  · intro i _
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg]
    exact (integrable_const (μ := volume.restrict (Ioc 0 (T : ℝ))) (‖r.coefficient i ω‖^2)).indicator measurableSet_Ioc

private theorem coefficient_top_Q {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    MemLp (r.coefficient i) ∞ (tableLaw r) := by
  have he : eLpNormEssSup (r.coefficient i) sourceLaw < ⊤ := by
    simpa only [eLpNorm_exponent_top] using (r.coefficient_bounded i).2
  obtain ⟨C,hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp he
  apply MemLp.of_bound ((r.coefficient_past i).mono (naturalFiltration.le _)).aestronglyMeasurable (C : ℝ)
  have hC' : ∀ᵐ ω ∂sourceLaw, ‖r.coefficient i ω‖₊ ≤ C := hC
  have hCQ : ∀ᵐ ω ∂tableLaw r, ‖r.coefficient i ω‖₊ ≤ C :=
    (prefixLaw_absolutelyContinuous r (Fin.last r.n)).ae_le hC'
  filter_upwards [hCQ] with ω hω
  exact_mod_cast hω

/-- Actual finite integral against the literal centered returned rows, not a newly chosen random variable. -/
def centeredIntegral {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, r.coefficient i ω*centeredRow r i ω

private theorem row_integrable {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    Integrable (r.coefficient i*centeredRow r i) (tableLaw r) :=
  (show MemLp (r.coefficient i) 2 (tableLaw r) from (coefficient_top_Q r i).mono_exponent le_top).integrable_mul
    (final_centered_law_indep r i).1.hasGaussianLaw.memLp_two

private theorem row_end_past {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    StronglyMeasurable[naturalFiltration T] (r.coefficient i*centeredRow r i) := by
  have ha := (cell_mono r i).trans (cell_end_le r i)
  have hc := (process_stronglyAdapted (r.clock i.succ)).mono (naturalFiltration.mono (cell_end_le r i))
  have hd := (process_stronglyAdapted (r.clock i.castSucc)).mono (naturalFiltration.mono ha)
  exact ((r.coefficient_past i).mono (naturalFiltration.mono ha)).mul
    ((hc.sub hd).sub (((r.coefficient_past i).mono (naturalFiltration.mono ha)).mul stronglyMeasurable_const))

theorem centeredIntegral_integrable {T : ℝ≥0} (r : ElementaryInput T) :
    Integrable (centeredIntegral r) (tableLaw r) := integrable_finsetSum _ (fun i _ => row_integrable r i)

theorem centeredIntegral_past {T : ℝ≥0} (r : ElementaryInput T) :
    StronglyMeasurable[naturalFiltration T] (centeredIntegral r) :=
  by
    have he : centeredIntegral r=∑ i : Fin r.n, r.coefficient i*centeredRow r i := by
      funext ω
      simp only [centeredIntegral,Finset.sum_apply,Pi.mul_apply]
    rw [he]
    exact Finset.stronglyMeasurable_sum Finset.univ (fun i _ => row_end_past r i)

theorem centeredIntegral_condExp_zero {T : ℝ≥0} (r : ElementaryInput T) :
    (tableLaw r)[centeredIntegral r | naturalFiltration 0] =ᵐ[tableLaw r] fun _ => 0 := by
  have hr : ∀ i : Fin r.n, (tableLaw r)[r.coefficient i*centeredRow r i | naturalFiltration 0] =ᵐ[tableLaw r] fun _ => 0 := by
    intro i
    have hc : (tableLaw r)[r.coefficient i*centeredRow r i | naturalFiltration (r.clock i.castSucc)] =ᵐ[tableLaw r] fun _ => 0 := by
      apply (condExp_mul_of_stronglyMeasurable_left (r.coefficient_past i) (row_integrable r i)
        (final_centered_law_indep r i).1.hasGaussianLaw.integrable).trans
      filter_upwards [final_centered_condExp_zero r i] with ω hω
      simp only [Pi.mul_apply,hω,mul_zero]
    have ht := condExp_condExp_of_le (μ := tableLaw r) (f := r.coefficient i*centeredRow r i)
      (naturalFiltration.mono (show (0 : ℝ≥0)≤r.clock i.castSucc from bot_le)) (naturalFiltration.le _)
    apply ht.symm.trans
    apply (condExp_congr_ae (m := naturalFiltration 0) hc).trans
    change (tableLaw r)[(0 : (ℝ≥0 → ℝ) → ℝ) | naturalFiltration 0] =ᵐ[tableLaw r] (0 : (ℝ≥0 → ℝ) → ℝ)
    rw [condExp_zero]
  have hh : centeredIntegral r=∑ i : Fin r.n, r.coefficient i*centeredRow r i := by
    funext ω
    simp only [centeredIntegral,Finset.sum_apply,Pi.mul_apply]
  rw [hh]
  apply (condExp_finsetSum (s := Finset.univ) (fun i _ => row_integrable r i) (naturalFiltration 0)).trans
  filter_upwards [ae_all_iff.mpr hr] with ω hω
  simp only [Finset.sum_apply,hω,Finset.sum_const_zero]

/-- SAME original-source returned integrator on the actual supplied table. -/
def baselineIntegral {T : ℝ≥0} (r : ElementaryInput T) : (ℝ≥0 → ℝ) → ℝ :=
  predictableIntegral T (literalPredictableInput r)

theorem baseline_returns_literal {T : ℝ≥0} (r : ElementaryInput T) :
    baselineIntegral r =ᵐ[sourceLaw] BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient := by
  rw [baselineIntegral,predictableIntegral_returns_literal]
  exact (BrownianSimplePredictableIntegral.simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp

/-- Pure literal algebra, on the actual returned coefficients and rows. -/
theorem literal_integral_shift {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient ω=centeredIntegral r ω+tableEnergy r ω := by
  simp only [BrownianSimplePredictableIntegral.simpleIntegral,centeredIntegral,tableEnergy,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold oneStep centeredRow BrownianPastStepTiltKernelSource.centeredIncrement
  rw [NNReal.coe_sub (cell_mono r i)]
  simp only [Pi.mul_apply]
  ring

/-- Literal finite sum of the row-prefix controlled integrals. It uses the
supplied B, H and clipped row clocks; no general Q-integrator is posited. -/
def centeredPrefixPath {T : ℝ≥0} (r : ElementaryInput T) (t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, BrownianPastStepGirsanovSource.controlledPath
    (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) t ω

private theorem centeredPrefixPath_zero {T : ℝ≥0} (r : ElementaryInput T) : centeredPrefixPath r 0=0 := by
  funext ω
  simp [centeredPrefixPath,BrownianPastStepGirsanovSource.controlledPath,BrownianCommonRefinement.clamp]

private theorem centeredPrefixPath_terminal {T : ℝ≥0} (r : ElementaryInput T) : centeredPrefixPath r T=centeredIntegral r := by
  funext ω
  apply Finset.sum_congr rfl
  intro i _
  have hcl : BrownianCommonRefinement.clamp (r.clock i.castSucc) (r.clock i.succ) T=r.clock i.succ := by
    simp only [BrownianCommonRefinement.clamp,min_eq_left (cell_end_le r i),max_eq_right (cell_mono r i)]
  change BrownianPastStepGirsanovSource.controlledPath (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) T ω=_
  rw [BrownianPastStepGirsanovSource.controlledPath,hcl]
  change BrownianPastStepGirsanovSource.controlledIntegral (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) ω=_
  rw [BrownianPastStepGirsanovSource.controlledIntegral_eq_centered _ _ _ (cell_mono r i)]
  rfl

/-- The actual row-prefix path at the original zero/terminal clocks is a
true native martingale under SAME tableQ, from actual row conditional laws. -/
theorem terminalIntegral_martingale {T : ℝ≥0} (r : ElementaryInput T) :
    Martingale (fun i => centeredPrefixPath r (BrownianConstantGirsanovSource.terminalClock T i))
      (BrownianConstantGirsanovSource.terminalFiltration T) (tableLaw r) := by
  refine ⟨fun i => ?_,fun i j hij => ?_⟩
  · fin_cases i
    · change StronglyMeasurable[naturalFiltration 0] (centeredPrefixPath r 0)
      rw [centeredPrefixPath_zero]
      exact stronglyMeasurable_zero
    · change StronglyMeasurable[naturalFiltration T] (centeredPrefixPath r T)
      rw [centeredPrefixPath_terminal]
      exact centeredIntegral_past r
  · fin_cases i <;> fin_cases j
    · change (tableLaw r)[centeredPrefixPath r 0 | naturalFiltration 0] =ᵐ[tableLaw r] centeredPrefixPath r 0
      rw [centeredPrefixPath_zero,condExp_zero]
    · change (tableLaw r)[centeredPrefixPath r T | naturalFiltration 0] =ᵐ[tableLaw r] centeredPrefixPath r 0
      rw [centeredPrefixPath_terminal,centeredPrefixPath_zero]
      exact centeredIntegral_condExp_zero r
    · norm_num at hij
    · change (tableLaw r)[centeredPrefixPath r T | naturalFiltration T] =ᵐ[tableLaw r] centeredPrefixPath r T
      rw [centeredPrefixPath_terminal]
      rw [condExp_of_stronglyMeasurable (naturalFiltration.le T) (centeredIntegral_past r) (centeredIntegral_integrable r)]

theorem tableEnergy_integrable {T : ℝ≥0} (r : ElementaryInput T) : Integrable (tableEnergy r) (tableLaw r) := by
  apply integrable_finsetSum
  intro i _
  exact ((coefficient_top_Q r i).mono_exponent (show (2 : ℝ≥0∞)≤∞ from le_top)).integrable_sq.const_mul _

/-- ORIGINAL terminal record binds SAME density, returned native baseline
integral, actual finite centered-row prefix, true dt energy and original
natural filtration. No KL or shifted-Brownian conclusion is supplied as input. -/
def actualTerminalData {T : ℝ≥0} (r : ElementaryInput T) :
    TerminalGirsanovData sourceLaw (tableLaw r) T (tableControl r) where
  density ω := ENNReal.ofReal (prefixExponential r (Fin.last r.n) ω)
  baselineIntegral := baselineIntegral r
  controlledIntegral := centeredIntegral r
  controlFiltration := BrownianConstantGirsanovSource.controlFiltration
  control_progressive := tableControl_progressive r
  energy_intervalIntegrable := Eventually.of_forall (tableControl_energy_intervalIntegrable r)
  measurable_density := ((prefix_past r (Fin.last r.n)).mono (naturalFiltration.le _)).measurable.ennreal_ofReal
  changeOfMeasure := rfl
  density_eq_exp := by
    filter_upwards [table_exponential_actual_integral r,timeEnergy_literal_horizon r] with ω hω he
    change timeEnergy T (literalPredictableInput r) T ω=tableEnergy r ω at he
    rw [he] at hω
    rw [tableControl_energy]
    simpa only [baselineIntegral,one_div] using congrArg ENNReal.ofReal hω
  integral_shift := by
    have hb : baselineIntegral r =ᵐ[tableLaw r] BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient :=
      (prefixLaw_absolutelyContinuous r (Fin.last r.n)).ae_le (baseline_returns_literal r)
    filter_upwards [hb] with ω hω
    rw [hω,tableControl_energy]
    exact literal_integral_shift r ω
  controlledIntegralProcess i := centeredPrefixPath r (BrownianConstantGirsanovSource.terminalClock T i)
  controlledFiltration := BrownianConstantGirsanovSource.terminalFiltration T
  controlledIntegral_martingale := terminalIntegral_martingale r
  controlledIntegral_initial := centeredPrefixPath_zero r
  controlledIntegral_terminal := centeredPrefixPath_terminal r
  energy_integrable := by
    have he : controlEnergy T (tableControl r)=tableEnergy r := funext (tableControl_energy r)
    rw [he]
    exact tableEnergy_integrable r

/-- Direct original P-KL-05 for the actual returned finite table. Expected
energy is evaluated under its actual FINAL controlled measure. -/
theorem actual_p_kl_05 {T : ℝ≥0} (r : ElementaryInput T) {Γ : Type*} [MeasurableSpace Γ]
    (readout : (ℝ≥0 → ℝ) → Γ) (hreadout : Measurable readout) :
    klDiv (tableLaw r) sourceLaw = ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, tableEnergy r ω ∂tableLaw r)) ∧
    klDiv ((tableLaw r).map readout) (sourceLaw.map readout) ≤
      ENNReal.ofReal ((1/2 : ℝ)*(∫ ω, tableEnergy r ω ∂tableLaw r)) := by
  have h := (actualTerminalData r).p_kl_05 readout hreadout
  have he : controlEnergy T (tableControl r)=tableEnergy r := funext (tableControl_energy r)
  simpa only [he,one_div] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepTerminalKLSource
