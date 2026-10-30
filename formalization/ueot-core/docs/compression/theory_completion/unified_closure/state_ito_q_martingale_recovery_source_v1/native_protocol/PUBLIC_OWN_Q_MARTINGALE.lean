import UEOT
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianIntegralLiteralIntervals BrownianCommonRefinement
open BrownianBoundedControlSource BrownianBoundedExponentialLimitSource BrownianBoundedGirsanovSource
open BrownianOwnQOneStepIntegral BrownianOwnQSimpleIntegral BrownianOwnQTimeInput BrownianOwnQIntegralClosure
open BrownianOwnQConditionalStep BrownianOwnQFinitePaths
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
namespace IndependentOwnQConditionalConsumer
noncomputable section
-- Different source and target clocks/readouts from the author fixture.
def controlH (ω : ℝ≥0→ℝ) := Real.cos (process 1 ω)
theorem controlH_past : StronglyMeasurable[naturalFiltration 1] controlH :=
  Real.continuous_cos.comp_stronglyMeasurable (process_stronglyAdapted 1)
theorem controlH_top : MemLp controlH ∞ sourceLaw :=
  memLp_top_of_bound (controlH_past.mono (naturalFiltration.le 1)).aestronglyMeasurable 1
    (ae_of_all _ (fun _=>Real.abs_cos_le_one _))
def control : fullPredictableL2 3 := intervalInput 3 1 3 (by norm_num) le_rfl controlH controlH_past controlH_top
theorem control_bound : ∀ᵐ p ∂inputLaw 3,|(control : Lp ℝ 2 (inputLaw 3)) p|≤1 := by
  filter_upwards [intervalInput_coe 3 1 3 (by norm_num) le_rfl controlH controlH_past controlH_top] with p hp
  change (control : Lp ℝ 2 (inputLaw 3)) p=intervalIntegrand controlH 1 3 p at hp
  rw [hp]
  change |(Ioc (1 : ℝ) 3).indicator (fun _=>1) p.1*controlH p.2|≤1
  by_cases h : p.1∈Ioc (1 : ℝ) 3
  · simpa only [Set.indicator_of_mem h,one_mul,controlH] using Real.abs_cos_le_one (process 1 p.2)
  · simp only [Set.indicator_of_notMem h,zero_mul,abs_zero,zero_le_one]
local instance actualQ_probability : IsProbabilityMeasure (fullLaw 3 control) :=
  fullLaw_probability 3 control 1 (by norm_num) control_bound
-- Reads original B2 inside the control window, and original B1; never assumes W-natural equality.
def rowH (ω : ℝ≥0→ℝ) : ℝ := 2+Real.sin (process 2 ω)+(1/4)*Real.cos (process 1 ω)
theorem rowH_past : StronglyMeasurable[naturalFiltration 2] rowH :=
  (stronglyMeasurable_const.add (Real.continuous_sin.comp_stronglyMeasurable (process_stronglyAdapted 2))).add
    (stronglyMeasurable_const.mul (Real.continuous_cos.comp_stronglyMeasurable
      ((process_stronglyAdapted 1).mono (naturalFiltration.mono (by norm_num : (1 : ℝ≥0)≤2)))))
theorem rowH_range (ω : ℝ≥0→ℝ) : (3/4 : ℝ)≤rowH ω ∧ rowH ω≤13/4 := by
  have hs := Real.abs_sin_le_one (process 2 ω)
  have hc := Real.abs_cos_le_one (process 1 ω)
  rw [abs_le] at hs hc
  constructor <;> unfold rowH <;> linarith
theorem rowH_bound (ω : ℝ≥0→ℝ) : ‖rowH ω‖≤13/4 := by
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · linarith [(rowH_range ω).1]
  · exact (rowH_range ω).2
theorem rowH_P : MemLp rowH ∞ sourceLaw :=
  memLp_top_of_bound (rowH_past.mono (naturalFiltration.le 2)).aestronglyMeasurable (13/4) (ae_of_all _ rowH_bound)
theorem rowH_Q : MemLp rowH ∞ (fullLaw 3 control) :=
  coefficient_bounded_Q 3 control 1 (by norm_num) control_bound rowH_P
-- ALL before/inside/after observations, exact originalFs and same actual Q.
example (u : ℝ≥0) : (fullLaw 3 control)[oneStep 3 control 1 rowH 2 5 | naturalFiltration u]=ᵐ[fullLaw 3 control]
    oneStep 3 control 1 rowH 2 (clamp 2 5 u) :=
  oneStep_condExp_prefix 3 control 1 (by norm_num) control_bound 2 5 u (by norm_num) rowH_past rowH_Q
example : (fullLaw 3 control)[oneStep 3 control 1 rowH 2 5 | naturalFiltration (3/2)]=ᵐ[fullLaw 3 control] fun _=>0 := by
  have h:=oneStep_condExp_prefix 3 control 1 (by norm_num) control_bound 2 5 (3/2) (by norm_num) rowH_past rowH_Q
  have hc : clamp (2 : ℝ≥0) 5 (3/2)=2 :=
    max_eq_left ((min_le_right 5 (3/2)).trans (NNReal.coe_le_coe.mp (by norm_num [NNReal.coe_div]) : (3/2 : ℝ≥0)≤2))
  rw [hc] at h
  exact h.trans (ae_of_all _ (fun ω=>by simp [oneStep,fullIncrement]))
example : (fullLaw 3 control)[oneStep 3 control 1 rowH 2 5 | naturalFiltration 4]=ᵐ[fullLaw 3 control]
    oneStep 3 control 1 rowH 2 4 := by
  have h:=oneStep_condExp_prefix 3 control 1 (by norm_num) control_bound 2 5 4 (by norm_num) rowH_past rowH_Q
  norm_num [clamp] at h
  exact h
example : (fullLaw 3 control)[oneStep 3 control 1 rowH 2 5 | naturalFiltration 7]=ᵐ[fullLaw 3 control]
    oneStep 3 control 1 rowH 2 5 := by
  have h:=oneStep_condExp_prefix 3 control 1 (by norm_num) control_bound 2 5 7 (by norm_num) rowH_past rowH_Q
  norm_num [clamp] at h
  exact h
example (u : ℝ≥0) : naturalProjection 3 control u
    ((oneStep_memLp_two 3 control 1 (by norm_num) control_bound rowH_Q 2 5).toLp (oneStep 3 control 1 rowH 2 5))=
      (oneStep_memLp_two 3 control 1 (by norm_num) control_bound rowH_Q 2 (clamp 2 5 u)).toLp
        (oneStep 3 control 1 rowH 2 (clamp 2 5 u)) :=
  oneStep_projection_prefix 3 control 1 (by norm_num) control_bound 2 5 u (by norm_num) rowH_past rowH_Q
-- Even after deployment A3, the SAME W still has genuine variance1 on4→5.
example : (∫ ω,fullIncrement 3 control 1 4 5 ω^2 ∂fullLaw 3 control)=1 := by
  have h:=increment_square_mean 3 control 1 (by norm_num) control_bound 4 5 (by norm_num)
  norm_num at h
  exact h
example : (9/16 : ℝ)≤∫ ω,oneStep 3 control 1 rowH 4 5 ω^2 ∂fullLaw 3 control := by
  rw [oneStep_isometry 3 control 1 (by norm_num) control_bound 4 5 (by norm_num)
    (rowH_past.mono (naturalFiltration.mono (by norm_num : (2 : ℝ≥0)≤4))) rowH_Q]
  norm_num
  have hi : Integrable (fun _ : ℝ≥0→ℝ=>(9/16 : ℝ)) (fullLaw 3 control) := integrable_const _
  have hineq := integral_mono hi (rowH_Q.mono_exponent (by simp : (2 : ℝ≥0∞)≤∞)).integrable_sq
    (fun ω=>by have h:=(rowH_range ω).1; nlinarith)
  simpa using hineq
-- Original supplied finite record includes a collapsed row retaining Fs2.
def repeatRecord : ElementaryInput 6 where
  n := 4
  clock := ![0,2,2,5,6]
  coefficient := ![fun _=>0,rowH,rowH,fun _=>0]
  clock_mono := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def] at *
  clock_zero := rfl
  clock_end := rfl
  coefficient_past := by intro i; fin_cases i; exact stronglyMeasurable_const; exact rowH_past; exact rowH_past; exact stronglyMeasurable_const
  coefficient_bounded := by intro i; fin_cases i; exact MemLp.zero; exact rowH_P; exact rowH_P; exact MemLp.zero

theorem repeat_actual (u : ℝ≥0) : literalPath 3 control 1 repeatRecord u=oneStep 3 control 1 rowH 2 (clamp 2 5 u) := by
  ext ω
  dsimp only [literalPath,repeatRecord]
  simp [Fin.sum_univ_succ,oneStep,fullIncrement,clamp]
example : Martingale (literalPath 3 control 1 repeatRecord) naturalFiltration (fullLaw 3 control) :=
  literalPath_martingale 3 control 1 (by norm_num) control_bound repeatRecord
example (ω : ℝ≥0→ℝ) : Continuous (fun u=>literalPath 3 control 1 repeatRecord u ω) :=
  literalPath_continuous 3 control 1 (by norm_num) repeatRecord ω
example : (fullLaw 3 control)[simpleIntegral 3 control 1 repeatRecord | naturalFiltration 4]=ᵐ[fullLaw 3 control]
    oneStep 3 control 1 rowH 2 4 := by
  have h:=literalPath_conditional_terminal 3 control 1 (by norm_num) control_bound repeatRecord 4
  rw [repeat_actual] at h
  norm_num [clamp] at h
  exact h
example : literalPath 3 control 1 repeatRecord 6=simpleIntegral 3 control 1 repeatRecord :=
  literalPath_horizon 3 control 1 repeatRecord
example : literalPath 3 control 1 repeatRecord 0=0 := literalPath_zero 3 control 1 repeatRecord
-- Q-native cutoff returns SAME actual Q finite output of the clamped original input.
def rInterval : ElementaryInput 6 := intervalRecord 6 2 5 (by norm_num) (by norm_num) rowH rowH_past rowH_P
example : BrownianOwnQTimeTruncation.integralClassProcess 3 control 1 (by norm_num) control_bound 6
    (representedInput 3 control 1 (by norm_num) control_bound rInterval) 4=
      outputValueQ 3 control 1 (by norm_num) control_bound (intervalRecord 6 2 4 (by norm_num) (by norm_num) rowH rowH_past rowH_P) := by
  change integral 3 control 1 (by norm_num) control_bound 6
    (BrownianOwnQTimeTruncation.truncate 3 control 1 (by norm_num) control_bound 6 4
      (representedInput 3 control 1 (by norm_num) control_bound (intervalRecord 6 2 5 (by norm_num) (by norm_num) rowH rowH_past rowH_P)))=_
  rw [BrownianOwnQTimeTruncation.truncate_represented_interval]
  have hc : clamp (2 : ℝ≥0) 5 4=4 := by norm_num [clamp]
  simp only [hc]
  exact integral_returns_literal 3 control 1 (by norm_num) control_bound _
-- Domain remains the explicit dt6×Q span closure, NOT all Q predictable L2.
example (u : ℝ≥0) (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    (∫ ω,BrownianOwnQTimeTruncation.integralClassProcess 3 control 1 (by norm_num) control_bound 6 g u ω^2 ∂fullLaw 3 control)=
      ∫ p in BrownianIntegralTimeTruncation.timeSet 6 u,(g : Lp ℝ 2 (inputLawQ 3 control 6)) p^2 ∂inputLawQ 3 control 6 :=
  BrownianOwnQTimeTruncation.integralClassProcess_energy 3 control 1 (by norm_num) control_bound 6 u g
example (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    BrownianOwnQTimeTruncation.truncate 3 control 1 (by norm_num) control_bound 6 0 g=0 :=
  BrownianOwnQTimeTruncation.truncate_zero 3 control 1 (by norm_num) control_bound 6 g
example (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    BrownianOwnQTimeTruncation.truncate 3 control 1 (by norm_num) control_bound 6 6 g=g :=
  BrownianOwnQTimeTruncation.truncate_horizon 3 control 1 (by norm_num) control_bound 6 g
example (u : ℝ≥0) (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    ‖BrownianOwnQTimeTruncation.truncate 3 control 1 (by norm_num) control_bound 6 u g‖≤‖g‖ :=
  BrownianOwnQTimeTruncation.truncate_norm_le 3 control 1 (by norm_num) control_bound 6 u g
-- IntegrationU0 is independent of controlA3; all original permitted zero cells have zero path.
def zeroRecord : ElementaryInput 0 := intervalRecord 0 0 0 le_rfl le_rfl (fun _=>1) stronglyMeasurable_const (memLp_top_const 1)
example (u : ℝ≥0) : literalPath 3 control 1 zeroRecord u=0 := by
  ext ω
  dsimp only [literalPath,zeroRecord,intervalRecord]
  simp [Fin.sum_univ_succ,oneStep,fullIncrement,clamp]
-- Genuine common consumer on ALL declared closure inputs, same actual Q/originalFs.
example (u : ℝ≥0) (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    naturalProjection 3 control u (integral 3 control 1 (by norm_num) control_bound 6 g)=
      BrownianOwnQTimeTruncation.integralClassProcess 3 control 1 (by norm_num) control_bound 6 g u :=
  BrownianOwnQIntegralMartingale.integral_projection_identity 3 control 1 (by norm_num) control_bound 6 u g
example (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    Martingale (BrownianOwnQIntegralMartingale.integralProcess 3 control 1 (by norm_num) control_bound 6 g)
      naturalFiltration (fullLaw 3 control) :=
  BrownianOwnQIntegralMartingale.integralProcess_martingale 3 control 1 (by norm_num) control_bound 6 g
example (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    StronglyAdapted naturalFiltration (BrownianOwnQIntegralMartingale.integralProcess 3 control 1 (by norm_num) control_bound 6 g) :=
  BrownianOwnQIntegralMartingale.integralProcess_stronglyAdapted 3 control 1 (by norm_num) control_bound 6 g
example (u : ℝ≥0) (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    BrownianOwnQIntegralMartingale.integralProcess 3 control 1 (by norm_num) control_bound 6 g u =ᵐ[fullLaw 3 control]
      BrownianOwnQTimeTruncation.integralClassProcess 3 control 1 (by norm_num) control_bound 6 g u :=
  BrownianOwnQIntegralMartingale.integralProcess_eq_truncated 3 control 1 (by norm_num) control_bound 6 u g
-- SAME supplied repeated-clock finite path is returned at EACH fixed observation time.
-- This does not assert a common AE event for all times for the canonical conditional version.
example (u : ℝ≥0) : BrownianOwnQIntegralMartingale.integralProcess 3 control 1 (by norm_num) control_bound 6
    (representedInput 3 control 1 (by norm_num) control_bound repeatRecord) u =ᵐ[fullLaw 3 control]
      literalPath 3 control 1 repeatRecord u :=
  BrownianOwnQIntegralMartingale.integralProcess_returns_literal 3 control 1 (by norm_num) control_bound repeatRecord u
example (u : ℝ≥0) (g : integralDomain 3 control 1 (by norm_num) control_bound 6) :
    (∫ ω,BrownianOwnQIntegralMartingale.integralProcess 3 control 1 (by norm_num) control_bound 6 g u ω^2 ∂fullLaw 3 control)=
      ∫ p in BrownianIntegralTimeTruncation.timeSet 6 u,(g : Lp ℝ 2 (inputLawQ 3 control 6)) p^2 ∂inputLawQ 3 control 6 :=
  BrownianOwnQIntegralMartingale.integralProcess_energy 3 control 1 (by norm_num) control_bound 6 u g
-- Unit input on U6 under SAME Q_A3: whole post-A noise remains live, second energy6.
def unitRecord : ElementaryInput 6 := intervalRecord 6 0 6 (by norm_num) le_rfl (fun _=>1) stronglyMeasurable_const (memLp_top_const 1)
example : (∫ ω,BrownianOwnQIntegralMartingale.integralProcess 3 control 1 (by norm_num) control_bound 6
    (representedInput 3 control 1 (by norm_num) control_bound unitRecord) 6 ω^2 ∂fullLaw 3 control)=6 := by
  have hp := BrownianOwnQIntegralMartingale.integralProcess_returns_literal 3 control 1 (by norm_num) control_bound unitRecord 6
  rw [literalPath_horizon] at hp
  have he : simpleIntegral 3 control 1 unitRecord=oneStep 3 control 1 (fun _=>1) 0 6 := by
    ext ω
    dsimp only [simpleIntegral,unitRecord,intervalRecord]
    simp [Fin.sum_univ_succ,oneStep,fullIncrement]
  rw [he] at hp
  rw [integral_congr_ae (hp.mono (fun _ h=>congrArg (fun x : ℝ=>x^2) h))]
  have h:=oneStep_isometry 3 control 1 (by norm_num) control_bound 0 6 (by norm_num)
    (stronglyMeasurable_const : StronglyMeasurable[naturalFiltration 0] (fun _ : ℝ≥0→ℝ=>(1 : ℝ)))
    (memLp_top_const (μ := fullLaw 3 control) 1)
  norm_num at h
  exact h

end
end IndependentOwnQConditionalConsumer
