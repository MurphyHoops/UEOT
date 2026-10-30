import UEOT
namespace IndependentQFullConsumer
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand
open BrownianPredictableInputs BrownianIntegralClosure BrownianIntegralLiteralIntervals BrownianIntegralConditionalStep
open BrownianBoundedControlSource BrownianBoundedGirsanovSource BrownianBoundedExponentialLimitSource
open BrownianOwnQTimeInput BrownianOwnQIntegralClosure BrownianOwnQTimeTruncation
open BrownianOwnQPredictableDensity BrownianOwnQFullIntegralSource BrownianOwnQUnboundedIntervalSource
open scoped NNReal ENNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
-- A DIFFERENT nonconstant control from the author's constant-drift fixture.
-- It reads original B1, stays active only on(1,2], and keeps SAME fixed Q_A2.
def controlH (ω : ℝ≥0→ℝ) : ℝ:=Real.cos (process 1 ω)
theorem controlH_past : StronglyMeasurable[naturalFiltration 1] controlH :=
  Real.continuous_cos.comp_stronglyMeasurable (process_stronglyAdapted 1)
theorem controlH_top : MemLp controlH ∞ sourceLaw :=
  memLp_top_of_bound (controlH_past.mono (naturalFiltration.le 1)).aestronglyMeasurable 1
    (ae_of_all _ (fun _=>Real.abs_cos_le_one _))
def f : fullPredictableL2 2 := intervalInput 2 1 2 (by norm_num) le_rfl controlH controlH_past controlH_top
theorem fb : ∀ᵐ p ∂inputLaw 2,|(f : Lp ℝ 2 (inputLaw 2)) p|≤1 := by
  filter_upwards [intervalInput_coe 2 1 2 (by norm_num) le_rfl controlH controlH_past controlH_top] with p hp
  change (f : Lp ℝ 2 (inputLaw 2)) p=intervalIntegrand controlH 1 2 p at hp
  rw [hp]
  change |(Ioc (1 : ℝ) 2).indicator (fun _=>1) p.1*controlH p.2|≤1
  by_cases h : p.1∈Ioc (1 : ℝ) 2
  · simpa only [intervalIntegrand,Set.indicator_of_mem h,one_mul,controlH] using Real.abs_cos_le_one (process 1 p.2)
  · simp only [Set.indicator_of_notMem h,zero_mul,abs_zero,zero_le_one]
local instance fixedQ_probability : IsProbabilityMeasure (fullLaw 2 f) := fullLaw_probability 2 f 1 zero_le_one fb
abbrev W := shiftedProcess 2 f 1
abbrev Q := fullLaw 2 f
abbrev g : fullPredictableL2Q 2 f 5 := brownianPastInput 2 f 1 zero_le_one fb 5 1 4

example : integralDomain 2 f 1 zero_le_one fb 5=lpMeas ℝ ℝ predictableSigma 2 (inputLawQ 2 f 5) :=
  integralDomain_eq_fullPredictableL2Q 2 f 1 zero_le_one fb 5
example (x : fullPredictableL2Q 2 f 5) : (domainIsometry 2 f 1 zero_le_one fb 5 x).val=x.val := rfl
example (x : fullPredictableL2Q 2 f 5) :
    Tendsto (fun n=>clippedInputQ 2 f 1 zero_le_one fb 5 x n) atTop (𝓝 x.val) :=
  clippedInputQ_tendsto 2 f 1 zero_le_one fb 5 x
example (x : fullPredictableL2Q 2 f 5) (n : ℕ) :
    clippedInputQ 2 f 1 zero_le_one fb 5 x n∈integralDomain 2 f 1 zero_le_one fb 5 :=
  clippedInputQ_mem_domain 2 f 1 zero_le_one fb 5 x n
example : MemLp (W 1) 2 Q := shifted_memLp_two 2 f 1 zero_le_one fb 1
example : ¬MemLp (W 1) ∞ Q := shifted_not_memLp_top 2 f 1 zero_le_one fb 1 (by norm_num)
example : StronglyMeasurable[naturalFiltration 1] (W 1) := shiftedProcess_stronglyAdapted 2 f 1 1
example : g.val∈lpMeas ℝ ℝ predictableSigma 2 (inputLawQ 2 f 5) := g.property
example : (fullIntegral 2 f 1 zero_le_one fb 5 g : (ℝ≥0→ℝ)→ℝ)=ᵐ[Q]
    fun ω=>W 1 ω*(W 4 ω-W 1 ω) :=
  brownianPastIntegral_literal 2 f 1 zero_le_one fb 5 1 4 (by norm_num) (by norm_num)
example : (∫ ω,fullIntegral 2 f 1 zero_le_one fb 5 g ω^2 ∂Q)=3 := by
  have h:=brownianPastIntegral_energy 2 f 1 zero_le_one fb 5 1 4 (by norm_num) (by norm_num)
  norm_num at h
  exact h
example : (∫ ω,fullIntegral 2 f 1 zero_le_one fb 5 g ω ∂Q)=0 := by
  have hz:=fullIntegralProcess_zero 2 f 1 zero_le_one fb 5 g
  have h : (∫ ω,fullIntegralProcess 2 f 1 zero_le_one fb 5 g 0 ω ∂Q)=
      ∫ ω,fullIntegral 2 f 1 zero_le_one fb 5 g ω ∂Q := integral_condExp (naturalFiltration.le 0)
  rw [integral_congr_ae hz] at h
  simpa only [Pi.zero_apply,integral_zero] using h.symm
example : Martingale (fullIntegralProcess 2 f 1 zero_le_one fb 5 g) naturalFiltration Q :=
  fullIntegralProcess_martingale 2 f 1 zero_le_one fb 5 g
example : StronglyAdapted naturalFiltration (fullIntegralProcess 2 f 1 zero_le_one fb 5 g) :=
  fullIntegralProcess_stronglyAdapted 2 f 1 zero_le_one fb 5 g
example (u : ℝ≥0) : fullIntegralProcess 2 f 1 zero_le_one fb 5 g u=
    Q[fullIntegral 2 f 1 zero_le_one fb 5 g|naturalFiltration u] :=
  fullIntegralProcess_conditional 2 f 1 zero_le_one fb 5 u g
example (u : ℝ≥0) : (∫ ω,fullIntegralProcess 2 f 1 zero_le_one fb 5 g u ω^2 ∂Q)=
    ∫ p in BrownianIntegralTimeTruncation.timeSet 5 u,(g : Lp ℝ 2 (inputLawQ 2 f 5)) p^2 ∂inputLawQ 2 f 5 :=
  fullIntegralProcess_energy 2 f 1 zero_le_one fb 5 u g
example : fullIntegralProcess 2 f 1 zero_le_one fb 5 g 5=ᵐ[Q] fullIntegral 2 f 1 zero_le_one fb 5 g :=
  fullIntegralProcess_horizon 2 f 1 zero_le_one fb 5 g
-- START is not permission to read future coefficients before their support:
-- SAME actual process has zero second energy at the actual START1.
example : (∫ ω,fullIntegralProcess 2 f 1 zero_le_one fb 5 g 1 ω^2 ∂Q)=0 := by
  rw [fullIntegralProcess_energy 2 f 1 zero_le_one fb 5 1 g]
  apply integral_eq_zero_of_ae
  have hc:=intervalInputQ_coe 2 f 1 zero_le_one fb 5 1 4 (W 1)
    (shiftedProcess_stronglyAdapted 2 f 1 1) (shifted_memLp_two 2 f 1 zero_le_one fb 1)
  filter_upwards [ae_restrict_mem (BrownianIntegralTimeTruncation.timeSet_measurable 5 1),ae_restrict_of_ae hc] with p ht hp
  change (g : Lp ℝ 2 (inputLawQ 2 f 5)) p=intervalIntegrand (W 1) 1 4 p at hp
  rw [hp]
  have hu : p.1≤(1 : ℝ) := by simpa only [min_eq_left (by norm_num : (1 : ℝ≥0)≤5),NNReal.coe_one] using ht.1.2
  have hn : p.1∉Ioc (1 : ℝ) 4 := fun h=>(not_lt_of_ge hu) h.1
  change ((Ioc (1 : ℝ) 4).indicator (fun _=>1) p.1*W 1 p.2)^2=0
  simp only [Set.indicator_of_notMem hn,zero_mul,zero_pow (by decide : (2 : ℕ)≠0)]
-- Repeated endpoints retain the original Fs1 permission and return actual zero.
example : (fullIntegral 2 f 1 zero_le_one fb 5 (brownianPastInput 2 f 1 zero_le_one fb 5 1 1) : (ℝ≥0→ℝ)→ℝ)=ᵐ[Q] fun _=>0 := by
  filter_upwards [brownianPastIntegral_literal 2 f 1 zero_le_one fb 5 1 1 le_rfl (by norm_num)] with ω h
  simpa only [fullIncrement,sub_self,mul_zero] using h
-- Zero U is valid for EVERY native Q input, even with nonzero deployment A2.
example (x : fullPredictableL2Q 2 f 0) : fullIntegral 2 f 1 zero_le_one fb 0 x=0 :=
  fullIntegral_zero_horizon 2 f 1 zero_le_one fb x
-- Zero deployment A0 does not zero the Brownian law or the integration horizon.
def f0 : fullPredictableL2 0:=0
theorem fb0 : ∀ᵐ p ∂inputLaw 0,|(f0 : Lp ℝ 2 (inputLaw 0)) p|≤1 := by
  filter_upwards [Lp.coeFn_zero ℝ 2 (inputLaw 0)] with p hp
  change (0 : Lp ℝ 2 (inputLaw 0)) p=0 at hp
  change |(0 : Lp ℝ 2 (inputLaw 0)) p|≤1
  rw [hp,abs_zero]
  exact zero_le_one
example : ¬MemLp (shiftedProcess 0 f0 1 1) ∞ (fullLaw 0 f0) :=
  shifted_not_memLp_top 0 f0 1 zero_le_one fb0 1 (by norm_num)
example : (∫ ω,fullIntegral 0 f0 1 zero_le_one fb0 5
    (brownianPastInput 0 f0 1 zero_le_one fb0 5 1 4) ω^2 ∂fullLaw 0 f0)=3 := by
  have h:=brownianPastIntegral_energy 0 f0 1 zero_le_one fb0 5 1 4 (by norm_num) (by norm_num)
  norm_num at h
  exact h
-- Public native inputs really need no closure-membership premise.
example (U : ℝ≥0) (x : lpMeas ℝ ℝ predictableSigma 2 (inputLawQ 2 f U)) :
    ‖fullIntegral 2 f 1 zero_le_one fb U x‖=‖x‖ ∧
      Martingale (fullIntegralProcess 2 f 1 zero_le_one fb U x) naturalFiltration Q :=
  ⟨fullIntegral_norm 2 f 1 zero_le_one fb U x,fullIntegralProcess_martingale 2 f 1 zero_le_one fb U x⟩
end
end IndependentQFullConsumer
