import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalL2Source
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
Original commitment: the original terminal KL consumer needs actual OWN-Q controlled terminal mean zero.
Existing result: actual D_n converge in L1 with uniform L2 bound; actual J_n converge strongly in L2 and pair to zero.
Premise reduced: derive weak source-L2 density convergence and transport the actual finite zero pairing to SAME D_f,J_f.
Model/witness: native fullPredictableL2, explicit source-AE bound K, original source P and unrenormalized own fullQ, including T=0.
Consumer/boundary: supplies original terminal record integrability/mean; does not construct a general Q stochastic integrator.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalMeanSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs BrownianPredictableDensity
open BrownianBoundedPredictableApproximation BrownianBoundedTerminalL2Source BrownianFiniteDensityL2Source
open BrownianBoundedExponentialLimitSource BrownianBoundedMovingLawSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section

/-- Weak L2 convergence is DERIVED from actual density L1 convergence and
its uniform L2 bound, using native simple-function density. -/
theorem approximation_density_weak_two (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (g : Lp ℝ 2 sourceLaw) :
    Tendsto (fun n => ⟪approximationDensityTwo T f K hK hbound n,g⟫_ℝ) atTop
      (𝓝 ⟪fullDensityTwo T f K hK hbound,g⟫_ℝ) := by
  let dn := approximationDensityTwo T f K hK hbound
  let d := fullDensityTwo T f K hK hbound
  let B := Real.exp (K^2*(T : ℝ))+1
  have hdnb (n : ℕ) : ‖dn n‖≤B :=
    finiteDensityTwo_norm_le (approximation T f K hK hbound n) K hK
      (fun i => Eventually.of_forall (approximation_bound T f K hK hbound n i))
  let C : ℝ≥0 := ⟨B+‖d‖, by dsimp [B]; positivity⟩
  let F := fun n (q : Lp ℝ 2 sourceLaw) => ⟪dn n-d,q⟫_ℝ
  have hLip (n : ℕ) : LipschitzWith C (F n) := by
    apply ((innerSL ℝ (dn n-d)).lipschitz).weaken
    change ‖(innerSL ℝ) (dn n-d)‖₊≤C
    apply_mod_cast (show ‖(innerSL ℝ) (dn n-d)‖≤(C : ℝ) from ?_)
    rw [innerSL_apply_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hdnb n) le_rfl)
  have hClosed : IsClosed {q : Lp ℝ 2 sourceLaw | Tendsto (fun n => F n q) atTop (𝓝 0)} :=
    ((LipschitzWith.uniformEquicontinuous F C hLip).equicontinuous).isClosed_setOfPred_tendsto continuous_const
  have hSimple (s : Lp.simpleFunc ℝ 2 sourceLaw) : Tendsto (fun n => F n s) atTop (𝓝 0) := by
    let b := Lp.simpleFunc.toSimpleFunc s
    obtain ⟨M,hM⟩ := b.exists_forall_norm_le
    let δ := fun n ω => terminalDensity (approximation T f K hK hbound n) ω-fullDensity T f ω
    have hδ (n : ℕ) : Integrable (δ n) sourceLaw := by
      apply ((Lp.memLp (dn n-d)).integrable one_le_two).congr
      exact (Lp.coeFn_sub _ _).trans
        ((finiteDensityTwo_coe (approximation T f K hK hbound n) K hK
          (fun i => Eventually.of_forall (approximation_bound T f K hK hbound n i))).sub
            (fullDensityTwo_coe T f K hK hbound))
    have he (n : ℕ) : F n s=∫ ω, δ n ω*b ω ∂sourceLaw := by
      dsimp only [F]
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (dn n) d,
        finiteDensityTwo_coe (approximation T f K hK hbound n) K hK
          (fun i => Eventually.of_forall (approximation_bound T f K hK hbound n i)),
        fullDensityTwo_coe T f K hK hbound,Lp.simpleFunc.toSimpleFunc_eq_toFun s] with ω hs hn hd hb
      change ⟪(dn n-d) ω,(s : Lp ℝ 2 sourceLaw) ω⟫_ℝ=δ n ω*b ω
      rw [hs]
      change ⟪dn n ω-d ω,(s : Lp ℝ 2 sourceLaw) ω⟫_ℝ=_
      change dn n ω=terminalDensity (approximation T f K hK hbound n) ω at hn
      change d ω=fullDensity T f ω at hd
      rw [hn,hd,← hb]
      simp [δ,b,RCLike.inner_apply,mul_comm]
    have hUpper (n : ℕ) : ‖F n s‖≤M*(∫ ω, ‖δ n ω‖ ∂sourceLaw) := by
      rw [he]
      apply (norm_integral_le_integral_norm _).trans
      rw [← integral_const_mul]
      apply integral_mono_ae ((hδ n).mul_bdd b.aestronglyMeasurable (Eventually.of_forall hM)).norm
        ((hδ n).norm.const_mul M)
      exact Eventually.of_forall (fun ω => by
        change ‖δ n ω*b ω‖≤M*‖δ n ω‖
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hM ω) (norm_nonneg (δ n ω))).trans_eq (mul_comm _ _))
    have hlim := (approximation_density_integral_norm_tendsto T f K hK hbound).const_mul M
    have hnorm := squeeze_zero (fun n => norm_nonneg (F n s)) hUpper (by simpa only [mul_zero] using hlim)
    exact (tendsto_zero_iff_norm_tendsto_zero).mpr hnorm
  have hzero : Tendsto (fun n => F n g) atTop (𝓝 0) :=
    (Lp.simpleFunc.denseRange (E := ℝ) (μ := sourceLaw) (p := 2) (by norm_num)).induction_on g hClosed hSimple
  have h := hzero.add_const ⟪d,g⟫_ℝ
  simpa only [F,inner_sub_left,sub_add_cancel,zero_add] using h

/-- The zero pairing is carried by the ACTUAL returned finite terminal
records and both proved limits; no target expectation is supplied as a field. -/
theorem full_density_controlled_inner_zero (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    ⟪fullDensityTwo T f K hK hbound,controlledTerminalTwo T f K hK hbound⟫_ℝ=0 := by
  let dn := approximationDensityTwo T f K hK hbound
  let Jn := approximationControlledTwo T f K hK hbound
  let J := controlledTerminalTwo T f K hK hbound
  let B := Real.exp (K^2*(T : ℝ))+1
  have hdnb (n : ℕ) : ‖dn n‖≤B :=
    finiteDensityTwo_norm_le (approximation T f K hK hbound n) K hK
      (fun i => Eventually.of_forall (approximation_bound T f K hK hbound n i))
  have hnorm : Tendsto (fun n => ‖Jn n-J‖) atTop (𝓝 0) := by
    simpa only [J,Jn,norm_zero,sub_self] using
      ((approximation_controlled_two_tendsto T f K hK hbound).sub_const J).norm
  have hErrNorm : Tendsto (fun n => ‖⟪dn n,Jn n-J⟫_ℝ‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hdnb n) (norm_nonneg _)))
      (by simpa only [mul_zero] using hnorm.const_mul B)
  have hErr : Tendsto (fun n => ⟪dn n,Jn n-J⟫_ℝ) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hErrNorm
  have h := (approximation_density_weak_two T f K hK hbound J).add hErr
  have hPair : Tendsto (fun n => ⟪dn n,Jn n⟫_ℝ) atTop
      (𝓝 ⟪fullDensityTwo T f K hK hbound,J⟫_ℝ) := by
    have he (n : ℕ) : ⟪dn n,J⟫_ℝ+⟪dn n,Jn n-J⟫_ℝ=⟪dn n,Jn n⟫_ℝ := by
      rw [inner_sub_right]
      ring
    have hh := (tendsto_congr' (Eventually.of_forall he)).mp h
    simpa only [add_zero] using hh
  have hz : (fun n => ⟪dn n,Jn n⟫_ℝ)=(fun _ : ℕ => (0 : ℝ)) :=
    funext (approximation_density_controlled_inner_zero T f K hK hbound)
  rw [hz] at hPair
  exact (tendsto_nhds_unique tendsto_const_nhds hPair).symm

/-- Actual OWN-Q mean of native I_f minus ACTUAL source energy is zero.
This is proved for SAME bounded full input; it is not asserted for every L2 exponential. -/
theorem controlledTerminal_mean_zero (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    (∫ ω, controlledTerminal T f ω ∂fullLaw T f)=0 := by
  rw [full_integral_density]
  have he : ⟪fullDensityTwo T f K hK hbound,controlledTerminalTwo T f K hK hbound⟫_ℝ=
      ∫ ω, fullDensity T f ω*controlledTerminal T f ω ∂sourceLaw := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [fullDensityTwo_coe T f K hK hbound,controlledTerminalTwo_coe T f K hK hbound] with ω hd hj
    rw [hd,hj]
    simp [RCLike.inner_apply,mul_comm]
  rw [← he]
  exact full_density_controlled_inner_zero T f K hK hbound

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalMeanSource
