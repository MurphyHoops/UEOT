import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQCrossDrift
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalKLSource

/-!
Original commitment: original controlled-terminal record must return a genuinely constructed integral against its actual Q-Brownian noise.
Existing result: SAME bounded control owns native Q integral and actual finite-Q outputs; literal P/Q shift and actual cross-energy convergence are proved.
Premise reduced: identify SAME native Q integral with native P integral minus actual energy and bind the ORIGINAL TerminalGirsanovData returned variable.
Model/witness: actual own Q/W, original Fs and actual dt control/energy, SAME original f and selected tables, T=0 included.
Consumer/boundary: original P-KL terminal integral has genuine same-control Q-integrator provenance; full time-process/vector/general-filter Ito obligations remain.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralShift
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeEnergy BrownianIntegralEnergyL1 BrownianIntegralCrossVariation
open BrownianBoundedPredictableApproximation BrownianBoundedControlSource BrownianBoundedExponentialLimitSource
open BrownianBoundedTerminalL2Source BrownianBoundedTerminalKLSource
open BrownianOwnQTimeInput BrownianOwnQBoundedInput BrownianOwnQCrossDrift
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem sub_inMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (U V : ℕ → Ω → ℝ) (u v : Ω → ℝ)
    (hM : ∀ n, AEStronglyMeasurable (fun ω => U n ω-V n ω) P)
    (hU : TendstoInMeasure P U atTop u) (hV : TendstoInMeasure P V atTop v) :
    TendstoInMeasure P (fun n ω => U n ω-V n ω) atTop (fun ω => u ω-v ω) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hM).mpr
  intro ns hns
  obtain ⟨ms,hms,hUa⟩ := (hU.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨ls,hls,hVa⟩ := (hV.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).exists_seq_tendsto_ae
  refine ⟨ms ∘ ls,hms.comp hls,?_⟩
  filter_upwards [hUa,hVa] with ω hu hv
  exact (hu.comp hls.tendsto_atTop).sub hv

variable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)
include hK hbound

/-- Finite actual own-Q absolute continuity transports in-measure limits;
no inverse process or natural-filtration equality is inserted. -/
private theorem ownQ_inMeasure_of_source (X : ℕ → (ℝ≥0 → ℝ) → ℝ) (x : (ℝ≥0 → ℝ) → ℝ)
    (hM : ∀ n, AEStronglyMeasurable (X n) (fullLaw T f)) (hX : TendstoInMeasure sourceLaw X atTop x) :
    TendstoInMeasure (fullLaw T f) X atTop x := by
  let _ := fullLaw_probability T f K hK hbound
  apply (exists_seq_tendstoInMeasure_atTop_iff hM).mpr
  intro ns hns
  obtain ⟨ms,hms,hAE⟩ := (hX.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  exact ⟨ms,hms,(fullLaw_absolutelyContinuous T f).ae_le hAE⟩

/-- Actual change-of-integrator identity: the CONSTRUCTED own-Q stochastic
integral of SAME control is native P integral minus ACTUAL energy. This is
not an assignment of the desired controlled integral to that expression. -/
theorem boundedIntegralQ_eq_actual : boundedIntegralQ T f K hK hbound=ᵐ[fullLaw T f] controlledTerminal T f := by
  let r := approximation T f K hK hbound
  let X := fun n ω => outputValue (r n) ω-crossEnergyClass T T (literalPredictableInput (r n)) f ω
  have hM_P (n : ℕ) : AEStronglyMeasurable (X n) sourceLaw :=
    (Lp.aestronglyMeasurable (outputValue (r n))).sub (Lp.aestronglyMeasurable (crossEnergyClass T T (literalPredictableInput (r n)) f))
  have hM_Q (n : ℕ) : AEStronglyMeasurable (X n) (fullLaw T f) :=
    (hM_P n).mono_ac (fullLaw_absolutelyContinuous T f)
  have hX_P : TendstoInMeasure sourceLaw X atTop (controlledTerminal T f) := by
    have h := sub_inMeasure sourceLaw (fun n => (outputValue (r n) : (ℝ≥0 → ℝ) → ℝ))
      (fun n => (crossEnergyClass T T (literalPredictableInput (r n)) f : (ℝ≥0 → ℝ) → ℝ))
      (predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ) (energyClass T T f : (ℝ≥0 → ℝ) → ℝ) hM_P
      (tendstoInMeasure_of_tendsto_Lp (approximation_outputs_tendsto T f K hK hbound))
      (tendstoInMeasure_of_tendsto_Lp (actual_crossEnergy_tendsto T f K hK hbound))
    exact h.congr_right ((EventuallyEq.refl _ _).sub (energyClass_coe T T f))
  have hX_Q := ownQ_inMeasure_of_source T f K hK hbound X (controlledTerminal T f) hM_Q hX_P
  have hEq (n : ℕ) : outputValueQ T f K hK hbound (r n)=ᵐ[fullLaw T f] X n :=
    (BrownianOwnQSimpleIntegral.simpleIntegral_memLp_two T f K hK hbound (r n)).coeFn_toLp.trans
      ((fullLaw_absolutelyContinuous T f).ae_le (literal_integral_shift T f K hK hbound (r n)))
  have hActual := tendstoInMeasure_of_tendsto_Lp (actual_outputs_tendsto T f K hK hbound)
  exact tendstoInMeasure_ae_unique hActual (hX_Q.congr_left (fun n => (hEq n).symm))

/-- Original certificate's actual returned controlled variable is the SAME
constructed Q integral, not only another zero-mean random variable. -/
theorem original_terminal_returns_Q_integral :
    (BrownianBoundedTerminalKLSource.actualTerminalData T f K hK hbound).controlledIntegral=ᵐ[fullLaw T f]
      boundedIntegralQ T f K hK hbound := by
  have ht : terminalValue T f=ᵐ[fullLaw T f] controlledTerminal T f :=
    (fullLaw_absolutelyContinuous T f).ae_le (terminalValue_eq_actual T f)
  exact ht.trans (boundedIntegralQ_eq_actual T f K hK hbound).symm

/-- SAME native baseline and actual Q-integral satisfy the literal original
control-energy shift, with coefficient ONE on the energy term. -/
theorem actual_integral_shift : (predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ)=ᵐ[fullLaw T f]
    fun ω => boundedIntegralQ T f K hK hbound ω+UEOT.V3.GirsanovPathKL.controlEnergy T (control T f K) ω := by
  filter_upwards [boundedIntegralQ_eq_actual T f K hK hbound,
    (fullLaw_absolutelyContinuous T f).ae_le (control_energy_eq_actual T f K hbound)] with ω hi he
  rw [hi,he]
  unfold controlledTerminal
  ring

/-- Log-density decomposition now consumes the ACTUAL own-Q integral,
not a stipulated mean-zero substitute. -/
theorem actual_density_eq_Q_integral : fullDensity T f=ᵐ[fullLaw T f]
    fun ω => Real.exp (boundedIntegralQ T f K hK hbound ω+(1/2 : ℝ)*timeEnergy T f T ω) := by
  filter_upwards [boundedIntegralQ_eq_actual T f K hK hbound] with ω hi
  rw [hi]
  unfold fullDensity controlledTerminal
  congr 1
  ring

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralShift
