import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedGirsanovSource

/-!
Original commitment: the original full-input terminal KL record needs actual controlled I-energy integrability and zero mean, not desired fields.
Existing result: SAME bounded f owns normalized D/fullQ, actual original-Fs Brownian source and SAME bounded finite-table approximants.
Premise reduced: derive actual source L2 density/energy bounds and strong L2 convergence of returned terminal I_n-energy_n.
Model/witness: native fullPredictableL2 f, source-AE sameK, actual originalP/Q and returned tables, literal actual timeEnergy including T=0.
Consumer/boundary: actual native weak L2 pairing limit supplies fullQ controlled terminal mean0 next; no generalQ integral framework is asserted.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalL2Source
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeEnergy BrownianIntegralEnergyL1
open BrownianBoundedPredictableApproximation BrownianFiniteDensityL2Source BrownianFiniteStepExponentialSource
open BrownianBoundedExponentialLimitSource BrownianBoundedControlSource BrownianBoundedMovingLawSource
open UEOT.V3.GirsanovPathKL
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory InnerProductSpace RealInnerProductSpace
noncomputable section

private theorem norm_sq_toLp (g : (ℝ≥0 → ℝ) → ℝ) (hg : MemLp g 2 sourceLaw) :
    ‖hg.toLp g‖^2=∫ ω, g ω^2 ∂sourceLaw := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
  apply integral_congr_ae
  exact hg.coeFn_toLp.mono (fun _ h => congrArg (fun x : ℝ => x^2) h)

/-- The actual permitted real control gives the actual SAME-input energy
bound; this uses its real dt integral rather than a desired bracket field. -/
theorem fullEnergy_bound (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    ∀ᵐ ω ∂sourceLaw, 0≤timeEnergy T f T ω ∧ timeEnergy T f T ω≤K^2*(T : ℝ) := by
  filter_upwards [control_energy_eq_actual T f K hbound] with ω he
  refine ⟨timeEnergy_nonneg _ _ _ _,?_⟩
  rw [← he]
  have hh := intervalIntegral.integral_mono_on T.coe_nonneg
    (control_energy_intervalIntegrable T f K hK ω) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => K^2) volume 0 (T : ℝ))
    (fun t _ => (sq_le_sq₀ (norm_nonneg _) hK).mpr (control_bound T f K hK t ω))
  simpa only [controlEnergy,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using hh

/-- Actual source energy is bounded/L2 under this explicit sufficient
bounded-input condition; no such L2 claim is made for arbitrary L2 inputs. -/
theorem fullEnergy_memLp_top (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : MemLp (timeEnergy T f T) ∞ sourceLaw := by
  apply MemLp.of_bound ((timeEnergy_stronglyAdapted T f T).mono (naturalFiltration.le T)).aestronglyMeasurable (K^2*(T : ℝ))
  filter_upwards [fullEnergy_bound T f K hK hbound] with ω hω
  simpa only [Real.norm_eq_abs,abs_of_nonneg hω.1] using hω.2

def fullEnergyTwo (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : Lp ℝ 2 sourceLaw :=
  ((fullEnergy_memLp_top T f K hK hbound).mono_exponent (show (2 : ℝ≥0∞)≤∞ from le_top)).toLp (timeEnergy T f T)

theorem fullEnergyTwo_coe (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    fullEnergyTwo T f K hK hbound=ᵐ[sourceLaw] timeEnergy T f T :=
  ((fullEnergy_memLp_top T f K hK hbound).mono_exponent (show (2 : ℝ≥0∞)≤∞ from le_top)).coeFn_toLp

private theorem finiteDensity_memLp_two {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) : MemLp (terminalDensity r) 2 sourceLaw :=
  (memLp_two_iff_integrable_sq ((prefix_past r _).mono (naturalFiltration.le _)).aestronglyMeasurable).mpr
    (bounded_density_square r K hK hH).1

def finiteDensityTwo {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) : Lp ℝ 2 sourceLaw :=
  (finiteDensity_memLp_two r K hK hH).toLp (terminalDensity r)

theorem finiteDensityTwo_coe {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) :
    finiteDensityTwo r K hK hH=ᵐ[sourceLaw] terminalDensity r := (finiteDensity_memLp_two r K hK hH).coeFn_toLp

/-- An explicit finite bound on the ACTUAL density L2 norm, uniform in the
number/locations of supplied rows. It is analysis evidence, not a threshold change. -/
theorem finiteDensityTwo_norm_le {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) :
    ‖finiteDensityTwo r K hK hH‖≤Real.exp (K^2*(T : ℝ))+1 := by
  have he : ‖finiteDensityTwo r K hK hH‖^2=∫ ω, terminalDensity r ω^2 ∂sourceLaw := norm_sq_toLp _ _
  have hb := (bounded_density_square r K hK hH).2
  have hp := Real.exp_pos (K^2*(T : ℝ))
  have hn := norm_nonneg (finiteDensityTwo r K hK hH)
  nlinarith [sq_nonneg (Real.exp (K^2*(T : ℝ)))]

/-- Actual full density lies in source L2 by native lower-semicontinuity
under the already proved actual D_n→D in measure. -/
theorem fullDensity_memLp_two (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : MemLp (fullDensity T f) 2 sourceLaw := by
  let r := approximation T f K hK hbound
  have hb (n : ℕ) : eLpNorm (terminalDensity (r n)) 2 sourceLaw≤ENNReal.ofReal (Real.exp (K^2*(T : ℝ))+1) := by
    have hn := finiteDensityTwo_norm_le (r n) K hK (fun i => Eventually.of_forall (approximation_bound T f K hK hbound n i))
    have hm := finiteDensity_memLp_two (r n) K hK (fun i => Eventually.of_forall (approximation_bound T f K hK hbound n i))
    rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    simpa only [finiteDensityTwo,Lp.norm_toLp] using hn
  have hl := eLpNorm_le_of_tendstoInMeasure (p := 2) (Eventually.of_forall hb)
    (actual_densities_tendstoInMeasure T f K hK hbound)
    (fun n => ((prefix_past (r n) _).mono (naturalFiltration.le _)).aestronglyMeasurable)
  exact ⟨(fullDensity_measurable T f).aestronglyMeasurable,hl.trans_lt ENNReal.ofReal_lt_top⟩

def fullDensityTwo (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : Lp ℝ 2 sourceLaw :=
  (fullDensity_memLp_two T f K hK hbound).toLp (fullDensity T f)

theorem fullDensityTwo_coe (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    fullDensityTwo T f K hK hbound=ᵐ[sourceLaw] fullDensity T f := (fullDensity_memLp_two T f K hK hbound).coeFn_toLp

private theorem finiteEnergy_measurable {T : ℝ≥0} (r : ElementaryInput T) : Measurable (tableEnergy r) := by
  unfold tableEnergy
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
    (((r.coefficient_past i).mono (naturalFiltration.le _)).measurable.pow_const 2))
private theorem finiteEnergy_nonneg {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) : 0≤tableEnergy r ω := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg _ (sq_nonneg _)
  exact sub_nonneg.mpr (by exact_mod_cast r.clock_mono (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ)))

private theorem finiteEnergy_memLp_top {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) : MemLp (tableEnergy r) ∞ sourceLaw := by
  apply MemLp.of_bound (finiteEnergy_measurable r).aestronglyMeasurable (K^2*(T : ℝ))
  filter_upwards [tableEnergy_le_of_coefficients r K hK hH] with ω hω
  simpa only [Real.norm_eq_abs,abs_of_nonneg (finiteEnergy_nonneg r ω)] using hω

def finiteEnergyTwo {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) : Lp ℝ 2 sourceLaw :=
  ((finiteEnergy_memLp_top r K hK hH).mono_exponent (show (2 : ℝ≥0∞)≤∞ from le_top)).toLp (tableEnergy r)

theorem finiteEnergyTwo_coe {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) :
    finiteEnergyTwo r K hK hH=ᵐ[sourceLaw] tableEnergy r :=
  ((finiteEnergy_memLp_top r K hK hH).mono_exponent (show (2 : ℝ≥0∞)≤∞ from le_top)).coeFn_toLp

/-- Exact full-input terminal quantity: native returned I minus ACTUAL
energy (coefficient ONE), matching the original substitution contract. -/
def controlledTerminal (T : ℝ≥0) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) : ℝ :=
  (predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ) ω-timeEnergy T f T ω

def controlledTerminalTwo (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : Lp ℝ 2 sourceLaw :=
  predictableIntegral T f-fullEnergyTwo T f K hK hbound

theorem controlledTerminalTwo_coe (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    controlledTerminalTwo T f K hK hbound=ᵐ[sourceLaw] controlledTerminal T f := by
  apply (Lp.coeFn_sub (predictableIntegral T f) (fullEnergyTwo T f K hK hbound)).trans
  exact EventuallyEq.rfl.sub (fullEnergyTwo_coe T f K hK hbound)

theorem controlledTerminal_memLp_two (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) : MemLp (controlledTerminal T f) 2 sourceLaw :=
  (memLp_congr_ae (controlledTerminalTwo_coe T f K hK hbound)).mp (Lp.memLp (controlledTerminalTwo T f K hK hbound))

/-- Actual fullQ integrability is derived by source Holder and literal
withDensity, rather than assumed with a desired martingale field. -/
theorem controlledTerminal_integrable_fullLaw (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Integrable (controlledTerminal T f) (fullLaw T f) := by
  have hi := (fullDensity_memLp_two T f K hK hbound).integrable_mul (controlledTerminal_memLp_two T f K hK hbound)
  apply (integrable_withDensity_iff_integrable_smul' (fullDensity_measurable T f).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  apply hi.congr
  exact Eventually.of_forall (fun ω => by
    change fullDensity T f ω*controlledTerminal T f ω=(ENNReal.ofReal (fullDensity T f ω)).toReal • controlledTerminal T f ω
    rw [ENNReal.toReal_ofReal (fullDensity_pos T f ω).le,smul_eq_mul])

private theorem approximation_bound_ae (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) :
    ∀ i, ∀ᵐ ω ∂sourceLaw, |(approximation T f K hK hbound n).coefficient i ω|≤K :=
  fun i => Eventually.of_forall (approximation_bound T f K hK hbound n i)

def approximationEnergyTwo (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) : Lp ℝ 2 sourceLaw :=
  finiteEnergyTwo (approximation T f K hK hbound n) K hK (approximation_bound_ae T f K hK hbound n)

def approximationDensityTwo (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) : Lp ℝ 2 sourceLaw :=
  finiteDensityTwo (approximation T f K hK hbound n) K hK (approximation_bound_ae T f K hK hbound n)

def approximationControlledTwo (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) : Lp ℝ 2 sourceLaw :=
  outputValue (approximation T f K hK hbound n)-approximationEnergyTwo T f K hK hbound n

/-- Bounded actual energies strengthen their original natural-L1
convergence to L2. This strengthening uses SAME explicit K and is NOT
asserted for general unbounded predictable L2 inputs. -/
theorem approximation_energy_two_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Tendsto (approximationEnergyTwo T f K hK hbound) atTop (𝓝 (fullEnergyTwo T f K hK hbound)) := by
  let r := approximation T f K hK hbound
  let C := K^2*(T : ℝ)
  let E := fun n => approximationEnergyTwo T f K hK hbound n-fullEnergyTwo T f K hK hbound
  let δ := fun n ω => tableEnergy (r n) ω-timeEnergy T f T ω
  have hco (n : ℕ) : E n=ᵐ[sourceLaw] δ n :=
    (Lp.coeFn_sub _ _).trans ((finiteEnergyTwo_coe (r n) K hK (approximation_bound_ae T f K hK hbound n)).sub
      (fullEnergyTwo_coe T f K hK hbound))
  have hδ (n : ℕ) : MemLp (δ n) 2 sourceLaw := (memLp_congr_ae (hco n)).mp (Lp.memLp (E n))
  have hL1 : Tendsto (fun n => eLpNorm (δ n) 1 sourceLaw) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (approximation_energy_tendsto T f K hK hbound T)
    have he (n : ℕ) : eLpNorm (⇑(energyClass T T (literalPredictableInput (r n)))-⇑(energyClass T T f)) 1 sourceLaw=eLpNorm (δ n) 1 sourceLaw := by
      apply eLpNorm_congr_ae
      exact ((energyClass_coe T T (literalPredictableInput (r n))).trans
        (BrownianLiteralGridBinding.timeEnergy_literal_horizon (r n))).sub (energyClass_coe T T f)
    exact (tendsto_congr' (Eventually.of_forall he)).mp h
  have hIntegralNorm : Tendsto (fun n => ∫ ω, ‖δ n ω‖ ∂sourceLaw) atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hL1
    have he (n : ℕ) : (eLpNorm (δ n) 1 sourceLaw).toReal=∫ ω, ‖δ n ω‖ ∂sourceLaw := by
      rw [eLpNorm_one_eq_lintegral_enorm,← integral_norm_eq_lintegral_enorm (hδ n).aestronglyMeasurable]
    simpa only [ENNReal.toReal_zero] using (tendsto_congr' (Eventually.of_forall he)).mp h
  have hb (n : ℕ) : ∀ᵐ ω ∂sourceLaw, δ n ω^2≤(2*C)*‖δ n ω‖ := by
    filter_upwards [tableEnergy_le_of_coefficients (r n) K hK (approximation_bound_ae T f K hK hbound n),
      fullEnergy_bound T f K hK hbound] with ω hn hf
    have hnon := finiteEnergy_nonneg (r n) ω
    have habs : |δ n ω|≤2*C := by
      rw [abs_le]
      change -(2*C)≤tableEnergy (r n) ω-timeEnergy T f T ω ∧ tableEnergy (r n) ω-timeEnergy T f T ω≤2*C
      have hC : 0≤C := mul_nonneg (sq_nonneg K) T.coe_nonneg
      constructor <;> dsimp only [C] at * <;> linarith
    have hh := mul_le_mul_of_nonneg_right habs (abs_nonneg (δ n ω))
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (δ n ω)]
  have hi (n : ℕ) : (∫ ω, δ n ω^2 ∂sourceLaw)≤(2*C)*(∫ ω, ‖δ n ω‖ ∂sourceLaw) := by
    have h := integral_mono_ae (hδ n).integrable_sq (((hδ n).integrable one_le_two).norm.const_mul (2*C)) (hb n)
    rw [integral_const_mul] at h
    exact h
  have hs : Tendsto (fun n => ∫ ω, δ n ω^2 ∂sourceLaw) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _)) hi
      (by simpa only [mul_zero] using hIntegralNorm.const_mul (2*C))
  have he (n : ℕ) : ‖E n‖^2=∫ ω, δ n ω^2 ∂sourceLaw := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]
    exact integral_congr_ae ((hco n).mono (fun _ h => congrArg (fun x : ℝ => x^2) h))
  have hsNorm : Tendsto (fun n => ‖E n‖^2) atTop (𝓝 0) := (tendsto_congr' (Eventually.of_forall he)).mpr hs
  have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsNorm
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _),Real.sqrt_zero] using h

/-- SAME returned I_n minus SAME actual energy_n converges strongly to
native I_f minus ACTUAL energy_f, with no external controlled terminal field. -/
theorem approximation_controlled_two_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Tendsto (approximationControlledTwo T f K hK hbound) atTop (𝓝 (controlledTerminalTwo T f K hK hbound)) :=
  (approximation_outputs_tendsto T f K hK hbound).sub (approximation_energy_two_tendsto T f K hK hbound)

/-- SAME original finite terminal controlled integral, with no alternate
policy, source or returned variable selected for the limiting proof. -/
theorem approximationControlledTwo_coe (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) :
    approximationControlledTwo T f K hK hbound n=ᵐ[sourceLaw]
      BrownianFiniteStepTerminalKLSource.centeredIntegral (approximation T f K hK hbound n) := by
  let r := approximation T f K hK hbound n
  have hI : outputValue r=ᵐ[sourceLaw] BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient :=
    (BrownianSimplePredictableIntegral.simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (outputValue r) (approximationEnergyTwo T f K hK hbound n),hI,
    finiteEnergyTwo_coe r K hK (approximation_bound_ae T f K hK hbound n)] with ω hs hi he
  change (outputValue r-approximationEnergyTwo T f K hK hbound n) ω=_
  rw [hs]
  simp only [Pi.sub_apply]
  change _-finiteEnergyTwo r K hK (approximation_bound_ae T f K hK hbound n) ω=_
  rw [hi,he]
  have hh := BrownianFiniteStepTerminalKLSource.literal_integral_shift r ω
  linarith

/-- Native source L2 pairing of THESE actual density and actual returned
controlled terminal values is zero, DERIVED from the original finite true
martingale consumer and literal same-Q density integral identity. -/
theorem approximation_density_controlled_inner_zero (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) :
    ⟪approximationDensityTwo T f K hK hbound n,approximationControlledTwo T f K hK hbound n⟫_ℝ=0 := by
  let r := approximation T f K hK hbound n
  have he : ⟪approximationDensityTwo T f K hK hbound n,approximationControlledTwo T f K hK hbound n⟫_ℝ=
      ∫ ω, terminalDensity r ω*BrownianFiniteStepTerminalKLSource.centeredIntegral r ω ∂sourceLaw := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [finiteDensityTwo_coe r K hK (approximation_bound_ae T f K hK hbound n),
      approximationControlledTwo_coe T f K hK hbound n] with ω hd hj
    change ⟪finiteDensityTwo r K hK (approximation_bound_ae T f K hK hbound n) ω,
      approximationControlledTwo T f K hK hbound n ω⟫_ℝ=_
    change approximationControlledTwo T f K hK hbound n ω=BrownianFiniteStepTerminalKLSource.centeredIntegral r ω at hj
    rw [hd,hj]
    simp [RCLike.inner_apply,mul_comm]
  rw [he,← table_integral_density]
  exact (BrownianFiniteStepTerminalKLSource.actualTerminalData r).controlledIntegral_mean_zero

/-- Actual densities converge in the ordinary source L1 norm; this is the
same unrenormalized exponential and the same selected finite tables. -/
theorem approximation_density_integral_norm_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Tendsto (fun n => ∫ ω, ‖terminalDensity (approximation T f K hK hbound n) ω-fullDensity T f ω‖ ∂sourceLaw)
      atTop (𝓝 0) := by
  have h := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp
    (actual_densities_tendsto_L1 T f K hK hbound)
  have he (n : ℕ) :
      (eLpNorm (terminalDensity (approximation T f K hK hbound n)-fullDensity T f) 1 sourceLaw).toReal=
        ∫ ω, ‖terminalDensity (approximation T f K hK hbound n) ω-fullDensity T f ω‖ ∂sourceLaw := by
    rw [eLpNorm_one_eq_lintegral_enorm,← integral_norm_eq_lintegral_enorm
      ((finiteDensity_memLp_two (approximation T f K hK hbound n) K hK
        (approximation_bound_ae T f K hK hbound n)).aestronglyMeasurable.sub
          (fullDensity_memLp_two T f K hK hbound).aestronglyMeasurable)]
    rfl
  simpa only [ENNReal.toReal_zero] using (tendsto_congr' (Eventually.of_forall he)).mp h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalL2Source
