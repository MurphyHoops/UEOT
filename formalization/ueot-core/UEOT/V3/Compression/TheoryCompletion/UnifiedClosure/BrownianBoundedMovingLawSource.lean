import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedDriftLimitSource
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
Original commitment: full-input actual Q must inherit genuine finite joint laws relative to ORIGINAL Fs, not an inverse-filtration assumption.
Existing result: SAME actual D_n→OWN D in L1, actual tableW_n→SAME B-drift in P measure at each fixed time.
Premise reduced: transport actual finite-vector/readout tests with an arbitrary fixed bounded original-past factor to SAME fullQ.
Model/witness: original P, actual computed tableQ_n/fullQ, same f/K and actual readouts; finite supports and all fixed observation times.
Consumer/boundary: actual full shifted Brownian finite laws and original-Fs independence; no general natural-filtration equality is inferred.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedMovingLawSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeEnergy
open BrownianBoundedPredictableApproximation BrownianFiniteDensityL2Source BrownianFiniteStepExponentialSource
open BrownianBoundedExponentialLimitSource BrownianBoundedControlSource BrownianBoundedDriftLimitSource BrownianFiniteStepShiftedSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory BoundedContinuousFunction
noncomputable section

/-- Finite coordinate convergence in measure is proved by actual finite
union bounds; it is not an illegal uncountable AE intersection. -/
theorem finite_pi_inMeasure {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (X : ℕ → Ω → I → ℝ) (Y : Ω → I → ℝ)
    (h : ∀ i, TendstoInMeasure P (fun n ω => X n ω i) atTop (fun ω => Y ω i)) :
    TendstoInMeasure P X atTop Y := by
  classical
  intro ε hε
  have hs : Tendsto (fun n => ∑ i : I, P {ω | ε≤edist (X n ω i) (Y ω i)}) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => h i ε hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => bot_le)
  intro n
  apply (measure_mono (show {ω | ε≤edist (X n ω) (Y ω)} ⊆ ⋃ i : I, {ω | ε≤edist (X n ω i) (Y ω i)} from ?_)).trans
    (measure_iUnion_fintype_le P _)
  intro ω hω
  change ε≤edist (X n ω) (Y ω) at hω
  rw [edist_pi_def] at hω
  obtain ⟨i,_,hi⟩ := (Finset.le_sup_iff hε).mp hω
  exact Set.mem_iUnion.mpr ⟨i,hi⟩

/-- A scalar first-moment test error is controlled by the ACTUAL density
L1 error, uniformly over every supplied bounded measurable test. -/
private theorem density_test_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (d e h : Ω → ℝ) (hd : Integrable d P) (he : Integrable e P)
    (hh : AEStronglyMeasurable h P) (M : ℝ) (hM : ∀ ω, ‖h ω‖≤M) :
    ‖(∫ ω, d ω*h ω ∂P)-(∫ ω, e ω*h ω ∂P)‖≤M*(∫ ω, ‖d ω-e ω‖ ∂P) := by
  have hdi := hd.mul_bdd hh (Eventually.of_forall hM)
  have hei := he.mul_bdd hh (Eventually.of_forall hM)
  rw [← integral_sub hdi hei]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono
  · exact (hdi.sub hei).norm
  · exact (hd.sub he).norm.const_mul M
  · intro ω
    change ‖d ω*h ω-e ω*h ω‖≤M*‖d ω-e ω‖
    rw [← sub_mul,norm_mul]
    exact (mul_le_mul_of_nonneg_left (hM ω) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The actual finite and full density integrals have the SAME moving
readout, plus any fixed bounded ambient factor. START-past events are a
special case used later; their permissions are not enlarged here. -/
theorem actual_weighted_tests_tendsto {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)
    (X : ℕ → (ℝ≥0 → ℝ) → E) (Y : (ℝ≥0 → ℝ) → E)
    (hX : ∀ n, Measurable (X n))
    (hXY : TendstoInMeasure sourceLaw X atTop Y)
    (a : (ℝ≥0 → ℝ) → ℝ) (ha : Measurable a) (R : ℝ) (hR : 0≤R) (hA : ∀ ω, ‖a ω‖≤R) (φ : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, terminalDensity (approximation T f K hK hbound n) ω*(a ω*φ (X n ω)) ∂sourceLaw) atTop
      (𝓝 (∫ ω, fullDensity T f ω*(a ω*φ (Y ω)) ∂sourceLaw)) := by
  let r := approximation T f K hK hbound
  let d := fullDensity T f
  let M := R*‖φ‖
  have hM : 0≤M := mul_nonneg hR (norm_nonneg _)
  have htest (n : ℕ) : Measurable (fun ω => a ω*φ (X n ω)) := ha.mul (φ.continuous.measurable.comp (hX n))
  have htestB (n : ℕ) (ω : ℝ≥0 → ℝ) : ‖a ω*φ (X n ω)‖≤M := by
    rw [norm_mul]
    exact mul_le_mul (hA ω) (φ.norm_coe_le_norm _) (norm_nonneg _) hR
  have hi : Integrable d sourceLaw := fullDensity_integrable T f K hK hbound
  have hdn (n : ℕ) : Integrable (terminalDensity (r n)) sourceLaw := (prefix_integrable_mean (r n) _).1
  have herr : Tendsto (fun n => ∫ ω, ‖terminalDensity (r n) ω-d ω‖ ∂sourceLaw) atTop (𝓝 0) := by
    have hh := actual_densities_tendsto_L1 T f K hK hbound
    have hzero := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hh
    have he (n : ℕ) : (eLpNorm (terminalDensity (r n)-d) 1 sourceLaw).toReal=
        ∫ ω, ‖terminalDensity (r n) ω-d ω‖ ∂sourceLaw := by
      rw [eLpNorm_one_eq_lintegral_enorm,← integral_norm_eq_lintegral_enorm (hdn n |>.sub hi).aestronglyMeasurable]
      simp only [Pi.sub_apply]
    simpa only [ENNReal.toReal_zero] using (tendsto_congr' (Eventually.of_forall he)).mp hzero
  have herror : Tendsto (fun n => (∫ ω, terminalDensity (r n) ω*(a ω*φ (X n ω)) ∂sourceLaw)-
      ∫ ω, d ω*(a ω*φ (X n ω)) ∂sourceLaw) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      density_test_error sourceLaw _ _ _ (hdn n) hi (htest n).aestronglyMeasurable M (htestB n))
      (by simpa only [mul_zero] using herr.const_mul M)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms,hms,hXYa⟩ := (hXY.comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  have hdom : ∀ n, ∀ᵐ ω ∂sourceLaw, ‖d ω*(a ω*φ (X (ns (ms n)) ω))‖≤M*‖d ω‖ := by
    intro n
    apply Eventually.of_forall
    intro ω
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (htestB _ ω) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hlim : ∀ᵐ ω ∂sourceLaw, Tendsto (fun n => d ω*(a ω*φ (X (ns (ms n)) ω))) atTop
      (𝓝 (d ω*(a ω*φ (Y ω)))) := by
    filter_upwards [hXYa] with ω hω
    exact ((φ.continuous.tendsto (Y ω)).comp hω).const_mul (a ω) |>.const_mul (d ω)
  have hc := tendsto_integral_of_dominated_convergence (fun ω => M*‖d ω‖)
    (fun n => (hi.aestronglyMeasurable.mul (htest (ns (ms n))).aestronglyMeasurable))
    (hi.norm.const_mul M) hdom hlim
  have he := (herror.comp (hns.comp hms.tendsto_atTop)).add hc
  simpa only [Function.comp_def,Pi.mul_apply,zero_add,sub_add_cancel,r,d] using he

private theorem integral_ofReal_density {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (d : Ω → ℝ) (hd : Measurable d) (hpos : ∀ ω, 0≤d ω) (g : Ω → ℝ) :
    (∫ ω, g ω ∂P.withDensity (fun ω => ENNReal.ofReal (d ω)))=∫ ω, d ω*g ω ∂P := by
  rw [integral_withDensity_eq_integral_toReal_smul hd.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => by
    change (ENNReal.ofReal (d ω)).toReal • g ω=d ω*g ω
    rw [ENNReal.toReal_ofReal (hpos ω),smul_eq_mul])

/-- Literal original finite changed-measure integral, using its computed D. -/
theorem table_integral_density {T : ℝ≥0} (r : ElementaryInput T) (g : (ℝ≥0 → ℝ) → ℝ) :
    (∫ ω, g ω ∂tableLaw r)=∫ ω, terminalDensity r ω*g ω ∂sourceLaw := by
  exact integral_ofReal_density sourceLaw (terminalDensity r)
    ((prefix_past r (Fin.last r.n)).mono (naturalFiltration.le _)).measurable
    (fun ω => (prefix_pos r _ ω).le) g

/-- Literal original full changed-measure integral, using f's OWN native D. -/
theorem full_integral_density (T : ℝ≥0) (f : fullPredictableL2 T) (g : (ℝ≥0 → ℝ) → ℝ) :
    (∫ ω, g ω ∂fullLaw T f)=∫ ω, fullDensity T f ω*g ω ∂sourceLaw :=
  integral_ofReal_density sourceLaw (fullDensity T f) (fullDensity_measurable T f) (fun ω => (fullDensity_pos T f ω).le) g

/-- Actual moving Q integrals, retaining a fixed arbitrary bounded source
factor (in particular an event from the ENTIRE original Fs past). -/
theorem actual_tests_tendsto {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K)
    (X : ℕ → (ℝ≥0 → ℝ) → E) (Y : (ℝ≥0 → ℝ) → E) (hX : ∀ n, Measurable (X n))
    (hXY : TendstoInMeasure sourceLaw X atTop Y)
    (a : (ℝ≥0 → ℝ) → ℝ) (ha : Measurable a) (R : ℝ) (hR : 0≤R) (hA : ∀ ω, ‖a ω‖≤R) (φ : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, a ω*φ (X n ω) ∂tableLaw (approximation T f K hK hbound n)) atTop
      (𝓝 (∫ ω, a ω*φ (Y ω) ∂fullLaw T f)) := by
  rw [full_integral_density]
  have he (n : ℕ) := table_integral_density (approximation T f K hK hbound n) (fun ω => a ω*φ (X n ω))
  exact (tendsto_congr' (Eventually.of_forall he)).mpr
    (actual_weighted_tests_tendsto T f K hK hbound X Y hX hXY a ha R hR hA φ)

/-- Actual finite path vectors converge jointly on the original source. -/
theorem actual_finite_paths_tendstoInMeasure (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (I : Finset ℝ≥0) :
    TendstoInMeasure sourceLaw (fun n ω => I.restrict (tableProcess (approximation T f K hK hbound n) · ω)) atTop
      (fun ω => I.restrict (BrownianBoundedControlSource.shiftedProcess T f K · ω)) :=
  by
    change TendstoInMeasure sourceLaw
      (fun n ω (i : I) => tableProcess (approximation T f K hK hbound n) i ω) atTop
      (fun ω (i : I) => BrownianBoundedControlSource.shiftedProcess T f K i ω)
    exact finite_pi_inMeasure sourceLaw _ _ (fun i : I => actual_paths_tendstoInMeasure T (i : ℝ≥0) f K hK hbound)

/-- Complete actual finite joint readouts and bounded original-source
factors, measured under SAME actual Q_n and SAME actual fullQ. -/
theorem actual_finite_tests_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (I : Finset ℝ≥0)
    (a : (ℝ≥0 → ℝ) → ℝ) (ha : Measurable a) (R : ℝ) (hR : 0≤R) (hA : ∀ ω, ‖a ω‖≤R) (φ : (I → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, a ω*φ (I.restrict (tableProcess (approximation T f K hK hbound n) · ω))
      ∂tableLaw (approximation T f K hK hbound n)) atTop
      (𝓝 (∫ ω, a ω*φ (I.restrict (BrownianBoundedControlSource.shiftedProcess T f K · ω)) ∂fullLaw T f)) :=
  by
    let r := approximation T f K hK hbound
    have hm (n : ℕ) : Measurable (fun ω (i : I) => tableProcess (r n) i ω) :=
      measurable_pi_lambda _ (fun i : I => prefixProcess_measurable (r n) (Fin.last (r n).n) (i : ℝ≥0))
    exact actual_tests_tendsto (E := I → ℝ) T f K hK hbound
      (fun n ω (i : I) => tableProcess (r n) i ω)
      (fun ω (i : I) => BrownianBoundedControlSource.shiftedProcess T f K i ω)
      hm (actual_finite_paths_tendstoInMeasure T f K hK hbound I) a ha R hR hA φ

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedMovingLawSource
