import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedPastMultiplier

/-!
Original commitment: the actual caller-left weighted M increment table must be consumed by SAME original input integral.
Existing result: original START sampling input L2 limit and actual bounded Fs future-window integral output identity.
Premise reduced: prove literal finite weighted output = I(sampled H*f), then consume its source L2 limit for actual weighted sums.
Model/witness: SAME original fullPredictableL2 T/sourceLaw/naturalFiltration, bounded continuous-adapted actual H and caller mono 0/T clocks.
Consumer: actual first-order Ito Riemann term; second-order weighted QV/Taylor remain separate, no Ito source field is assumed.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianWeightedIncrementBinding
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralContinuousVersion BrownianContinuousAdaptedInputs
open BrownianBoundedMultiplierLimit
open BrownianPartitionLeftInputs BrownianLeftMultiplierInputs BrownianBoundedPastMultiplier BrownianPredictableMultiplier BrownianQuadraticVariation
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem lp_sum_coe {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι) (F : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, F i : Lp ℝ 2 μ) =ᵐ[μ] fun ω => ∑ i ∈ s, F i ω := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
    simp only [Finset.sum_empty]
    exact hω
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j),ih] with ω ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

private theorem clock_cell_le {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ) (i : Fin n) :
    τ i.castSucc ≤ τ i.succ := hmono (by exact_mod_cast Nat.le_succ (i : ℕ))
private theorem clock_cell_end {T : ℝ≥0} {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hend : τ (Fin.last n)=T) (i : Fin n) : τ i.succ ≤ T :=
  (hmono (Fin.le_last i.succ)).trans hend.le

/-- Actual finite output table, evaluated on the SAME original continuous M. -/
def weightedIncrementSum (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (f : fullPredictableL2 T) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin n, H (τ i.castSucc) ω*
    (continuousIntegralProcess T f (τ i.succ) ω-continuousIntegralProcess T f (τ i.castSucc) ω)

private def cellInput (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hend : τ (Fin.last n)=T) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ u ω, ‖H u ω‖ ≤ K) (i : Fin n) (f : fullPredictableL2 T) : fullPredictableL2 T :=
  windowMultiplier T (τ i.castSucc) (τ i.succ) (clock_cell_le τ hmono i) (clock_cell_end τ hmono hend i)
    (H (τ i.castSucc)) (hadapt _) K hK (hb _) f

theorem sampledMultiplier_decomposition (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f =
      ∑ i : Fin n, cellInput T τ hmono hend H hadapt K hK hb i f := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  apply Lp.ext
  let r := sampleRecord T τ hmono hzero hend H hadapt K hb
  have hc : ∀ᵐ p ∂inputLaw T, ∀ i : Fin n,
      (cellInput T τ hmono hend H hadapt K hK hb i f : Lp ℝ 2 (inputLaw T)) p =
        intervalIntegrand (H (τ i.castSucc)) (τ i.castSucc) (τ i.succ) p*(f : Lp ℝ 2 (inputLaw T)) p :=
    ae_all_iff.mpr (fun i => windowMultiplier_coe T _ _ (clock_cell_le τ hmono i)
      (clock_cell_end τ hmono hend i) (H (τ i.castSucc)) (hadapt _) K hK (hb _) f)
  filter_upwards [boundedMultiplier_coe T (recordCoefficient r) (recordCoefficient_predictable r) K
    (Eventually.of_forall (recordCoefficient_bound r K hK (fun i ω => hb (τ i.castSucc) ω))) f,
    lp_sum_coe (inputLaw T) Finset.univ (fun i => (cellInput T τ hmono hend H hadapt K hK hb i f : Lp ℝ 2 (inputLaw T))),hc]
    with p hs hsum hc
  change (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f : Lp ℝ 2 (inputLaw T)) p = _ at hs
  rw [hs,hsum,Finset.sum_congr rfl (fun i _ => hc i)]
  change (∑ i : Fin n, intervalIntegrand (H (τ i.castSucc)) (τ i.castSucc) (τ i.succ) p)*
    (f : Lp ℝ 2 (inputLaw T)) p = _
  exact Finset.sum_mul _ _ _

/-- Concrete actual returned output of the original caller sample record:
EXACTLY the caller's finite START-weighted actual M increment table. -/
theorem sampledMultiplier_integral_coe (T : ℝ≥0) {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ)
    (hzero : τ 0=0) (hend : τ (Fin.last n)=T) (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hadapt : StronglyAdapted naturalFiltration H) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    (predictableIntegral T (sampledMultiplier T τ hmono hzero hend H hadapt K hK hb f) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      weightedIncrementSum T τ H f := by
  rw [sampledMultiplier_decomposition,map_sum]
  have hc : ∀ᵐ ω ∂sourceLaw, ∀ i : Fin n,
      predictableIntegral T (cellInput T τ hmono hend H hadapt K hK hb i f) ω =
        H (τ i.castSucc) ω*(continuousIntegralProcess T f (τ i.succ) ω-continuousIntegralProcess T f (τ i.castSucc) ω) :=
    ae_all_iff.mpr (fun i => windowMultiplier_integral_coe T _ _ (clock_cell_le τ hmono i)
      (clock_cell_end τ hmono hend i) (H (τ i.castSucc)) (hadapt _) K hK (hb _) f)
  filter_upwards [lp_sum_coe sourceLaw Finset.univ (fun i => predictableIntegral T
    (cellInput T τ hmono hend H hadapt K hK hb i f)),hc] with ω hs hc
  exact hs.trans (Finset.sum_congr rfl (fun i _ => hc i))

/-- Actual caller weighted increment tables converge to the SAME actual
continuous integral of SAME H*f. This is the first-order Ito Riemann term,
not a substituted existential integral or a desired source certificate. -/
theorem weightedIncrementSum_tendstoInMeasure (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (hjoint : Measurable (Function.uncurry H))
    (hadapt : StronglyAdapted naturalFiltration H) (hcont : ∀ᵐ ω ∂sourceLaw, Continuous (fun u => H u ω))
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ u ω, ‖H u ω‖ ≤ K) (f : fullPredictableL2 T) :
    TendstoInMeasure sourceLaw (fun m => weightedIncrementSum T (τ m) H f) atTop
      (continuousIntegralProcess T (continuousMultiplier T H hjoint hadapt hcont K hK hb f) T) :=
  TendstoInMeasure.congr (fun m => sampledMultiplier_integral_coe T (τ m) (hmono m) (hzero m) (hend m) H hadapt K hK hb f)
    (continuousIntegralProcess_horizon T _).symm (tendstoInMeasure_of_tendsto_Lp
      (sampledMultipliedIntegral_tendsto T N τ hmono hzero hend hmesh H hjoint hadapt hcont K hK hb f))

/-- Actual nonlinear first-order Ito consumer: the caller's literal
F(M_start) weighted SAME-M increments converge to the SAME source integral
of F(M)*f. For Ito choose F = phi'; no chain rule is assumed here. -/
theorem functionOfIntegral_weightedIncrement_tendstoInMeasure (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hzero : ∀ m, τ m 0=0) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (f : fullPredictableL2 T) (F : ℝ → ℝ) (hF : Continuous F)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x, ‖F x‖ ≤ K) :
    TendstoInMeasure sourceLaw (fun m => weightedIncrementSum T (τ m)
      (fun u ω => F (continuousIntegralProcess T f u ω)) f) atTop
      (continuousIntegralProcess T (functionOfIntegralInput T f F hF K hK hb) T) :=
  weightedIncrementSum_tendstoInMeasure T N τ hmono hzero hend hmesh
    (fun u ω => F (continuousIntegralProcess T f u ω))
    (hF.measurable.comp (continuousIntegralProcess_measurable T f))
    (fun u => hF.comp_stronglyMeasurable (continuousIntegralProcess_stronglyAdapted T f u))
    ((continuousIntegralProcess_continuous T f).mono (fun _ h => hF.comp h)) K hK (fun _ _ => hb _) f

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianWeightedIncrementBinding
