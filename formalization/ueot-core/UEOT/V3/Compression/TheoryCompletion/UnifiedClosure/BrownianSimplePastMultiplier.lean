import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLeftMultiplierInputs

/-!
Original commitment: actual weighted increment sums must bind to actual multiplied inputs, using ONLY each START's past.
Existing result: full-input event localization, native finite linear integration and actual continuous output readout.
Premise reduced: derive true integral = past coefficient * actual increment for ORIGINAL Fs SIMPLE coefficients by actual finite event decomposition.
Model/witness: SAME original fullPredictableL2 T/sourceLaw/naturalFiltration, actual finite SimpleFunc with original Fs fibers, future (s,min(t,T)].
Consumer: bounded Fs coefficient approximation and actual left-weighted increment binding; not yet general bounded coefficient or Ito.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSimplePastMultiplier
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralContinuousVersion BrownianIntegralPastLocalization
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

private theorem linear_sum_coe {α ι E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure α) (L : E →L[ℝ] Lp ℝ 2 μ)
    (S : Finset ι) (c : ι → ℝ) (v : ι → E) (F : ι → α → ℝ)
    (hF : ∀ i ∈ S, (L (v i) : α → ℝ) =ᵐ[μ] F i) :
    (L (∑ i ∈ S, c i • v i) : α → ℝ) =ᵐ[μ] fun x => ∑ i ∈ S, c i*F i x := by
  have he : L (∑ i ∈ S, c i • v i) = ∑ i ∈ S, c i • L (v i) := by simp only [map_sum,map_smul]
  rw [he]
  have hi : ∀ᵐ x ∂μ, ∀ i ∈ S, (c i • L (v i)) x = c i*F i x := by
    apply (eventually_all_finset S).mpr
    intro i hi
    filter_upwards [Lp.coeFn_smul (c i) (L (v i)),hF i hi] with x hsm hv
    simp only [Pi.smul_apply,smul_eq_mul] at hsm
    exact hsm.trans (congrArg (fun t : ℝ => c i*t) hv)
  filter_upwards [lp_sum_coe μ S (fun i => c i • L (v i)),hi] with x hs hi
  exact hs.trans (Finset.sum_congr rfl hi)

/-- Original Fs finite source partition, followed by actual original window
localizations. No coefficient is permitted before original s. -/
def simplePastInput (T s t : ℝ≥0) (S : SimpleFunc (ℝ≥0 → ℝ) ℝ)
    (hSp : ∀ c, MeasurableSet[naturalFiltration s] (S ⁻¹' {c}))
    (f : fullPredictableL2 T) : fullPredictableL2 T :=
  ∑ c ∈ S.range, c • localize T s t (S ⁻¹' {c}) (hSp c) f

private theorem simple_fiber_sum (S : SimpleFunc (ℝ≥0 → ℝ) ℝ)
    (ω : ℝ≥0 → ℝ) (Y : (ℝ≥0 → ℝ) → ℝ) :
    (∑ c ∈ S.range, c*(S ⁻¹' {c}).indicator Y ω) = S ω*Y ω := by
  classical
  rw [Finset.sum_eq_single (S ω)]
  · simp
  · intro c _ hc
    have h : ω ∉ S ⁻¹' {c} := by simpa only [mem_preimage,mem_singleton_iff] using Ne.symm hc
    simp only [Set.indicator_of_notMem h,mul_zero]
  · simp only [S.mem_range_self,not_true_eq_false,IsEmpty.forall_iff]

theorem simplePastInput_coe (T s t : ℝ≥0) (S : SimpleFunc (ℝ≥0 → ℝ) ℝ)
    (hSp : ∀ c, MeasurableSet[naturalFiltration s] (S ⁻¹' {c})) (f : fullPredictableL2 T) : (simplePastInput T s t S hSp f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T]
      fun p => S p.2*(eventWindow T s t univ).indicator (f : Lp ℝ 2 (inputLaw T)) p := by
  have he : (simplePastInput T s t S hSp f : Lp ℝ 2 (inputLaw T)) =
      ∑ c ∈ S.range, c • (localize T s t (S ⁻¹' {c}) (hSp c) f : Lp ℝ 2 (inputLaw T)) := by
    simp only [simplePastInput,Submodule.coe_sum,Submodule.coe_smul]
  rw [he]
  have hc : ∀ᵐ p ∂inputLaw T, ∀ c ∈ S.range,
      (c • (localize T s t (S ⁻¹' {c}) (hSp c) f : Lp ℝ 2 (inputLaw T))) p =
        c*(eventWindow T s t (S ⁻¹' {c})).indicator (f : Lp ℝ 2 (inputLaw T)) p := by
    apply (eventually_all_finset S.range).mpr
    intro c _
    filter_upwards [Lp.coeFn_smul c (localize T s t (S ⁻¹' {c}) (hSp c) f : Lp ℝ 2 (inputLaw T)),
      localize_coe T s t (S ⁻¹' {c}) (hSp c) f] with p hsm hl
    simp only [Pi.smul_apply,smul_eq_mul] at hsm
    exact hsm.trans (congrArg (fun x : ℝ => c*x) hl)
  filter_upwards [lp_sum_coe (inputLaw T) S.range (fun c => c •
    (localize T s t (S ⁻¹' {c}) (hSp c) f : Lp ℝ 2 (inputLaw T))),hc] with p hs hc
  rw [hs,Finset.sum_congr rfl hc]
  by_cases ht : p.1 ∈ Ioc (s : ℝ) ((min t T : ℝ≥0) : ℝ)
  · have he (c : ℝ) : (eventWindow T s t (S ⁻¹' {c})).indicator (f : Lp ℝ 2 (inputLaw T)) p =
        (S ⁻¹' {c}).indicator (fun _ => (f : Lp ℝ 2 (inputLaw T)) p) p.2 := by
      by_cases hc : p.2 ∈ S ⁻¹' {c}
      · have hp : p ∈ eventWindow T s t (S ⁻¹' {c}) := ⟨ht,hc⟩
        rw [Set.indicator_of_mem hp,Set.indicator_of_mem hc]
      · have hp : p ∉ eventWindow T s t (S ⁻¹' {c}) := fun hp => hc hp.2
        rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hc]
    simp_rw [he]
    rw [simple_fiber_sum]
    rw [Set.indicator_of_mem (show p ∈ eventWindow T s t univ from ⟨ht,mem_univ _⟩)]
  · have he (c : ℝ) : p ∉ eventWindow T s t (S ⁻¹' {c}) := fun hp => ht hp.1
    simp only [Set.indicator_of_notMem (he _),mul_zero,Finset.sum_const_zero]
    have hp : p ∉ eventWindow T s t univ := fun hp => ht hp.1
    simp only [Set.indicator_of_notMem hp,mul_zero]

/-- Actual finite source output bound by original event-localization theorem. -/
theorem simplePastInput_integral_coe (T s t : ℝ≥0) (hst : s ≤ t)
    (S : SimpleFunc (ℝ≥0 → ℝ) ℝ)
    (hSp : ∀ c, MeasurableSet[naturalFiltration s] (S ⁻¹' {c})) (f : fullPredictableL2 T) :
    (predictableIntegral T (simplePastInput T s t S hSp f) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      fun ω => S ω*(continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω) := by
  have hi := linear_sum_coe sourceLaw (predictableIntegral T) S.range (fun c => c)
    (fun c => localize T s t (S ⁻¹' {c}) (hSp c) f)
    (fun c => (S ⁻¹' {c}).indicator (fun ω => continuousIntegralProcess T f t ω-continuousIntegralProcess T f s ω))
    (fun c _ => predictableIntegral_localize_coe T s t hst (S ⁻¹' {c}) (hSp c) f)
  exact hi.trans (Eventually.of_forall (fun ω => simple_fiber_sum S ω _))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianSimplePastMultiplier
