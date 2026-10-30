import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteSpanLeftInputs
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralTimeEnergy
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteDensityL2Source
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralEnergyL1

/-!
Original commitment: bounded full-predictable density limits must derive actual SAME-input finite tables with the SAME K.
Existing result: native fullPredictableL2 is genuinely predictable; original finite spans have actual causal left-table approximations.
Premise reduced: derive bounded predictable representatives and SAME-K actual ElementaryInput approximants, not an approximant-exists field.
Model/witness: SAME inputLaw T=dt|[0,T] times sourceLaw, true original Fs START permissions, source-AE |f|<=K, including T=0.
Consumer/boundary: actual density UI/normalization limit; no raw Lp coercion is upgraded to pointwise progressive control or general limit-Q source.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedPredictableApproximation
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralFinitePaths BrownianContinuousAdaptedInputs
open BrownianFiniteSpanLeftInputs BrownianIntegralTimeEnergy
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem clip_continuous (K : ℝ) : Continuous (clip K) :=
  continuous_const.max (continuous_const.min continuous_id)
private theorem clip_bound (K : ℝ) (hK : 0≤K) (x : ℝ) : ‖clip K x‖≤K := by
  rw [Real.norm_eq_abs,abs_le]
  exact ⟨le_max_left _ _,max_le (by linarith) (min_le_left _ _)⟩
private theorem clip_fixed (K y : ℝ) (hy : |y|≤K) : clip K y=y := by
  have h := abs_le.mp hy
  simp only [clip,min_eq_right h.2,max_eq_right h.1]
private theorem clip_distance (K x y : ℝ) (hy : |y|≤K) : ‖clip K x-y‖≤‖x-y‖ := by
  have hL : LipschitzWith 1 (clip K) := (LipschitzWith.id.const_min K).const_max (-K)
  have h := hL.dist_le_mul x y
  rw [clip_fixed K y hy] at h
  simp only [NNReal.coe_one,one_mul] at h
  simpa only [dist_eq_norm] using h

/-- Actual predictable representative, clipped everywhere to SAME K.
Its permission is selected from native lpMeas, not inferred from raw coercions. -/
def boundedRepresentative (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (p : ℝ × (ℝ≥0 → ℝ)) : ℝ :=
  clip K (representative T f p)

theorem boundedRepresentative_predictable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) :
    StronglyMeasurable[predictableSigma] (boundedRepresentative T f K) :=
  (clip_continuous K).comp_stronglyMeasurable (representative_predictable T f)

theorem boundedRepresentative_bound (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K) (p : ℝ × (ℝ≥0 → ℝ)) :
    ‖boundedRepresentative T f K p‖≤K := clip_bound K hK _

theorem boundedRepresentative_ae (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    (f : Lp ℝ 2 (inputLaw T)) =ᵐ[inputLaw T] boundedRepresentative T f K := by
  filter_upwards [representative_ae T f,hbound] with p hp hb
  change _=clip K (representative T f p)
  rw [← hp,clip_fixed K _ hb]

/-- Bounded causal trace of the actual ORIGINAL finite span. Clipping does
not look at any future or change the target full-predictable class. -/
def boundedSpanTrace (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (K : ℝ) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  clip K (spanTrace T a u ω)
private theorem trace_joint (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (K : ℝ) :
    Measurable (Function.uncurry (boundedSpanTrace T a K)) :=
  (clip_continuous K).measurable.comp (spanTrace_measurable T a)
private theorem trace_adapted (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (K : ℝ) :
    StronglyAdapted naturalFiltration (boundedSpanTrace T a K) :=
  fun u => (clip_continuous K).comp_stronglyMeasurable (spanTrace_adapted T a u)
private theorem trace_bound (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (K : ℝ) (hK : 0≤K) :
    ∀ u ω, ‖boundedSpanTrace T a K u ω‖≤K := fun _ _ => clip_bound K hK _
private theorem trace_left (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (K : ℝ) (u : ℝ≥0) (ω : ℝ≥0 → ℝ) :
    ContinuousWithinAt (fun v => boundedSpanTrace T a K v ω) (Iic u) u :=
  (clip_continuous K).continuousAt.comp_continuousWithinAt (spanTrace_left T a u ω)

def boundedSpanClass (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (K : ℝ) (hK : 0≤K) : Lp ℝ 2 (inputLaw T) :=
  continuousInputClass T (boundedSpanTrace T a K) (trace_joint T a K) K (trace_bound T a K hK)

/-- SAME-K clipping cannot increase distance to the SAME bounded target f.
All identities are on the original product source, never a new sample batch. -/
theorem boundedSpanClass_distance (T : ℝ≥0) (a : ElementaryInput T →₀ ℝ) (f : fullPredictableL2 T)
    (K : ℝ) (hK : 0≤K) (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    dist (boundedSpanClass T a K hK) (f : Lp ℝ 2 (inputLaw T))≤
      dist (spanInput T a : Lp ℝ 2 (inputLaw T)) (f : Lp ℝ 2 (inputLaw T)) := by
  rw [dist_eq_norm,dist_eq_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (boundedSpanClass T a K hK) (f : Lp ℝ 2 (inputLaw T)),
    Lp.coeFn_sub (spanInput T a : Lp ℝ 2 (inputLaw T)) (f : Lp ℝ 2 (inputLaw T)),
    (inputFunction_memLp_two T (boundedSpanTrace T a K) (trace_joint T a K) K (trace_bound T a K hK)).coeFn_toLp,
    spanInput_coe_trace T a,hbound] with p hsub hsub' hc hs hb
  change boundedSpanClass T a K hK p=inputFunction (boundedSpanTrace T a K) p at hc
  rw [hsub,hsub']
  simp only [Pi.sub_apply]
  rw [hc,hs]
  exact clip_distance K (inputFunction (spanTrace T a) p) _ hb

/-- A real finite allowed table with SAME declared K is DERIVED from every
native bounded full-predictable input. No approximant existence is assumed. -/
theorem exists_bounded_table_dist_lt (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (ε : ℝ) (hε : 0<ε) :
    ∃ r : ElementaryInput T, (∀ i ω, |r.coefficient i ω|≤K) ∧
      dist (inputValue r) (f : Lp ℝ 2 (inputLaw T))<ε := by
  obtain ⟨a,ha⟩ := exists_spanInput_dist_lt T f (ε/2) (half_pos hε)
  have hd : dist (boundedSpanClass T a K hK) (f : Lp ℝ 2 (inputLaw T))<ε/2 :=
    lt_of_le_of_lt (boundedSpanClass_distance T a f K hK hbound) ha
  have ht := leftRegular_inputClass_tendsto T (boundedSpanTrace T a K) (trace_joint T a K)
    (trace_adapted T a K) (Eventually.of_forall (fun ω u => trace_left T a K u ω)) K hK (trace_bound T a K hK)
  obtain ⟨n,hn⟩ := (ht.eventually (Metric.ball_mem_nhds (boundedSpanClass T a K hK) (half_pos hε))).exists
  let r := leftRecord T (boundedSpanTrace T a K) (trace_adapted T a K) K (trace_bound T a K hK) n
  refine ⟨r,?_,?_⟩
  · intro i ω
    change |boundedSpanTrace T a K (r.clock i.castSucc) ω|≤K
    simpa only [Real.norm_eq_abs] using trace_bound T a K hK (r.clock i.castSucc) ω
  · have hdist : dist (inputValue r) (boundedSpanClass T a K hK)<ε/2 := hn
    have htri := dist_triangle (inputValue r) (boundedSpanClass T a K hK) (f : Lp ℝ 2 (inputLaw T))
    linarith

/-- Actual selected tables, with explicit proved approximation accuracy;
selection uses a theorem about the SAME f, not desired normalized densities. -/
def approximation (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) : ElementaryInput T :=
  Classical.choose (exists_bounded_table_dist_lt T f K hK hbound ((1/2 : ℝ)^(n+1)) (by positivity))

theorem approximation_bound (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) :
    ∀ i ω, |(approximation T f K hK hbound n).coefficient i ω|≤K :=
  (Classical.choose_spec (exists_bounded_table_dist_lt T f K hK hbound ((1/2 : ℝ)^(n+1)) (by positivity))).1

theorem approximation_error (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (n : ℕ) :
    dist (inputValue (approximation T f K hK hbound n)) (f : Lp ℝ 2 (inputLaw T))<(1/2 : ℝ)^(n+1) :=
  (Classical.choose_spec (exists_bounded_table_dist_lt T f K hK hbound ((1/2 : ℝ)^(n+1)) (by positivity))).2

theorem approximation_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Tendsto (fun n => inputValue (approximation T f K hK hbound n)) atTop (𝓝 (f : Lp ℝ 2 (inputLaw T))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hg : Tendsto (fun n : ℕ => (1/2 : ℝ)^(n+1)) atTop (𝓝 0) := by
    simpa only [pow_succ,zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num)).mul_const (1/2 : ℝ)
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => (approximation_error T f K hK hbound n).le) hg

/-- SAME original full-predictable class convergence, not merely convergence
in a newly named elementary closure. -/
theorem approximation_full_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Tendsto (fun n => literalPredictableInput (approximation T f K hK hbound n)) atTop (𝓝 f) :=
  tendsto_subtype_rng.mpr (approximation_tendsto T f K hK hbound)

/-- Their actual returned literal outputs converge to the native integral
of that SAME f. No independently chosen integral is introduced. -/
theorem approximation_outputs_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Tendsto (fun n => outputValue (approximation T f K hK hbound n)) atTop (𝓝 (predictableIntegral T f)) := by
  simpa only [Function.comp_def,predictableIntegral_returns_literal] using
    ((predictableIntegral T).continuous.tendsto f).comp (approximation_full_tendsto T f K hK hbound)

/-- Their SAME actual dt energies converge at every observation time on
the natural L1 scale, rather than a fabricated L2 bracket scale. -/
theorem approximation_energy_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) :
    Tendsto (fun n => BrownianIntegralEnergyL1.energyClass T s (literalPredictableInput (approximation T f K hK hbound n)))
      atTop (𝓝 (BrownianIntegralEnergyL1.energyClass T s f)) :=
  BrownianIntegralEnergyL1.energyClass_tendsto T s (approximation_full_tendsto T f K hK hbound)

/-- Native uniform integrability is now DERIVED for the actual tables
selected from SAME bounded f, not an externally provided table sequence. -/
theorem approximation_densities_uniformIntegrable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    UniformIntegrable (fun n => BrownianFiniteDensityL2Source.terminalDensity (approximation T f K hK hbound n)) 1 sourceLaw :=
  BrownianFiniteDensityL2Source.densities_uniformIntegrable _ K hK (fun n i =>
    Eventually.of_forall (fun ω => approximation_bound T f K hK hbound n i ω))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedPredictableApproximation
