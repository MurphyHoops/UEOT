import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralLiteralIntervals

/-!
Original commitment: the actual full predictable stochastic integral needs its genuine natural-filtration martingale.
Existing result: actual truncation/source classes and literal intervals obey native conditional prefix identities.
Premise reduced: transfer those identities through actual finite inputs and the proved native dense span.
Model/witness: SAME fixed inputLaw T/sourceLaw/natural filtration, all genuine predictable L2 inputs, including T=0.
Consumer: actual L2-adapted martingale and energy; continuous sample paths/quadratic variation/general Ito remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralMartingale
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianMartingaleSource BrownianOneStepIntegral BrownianSimplePredictableIntegral
open BrownianTimeIntegrand BrownianIntegralClosure BrownianPredictableInputs BrownianPredictableDensity
open BrownianIntegralTimeTruncation BrownianIntegralConditionalStep BrownianIntegralLiteralIntervals
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

private theorem lp_sum_coe {ι α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (F : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, F i : Lp ℝ 2 μ) =ᵐ[μ] fun a => ∑ i ∈ s, F i a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with a ha
    simp only [Finset.sum_empty]
    exact ha
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ s, F j),ih] with a ha hs
    simp only [Pi.add_apply] at ha
    rw [ha,hs]

private theorem part_order {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    r.clock i.castSucc ≤ r.clock i.succ := r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))

private theorem part_horizon {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    r.clock i.succ ≤ T := (r.clock_mono (Fin.le_last i.succ)).trans r.clock_end.le

private def partInput {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : fullPredictableL2 T :=
  intervalInput T (r.clock i.castSucc) (r.clock i.succ) (part_order r i) (part_horizon r i)
    (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)

/-- The actual original finite input equals the sum of its actual permitted
interval inputs in the ORIGINAL native full predictable L2 space. -/
private theorem literalInput_decomposition {T : ℝ≥0} (r : ElementaryInput T) :
    literalPredictableInput r = ∑ i : Fin r.n, partInput r i := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  apply Lp.ext
  have hall : ∀ᵐ p ∂inputLaw T, ∀ i : Fin r.n,
      (partInput r i : Lp ℝ 2 (inputLaw T)) p =
        intervalIntegrand (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ) p :=
    ae_all_iff.mpr (fun i => intervalInput_coe T _ _ (part_order r i) (part_horizon r i)
      (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i))
  filter_upwards [(integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).coeFn_toLp,
    lp_sum_coe (inputLaw T) Finset.univ (fun i => (partInput r i : Lp ℝ 2 (inputLaw T))),hall] with p hp hs hi
  change ((integrand_memLp_two T r.clock r.coefficient r.coefficient_bounded).toLp
    (integrand r.clock r.coefficient)) p = (∑ i : Fin r.n, (partInput r i : Lp ℝ 2 (inputLaw T))) p
  rw [hp,hs]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

private theorem literal_projection (T u : ℝ≥0) (r : ElementaryInput T) :
    naturalProjection u (predictableIntegral T (literalPredictableInput r)) =
      integralAt T u (literalPredictableInput r) := by
  let A := (naturalProjection u).comp (predictableIntegral T)
  let B := integralAt T u
  have hi (i : Fin r.n) : A (partInput r i) = B (partInput r i) :=
    projection_integral_interval T _ _ u (part_order r i) (part_horizon r i)
      (r.coefficient i) (r.coefficient_past i) (r.coefficient_bounded i)
  change A (literalPredictableInput r) = B (literalPredictableInput r)
  rw [literalInput_decomposition,map_sum,map_sum]
  exact Finset.sum_congr rfl (fun i _ => hi i)

private def domainToPredictable (T : ℝ≥0) : integralDomain T →ₗᵢ[ℝ] fullPredictableL2 T :=
  { Submodule.inclusion (integralDomain_le_fullPredictableL2 T) with norm_map' := fun _ => rfl }

private theorem domainToPredictable_surjective (T : ℝ≥0) : Function.Surjective (domainToPredictable T) := by
  intro f
  exact ⟨predictableInclusion T f,Subtype.ext rfl⟩

private theorem literal_span_dense (T : ℝ≥0) :
    Dense (Submodule.span ℝ (Set.range (literalPredictableInput (T := T))) : Set (fullPredictableL2 T)) := by
  let S := Submodule.span ℝ (Set.range (literalPredictableInput (T := T)))
  have hd : DenseRange (fun x : elementarySpan T => domainToPredictable T (inclusionIsometry T x)) :=
    (domainToPredictable_surjective T).denseRange.comp (inclusion_dense T) (domainToPredictable T).continuous
  have hmap : elementarySpan T ≤ S.map (fullPredictableL2 T).subtype := by
    rw [elementarySpan_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨r,rfl⟩
    exact ⟨literalPredictableInput r,Submodule.subset_span ⟨r,rfl⟩,rfl⟩
  apply hd.mono
  rintro y ⟨x,rfl⟩
  obtain ⟨z,hz,he⟩ := hmap x.property
  have heq : domainToPredictable T (inclusionIsometry T x) = z := Subtype.ext he.symm
  change domainToPredictable T (inclusionIsometry T x) ∈ S
  rw [heq]
  exact hz

/-- Actual full-input conditional identity. Native continuous linear maps
agree on the ACTUAL finite inputs, then on their PROVED dense span. -/
theorem integral_projection_identity (T u : ℝ≥0) (f : fullPredictableL2 T) :
    naturalProjection u (predictableIntegral T f) = integralClassProcess T f u := by
  have he : (naturalProjection u).comp (predictableIntegral T) = integralAt T u := by
    apply ContinuousLinearMap.ext_on (literal_span_dense T)
    rintro _ ⟨r,rfl⟩
    exact literal_projection T u r
  exact congrArg (fun L : fullPredictableL2 T →L[ℝ] Lp ℝ 2 sourceLaw => L f) he

private theorem naturalProjection_condExp (u : ℝ≥0) (g : Lp ℝ 2 sourceLaw) :
    (naturalProjection u g : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw] sourceLaw[g | naturalFiltration u] := by
  have h := (Lp.memLp g).condExpL2_ae_eq_condExp (𝕜 := ℝ) (naturalFiltration.le u)
  have he : (Lp.memLp g).toLp g = g := Lp.ext (Lp.memLp g).coeFn_toLp
  rw [he] at h
  exact h

/-- Strongly adapted canonical version of the ACTUAL integral process.
Its identity with the actual cutoff source is proved immediately below. -/
def integralProcess (T : ℝ≥0) (f : fullPredictableL2 T) (u : ℝ≥0) : (ℝ≥0 → ℝ) → ℝ :=
  sourceLaw[(predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ) | naturalFiltration u]

/-- EACH fixed-time canonical value is the SAME actual truncated integral
class. This is derived from literal source steps and L2 continuity, not assumed. -/
theorem integralProcess_eq_truncated (T u : ℝ≥0) (f : fullPredictableL2 T) :
    integralProcess T f u =ᵐ[sourceLaw] (integralClassProcess T f u : (ℝ≥0 → ℝ) → ℝ) := by
  have h := naturalProjection_condExp u (predictableIntegral T f)
  rw [integral_projection_identity T u f] at h
  exact h.symm

/-- The actual truncated integral class is genuinely L2-adapted to the source
natural past, not merely measurable in the full source sigma algebra. -/
theorem integralClassProcess_adapted (T u : ℝ≥0) (f : fullPredictableL2 T) :
    integralClassProcess T f u ∈ lpMeas ℝ ℝ (naturalFiltration u) 2 sourceLaw := by
  rw [← integral_projection_identity T u f]
  exact (condExpL2 ℝ ℝ (naturalFiltration.le u) (predictableIntegral T f)).property

/-- The canonical actual process is a genuine natural-filtration martingale;
its actual integral binding is the proved fixed-time identity above. -/
theorem integralProcess_martingale (T : ℝ≥0) (f : fullPredictableL2 T) :
    Martingale (integralProcess T f) naturalFiltration sourceLaw :=
  martingale_condExp (predictableIntegral T f) naturalFiltration sourceLaw

theorem integralProcess_stronglyAdapted (T : ℝ≥0) (f : fullPredictableL2 T) :
    StronglyAdapted naturalFiltration (integralProcess T f) :=
  (integralProcess_martingale T f).stronglyAdapted

theorem integralProcess_memLp_two (T u : ℝ≥0) (f : fullPredictableL2 T) :
    MemLp (integralProcess T f u) 2 sourceLaw :=
  (memLp_congr_ae (integralProcess_eq_truncated T u f)).mpr (Lp.memLp (integralClassProcess T f u))

/-- Actual source-process energy, transferred through the proved integral
identity. It is not a quadratic-variation or sample-path continuity assertion. -/
theorem integralProcess_energy (T u : ℝ≥0) (f : fullPredictableL2 T) :
    (∫ ω, integralProcess T f u ω ^ 2 ∂sourceLaw) =
      ∫ p in timeSet T u, (f : Lp ℝ 2 (inputLaw T)) p ^ 2 ∂inputLaw T := by
  have he : (fun ω => integralProcess T f u ω ^ 2) =ᵐ[sourceLaw]
      (fun ω => integralClassProcess T f u ω ^ 2) :=
    (integralProcess_eq_truncated T u f).mono (fun _ h => congrArg (fun x : ℝ => x^2) h)
  rw [integral_congr_ae he,integralClassProcess_energy]

theorem integralProcess_zero (T : ℝ≥0) (f : fullPredictableL2 T) :
    integralProcess T f 0 =ᵐ[sourceLaw] fun _ => 0 := by
  have h := integralProcess_eq_truncated T 0 f
  rw [integralClassProcess_zero] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 sourceLaw)

theorem integralProcess_horizon (T : ℝ≥0) (f : fullPredictableL2 T) :
    integralProcess T f T =ᵐ[sourceLaw] (predictableIntegral T f : (ℝ≥0 → ℝ) → ℝ) := by
  have h := integralProcess_eq_truncated T T f
  rw [integralClassProcess_horizon] at h
  exact h

/-- Original finite input returns its original literal finite output at the
horizon, on the SAME source sample space. -/
theorem integralProcess_returns_literal {T : ℝ≥0} (r : ElementaryInput T) :
    integralProcess T (literalPredictableInput r) T =ᵐ[sourceLaw]
      BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient := by
  have h := integralProcess_horizon T (literalPredictableInput r)
  rw [predictableIntegral_returns_literal] at h
  exact h.trans (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp

/-- The actual process starts at zero and hence has zero mean at every time,
with no separate mean-zero stochastic-integral premise. -/
theorem integralProcess_mean_zero (T u : ℝ≥0) (f : fullPredictableL2 T) :
    (∫ ω, integralProcess T f u ω ∂sourceLaw) = 0 := by
  have h := (integralProcess_martingale T f).setIntegral_eq
    (show (0 : ℝ≥0) ≤ u from bot_le) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [integral_congr_ae (integralProcess_zero T f),integral_zero] at h
  exact h.symm

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralMartingale
