import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepExponentialSource

/-!
Original commitment: random START-past action must preserve genuine joint past/noise law after its actual exponential change of measure.
Existing result: SAME H*DeltaB exponent is conditionally normalized and its actual Q preserves every original START event.
Premise reduced: derive parameter-dependent Gaussian recentering and apply it to the ENTIRE original START past.
Model/witness: actual Fa-measurable H and a<=b, SAME source increment/Q/energy; no shifted-law or independence field input.
Consumer: actual one-step random-coefficient Girsanov source; full shifted process and finite/simple/general predictable controls remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepTiltKernelSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianGaussianTiltSource
open BrownianPastStepExponentialSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Native fiberwise Esscher recentering, retaining the actual parameter
coordinate. It will be consumed by the whole actual START past readout. -/
theorem gaussian_fiber_centered_joint {A : Type*} [MeasurableSpace A] (μ : Measure A) [SFinite μ]
    (H : A → ℝ) (hH : Measurable H) (d : ℝ≥0) :
    ((μ.prod (gaussianReal 0 d)).withDensity (fun p => gaussianTiltWeight (H p.1) d p.2)).map
      (fun p => (p.1,p.2-H p.1*(d : ℝ))) = μ.prod (gaussianReal 0 d) := by
  have hw : Measurable (fun p : A × ℝ => gaussianTiltWeight (H p.1) d p.2) := by
    unfold gaussianTiltWeight
    fun_prop
  have hc : Measurable (fun p : A × ℝ => (p.1,p.2-H p.1*(d : ℝ))) := by fun_prop
  ext S hS
  rw [Measure.map_apply hc hS,withDensity_apply _ (hc hS),← lintegral_indicator (hc hS),
    lintegral_prod _ (hw.indicator (hc hS)).aemeasurable,Measure.prod_apply hS]
  apply lintegral_congr
  intro x
  have hf : MeasurableSet (Prod.mk x ⁻¹' S) := measurable_prodMk_left hS
  have hshift : Measurable (fun z : ℝ => z-H x*(d : ℝ)) := by fun_prop
  have hlaw : ((gaussianReal 0 d).withDensity (gaussianTiltWeight (H x) d)).map
      (fun z => z-H x*(d : ℝ)) = gaussianReal 0 d := by
    rw [gaussian_exponential_tilt,gaussianReal_map_sub_const,sub_self]
  have h := congrArg (fun ν : Measure ℝ => ν (Prod.mk x ⁻¹' S)) hlaw
  rw [Measure.map_apply hshift hf,withDensity_apply _ (hshift hf),← lintegral_indicator (hshift hf)] at h
  exact h

/-- An actual independent Gaussian coordinate, tilted by a coefficient read
from the other coordinate, has exactly its original joint law after the
literal recentering. No target changed law is supplied to this theorem. -/
theorem independent_gaussian_random_tilt_joint {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → A) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y) (d : ℝ≥0) (hLaw : HasLaw Y (gaussianReal 0 d) P)
    (hXY : IndepFun X Y P) (H : A → ℝ) (hH : Measurable H) :
    (P.withDensity (fun ω => gaussianTiltWeight (H (X ω)) d (Y ω))).map
      (fun ω => (X ω,Y ω-H (X ω)*(d : ℝ))) = P.map (fun ω => (X ω,Y ω)) := by
  have hc : Measurable (fun p : A × ℝ => (p.1,p.2-H p.1*(d : ℝ))) := by fun_prop
  have hw : Measurable (fun p : A × ℝ => gaussianTiltWeight (H p.1) d p.2) := by
    unfold gaussianTiltWeight
    fun_prop
  have he : (fun ω => (X ω,Y ω-H (X ω)*(d : ℝ))) =
      (fun p : A × ℝ => (p.1,p.2-H p.1*(d : ℝ))) ∘ (fun ω => (X ω,Y ω)) := rfl
  rw [he,← Measure.map_map hc (hX.prodMk hY),map_readout_density P _ (hX.prodMk hY) _ hw,
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,hLaw.map_eq,
    gaussian_fiber_centered_joint _ H hH d]

/-- SAME one-step Q and centered actual increment preserve the full joint
law with the ENTIRE original START sigma-algebra, not merely H or B_a. -/
theorem stepLaw_centered_original_past_joint (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration a).prod inferInstance)
      (fun ω => (id ω,increment a b ω-H ω*((b-a : ℝ≥0) : ℝ))) (stepLaw H a b) =
    @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration a).prod inferInstance)
      (fun ω => (id ω,increment a b ω)) sourceLaw := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id :=
    measurable_id'' (naturalFiltration.le a)
  have hi : @IndepFun (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance (naturalFiltration a) inferInstance id (increment a b) sourceLaw := by
    change Indep (MeasurableSpace.comap id (naturalFiltration a)) (MeasurableSpace.comap (increment a b) inferInstance) sourceLaw
    rw [MeasurableSpace.comap_id]
    apply Indep.symm
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact increment_indep_past a b hab
  exact @independent_gaussian_random_tilt_joint (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a)
    sourceLaw inferInstance id hid (increment a b) (measurable_increment a b) (b-a)
    (increment_hasLaw a b hab) hi H hH.measurable

/-- Typed Gaussian-law/independence consumers of the proved joint identity.
Both the changed measure and the centered coordinate are the literal ones. -/
theorem gaussian_random_tilt_law_indep {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → A) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y) (d : ℝ≥0) (hLaw : HasLaw Y (gaussianReal 0 d) P)
    (hXY : IndepFun X Y P) (H : A → ℝ) (hH : Measurable H) :
    let Q := P.withDensity (fun ω => gaussianTiltWeight (H (X ω)) d (Y ω))
    HasLaw (fun ω => Y ω-H (X ω)*(d : ℝ)) (gaussianReal 0 d) Q ∧
      IndepFun X (fun ω => Y ω-H (X ω)*(d : ℝ)) Q := by
  dsimp only
  let Q := P.withDensity (fun ω => gaussianTiltWeight (H (X ω)) d (Y ω))
  let Z := fun ω => Y ω-H (X ω)*(d : ℝ)
  have hZ : Measurable Z := hY.sub ((hH.comp hX).mul_const _)
  have hj := independent_gaussian_random_tilt_joint P X hX Y hY d hLaw hXY H hH
  change Q.map (fun ω => (X ω,Z ω))=P.map (fun ω => (X ω,Y ω)) at hj
  have hmapP : IsProbabilityMeasure (P.map (fun ω => (X ω,Y ω))) :=
    Measure.isProbabilityMeasure_map (hX.prodMk hY).aemeasurable
  have hmapQ : IsProbabilityMeasure (Q.map (fun ω => (X ω,Z ω))) := hj.symm ▸ hmapP
  have : IsProbabilityMeasure Q := Q.isProbabilityMeasure_of_map (fun ω => (X ω,Z ω))
  have hz := congrArg (fun μ : Measure (A × ℝ) => μ.snd) hj
  rw [Measure.snd_map_prodMk hX,Measure.snd_map_prodMk hX,hLaw.map_eq] at hz
  have hx := congrArg (fun μ : Measure (A × ℝ) => μ.fst) hj
  rw [Measure.fst_map_prodMk hZ,Measure.fst_map_prodMk hY] at hx
  refine ⟨⟨hZ.aemeasurable,hz⟩,?_⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).mpr
  rw [hj,hx,hz,← hLaw.map_eq]
  exact hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable

def centeredIncrement (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  increment a b ω-H ω*((b-a : ℝ≥0) : ℝ)

private theorem pastId_indep_increment (a b : ℝ≥0) (hab : a ≤ b) :
    @IndepFun (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance (naturalFiltration a) inferInstance id (increment a b) sourceLaw := by
  change Indep (MeasurableSpace.comap id (naturalFiltration a)) (MeasurableSpace.comap (increment a b) inferInstance) sourceLaw
  rw [MeasurableSpace.comap_id]
  apply Indep.symm
  rw [naturalFiltration,Filtration.natural_eq_comap]
  exact increment_indep_past a b hab

/-- Actual one-step shifted increment has the original Gaussian law under
its actual Q, and is independent of the ENTIRE original START past. -/
theorem centeredIncrement_law_indep (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    HasLaw (centeredIncrement H a b) (gaussianReal 0 (b-a)) (stepLaw H a b) ∧
      Indep (naturalFiltration a) (MeasurableSpace.comap (centeredIncrement H a b) inferInstance) (stepLaw H a b) := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id :=
    measurable_id'' (naturalFiltration.le a)
  have h := @gaussian_random_tilt_law_indep (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a)
    sourceLaw inferInstance id hid (increment a b) (measurable_increment a b) (b-a)
    (increment_hasLaw a b hab) (pastId_indep_increment a b hab) H hH.measurable
  refine ⟨h.1,?_⟩
  have hi := h.2
  change Indep (MeasurableSpace.comap id (naturalFiltration a))
    (MeasurableSpace.comap (centeredIncrement H a b) inferInstance) (stepLaw H a b) at hi
  simpa only [MeasurableSpace.comap_id] using hi

/-- This is the original entire Brownian past readout, not just H or B_a. -/
theorem centeredIncrement_indep_original_past (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    IndepFun (centeredIncrement H a b) (fun ω (r : Iic a) => process r ω) (stepLaw H a b) := by
  have h := (centeredIncrement_law_indep H a b hab hH).2.symm
  rw [naturalFiltration,Filtration.natural_eq_comap] at h
  exact h

/-- The actual centered increment is integrable and has zero conditional
mean under the SAME original START sigma algebra and actual Q. -/
theorem centeredIncrement_condExp_zero (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    (stepLaw H a b)[centeredIncrement H a b | naturalFiltration a] =ᵐ[stepLaw H a b] fun _ => 0 := by
  let _ := stepLaw_probability H a b hab hH
  have hg : Measurable (centeredIncrement H a b) :=
    (measurable_increment a b).sub (((hH.mono (naturalFiltration.le a)).measurable).mul_const _)
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ (MeasurableSpace.comap (centeredIncrement H a b) inferInstance)
      inferInstance (centeredIncrement H a b) := measurable_iff_comap_le.mpr le_rfl
  have hi := (centeredIncrement_law_indep H a b hab hH).2.symm
  have hc := condExp_indep_eq hg.comap_le (naturalFiltration.le a) hm.stronglyMeasurable hi
  have hmean : (∫ ω, centeredIncrement H a b ω ∂stepLaw H a b)=0 := by
    have h := (centeredIncrement_law_indep H a b hab hH).1.integral_comp (f := id) (by fun_prop)
    simpa only [Function.id_comp,id_eq,integral_id_gaussianReal] using h
  exact hc.trans (Eventually.of_forall (fun _ => hmean))

/-- Complete one-step conditional Gaussian law under actual Q and the
ENTIRE original START past. No future coefficient permission is granted. -/
theorem centeredIncrement_condExp_transform (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (stepLaw H a b)[fun ω => φ (centeredIncrement H a b ω) | naturalFiltration a] =ᵐ[stepLaw H a b]
      fun _ => ∫ z, φ z ∂gaussianReal 0 (b-a) := by
  let _ := stepLaw_probability H a b hab hH
  have hg : Measurable (centeredIncrement H a b) :=
    (measurable_increment a b).sub (((hH.mono (naturalFiltration.le a)).measurable).mul_const _)
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ (MeasurableSpace.comap (centeredIncrement H a b) inferInstance)
      inferInstance (centeredIncrement H a b) := measurable_iff_comap_le.mpr le_rfl
  have hi := (centeredIncrement_law_indep H a b hab hH).2.symm
  have hc := condExp_indep_eq hg.comap_le (naturalFiltration.le a) (hφ.comp hm).stronglyMeasurable hi
  exact hc.trans (Eventually.of_forall (fun _ => (centeredIncrement_law_indep H a b hab hH).1.integral_comp hφ.aestronglyMeasurable))

/-- Actual one-step conditional noise energy has the original elapsed
clock. Finite Q-energy of H is a separate already-derived source statement. -/
theorem centeredIncrement_condExp_square (H : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) :
    (stepLaw H a b)[fun ω => (centeredIncrement H a b ω)^2 | naturalFiltration a] =ᵐ[stepLaw H a b]
      fun _ => (b : ℝ)-(a : ℝ) := by
  have hsecond : (∫ z : ℝ, z^2 ∂gaussianReal 0 (b-a))=((b-a : ℝ≥0) : ℝ) := by
    have h := variance_id_gaussianReal (μ := 0) (v := b-a)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simpa only [id_eq,integral_id_gaussianReal,sub_zero] using h
  exact (centeredIncrement_condExp_transform H a b hab hH (fun z => z^2) (by fun_prop)).trans
    (Eventually.of_forall (fun _ => hsecond.trans (NNReal.coe_sub hab)))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepTiltKernelSource
