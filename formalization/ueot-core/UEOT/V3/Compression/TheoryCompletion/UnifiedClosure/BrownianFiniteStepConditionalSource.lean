import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepExponentialSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepTiltKernelSource

/-!
Original commitment: normalized finite-table density must yield actual causal Gaussian innovations, not a shifted-law field.
Existing result: SAME table prefix martingale/measures, actual step composition and future-tail readout cancellation.
Premise reduced: derive centered row Gaussian law and whole original START-past independence under the SAME FINAL tableQ.
Model/witness: original ElementaryInput T, originalFs permissions, actual rowH/DeltaB, repeated/empty clocks; prior controlled past law is retained.
Consumer: genuine finite-table shifted-path source and eventual P-KL; arbitrary-time refinement/full shiftedBrownian remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepConditionalSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianGaussianTiltSource
open BrownianIntegralClosure BrownianFiniteStepExponentialSource BrownianPastStepTiltKernelSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Weighting only the actual first readout preserves independence of the
other coordinate, with its original law. This is a native measure identity. -/
theorem independent_first_weight_joint {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → A) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y) (hXY : IndepFun X Y P) (w : A → ℝ≥0∞) (hw : Measurable w) :
    (P.withDensity (fun ω => w (X ω))).map (fun ω => (X ω,Y ω)) =
      ((P.map X).withDensity w).prod (P.map Y) := by
  rw [map_readout_density P _ (hX.prodMk hY) (fun p : A × ℝ => w p.1) (hw.comp measurable_fst),
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,← prod_withDensity_left hw]

private theorem gaussian_joint_law_indep {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X : Ω → A) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y) (d : ℝ≥0)
    (hJ : Q.map (fun ω => (X ω,Y ω))=(Q.map X).prod (gaussianReal 0 d)) :
    HasLaw Y (gaussianReal 0 d) Q ∧ IndepFun X Y Q := by
  have : IsProbabilityMeasure (Q.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hy := congrArg (fun μ : Measure (A × ℝ) => μ.snd) hJ
  rw [Measure.snd_map_prodMk hX,Measure.snd_prod] at hy
  refine ⟨⟨hY.aemeasurable,hy⟩,?_⟩
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mpr
  rw [hy]
  exact hJ

private theorem cell_mono {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : r.clock i.castSucc ≤ r.clock i.succ :=
  r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))

private theorem pastId_indep_increment (a b : ℝ≥0) (hab : a ≤ b) :
    @IndepFun (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance (naturalFiltration a) inferInstance id (increment a b) sourceLaw := by
  change Indep (MeasurableSpace.comap id (naturalFiltration a)) (MeasurableSpace.comap (increment a b) inferInstance) sourceLaw
  rw [MeasurableSpace.comap_id]
  apply Indep.symm
  rw [naturalFiltration,Filtration.natural_eq_comap]
  exact increment_indep_past a b hab

/-- Earlier actual controls change the past law, but the current original
increment is STILL Gaussian and independent of the ENTIRE original START
past under the actual PRIOR-prefix measure. -/
theorem prior_increment_law_indep {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    HasLaw (increment (r.clock i.castSucc) (r.clock i.succ))
      (gaussianReal 0 (r.clock i.succ-r.clock i.castSucc)) (prefixLaw r i.castSucc) ∧
    @IndepFun (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) ℝ inferInstance (naturalFiltration (r.clock i.castSucc)) inferInstance
      id (increment (r.clock i.castSucc) (r.clock i.succ)) (prefixLaw r i.castSucc) := by
  let a := r.clock i.castSucc
  let b := r.clock i.succ
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id :=
    measurable_id'' (naturalFiltration.le a)
  let w := fun ω => ENNReal.ofReal (prefixExponential r i.castSucc ω)
  have hw : @Measurable (ℝ≥0 → ℝ) ℝ≥0∞ (naturalFiltration a) inferInstance w := (prefix_past r i.castSucc).measurable.ennreal_ofReal
  have hj := @independent_first_weight_joint (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a)
    sourceLaw inferInstance id hid (increment a b) (measurable_increment a b) (pastId_indep_increment a b (cell_mono r i)) w hw
  have hp := @map_readout_density (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) sourceLaw id hid w hw
  change @Measure.map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id (prefixLaw r i.castSucc)=
    (@Measure.map (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a) id sourceLaw).withDensity w at hp
  change @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration a).prod inferInstance)
    (fun ω => (id ω,increment a b ω)) (prefixLaw r i.castSucc)=_ at hj
  rw [← hp,(increment_hasLaw a b (cell_mono r i)).map_eq] at hj
  exact @gaussian_joint_law_indep (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration a)
    (prefixLaw r i.castSucc) inferInstance id hid (increment a b) (measurable_increment a b) (b-a) hj

/-- SAME actual centered row, retaining original coefficient and elapsed
clock rather than choosing an alternative innovation. -/
def centeredRow {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : (ℝ≥0 → ℝ) → ℝ :=
  centeredIncrement (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)

private theorem centeredRow_end_past {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    StronglyMeasurable[naturalFiltration (r.clock i.succ)] (centeredRow r i) := by
  have hi := (process_stronglyAdapted (r.clock i.succ)).sub
    ((process_stronglyAdapted (r.clock i.castSucc)).mono (naturalFiltration.mono (cell_mono r i)))
  exact hi.sub (((r.coefficient_past i).mono (naturalFiltration.mono (cell_mono r i))).mul stronglyMeasurable_const)

/-- Actual NEXT-prefix joint law after centering is its actual PRIOR-prefix
joint law before centering. The local base measure is itself constructed. -/
theorem next_centered_joint {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration (r.clock i.castSucc)).prod inferInstance)
      (fun ω => (id ω,centeredRow r i ω)) (prefixLaw r i.succ) =
    @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration (r.clock i.castSucc)).prod inferInstance)
      (fun ω => (id ω,increment (r.clock i.castSucc) (r.clock i.succ) ω)) (prefixLaw r i.castSucc) := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration (r.clock i.castSucc)) id :=
    measurable_id'' (naturalFiltration.le (r.clock i.castSucc))
  have hp := prior_increment_law_indep r i
  have hj := @independent_gaussian_random_tilt_joint (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration (r.clock i.castSucc))
    (prefixLaw r i.castSucc) inferInstance id hid (increment (r.clock i.castSucc) (r.clock i.succ))
    (measurable_increment _ _) (r.clock i.succ-r.clock i.castSucc) hp.1 hp.2 (r.coefficient i) (r.coefficient_past i).measurable
  change @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration (r.clock i.castSucc)).prod inferInstance)
    (fun ω => (id ω,centeredRow r i ω))
      ((prefixLaw r i.castSucc).withDensity (fun ω => ENNReal.ofReal (stepFactor r i ω)))=_ at hj
  rw [← prefixLaw_step_composition r i] at hj
  exact hj

/-- Real future-tail cancellation: FINAL-tableQ has the actual original
START-past/centered-row joint law of NEXT-prefixQ, not a new chosen measure. -/
theorem final_centered_joint {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration (r.clock i.castSucc)).prod inferInstance)
      (fun ω => (id ω,centeredRow r i ω)) (tableLaw r) =
    @Measure.map (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) inferInstance ((naturalFiltration (r.clock i.castSucc)).prod inferInstance)
      (fun ω => (id ω,increment (r.clock i.castSucc) (r.clock i.succ) ω)) (prefixLaw r i.castSucc) := by
  have hidEnd : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) (naturalFiltration (r.clock i.succ))
      (naturalFiltration (r.clock i.castSucc)) id := measurable_id'' (naturalFiltration.mono (cell_mono r i))
  have hp : @Measurable (ℝ≥0 → ℝ) ((ℝ≥0 → ℝ) × ℝ) (naturalFiltration (r.clock i.succ))
      ((naturalFiltration (r.clock i.castSucc)).prod inferInstance) (fun ω => (id ω,centeredRow r i ω)) :=
    hidEnd.prodMk (centeredRow_end_past r i).measurable
  exact (@tableLaw_map_prefix_readout T r i.succ ((ℝ≥0 → ℝ) × ℝ)
    ((naturalFiltration (r.clock i.castSucc)).prod inferInstance) _ hp).trans (next_centered_joint r i)

private theorem law_indep_joint {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X : Ω → A) (hX : Measurable X)
    (Y : Ω → ℝ) (hY : Measurable Y) (d : ℝ≥0)
    (hYlaw : HasLaw Y (gaussianReal 0 d) Q) (hXY : IndepFun X Y Q) :
    Q.map (fun ω => (X ω,Y ω))=(Q.map X).prod (gaussianReal 0 d) := by
  rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,hYlaw.map_eq]

/-- Under the SAME final table measure, this literal centered row is Gaussian
and independent of the ENTIRE original START past. Earlier controls are
retained in that past law; future density factors have actually canceled. -/
theorem final_centered_law_indep {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    HasLaw (centeredRow r i) (gaussianReal 0 (r.clock i.succ-r.clock i.castSucc)) (tableLaw r) ∧
      Indep (naturalFiltration (r.clock i.castSucc))
        (MeasurableSpace.comap (centeredRow r i) inferInstance) (tableLaw r) := by
  have hid : @Measurable (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration (r.clock i.castSucc)) id :=
    measurable_id'' (naturalFiltration.le (r.clock i.castSucc))
  have hi := prior_increment_law_indep r i
  have hj := @law_indep_joint (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration (r.clock i.castSucc))
    (prefixLaw r i.castSucc) inferInstance id hid (increment (r.clock i.castSucc) (r.clock i.succ))
    (measurable_increment _ _) _ hi.1 hi.2
  have hp := @tableLaw_map_prefix_readout T r i.castSucc (ℝ≥0 → ℝ)
    (naturalFiltration (r.clock i.castSucc)) id measurable_id
  rw [← hp] at hj
  have h := @gaussian_joint_law_indep (ℝ≥0 → ℝ) (ℝ≥0 → ℝ) inferInstance (naturalFiltration (r.clock i.castSucc))
    (tableLaw r) inferInstance id hid (centeredRow r i)
    ((centeredRow_end_past r i).mono (naturalFiltration.le _)).measurable _ ((final_centered_joint r i).trans hj)
  refine ⟨h.1,?_⟩
  have hd := h.2
  change Indep (MeasurableSpace.comap id (naturalFiltration (r.clock i.castSucc)))
    (MeasurableSpace.comap (centeredRow r i) inferInstance) (tableLaw r) at hd
  simpa only [MeasurableSpace.comap_id] using hd

/-- The whole original past readout, rather than merely the coefficient or
left endpoint state, is independent of the actual centered row. -/
theorem final_centered_indep_original_past {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    IndepFun (centeredRow r i) (fun ω (s : Iic (r.clock i.castSucc)) => process s ω) (tableLaw r) := by
  have h := (final_centered_law_indep r i).2.symm
  rw [naturalFiltration,Filtration.natural_eq_comap] at h
  exact h

/-- Actual final-table conditional Gaussian transform, with the original
START sigma algebra and SAME returned row, for every measurable test. -/
theorem final_centered_condExp_transform {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (tableLaw r)[fun ω => φ (centeredRow r i ω) | naturalFiltration (r.clock i.castSucc)] =ᵐ[tableLaw r]
      fun _ => ∫ z, φ z ∂gaussianReal 0 (r.clock i.succ-r.clock i.castSucc) := by
  have hg := ((centeredRow_end_past r i).mono (naturalFiltration.le _)).measurable
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ (MeasurableSpace.comap (centeredRow r i) inferInstance)
      inferInstance (centeredRow r i) := measurable_iff_comap_le.mpr le_rfl
  have hi := (final_centered_law_indep r i).2.symm
  have hc := condExp_indep_eq hg.comap_le (naturalFiltration.le _) (hφ.comp hm).stronglyMeasurable hi
  exact hc.trans (Eventually.of_forall (fun _ => (final_centered_law_indep r i).1.integral_comp hφ.aestronglyMeasurable))

/-- Literal centered row conditional mean zero under FINAL tableQ. -/
theorem final_centered_condExp_zero {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    (tableLaw r)[centeredRow r i | naturalFiltration (r.clock i.castSucc)] =ᵐ[tableLaw r] fun _ => 0 := by
  simpa only [id_eq, integral_id_gaussianReal] using
    final_centered_condExp_transform r i id measurable_id

/-- Conditional noise energy is the original elapsed clock, including
collapsed cells. No L4 or desired energy field is supplied. -/
theorem final_centered_condExp_square {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    (tableLaw r)[fun ω => (centeredRow r i ω)^2 | naturalFiltration (r.clock i.castSucc)] =ᵐ[tableLaw r]
      fun _ => (r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ) := by
  have hsecond : (∫ z : ℝ, z^2 ∂gaussianReal 0 (r.clock i.succ-r.clock i.castSucc))=
      ((r.clock i.succ-r.clock i.castSucc : ℝ≥0) : ℝ) := by
    have h := variance_id_gaussianReal (μ := 0) (v := r.clock i.succ-r.clock i.castSucc)
    rw [variance_eq_integral measurable_id.aemeasurable] at h
    simpa only [id_eq,integral_id_gaussianReal,sub_zero] using h
  exact (final_centered_condExp_transform r i (fun z => z^2) (by fun_prop)).trans
    (Eventually.of_forall (fun _ => hsecond.trans (NNReal.coe_sub (cell_mono r i))))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepConditionalSource
