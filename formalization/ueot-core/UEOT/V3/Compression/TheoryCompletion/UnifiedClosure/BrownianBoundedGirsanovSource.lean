import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedMovingLawSource

/-!
Original commitment: SAME bounded full-predictable control must generate genuine Brownian noise under its OWN computed fullQ and ORIGINAL Fs.
Existing result: actual normalized density, actual permitted continuous shifted path, and actual finite-table mixed-test transport retaining past events.
Premise reduced: derive whole finite Gaussian laws and original-past independence by native measure uniqueness, not source fields or inverse SDE assumptions.
Model/witness: native fullPredictableL2 f on original dt×P, source-AE |f|<=K, original Fs, SAME actual Q=withDensity(exp(nativeI-actualA/2)).
Consumer/boundary: bounded canonical-source Girsanov/P-KL source; no general natural-filtration equality or arbitrary-L2 normalization is inferred.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedGirsanovSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource BrownianTimeIntegrand BrownianIntegralClosure
open BrownianPredictableInputs BrownianPredictableDensity BrownianIntegralTimeEnergy
open BrownianBoundedPredictableApproximation BrownianFiniteDensityL2Source BrownianFiniteStepExponentialSource
open BrownianBoundedExponentialLimitSource BrownianBoundedControlSource BrownianBoundedDriftLimitSource
open BrownianBoundedMovingLawSource BrownianFiniteStepShiftedSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory BoundedContinuousFunction
noncomputable section

private theorem shifted_measurable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) :
    Measurable (BrownianBoundedControlSource.shiftedProcess T f K s) :=
  ((BrownianBoundedControlSource.shiftedProcess_stronglyAdapted T f K s).mono (naturalFiltration.le s)).measurable

/-- Every finite law comes from the computed table laws and actual Q_n→Q
mixed-test transport, rather than an external desired path law. -/
theorem full_finite_hasLaw (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (I : Finset ℝ≥0) :
    HasLaw (fun ω => I.restrict (BrownianBoundedControlSource.shiftedProcess T f K · ω))
      (BrownianReal.projectiveFamily I) (fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  have hm : Measurable (fun ω (i : I) => BrownianBoundedControlSource.shiftedProcess T f K i ω) :=
    measurable_pi_lambda _ (fun i => shifted_measurable T f K i)
  refine ⟨hm.aemeasurable,?_⟩
  have : IsProbabilityMeasure ((fullLaw T f).map (fun ω (i : I) => BrownianBoundedControlSource.shiftedProcess T f K i ω)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  change (∫ x, φ x ∂(fullLaw T f).map (fun ω (i : I) => BrownianBoundedControlSource.shiftedProcess T f K i ω))=_
  rw [integral_map hm.aemeasurable φ.continuous.measurable.aestronglyMeasurable]
  have h := actual_finite_tests_tendsto T f K hK hbound I (fun _ => 1) measurable_const 1 zero_le_one (fun _ => by norm_num) φ
  simp only [one_mul] at h
  have he (n : ℕ) : (∫ ω, φ (I.restrict (tableProcess (approximation T f K hK hbound n) · ω))
      ∂tableLaw (approximation T f K hK hbound n))=∫ x, φ x ∂BrownianReal.projectiveFamily I :=
    ((tableProcess_isBrownian (approximation T f K hK hbound n)).toIsPreBrownianReal.hasLaw I).integral_comp
      φ.continuous.measurable.aestronglyMeasurable
  have hc : Tendsto (fun n => ∫ ω, φ (I.restrict (tableProcess (approximation T f K hK hbound n) · ω))
      ∂tableLaw (approximation T f K hK hbound n)) atTop (𝓝 (∫ x, φ x ∂BrownianReal.projectiveFamily I)) :=
    (tendsto_congr' (Eventually.of_forall he)).mpr tendsto_const_nhds
  exact tendsto_nhds_unique h hc

theorem full_isPreBrownian (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    IsPreBrownianReal (BrownianBoundedControlSource.shiftedProcess T f K) (fullLaw T f) :=
  ⟨full_finite_hasLaw T f K hK hbound⟩

/-- Genuine SAME-input Brownian source under its OWN actual normalized Q.
Original-Fs independence is proved separately below; no filtration inverse is used. -/
theorem full_isBrownian (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    IsBrownianReal (BrownianBoundedControlSource.shiftedProcess T f K) (fullLaw T f) :=
  ⟨full_isPreBrownian T f K hK hbound,Eventually.of_forall (BrownianBoundedControlSource.shiftedProcess_continuous T f K hK)⟩

private theorem continuous_readout_inMeasure {Ω E F : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [PseudoMetricSpace F] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ → Ω → E) (Y : Ω → E) (G : E → F) (hG : Continuous G)
    (hm : ∀ n, AEStronglyMeasurable (fun ω => G (X n ω)) P)
    (hXY : TendstoInMeasure P X atTop Y) :
    TendstoInMeasure P (fun n ω => G (X n ω)) atTop (fun ω => G (Y ω)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hm).mpr
  intro ns hns
  obtain ⟨ms,hms,ha⟩ := (hXY.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [ha] with ω hω
  exact (hG.tendsto (Y ω)).comp hω

def futureReadout (B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ) (s : ℝ≥0) (I : Finset ℝ≥0) (ω : ℝ≥0 → ℝ) : I → ℝ :=
  fun i => B (s+i) ω-B s ω

private theorem future_table_measurable {T : ℝ≥0} (r : ElementaryInput T) (s : ℝ≥0) (I : Finset ℝ≥0) :
    Measurable (futureReadout (tableProcess r) s I) :=
  measurable_pi_lambda _ (fun i => (prefixProcess_measurable r _ (s+i)).sub (prefixProcess_measurable r _ s))

/-- Finite future increments converge on original P with all their joint
coordinates retained. The finite time set includes START explicitly. -/
theorem futureReadout_tendstoInMeasure (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) (I : Finset ℝ≥0) :
    TendstoInMeasure sourceLaw (fun n => futureReadout (tableProcess (approximation T f K hK hbound n)) s I) atTop
      (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I) := by
  classical
  let J := insert s (I.image (fun u => s+u))
  let G : (J → ℝ) → I → ℝ := fun x i => x ⟨s+i,by simp [J]⟩-x ⟨s,by simp [J]⟩
  have hG : Continuous G := continuous_pi (fun _ => (continuous_apply _).sub (continuous_apply _))
  let r := approximation T f K hK hbound
  let X : ℕ → (ℝ≥0 → ℝ) → J → ℝ := fun n ω j => tableProcess (r n) j ω
  let Y : (ℝ≥0 → ℝ) → J → ℝ := fun ω j => BrownianBoundedControlSource.shiftedProcess T f K j ω
  have hxy : TendstoInMeasure sourceLaw X atTop Y := actual_finite_paths_tendstoInMeasure T f K hK hbound J
  have hm (n : ℕ) : AEStronglyMeasurable (fun ω => G (X n ω)) sourceLaw :=
    (future_table_measurable (r n) s I).aestronglyMeasurable
  exact continuous_readout_inMeasure sourceLaw X Y G hG hm hxy

/-- The actual moving-Q future tests retain an arbitrary fixed bounded
original-source factor, ready for original Fs event consumers. -/
theorem future_tests_tendsto (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) (I : Finset ℝ≥0)
    (a : (ℝ≥0 → ℝ) → ℝ) (ha : Measurable a) (R : ℝ) (hR : 0≤R) (hA : ∀ ω, ‖a ω‖≤R) (φ : (I → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, a ω*φ (futureReadout (tableProcess (approximation T f K hK hbound n)) s I ω)
      ∂tableLaw (approximation T f K hK hbound n)) atTop
      (𝓝 (∫ ω, a ω*φ (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I ω) ∂fullLaw T f)) :=
  actual_tests_tendsto (E := I → ℝ) T f K hK hbound
    (fun n => futureReadout (tableProcess (approximation T f K hK hbound n)) s I)
    (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I)
    (fun n => future_table_measurable (approximation T f K hK hbound n) s I)
    (futureReadout_tendstoInMeasure T f K hK hbound s I) a ha R hR hA φ

/-- Finite-table future conditional tests use the ENTIRE ORIGINAL past,
not just the left endpoint or the shifted process's own past. -/
private theorem table_future_factor {T : ℝ≥0} (r : ElementaryInput T) (s : ℝ≥0) (I : Finset ℝ≥0)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (φ : (I → ℝ) →ᵇ ℝ) :
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω*φ (futureReadout (tableProcess r) s I ω) ∂tableLaw r)=
      (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂tableLaw r)*(∫ x, φ x ∂BrownianReal.projectiveFamily I) := by
  have hi : Indep (MeasurableSpace.comap (futureReadout (tableProcess r) s I) inferInstance) (naturalFiltration s) (tableLaw r) := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact (tableProcess_indep_original_past r s).comp
      (measurable_pi_lambda _ (fun i : I => measurable_pi_apply (i : ℝ≥0))) measurable_id
  have hm : @Measurable (ℝ≥0 → ℝ) (I → ℝ)
      (MeasurableSpace.comap (futureReadout (tableProcess r) s I) inferInstance) inferInstance
      (futureReadout (tableProcess r) s I) := measurable_iff_comap_le.mpr le_rfl
  have hφ := (φ.continuous.measurable.comp hm).comap_le
  have hAm : StronglyMeasurable[naturalFiltration s] (A.indicator (fun _ => (1 : ℝ))) := stronglyMeasurable_const.indicator hA
  have hInd : IndepFun (A.indicator (fun _ => (1 : ℝ))) (fun ω => φ (futureReadout (tableProcess r) s I ω)) (tableLaw r) :=
    (indep_of_indep_of_le_right (indep_of_indep_of_le_left hi hφ) hAm.measurable.comap_le).symm
  have hg : (∫ ω, φ (futureReadout (tableProcess r) s I ω) ∂tableLaw r)=∫ x, φ x ∂BrownianReal.projectiveFamily I :=
    (((tableProcess_isBrownian r).toIsPreBrownianReal.shift s).hasLaw I).integral_comp φ.continuous.measurable.aestronglyMeasurable
  have hh := hInd.integral_mul_eq_mul_integral (hAm.mono (naturalFiltration.le s)).aestronglyMeasurable
    (φ.continuous.measurable.comp (future_table_measurable r s I)).aestronglyMeasurable
  rw [hg] at hh
  simpa only [Pi.mul_apply] using hh

/-- Actual full-Q conditional Gaussian tests retain EVERY original Fs
past event. They follow from finite true source factorization plus actual
moving-density joint tests; no limit inverse-filtration premise is used. -/
theorem full_future_factor (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) (I : Finset ℝ≥0)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) (φ : (I → ℝ) →ᵇ ℝ) :
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω*φ (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I ω) ∂fullLaw T f)=
      (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂fullLaw T f)*(∫ x, φ x ∂BrownianReal.projectiveFamily I) := by
  have hm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator (naturalFiltration.le s A hA)
  have hb (ω : ℝ≥0 → ℝ) : ‖A.indicator (fun _ => (1 : ℝ)) ω‖≤(1 : ℝ) := by
    by_cases h : ω∈A <;> simp [h]
  have hmain := future_tests_tendsto T f K hK hbound s I _ hm 1 zero_le_one hb φ
  have hmass := future_tests_tendsto T f K hK hbound s ∅ _ hm 1 zero_le_one hb (1 : ((∅ : Finset ℝ≥0) → ℝ) →ᵇ ℝ)
  simp only [BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one] at hmass
  have hc := hmass.mul_const (∫ x, φ x ∂BrownianReal.projectiveFamily I)
  have he (n : ℕ) := table_future_factor (approximation T f K hK hbound n) s I A hA φ
  have hh := (tendsto_congr' (Eventually.of_forall he)).mpr hc
  exact tendsto_nhds_unique hmain hh

private theorem future_full_measurable (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) (I : Finset ℝ≥0) :
    Measurable (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I) :=
  measurable_pi_lambda _ (fun i => (shifted_measurable T f K (s+i)).sub (shifted_measurable T f K s))

/-- Native finite-measure uniqueness upgrades the proved conditional tests
to the actual entire Borel finite-future law for each ORIGINAL past event. -/
theorem full_future_restricted_law (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) (I : Finset ℝ≥0)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration s] A) :
    ((fullLaw T f).restrict A).map (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I)=
      ((fullLaw T f) A) • BrownianReal.projectiveFamily I := by
  let _ := fullLaw_probability T f K hK hbound
  have hm := future_full_measurable T f K s I
  have hAg := naturalFiltration.le s A hA
  have : IsFiniteMeasure (((fullLaw T f) A) • BrownianReal.projectiveFamily I) := ⟨by
    simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact measure_lt_top _ _⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map hm.aemeasurable φ.continuous.measurable.aestronglyMeasurable,integral_smul_measure,smul_eq_mul]
  have hh := full_future_factor T f K hK hbound s I A hA φ
  have he : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω*φ (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I ω))=
      A.indicator (fun ω => φ (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I ω)) := by
    funext ω
    by_cases h : ω∈A <;> simp [h]
  have hmass : (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂fullLaw T f)=((fullLaw T f) A).toReal := by
    rw [integral_indicator hAg,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
  rw [he,integral_indicator hAg,hmass] at hh
  exact hh

/-- Genuine finite future/original-Fs independence, including all Borel
future sets. This does NOT follow merely from Brownian own-past independence. -/
theorem full_finite_future_indep (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) (I : Finset ℝ≥0) :
    Indep (MeasurableSpace.comap (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I) inferInstance)
      (naturalFiltration s) (fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  have hm := future_full_measurable T f K s I
  have hlaw : (fullLaw T f).map (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I)=BrownianReal.projectiveFamily I :=
    (((full_isPreBrownian T f K hK hbound).shift s).hasLaw I).map_eq
  apply (indep_iff_forall_indepSet (fullLaw T f)).mpr
  intro U A hU hA
  rcases MeasurableSpace.measurableSet_comap.mp hU with ⟨B,hB,rfl⟩
  apply (indepSet_iff_measure_inter_eq_mul (hm hB) (naturalFiltration.le s A hA) (fullLaw T f)).mpr
  have hr := congrArg (fun μ : Measure (I → ℝ) => μ B) (full_future_restricted_law T f K hK hbound s I A hA)
  rw [Measure.map_apply hm hB,Measure.restrict_apply (hm hB),Measure.smul_apply,smul_eq_mul] at hr
  have hL := congrArg (fun μ : Measure (I → ℝ) => μ B) hlaw
  rw [Measure.map_apply hm hB] at hL
  rw [← hL] at hr
  exact hr.trans (mul_comm _ _)

/-- Entire future noise readout of the SAME actual full-input process. -/
def fullFuture (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s : ℝ≥0) (ω : ℝ≥0 → ℝ) (u : ℝ≥0) : ℝ :=
  BrownianBoundedControlSource.shiftedProcess T f K (s+u) ω-BrownianBoundedControlSource.shiftedProcess T f K s ω

/-- Genuine independence of the ENTIRE future from ORIGINAL Fs. Native
directed sigma-algebra independence upgrades already proved finite Borel
laws; no uncountable AE intersection or inverse filtration is used. -/
theorem full_future_indep (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (fullFuture T f K s) inferInstance) (naturalFiltration s) (fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  let m : Finset ℝ≥0 → MeasurableSpace (ℝ≥0 → ℝ) := fun I =>
    MeasurableSpace.comap (futureReadout (BrownianBoundedControlSource.shiftedProcess T f K) s I) inferInstance
  have hm (I : Finset ℝ≥0) : m I=⨆ i : I, MeasurableSpace.comap
      (fun ω => BrownianBoundedControlSource.shiftedProcess T f K (s+i) ω-BrownianBoundedControlSource.shiftedProcess T f K s ω) inferInstance :=
    MeasurableSpace.comap_process_pi (fun i : I => fun ω =>
      BrownianBoundedControlSource.shiftedProcess T f K (s+i) ω-BrownianBoundedControlSource.shiftedProcess T f K s ω)
  have hmono : Monotone m := by
    intro I J hIJ
    rw [hm I,hm J]
    exact iSup_le (fun i : I => le_iSup_of_le (⟨i,hIJ i.property⟩ : J) le_rfl)
  have hi := indep_iSup_of_monotone (fun I => full_finite_future_indep T f K hK hbound s I)
    (fun I => (future_full_measurable T f K s I).comap_le) (naturalFiltration.le s) hmono
  have he : MeasurableSpace.comap (fullFuture T f K s) inferInstance=⨆ I : Finset ℝ≥0, m I := by
    calc
      _ = ⨆ u : ℝ≥0, MeasurableSpace.comap (fun ω => fullFuture T f K s ω u) inferInstance :=
        MeasurableSpace.comap_process_pi (fun u ω => fullFuture T f K s ω u)
      _ = _ := by
        apply le_antisymm
        · refine iSup_le (fun u => le_iSup_of_le ({u} : Finset ℝ≥0) ?_)
          rw [hm]
          exact le_iSup_of_le (⟨u,by simp⟩ : ({u} : Finset ℝ≥0)) le_rfl
        · refine iSup_le (fun I => ?_)
          rw [hm]
          exact iSup_le (fun i : I => le_iSup_of_le (i : ℝ≥0) le_rfl)
  rw [he]
  exact hi

/-- Original ENTIRE source past, not just endpoint state or the shifted
process's own natural past, is independent of the actual full future. -/
theorem full_future_indep_original_past (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s : ℝ≥0) :
    IndepFun (fullFuture T f K s) (fun ω (u : Iic s) => process u ω) (fullLaw T f) := by
  have hi := full_future_indep T f K hK hbound s
  rw [naturalFiltration,Filtration.natural_eq_comap] at hi
  exact hi

def fullIncrement (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (s t : ℝ≥0) (ω : ℝ≥0 → ℝ) : ℝ :=
  BrownianBoundedControlSource.shiftedProcess T f K t ω-BrownianBoundedControlSource.shiftedProcess T f K s ω

theorem full_increment_indep_original_past (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s t : ℝ≥0) (hst : s≤t) :
    IndepFun (fullIncrement T f K s t) (fun ω (u : Iic s) => process u ω) (fullLaw T f) := by
  have hi := (full_future_indep_original_past T f K hK hbound s).comp (measurable_pi_apply (t-s)) measurable_id
  have he : s+(t-s)=t := add_tsub_cancel_of_le hst
  change IndepFun (fun ω => BrownianBoundedControlSource.shiftedProcess T f K (s+(t-s)) ω-
    BrownianBoundedControlSource.shiftedProcess T f K s ω) (fun ω (u : Iic s) => process u ω) (fullLaw T f) at hi
  rw [he] at hi
  exact hi

theorem full_increment_condExp_zero (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) (s t : ℝ≥0) (hst : s≤t) :
    (fullLaw T f)[fullIncrement T f K s t | naturalFiltration s]=ᵐ[fullLaw T f] fun _ => 0 := by
  let _ := fullLaw_probability T f K hK hbound
  have hg : Measurable (fullIncrement T f K s t) := (shifted_measurable T f K t).sub (shifted_measurable T f K s)
  have hi : Indep (MeasurableSpace.comap (fullIncrement T f K s t) inferInstance) (naturalFiltration s) (fullLaw T f) := by
    rw [naturalFiltration,Filtration.natural_eq_comap]
    exact full_increment_indep_original_past T f K hK hbound s t hst
  have hm : @Measurable (ℝ≥0 → ℝ) ℝ (MeasurableSpace.comap (fullIncrement T f K s t) inferInstance) inferInstance
      (fullIncrement T f K s t) := measurable_iff_comap_le.mpr le_rfl
  have hc := condExp_indep_eq hg.comap_le (naturalFiltration.le s) hm.stronglyMeasurable hi
  have hB := full_isPreBrownian T f K hK hbound
  have hmean : (∫ ω, fullIncrement T f K s t ω ∂fullLaw T f)=0 := by
    change (∫ ω, BrownianBoundedControlSource.shiftedProcess T f K t ω-
      BrownianBoundedControlSource.shiftedProcess T f K s ω ∂fullLaw T f)=0
    rw [integral_sub (hB.integrable_eval t) (hB.integrable_eval s),hB.integral_eval,hB.integral_eval,sub_self]
  exact hc.trans (Eventually.of_forall (fun _ => hmean))

/-- Actual Brownian martingale for the ORIGINAL natural filtration, under
SAME computed fullQ and SAME real control/drift. -/
theorem full_process_martingale (T : ℝ≥0) (f : fullPredictableL2 T) (K : ℝ) (hK : 0≤K)
    (hbound : ∀ᵐ p ∂inputLaw T, |(f : Lp ℝ 2 (inputLaw T)) p|≤K) :
    Martingale (BrownianBoundedControlSource.shiftedProcess T f K) naturalFiltration (fullLaw T f) := by
  let _ := fullLaw_probability T f K hK hbound
  refine ⟨BrownianBoundedControlSource.shiftedProcess_stronglyAdapted T f K,fun s t hst => ?_⟩
  have hB := full_isPreBrownian T f K hK hbound
  have hi : Integrable (fullIncrement T f K s t) (fullLaw T f) := (hB.integrable_eval t).sub (hB.integrable_eval s)
  have he : BrownianBoundedControlSource.shiftedProcess T f K t=fullIncrement T f K s t+BrownianBoundedControlSource.shiftedProcess T f K s := by
    funext ω
    simp only [fullIncrement,Pi.add_apply,sub_add_cancel]
  rw [he]
  apply (condExp_add hi (hB.integrable_eval s) (naturalFiltration s)).trans
  rw [condExp_of_stronglyMeasurable (naturalFiltration.le s)
    (BrownianBoundedControlSource.shiftedProcess_stronglyAdapted T f K s) (hB.integrable_eval s)]
  filter_upwards [full_increment_condExp_zero T f K hK hbound s t hst] with ω hω
  simp only [Pi.add_apply,hω,zero_add]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedGirsanovSource
