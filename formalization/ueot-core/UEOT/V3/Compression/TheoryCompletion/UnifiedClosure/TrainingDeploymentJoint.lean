import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.EmpiricalReferenceRisk
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.AbsorbingLeakage

/-!
# Finite training selection and its actual deployment joint law

The training outcome remains part of the constructed joint sample. The
deployment law is selected from that outcome; no independence between the
training outcome and deployed path is postulated. This file concerns finite
training and path spaces with their measurable singleton structures.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open MeasureTheory UEOT.V3.PathError
open scoped BigOperators Classical

noncomputable section

universe uΩ uC uH

/-- Retain the training data and draw from its selected deployment PMF. -/
def selectedTrainingDeployment
    {Ω : Type uΩ} {C : Type uC} {H : Type uH}
    (training : PMF Ω) (select : Ω → C) (deployment : C → PMF H) : PMF (Ω × H) :=
  pmfExtend training (fun ω => deployment (select ω))

section FiniteJoint

variable {Ω : Type uΩ} {C : Type uC} {H : Type uH}
variable [Fintype Ω] [Fintype H]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [MeasurableSpace H] [MeasurableSingletonClass H]
variable (training : PMF Ω) (select : Ω → C) (deployment : C → PMF H)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace H] [MeasurableSingletonClass H] in
/-- The joint mass is derived from the PMF bind/map construction. -/
theorem selectedTrainingDeployment_mass (ω : Ω) (h : H) :
    selectedTrainingDeployment training select deployment (ω, h) =
      training ω * deployment (select ω) h :=
  pmfExtend_apply training (fun ω => deployment (select ω)) ω h

/-- Selection into any measurable candidate space is measurable here because
the training alphabet is finite and singletons are measurable. -/
theorem finite_training_selection_measurable [MeasurableSpace C] :
    Measurable select := measurable_of_finite _

omit [Fintype H] [MeasurableSingletonClass H] in
/-- The selected conditional deployment measure is an actual measurable
family, rather than a separately assumed conditional-law equality. -/
theorem selectedDeployment_measure_measurable :
    Measurable (fun ω => (deployment (select ω)).toMeasure) :=
  measurable_of_finite _

omit [Fintype Ω] [Fintype H] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace H] [MeasurableSingletonClass H] in
/-- Discarding the deployed path recovers the original training PMF. -/
theorem selectedTrainingDeployment_training_marginal :
    (selectedTrainingDeployment training select deployment).map Prod.fst = training := by
  unfold selectedTrainingDeployment pmfExtend
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (training.bind fun ω =>
    (deployment (select ω)).map (Function.const H ω)) = training
  simp_rw [PMF.map_const]
  exact PMF.bind_pure training

omit [Fintype Ω] [Fintype H] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace H] [MeasurableSingletonClass H] in
/-- Discarding the training coordinate gives the selected mixture. -/
theorem selectedTrainingDeployment_path_marginal :
    (selectedTrainingDeployment training select deployment).map Prod.snd =
      training.bind (fun ω => deployment (select ω)) := by
  unfold selectedTrainingDeployment pmfExtend
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (training.bind fun ω => (deployment (select ω)).map id) =
    training.bind (fun ω => deployment (select ω))
  simp_rw [PMF.map_id]

private theorem joint_finite_event_sum
    {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (p : PMF S) (E : Set S) :
    p.toMeasure.real E = ∑ s, if s ∈ E then (p s).toReal else 0 := by
  have hE : MeasurableSet E := Set.to_countable E |>.measurableSet
  rw [← integral_indicator_one hE, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s ∈ E <;> simp [hs, smul_eq_mul]

/-- A finite tower identity for any training-dependent failure event.
The equality follows from the real joint masses; it is not a premise. -/
theorem selectedTrainingDeployment_failure_tower (E : Ω → Set H) :
    (selectedTrainingDeployment training select deployment).toMeasure.real
        {z | z.2 ∈ E z.1} =
      ∑ ω, (training ω).toReal * (deployment (select ω)).toMeasure.real (E ω) := by
  rw [joint_finite_event_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [joint_finite_event_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hE : h ∈ E ω <;>
    simp [hE, selectedTrainingDeployment_mass, ENNReal.toReal_mul]

/-- The finite tower identity in integral form. The conditional risk is
computed from the same selected PMF used to construct the joint. -/
theorem selectedTrainingDeployment_failure_integral (E : Ω → Set H) :
    (selectedTrainingDeployment training select deployment).toMeasure.real
        {z | z.2 ∈ E z.1} =
      ∫ ω, (deployment (select ω)).toMeasure.real (E ω) ∂training.toMeasure := by
  rw [selectedTrainingDeployment_failure_tower, PMF.integral_eq_sum]
  simp only [smul_eq_mul]

/-- Preserve a data-dependent deployment budget on the same good event.
This permits later path or coverage budgets to remain conditional on the
training outcome; no uniform bound or surrogate training occupancy is used. -/
theorem selectedTrainingDeployment_data_dependent_bound
    (G : Set Ω) (E : Ω → Set H) (budget : Ω → ℝ)
    (hgood : ∀ ω ∈ G,
      (deployment (select ω)).toMeasure.real (E ω) ≤ budget ω) :
    (selectedTrainingDeployment training select deployment).toMeasure.real
        {z | z.2 ∈ E z.1} ≤
      training.toMeasure.real Gᶜ +
        ∑ ω, if ω ∈ G then (training ω).toReal * budget ω else 0 := by
  rw [selectedTrainingDeployment_failure_tower]
  calc
    (∑ ω, (training ω).toReal * (deployment (select ω)).toMeasure.real (E ω)) ≤
        ∑ ω, if ω ∈ G then (training ω).toReal * budget ω else (training ω).toReal := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases hω : ω ∈ G
      · simp only [if_pos hω]
        exact mul_le_mul_of_nonneg_left (hgood ω hω) ENNReal.toReal_nonneg
      · simp only [if_neg hω]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left
            (measureReal_le_one (μ := (deployment (select ω)).toMeasure) (s := E ω))
            (ENNReal.toReal_nonneg (a := training ω))
    _ = training.toMeasure.real Gᶜ +
        ∑ ω, if ω ∈ G then (training ω).toReal * budget ω else 0 := by
      rw [joint_finite_event_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : ω ∈ G <;> simp [hω]

/-- Integrating a common bound on the same good training event yields the
exact good/bad mixture budget. This specializes the data-dependent theorem. -/
theorem selectedTrainingDeployment_good_bad_bound
    (G : Set Ω) (E : Ω → Set H) (β : ℝ)
    (hgood : ∀ ω ∈ G, (deployment (select ω)).toMeasure.real (E ω) ≤ β) :
    (selectedTrainingDeployment training select deployment).toMeasure.real
        {z | z.2 ∈ E z.1} ≤
      β * training.toMeasure.real G + training.toMeasure.real Gᶜ := by
  have h := selectedTrainingDeployment_data_dependent_bound training select deployment
    G E (fun _ => β) hgood
  have hsum : (∑ ω, if ω ∈ G then (training ω).toReal * β else 0) =
      β * training.toMeasure.real G := by
    rw [joint_finite_event_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : ω ∈ G <;> simp [hω, mul_comm]
  rw [hsum, add_comm] at h
  exact h

/-- Training failure mass `α` and a common good-event deployment risk `β`
give the sharper mixture bound `α + (1-α)β`, capped by one. -/
theorem selectedTrainingDeployment_failure_le
    (G : Set Ω) (E : Ω → Set H) (α β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hbad : training.toMeasure.real Gᶜ ≤ α)
    (hgood : ∀ ω ∈ G, (deployment (select ω)).toMeasure.real (E ω) ≤ β) :
    (selectedTrainingDeployment training select deployment).toMeasure.real
        {z | z.2 ∈ E z.1} ≤ min 1 (α + (1 - α) * β) := by
  apply le_min measureReal_le_one
  have hG : MeasurableSet G := Set.to_countable G |>.measurableSet
  have hcompl : training.toMeasure.real Gᶜ = 1 - training.toMeasure.real G := by
    rw [measureReal_compl hG]
    simp
  calc
    (selectedTrainingDeployment training select deployment).toMeasure.real
        {z | z.2 ∈ E z.1} ≤
        β * training.toMeasure.real G + training.toMeasure.real Gᶜ :=
      selectedTrainingDeployment_good_bad_bound training select deployment G E β hgood
    _ = β + (1 - β) * training.toMeasure.real Gᶜ := by rw [hcompl]; ring
    _ ≤ β + (1 - β) * α :=
      add_le_add_right (mul_le_mul_of_nonneg_left hbad (sub_nonneg.mpr hβ.2)) β
    _ = α + (1 - α) * β := by ring

end FiniteJoint

section SourceDeployment

universe u

variable {Ω : Type uΩ} {X Y A C R O : Type u}
variable [Fintype Ω] [Fintype X] [Fintype Y] [Fintype A]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable [MeasurableSpace C]

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.TotalVariation ProbabilityTheory

/-- Every selected deployment is the actual causal path law of the same
microscopic source family, with its selected observation map and policy. -/
def candidateSourceDeployment
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (q : C → X → Y) (initial : C → PMF X)
    (policy : C → ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (T : ℕ) (c : C) : PMF (CausalHistory X (A × X) T) :=
  causalLaw (initial c)
    (riskMicroControlKernel (q c)
      (fun n x a => finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a)
      (policy c)) T

/-- The empirical-reference risk expression for the selected model and initial law. -/
def selectedEmpiricalReferenceUpper
    {N : ℕ} (hN : 0 < N)
    (sample : ℕ → A → X → Fin N → Ω → X) (ω : Ω)
    (q : X → Y) (r : Y → X) (initial : PMF X)
    (policy : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (rho eta : ℕ → ℝ) (T : ℕ)
    (F : Set (CausalHistory Y (A × Y) T)) : ℝ :=
  min 1
    ((causalLaw (initial.map q)
      (riskMacroControlKernel
        (riskRepresentativeKernel q r
          (fun n x a => empiricalResponsePMF hN (sample n a x) ω)) policy) T).toMeasure.real F +
      (1 - (∏ n ∈ Finset.range T, (1 - min 1 (rho n + eta n)))))

/-- Actual source sampling, a total data-dependent checked selection, and
the checked empirical-reference budget yield an unconditional joint failure
bound. All candidates use one microscopic source; the conditional deployed
PMF is constructed, not supplied through a law-matching conclusion field.

The source sampling law is the original finite probability measure. Its
canonical PMF has exactly that measure, so the sampling experiment is retained.
The microscopic failure event is common to every candidate; only its coarse
covering event may vary with the representation. The total selection must
pass the explicit checks for every training outcome. This does not claim
that a feasible selection always exists. -/
theorem statistical_selected_empirical_deployment_risk
    {N : ℕ} (hN : 0 < N) (training : Measure Ω) [IsProbabilityMeasure training]
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (sample : ℕ → A → X → Fin N → Ω → X) (rho : ℕ → ℝ) (T : ℕ)
    (hmeas : ∀ n, n < T → ∀ a x k, Measurable (sample n a x k))
    (hindep : ∀ n, n < T → ∀ a x,
      iIndepFun (sample n a x) training)
    (hlaw : ∀ n, n < T → ∀ a x k,
      training.map (sample n a x k) =
        (finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n)
    (select : Ω → C) (q : C → X → Y) (r : C → Y → X)
    (initial : C → PMF X)
    (policy : C → ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (eta : Ω → ℕ → ℝ)
    (E : Set (CausalHistory X (A × X) T))
    (F : C → Set (CausalHistory Y (A × Y) T))
    (heta : ∀ ω n, n < T → 0 ≤ eta ω n)
    (hfit : ∀ ω n, n < T → ∀ x a,
      tvDist
        ((empiricalResponsePMF hN (sample n a x) ω).map (q (select ω))).toMeasure
        ((empiricalResponsePMF hN
          (sample n a (r (select ω) (q (select ω) x))) ω).map (q (select ω))).toMeasure
          ≤ eta ω n)
    (henvelope : ∀ c,
      E ⊆ (riskHistoryMap (q c)
        (fun ax : A × X => (ax.1, q c ax.2)) T) ⁻¹' F c)
    (β : ℝ) (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hchecked : ∀ ω,
      selectedEmpiricalReferenceUpper hN sample ω (q (select ω)) (r (select ω))
        (initial (select ω)) (policy (select ω)) rho (eta ω) T (F (select ω)) ≤ β) :
    Measurable select ∧
      (selectedTrainingDeployment training.toPMF select
        (candidateSourceDeployment M q initial policy T)).toMeasure.real
        {z | z.2 ∈ E} ≤
          min 1 (transitionCalibrationFailureBudget X A (Finset X) N T rho +
            (1 - transitionCalibrationFailureBudget X A (Finset X) N T rho) * β) := by
  refine ⟨measurable_of_finite _, ?_⟩
  obtain ⟨good, _hgood, hbad, hcertificate⟩ :=
    statistical_empirical_reference_certificate hN M sample rho T
      training hmeas hindep hlaw hrho
  have hbad' : training.toPMF.toMeasure.real goodᶜ ≤
      transitionCalibrationFailureBudget X A (Finset X) N T rho := by
    simpa only [Measure.toPMF_toMeasure] using hbad
  apply selectedTrainingDeployment_failure_le training.toPMF select
    (candidateSourceDeployment M q initial policy T) good
    (fun _ => E)
    (transitionCalibrationFailureBudget X A (Finset X) N T rho) β hβ hbad'
  intro ω hω
  have h := hcertificate ω hω Y (q (select ω)) (r (select ω))
    (initial (select ω)) (policy (select ω)) (eta ω) (heta ω) (hfit ω)
  exact (h.2.2 E (F (select ω)) (henvelope (select ω))).trans (hchecked ω)

end SourceDeployment

namespace TrainingDeploymentWitness

open UEOT.V3.FiniteDiscountedControl

/-- An actual training PMF gives positive mass to both selected choices. -/
def training : PMF Bool :=
  AbsorbingLeakage.kernel (1 / 4) (by norm_num) (by norm_num) false

/-- Good data select a fair failure row; bad data select certain failure. -/
def deployment (choice : Bool) : PMF Bool :=
  if choice then PMF.pure true
  else AbsorbingLeakage.kernel (1 / 2) (by norm_num) (by norm_num) false

def joint : PMF (Bool × Bool) := selectedTrainingDeployment training id deployment

theorem training_bad_probability : training.toMeasure.real {ω | ω = true} = 1 / 4 := by
  rw [joint_finite_event_sum]
  norm_num [training, AbsorbingLeakage.kernel, FiniteProbabilityRow.ofRealRow,
    AbsorbingLeakage.transitionMass, Fintype.sum_bool]

theorem good_deployment_probability :
    (deployment false).toMeasure.real {h | h = true} = 1 / 2 := by
  rw [joint_finite_event_sum]
  norm_num [deployment, AbsorbingLeakage.kernel, FiniteProbabilityRow.ofRealRow,
    AbsorbingLeakage.transitionMass, Fintype.sum_bool]

theorem bad_deployment_probability :
    (deployment true).toMeasure.real {h | h = true} = 1 := by
  rw [joint_finite_event_sum]
  simp [deployment]

/-- Both choices are possible, and their actual deployment laws differ. -/
theorem selected_deployments_are_nonconstant :
    0 < training false ∧ 0 < training true ∧ deployment false ≠ deployment true := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [training, AbsorbingLeakage.kernel, FiniteProbabilityRow.ofRealRow,
      AbsorbingLeakage.transitionMass]
  · norm_num [training, AbsorbingLeakage.kernel, FiniteProbabilityRow.ofRealRow,
      AbsorbingLeakage.transitionMass]
  · intro h
    have he := congrArg (fun p : PMF Bool => p.toMeasure.real {h | h = true}) h
    rw [good_deployment_probability, bad_deployment_probability] at he
    norm_num at he

/-- The actual selected joint PMF attains the sharp good/bad mixture bound. -/
theorem sharp_joint_failure_probability :
    joint.toMeasure.real {z | z.2 = true} = 5 / 8 := by
  change (selectedTrainingDeployment training id deployment).toMeasure.real
    {z | z.2 ∈ ({h | h = true} : Set Bool)} = 5 / 8
  rw [selectedTrainingDeployment_failure_tower training id deployment
    (fun _ => {h : Bool | h = true})]
  simp only [Fintype.sum_bool, id_eq, good_deployment_probability, bad_deployment_probability]
  norm_num [training, AbsorbingLeakage.kernel, FiniteProbabilityRow.ofRealRow,
    AbsorbingLeakage.transitionMass]

theorem sharp_mixture_is_attained :
    joint.toMeasure.real {z | z.2 = true} =
      (1 / 4 : ℝ) + (1 - 1 / 4) * (1 / 2) := by
  rw [sharp_joint_failure_probability]
  norm_num

/-- Checking one family of safe conditional laws cannot certify another
deployed family, even when training, selection and failure labels agree. -/
theorem wrong_conditional_law_counterexample :
    (∀ _c : Bool, (PMF.pure false : PMF Bool).toMeasure.real {h | h = true} = 0) ∧
    (selectedTrainingDeployment training id (fun _ : Bool => PMF.pure false)).toMeasure.real
        {z | z.2 = true} = 0 ∧
    (selectedTrainingDeployment training id (fun _ : Bool => PMF.pure true)).toMeasure.real
        {z | z.2 = true} = 1 := by
  have hpure (b : Bool) :
      (PMF.pure b : PMF Bool).toMeasure.real {h | h = true} = if b then 1 else 0 := by
    rw [joint_finite_event_sum]
    cases b <;> simp
  refine ⟨fun _ => by simpa using hpure false, ?_, ?_⟩
  · change (selectedTrainingDeployment training id (fun _ : Bool => PMF.pure false)).toMeasure.real
      {z | z.2 ∈ ({h | h = true} : Set Bool)} = 0
    rw [selectedTrainingDeployment_failure_tower training id
      (fun _ : Bool => PMF.pure false) (fun _ => {h : Bool | h = true})]
    simp only [hpure]
    simp
  · change (selectedTrainingDeployment training id (fun _ : Bool => PMF.pure true)).toMeasure.real
      {z | z.2 ∈ ({h | h = true} : Set Bool)} = 1
    rw [selectedTrainingDeployment_failure_tower training id
      (fun _ : Bool => PMF.pure true) (fun _ => {h : Bool | h = true})]
    simp only [hpure]
    norm_num [Fintype.sum_bool, training, AbsorbingLeakage.kernel,
      FiniteProbabilityRow.ofRealRow, AbsorbingLeakage.transitionMass]

end TrainingDeploymentWitness

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
