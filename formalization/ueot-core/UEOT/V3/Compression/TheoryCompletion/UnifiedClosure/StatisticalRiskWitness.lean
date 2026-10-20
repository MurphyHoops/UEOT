import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration
import UEOT.V3.HilbertMeanProductBlockIndependence
import UEOT.V3.RepresentationCovariance

/-!
# Constructed sampling experiments and a nontrivial controlled witness

The registered sampling law and within-row independence are constructed from
finite products of the actual source PMFs. They are not assumptions about an
unspecified observation stream. This is a mathematical generative experiment;
it does not assert that a physical system can be reset to every source row.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness

open MeasureTheory ProbabilityTheory
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState
open UEOT.V3.HilbertMeanProductBlockIndependence
open scoped BigOperators Classical

noncomputable section

universe u uJ

section ProductRows

variable {J : Type uJ} {X : Type u} [Fintype J] [MeasurableSpace X]

/-- The product experiment contains `N` independent draws from each actual row. -/
def productRowLaw (row : J → PMF X) (N : ℕ) : Measure ((J × Fin N) → X) :=
  Measure.pi (fun jk : J × Fin N => (row jk.1).toMeasure)

instance productRowLaw_isProbability (row : J → PMF X) (N : ℕ) :
    IsProbabilityMeasure (productRowLaw row N) := by
  unfold productRowLaw
  infer_instance

/-- Registered samples are coordinate projections of the constructed experiment. -/
def productRowSample {N : ℕ} (j : J) (k : Fin N) (ω : (J × Fin N) → X) : X :=
  ω (j, k)

theorem productRowSample_measurable {N : ℕ} (j : J) (k : Fin N) :
    Measurable (productRowSample (X := X) j k) :=
  measurable_pi_apply (j, k)

/-- The marginal is the supplied source PMF, not an independently postulated law. -/
theorem productRowSample_law (row : J → PMF X) {N : ℕ} (j : J) (k : Fin N) :
    (productRowLaw row N).map (productRowSample j k) = (row j).toMeasure := by
  exact (measurePreserving_eval
    (fun jk : J × Fin N => (row jk.1).toMeasure) (j, k)).map_eq

/-- Reuse the existing P-STAT-06 coordinate-independence theorem and restrict
its index family to the requested row. -/
theorem productRowSample_independent (row : J → PMF X) (N : ℕ) (j : J) :
    iIndepFun (productRowSample (X := X) (N := N) j) (productRowLaw row N) := by
  have hall := coordinate_iIndep
    (fun jk : J × Fin N => (row jk.1).toMeasure)
  exact iIndepFun.precomp
    (g := fun k : Fin N => (j, k))
    (by intro k l h; exact congrArg Prod.snd h) hall

end ProductRows

section SourceExperiment

variable {X A R O I : Type u}
variable [Fintype X] [Fintype A] [Fintype I]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The finite experiment registers exactly the rows used before horizon `T`. -/
def sourceRows (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O) (T : ℕ) :
    (Fin T × A × X) → PMF X :=
  fun row => finiteKernelRowPMF (modelAsFiniteKernel (M row.1)) row.2.2 row.2.1

def sourceExperimentLaw
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O) (N T : ℕ) :
    Measure (((Fin T × A × X) × Fin N) → X) :=
  productRowLaw (sourceRows M T) N

instance sourceExperimentLaw_isProbability
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O) (N T : ℕ) :
    IsProbabilityMeasure (sourceExperimentLaw M N T) := by
  unfold sourceExperimentLaw
  infer_instance

/-- Only `n < T` is sampled. The irrelevant later values are totalized by `x`. -/
def sourceSample (N T : ℕ) (n : ℕ) (a : A) (x : X) (k : Fin N)
    (ω : ((Fin T × A × X) × Fin N) → X) : X :=
  if h : n < T then productRowSample (⟨n, h⟩, a, x) k ω else x

theorem sourceSample_before (N T n : ℕ) (hn : n < T) (a : A) (x : X) :
    sourceSample N T n a x =
      productRowSample (X := X) (N := N) ((⟨n, hn⟩ : Fin T), a, x) := by
  funext k ω
  simp only [sourceSample, dif_pos hn]

theorem sourceSample_measurable (N T n : ℕ) (hn : n < T)
    (a : A) (x : X) (k : Fin N) :
    Measurable (sourceSample N T n a x k) := by
  rw [sourceSample_before N T n hn a x]
  exact productRowSample_measurable (X := X) ((⟨n, hn⟩ : Fin T), a, x) k

theorem sourceSample_law
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (N T n : ℕ) (hn : n < T) (a : A) (x : X) (k : Fin N) :
    (sourceExperimentLaw M N T).map (sourceSample N T n a x k) =
      (finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a).toMeasure := by
  rw [sourceSample_before N T n hn a x]
  exact productRowSample_law (sourceRows M T) ((⟨n, hn⟩ : Fin T), a, x) k

theorem sourceSample_independent
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (N T n : ℕ) (hn : n < T) (a : A) (x : X) :
    iIndepFun (sourceSample N T n a x) (sourceExperimentLaw M N T) := by
  rw [sourceSample_before N T n hn a x]
  exact productRowSample_independent (sourceRows M T) N ((⟨n, hn⟩ : Fin T), a, x)

/-- An actual finite product experiment supplies every sampling premise of
the statistical risk theorem. Only the fixed bounded tests and radii remain
inputs; the sample law, measurability and independence are derived here. -/
theorem product_experiment_risk_certificate
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (test : ℕ → I → X → ℝ) (N T : ℕ) (rho : ℕ → ℝ) (hN : 0 < N)
    (htest : ∀ n, n < T → ∀ i, Measurable (test n i))
    (hbounded : ∀ n, n < T → ∀ i x, test n i x ∈ Set.Icc (0 : ℝ) 1)
    (hrho : ∀ n, n < T → 0 ≤ rho n) :
    ∃ good : Set (((Fin T × A × X) × Fin N) → X), MeasurableSet good ∧
      (sourceExperimentLaw M N T).real goodᶜ ≤
        transitionCalibrationFailureBudget X A I N T rho ∧
      ∀ ω ∈ good,
        UniformEmpiricalRepresentativeRisk M test (sourceSample N T) rho T ω := by
  exact statistical_representative_risk_certificate M test (sourceSample N T) rho T
    hN (sourceExperimentLaw M N T) htest hbounded
    (sourceSample_measurable N T)
    (sourceSample_independent M N T)
    (sourceSample_law M N T) hrho

end SourceExperiment

section HiddenBitModel

abbrev State := Bool × Bool

local instance : MeasurableSpace Bool := ⊤
local instance : MeasurableSpace State := ⊤

/-- The first bit is observed; the second is persistent hidden state. -/
def coarse (x : State) : Bool := x.1

def partition : Setoid State := Setoid.ker coarse

@[simp] theorem partition_iff (x y : State) :
    partition.r x y ↔ coarse x = coarse y := Iff.rfl

/-- Both the hidden state and the chosen action affect the genuine failure chance. -/
def failureChance (hidden action : Bool) : ℝ :=
  1 / 16 + (if hidden then 1 / 8 else 0) + (if action then 1 / 8 else 0)

def transitionMass (a : Bool) (x z : State) : ℝ :=
  if z.2 = x.2 then
    if z.1 then failureChance x.2 a else 1 - failureChance x.2 a
  else 0

private theorem transition_nonneg (a : Bool) (x z : State) :
    0 ≤ transitionMass a x z := by
  rcases x with ⟨b, h⟩
  rcases z with ⟨c, g⟩
  cases a <;> cases h <;> cases c <;> cases g <;>
    norm_num [transitionMass, failureChance]

private theorem transition_sum (a : Bool) (x : State) :
    ∑ z, transitionMass a x z = 1 := by
  rcases x with ⟨b, h⟩
  cases a <;> cases h <;>
    norm_num [transitionMass, failureChance, Fintype.sum_prod_type, Fintype.sum_bool]

/-- One normalized controlled model supplies dynamics, sampling and calibration. -/
def model : UEOT.V3.FiniteStablePartition.Model State Bool Unit Bool where
  transition := transitionMass
  reward := fun _ _ => ()
  output := coarse
  transition_nonneg := transition_nonneg
  transition_sum_one := transition_sum

def actualRow (x : State) (a : Bool) : PMF State :=
  finiteKernelRowPMF (modelAsFiniteKernel model) x a

@[simp] theorem actualRow_mass (x : State) (a : Bool) (z : State) :
    (actualRow x a z).toReal = transitionMass a x z := by
  simp [actualRow, modelAsFiniteKernel, model]

def test (i : Bool) (x : State) : ℝ := if coarse x = i then 1 else 0

def coeff (z : State) (i : Bool) : ℝ := if coarse z = i then 1 else 0

theorem test_bounded (i : Bool) (x : State) : test i x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : coarse x = i <;> norm_num [test, h]

theorem indicators_spanned : ApproxSpansPartitionIndicators partition test coeff 0 := by
  intro z y
  simp only [partition_iff]
  rcases z with ⟨b, h⟩
  rcases y with ⟨c, g⟩
  cases b <;> cases c <;>
    norm_num [coarse, test, coeff, Fintype.sum_bool]

theorem coefficient_norm (z : State) : ∑ i, |coeff z i| = 1 := by
  rcases z with ⟨b, h⟩
  cases b <;> norm_num [coeff, coarse, Fintype.sum_bool]

/-- The test expectations are computed from the same normalized transition table. -/
theorem test_expectation (a i : Bool) (x : State) :
    transitionTestExpectation model (test i) a x =
      if i then failureChance x.2 a else 1 - failureChance x.2 a := by
  rcases x with ⟨b, h⟩
  cases a <;> cases i <;> cases h <;>
    norm_num [transitionTestExpectation, model, transitionMass, failureChance,
      test, coarse, Fintype.sum_prod_type, Fintype.sum_bool]

theorem fibre_test_gap (x y : State) (a i : Bool) :
    |transitionTestExpectation model (test i) a x -
      transitionTestExpectation model (test i) a y| ≤ 1 / 8 := by
  rw [test_expectation, test_expectation]
  rcases x with ⟨b, h⟩
  rcases y with ⟨c, g⟩
  cases a <;> cases i <;> cases h <;> cases g <;>
    norm_num [failureChance]

/-- Compression hides a dynamically relevant bit: the within-fibre gap is positive. -/
theorem hidden_gap_nonzero :
    coarse (false, false) = coarse (false, true) ∧
    transitionTestExpectation model (test true) false (false, true) -
      transitionTestExpectation model (test true) false (false, false) = 1 / 8 := by
  norm_num [coarse, test_expectation, failureChance]

/-- The action is consequential in this same model. -/
theorem action_gap_nonzero :
    transitionTestExpectation model (test true) true (false, false) -
      transitionTestExpectation model (test true) false (false, false) = 1 / 8 := by
  norm_num [test_expectation, failureChance]

theorem coarse_not_injective : ¬ Function.Injective coarse := by
  intro h
  have he := h (show coarse (false, false) = coarse (false, true) from rfl)
  have := congrArg Prod.snd he
  cases this

/-- The example cannot silently satisfy an exact state-only quotient premise. -/
theorem partition_not_stable : ¬ UEOT.V3.FiniteStablePartition.Stable model partition := by
  intro h
  have hh := h (x := (false, false)) (y := (false, true)) rfl false (true, false)
  simp only [UEOT.V3.FiniteStablePartition.blockMass, partition_iff] at hh
  norm_num [model, coarse, transitionMass, failureChance,
    Fintype.sum_prod_type, Fintype.sum_bool] at hh

abbrev Class := ReachableState (setoidRepresentation partition)

def classBit (c : Class) : Bool :=
  Quotient.lift coarse (fun _ _ h => h) c.1

@[simp] theorem classBit_project (x : State) :
    classBit (toReachable (setoidRepresentation partition) x) = coarse x := rfl

def representative (c : Class) : State := (classBit c, false)

theorem representative_section (c : Class) :
    toReachable (setoidRepresentation partition) (representative c) = c := by
  obtain ⟨x, hx⟩ := c.property
  have hc : c = toReachable (setoidRepresentation partition) x := Subtype.ext hx.symm
  rw [hc]
  apply Subtype.ext
  apply Quotient.sound
  rfl

def classEquivBool : Class ≃ Bool where
  toFun := classBit
  invFun := fun b => toReachable (setoidRepresentation partition) (b, false)
  left_inv := representative_section
  right_inv := fun _ => rfl

theorem class_card : Nat.card Class = 2 := by
  rw [Nat.card_congr classEquivBool]
  simp

/-- This confidence budget accounts for 16 transition rows and two fixed tests. -/
theorem concrete_confidence_budget :
    transitionCalibrationFailureBudget State Bool Bool 4096 2 (fun _ => 1 / 32) =
      64 * Real.exp (-8) := by
  norm_num [transitionCalibrationFailureBudget]
  ring

/-- A certified, deliberately conservative numerical confidence bound. -/
theorem concrete_confidence_nonvacuous :
    64 * Real.exp (-8) ≤ (1 / 4 : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hpow : (256 : ℝ) ≤ (Real.exp 1) ^ 8 := by
    calc
      (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 := pow_le_pow_left₀ (by norm_num) htwo 8
  have hexp : (256 : ℝ) ≤ Real.exp 8 := by
    simpa using hpow.trans_eq (Real.exp_nat_mul 1 8).symm
  rw [Real.exp_neg]
  have hinv : (Real.exp 8)⁻¹ ≤ (1 / 256 : ℝ) := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp
  linarith

def modelFamily : ℕ → UEOT.V3.FiniteStablePartition.Model State Bool Unit Bool :=
  fun _ => model

def testFamily : ℕ → Bool → State → ℝ := fun _ => test

def radius : ℕ → ℝ := fun _ => 1 / 32

abbrev SampleSpace := ((Fin 2 × Bool × State) × Fin 4096) → State

def trainingLaw : Measure SampleSpace := sourceExperimentLaw modelFamily 4096 2

instance trainingLaw_isProbability : IsProbabilityMeasure trainingLaw := by
  unfold trainingLaw
  infer_instance

def samples : ℕ → Bool → State → Fin 4096 → SampleSpace → State :=
  sourceSample 4096 2

def Good (ω : SampleSpace) : Prop :=
  EmpiricalTransitionCalibrated modelFamily testFamily samples radius 2 ω

theorem measurable_good : MeasurableSet {ω | Good ω} := by
  exact measurableSet_empirical_transition_calibrated
    modelFamily testFamily samples radius 2
    (fun _ _ _ => measurable_of_finite _)
    (sourceSample_measurable 4096 2)

/-- The finite experiment has an actual confidence bound, with no sampling
or law-matching hypotheses left to discharge. -/
theorem training_bad_probability_le : trainingLaw.real {ω | ¬ Good ω} ≤ 1 / 4 := by
  have h := measure_empirical_transition_uncalibrated_le
    (by norm_num : 0 < 4096) trainingLaw modelFamily testFamily samples radius 2
    (fun _ _ _ => measurable_of_finite _)
    (fun _ _ i x => test_bounded i x)
    (sourceSample_measurable 4096 2)
    (sourceSample_independent modelFamily 4096 2)
    (sourceSample_law modelFamily 4096 2)
    (fun _ _ => by norm_num [radius])
  calc
    trainingLaw.real {ω | ¬ Good ω} ≤
        transitionCalibrationFailureBudget State Bool Bool 4096 2 radius := h
    _ = 64 * Real.exp (-8) := concrete_confidence_budget
    _ ≤ 1 / 4 := concrete_confidence_nonvacuous

theorem training_good_probability_ge : (3 / 4 : ℝ) ≤ trainingLaw.real {ω | Good ω} := by
  have h := training_bad_probability_le
  change trainingLaw.real {ω | Good ω}ᶜ ≤ 1 / 4 at h
  rw [measureReal_compl measurable_good] at h
  have huniv : trainingLaw.real Set.univ = 1 := by simp
  rw [huniv] at h
  linarith

/-- This is a nonempty simultaneous event in the constructed experiment. -/
theorem good_sample_exists : ∃ ω, Good ω := by
  by_contra h
  have hempty : {ω | Good ω} = (∅ : Set SampleSpace) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hω => h ⟨ω, hω⟩
  have hp := training_good_probability_ge
  rw [hempty] at hp
  norm_num at hp

/-- The measured fibre test passes on this same good event; it is derived
from the model's true nonzero gap and the two actual calibration errors. -/
theorem measured_fibre_bound (ω : SampleSpace) (hgood : Good ω)
    (n : ℕ) (hn : n < 2) (x y : State) (a i : Bool) :
    |empiricalTransitionTests testFamily samples ω n a x i -
      empiricalTransitionTests testFamily samples ω n a y i| ≤ 3 / 16 := by
  have hx := hgood n hn a x i
  have hy := hgood n hn a y i
  change |transitionTestExpectation model (test i) a x -
    empiricalTransitionTests testFamily samples ω n a x i| ≤ 1 / 32 at hx
  change |transitionTestExpectation model (test i) a y -
    empiricalTransitionTests testFamily samples ω n a y i| ≤ 1 / 32 at hy
  have hx' : |empiricalTransitionTests testFamily samples ω n a x i -
      transitionTestExpectation model (test i) a x| ≤ 1 / 32 := by
    simpa only [abs_sub_comm] using hx
  have hgap := fibre_test_gap x y a i
  have hleft := abs_sub_le (empiricalTransitionTests testFamily samples ω n a x i)
    (transitionTestExpectation model (test i) a x)
    (empiricalTransitionTests testFamily samples ω n a y i)
  have hright := abs_sub_le (transitionTestExpectation model (test i) a x)
    (transitionTestExpectation model (test i) a y)
    (empiricalTransitionTests testFamily samples ω n a y i)
  linarith

/-- The same process simultaneously satisfies the statistical, reconstruction,
measured-fibre and policy-sharing contracts of the actual path-risk theorem. -/
theorem representative_risk_on_good
    (ω : SampleSpace) (hgood : Good ω) (p₀ : PMF State)
    (policy : ∀ n, UEOT.V3.PathError.CausalHistory Class (Bool × Class) n → PMF Bool) :
    RepresentativeRiskConclusion modelFamily partition representative p₀ policy
      (fun _ => 0) (fun _ => 3 / 16) radius (fun _ => 1) 2 := by
  have hu := empirical_representative_risk_of_calibrated
    modelFamily testFamily samples radius 2 (fun _ _ => by norm_num [radius]) ω hgood
  exact hu partition representative representative_section p₀ policy
    (fun _ => coeff) (fun _ => 0) (fun _ => 3 / 16) (fun _ => 1)
    (fun _ _ => indicators_spanned)
    (fun n hn x y _ a i => measured_fibre_bound ω hgood n hn x y a i)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    (fun _ _ z => le_of_eq (coefficient_norm z))

/-- The radius used by the calibrated two-class path theorem is exactly 1/4. -/
theorem concrete_row_budget :
    letI : Fintype Class := Fintype.ofFinite _
    min 1 ((1 / 2 : ℝ) * ((Fintype.card Class : ℝ) *
      (2 * 0 + (3 / 16 + 2 * (1 / 32)) * 1))) = 1 / 4 := by
  letI : Fintype Class := Fintype.ofFinite _
  have hc : Fintype.card Class = 2 := by
    simpa only [Nat.card_eq_fintype_card] using class_card
  norm_num [hc]

/-- The resulting multi-step budget is strictly below the vacuous TV cap. -/
theorem concrete_path_budget :
    (1 - (∏ _n ∈ Finset.range 2, (1 - (1 / 4 : ℝ)))) = 7 / 16 ∧
      (7 / 16 : ℝ) < 1 := by
  norm_num [Finset.prod_range_succ]

/-! ## An actual reference event and the microscopic risk bound -/

open UEOT.V3.PathError

/-- Initially the observed bit is safe and the hidden bit is uniform. -/
def referenceInitialLaw : PMF State :=
  (PMF.uniformOfFintype Bool).map (fun hidden => (false, hidden))

/-- The comparison and microscopic source use the same constant action false. -/
def referencePolicy (n : ℕ) (_h : CausalHistory Bool (Bool × Bool) n) : PMF Bool :=
  PMF.pure false

/-- The chosen prototype has hidden bit false; its true row defines the reference. -/
def boolReferenceKernel : ℕ → Bool → Bool → PMF Bool :=
  riskRepresentativeKernel coarse (fun b => (b, false)) (fun _ => actualRow)

def boolReferenceLaw (n : ℕ) : PMF (CausalHistory Bool (Bool × Bool) n) :=
  causalLaw (referenceInitialLaw.map coarse)
    (riskMacroControlKernel boolReferenceKernel referencePolicy) n

theorem referenceInitialLaw_project : referenceInitialLaw.map coarse = PMF.pure false := by
  unfold referenceInitialLaw
  rw [PMF.map_comp]
  change (PMF.uniformOfFintype Bool).map (fun _ => false) = PMF.pure false
  ext b
  rw [PMF.map_apply]
  cases b <;> norm_num [PMF.tsum_coe]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem actualRow_ofReal (x : State) (a : Bool) (z : State) :
    actualRow x a z = ENNReal.ofReal (transitionMass a x z) := by
  rw [← actualRow_mass]
  exact (ENNReal.ofReal_toReal (PMF.apply_ne_top (actualRow x a) z)).symm

/-- The true projected prototype row has failure chance 1/16 under action false. -/
theorem boolReferenceKernel_apply (n : ℕ) (b a z : Bool) :
    boolReferenceKernel n b a z =
      ENNReal.ofReal (if z then failureChance false a else 1 - failureChance false a) := by
  unfold boolReferenceKernel riskRepresentativeKernel
  rw [PMF.map_apply, tsum_fintype]
  cases a <;> cases z <;>
    norm_num [Fintype.sum_prod_type, Fintype.sum_bool, coarse,
      actualRow_ofReal, transitionMass, failureChance]

private theorem boolReferenceLaw_two_apply (b a₁ z₁ a₂ z₂ : Bool) :
    boolReferenceLaw 2 ((b, (a₁, z₁)), (a₂, z₂)) =
      ((PMF.pure false b) *
        ((PMF.pure false a₁) * ENNReal.ofReal
          (if z₁ then failureChance false a₁ else 1 - failureChance false a₁))) *
        ((PMF.pure false a₂) * ENNReal.ofReal
          (if z₂ then failureChance false a₂ else 1 - failureChance false a₂)) := by
  unfold boolReferenceLaw
  rw [referenceInitialLaw_project]
  let K₀ : Bool → PMF (Bool × Bool) :=
    fun initial => pmfExtend (PMF.pure false) (boolReferenceKernel 0 initial)
  let K₁ : (Bool × (Bool × Bool)) → PMF (Bool × Bool) :=
    fun h => pmfExtend (PMF.pure false) (boolReferenceKernel 1 h.2.2)
  change pmfExtend (pmfExtend (PMF.pure false) K₀) K₁
    ((b, (a₁, z₁)), (a₂, z₂)) = _
  rw [pmfExtend_apply, pmfExtend_apply]
  dsimp only [K₀, K₁]
  rw [pmfExtend_apply, pmfExtend_apply,
    boolReferenceKernel_apply, boolReferenceKernel_apply]

private theorem boolReference_failure_iff (b a₁ z₁ a₂ z₂ : Bool) :
    ((b, (a₁, z₁)), (a₂, z₂)) ∈
      {h : CausalHistory Bool (Bool × Bool) 2 |
        riskEverFailure (fun x : Bool => x = true) 2 h} ↔
      (b = true ∨ z₁ = true) ∨ z₂ = true := by
  rfl

/-- An independent scalar-indicator proof for the same typed history event. -/
private theorem boolReference_indicator (b a₁ z₁ a₂ z₂ : Bool) :
    ({h | riskEverFailure (fun x : Bool => x = true) 2 h}.indicator
      (1 : CausalHistory Bool (Bool × Bool) 2 → ℝ))
      ((b, (a₁, z₁)), (a₂, z₂)) =
        if (b = true ∨ z₁ = true) ∨ z₂ = true then 1 else 0 := by
  classical
  by_cases hb : (b = true ∨ z₁ = true) ∨ z₂ = true
  · have hmem := (boolReference_failure_iff b a₁ z₁ a₂ z₂).mpr hb
    calc
      _ = (1 : CausalHistory Bool (Bool × Bool) 2 → ℝ)
          ((b, (a₁, z₁)), (a₂, z₂)) := Set.indicator_of_mem hmem
            (1 : CausalHistory Bool (Bool × Bool) 2 → ℝ)
      _ = _ := by rw [if_pos hb]; rfl
  · have hnot : ((b, (a₁, z₁)), (a₂, z₂)) ∉
        {h : CausalHistory Bool (Bool × Bool) 2 |
          riskEverFailure (fun x : Bool => x = true) 2 h} :=
      fun hm => hb ((boolReference_failure_iff b a₁ z₁ a₂ z₂).mp hm)
    calc
      _ = 0 := Set.indicator_of_notMem hnot
        (1 : CausalHistory Bool (Bool × Bool) 2 → ℝ)
      _ = _ := (if_neg hb).symm

/-- Exact probability of ever failing in the actual two-step reference path.
The reference is allowed to recover; no absorbing-law equality is assumed. -/
theorem boolReference_two_step_failure :
    (boolReferenceLaw 2).toMeasure.real
      {h | riskEverFailure (fun b : Bool => b = true) 2 h} = 31 / 256 := by
  classical
  have hF : MeasurableSet
      {h : CausalHistory Bool (Bool × Bool) 2 |
        riskEverFailure (fun b : Bool => b = true) 2 h} :=
    Set.to_countable _ |>.measurableSet
  let term : ((Bool × (Bool × Bool)) × (Bool × Bool)) → ℝ := fun h =>
    if h.1.1 = false ∧ h.1.2.1 = false ∧ h.2.1 = false then
      if h.1.2.2 = true ∨ h.2.2 = true then
        (if h.1.2.2 then 1 / 16 else 15 / 16) *
          (if h.2.2 then 1 / 16 else 15 / 16)
      else 0
    else 0
  have hterm (h : CausalHistory Bool (Bool × Bool) 2) :
      (boolReferenceLaw 2 h).toReal •
        ({h | riskEverFailure (fun b : Bool => b = true) 2 h}.indicator
          (1 : CausalHistory Bool (Bool × Bool) 2 → ℝ)) h = term h := by
    rcases h with ⟨⟨b, a₁, z₁⟩, a₂, z₂⟩
    change Bool at b
    erw [boolReferenceLaw_two_apply b a₁ z₁ a₂ z₂]
    erw [boolReference_indicator b a₁ z₁ a₂ z₂]
    cases b <;> cases a₁ <;> cases z₁ <;> cases a₂ <;> cases z₂ <;>
      norm_num [term, smul_eq_mul, PMF.pure_apply,
        failureChance, ENNReal.toReal_mul, Pi.one_apply]
  rw [← integral_indicator_one hF, PMF.integral_eq_sum]
  trans ∑ h : CausalHistory Bool (Bool × Bool) 2, term h
  · exact Finset.sum_congr rfl (fun h _ => hterm h)
  · change (∑ h : (Bool × (Bool × Bool)) × (Bool × Bool), term h) = (31 / 256 : ℝ)
    norm_num [term, Fintype.sum_prod_type, Fintype.sum_bool]

open UEOT.V3.PathError UEOT.V3.RepresentationCovariance

local instance : Fintype Class := Fintype.ofFinite _
local instance : MeasurableSpace Class := ⊤

def classReferencePolicy (n : ℕ) (_h : CausalHistory Class (Bool × Class) n) : PMF Bool :=
  PMF.pure false

def classReferenceKernel : ℕ → Class → Bool → PMF Class :=
  riskRepresentativeKernel (toReachable (setoidRepresentation partition))
    representative (fun _ => actualRow)

def classReferenceLaw (n : ℕ) : PMF (CausalHistory Class (Bool × Class) n) :=
  causalLaw (referenceInitialLaw.map (toReachable (setoidRepresentation partition)))
    (riskMacroControlKernel classReferenceKernel classReferencePolicy) n

def classHistoryEquiv (n : ℕ) :
    CausalHistory Class (Bool × Class) n ≃ CausalHistory Bool (Bool × Bool) n :=
  causalHistoryEquiv classEquivBool ((Equiv.refl Bool).prodCongr classEquivBool) n

theorem class_history_last (n : ℕ) (h : CausalHistory Class (Bool × Class) n) :
    riskLastState n (classHistoryEquiv n h) = classBit (riskLastState n h) := by
  cases n <;> rfl

/-- The quotient and Boolean presentations use exactly the same prototype row. -/
theorem classReferenceKernel_map (n : ℕ) (c : Class) (a : Bool) :
    (classReferenceKernel n c a).map classEquivBool =
      boolReferenceKernel n (classBit c) a := by
  unfold classReferenceKernel boolReferenceKernel riskRepresentativeKernel
  rw [PMF.map_comp]
  rfl

theorem class_reference_control_map (n : ℕ)
    (h : CausalHistory Class (Bool × Class) n) :
    (riskMacroControlKernel classReferenceKernel classReferencePolicy n h).map
        ((Equiv.refl Bool).prodCongr classEquivBool) =
      riskMacroControlKernel boolReferenceKernel referencePolicy n (classHistoryEquiv n h) := by
  change (pmfExtend (PMF.pure false) (classReferenceKernel n (riskLastState n h))).map
      ((Equiv.refl Bool).prodCongr classEquivBool) =
    pmfExtend (PMF.pure false) (boolReferenceKernel n (riskLastState n (classHistoryEquiv n h)))
  rw [pmfExtend_map_equiv]
  have hi : (PMF.pure false).map (Equiv.refl Bool) = PMF.pure false := by
    change (PMF.pure false).map id = PMF.pure false
    rw [PMF.map_id]
  rw [hi]
  apply congrArg (pmfExtend (PMF.pure false))
  funext a
  change (classReferenceKernel n (riskLastState n h) a).map classEquivBool =
    boolReferenceKernel n (riskLastState n (classHistoryEquiv n h)) a
  rw [class_history_last]
  exact classReferenceKernel_map n (riskLastState n h) a

/-- Reuse P-FAC-01 path naturality to identify the actual quotient reference
with the explicit Boolean reference whose event mass is computed above. -/
theorem class_reference_transport (n : ℕ) :
    (classReferenceLaw n).map (classHistoryEquiv n) = boolReferenceLaw n := by
  have h := causalLaw_transport_equiv
    (referenceInitialLaw.map (toReachable (setoidRepresentation partition)))
    (riskMacroControlKernel classReferenceKernel classReferencePolicy)
    (riskMacroControlKernel boolReferenceKernel referencePolicy)
    classEquivBool ((Equiv.refl Bool).prodCongr classEquivBool)
    (fun k hk => (class_reference_control_map k hk).symm) n
  have hinit :
      (referenceInitialLaw.map (toReachable (setoidRepresentation partition))).map
        classEquivBool = referenceInitialLaw.map coarse := by
    rw [PMF.map_comp]
    rfl
  simpa only [classReferenceLaw, boolReferenceLaw, classHistoryEquiv, hinit] using h

theorem class_ever_failure_equiv (n : ℕ)
    (h : CausalHistory Class (Bool × Class) n) :
    riskEverFailure (fun c => classBit c = true) n h ↔
      riskEverFailure (fun b : Bool => b = true) n (classHistoryEquiv n h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (riskEverFailure (fun c => classBit c = true) n h.1 ∨
      classBit h.2.2 = true) ↔
      (riskEverFailure (fun b : Bool => b = true) n (classHistoryEquiv n h.1) ∨
        classBit h.2.2 = true)
    exact or_congr (ih h.1) Iff.rfl

theorem class_reference_two_step_failure :
    (classReferenceLaw 2).toMeasure.real
      {h | riskEverFailure (fun c => classBit c = true) 2 h} = 31 / 256 := by
  let F : Set (CausalHistory Bool (Bool × Bool) 2) :=
    {h | riskEverFailure (fun b : Bool => b = true) 2 h}
  have hF : MeasurableSet F := Set.to_countable F |>.measurableSet
  have hf : Measurable (classHistoryEquiv 2) := measurable_of_countable _
  have hset : {h | riskEverFailure (fun c => classBit c = true) 2 h} =
      (classHistoryEquiv 2) ⁻¹' F := by
    ext h
    exact class_ever_failure_equiv 2 h
  rw [hset]
  calc
    (classReferenceLaw 2).toMeasure.real ((classHistoryEquiv 2) ⁻¹' F) =
        ((classReferenceLaw 2).map (classHistoryEquiv 2)).toMeasure.real F := by
      rw [← PMF.toMeasure_map _ _ hf]
      simp only [Measure.real, Measure.map_apply hf hF]
    _ = (boolReferenceLaw 2).toMeasure.real F := by rw [class_reference_transport]
    _ = 31 / 256 := boolReference_two_step_failure

def actualMicroLaw (n : ℕ) : PMF (CausalHistory State (Bool × State) n) :=
  causalLaw referenceInitialLaw
    (riskMicroControlKernel (toReachable (setoidRepresentation partition))
      (fun _ => actualRow) classReferencePolicy) n

/-- Actual failure of the microscopic source is bounded through its observed
unsafe-state event, on the same positive-probability training event. -/
theorem microscopic_two_step_risk_on_good (ω : SampleSpace) (hgood : Good ω) :
    (actualMicroLaw 2).toMeasure.real
      {h | riskEverFailure (fun x : State => coarse x = true) 2 h} ≤ 143 / 256 := by
  let q := toReachable (setoidRepresentation partition)
  let E : Set (CausalHistory State (Bool × State) 2) :=
    {h | riskEverFailure (fun x : State => coarse x = true) 2 h}
  let F : Set (CausalHistory Class (Bool × Class) 2) :=
    {h | riskEverFailure (fun c => classBit c = true) 2 h}
  have hEF : E ⊆ (riskHistoryMap q (fun ax : Bool × State => (ax.1, q ax.2)) 2) ⁻¹' F := by
    intro h hh
    exact risk_ever_failure_envelope q (fun x : State => coarse x = true)
      (fun c => classBit c = true) (fun x hx => hx) 2 h hh
  have hr := representative_risk_on_good ω hgood referenceInitialLaw classReferencePolicy
  have h := hr.2.2.2 E F hEF
  have hc : Fintype.card Class = 2 := by
    simpa only [Nat.card_eq_fintype_card] using class_card
  change (actualMicroLaw 2).toMeasure.real E ≤
    min 1 ((classReferenceLaw 2).toMeasure.real F +
      (1 - (∏ n ∈ Finset.range 2, (1 - min 1 ((1 / 2 : ℝ) *
        ((Fintype.card Class : ℝ) * (2 * 0 + (3 / 16 + 2 * radius n) * 1))))))) at h
  have hFmass : (classReferenceLaw 2).toMeasure.real F = 31 / 256 :=
    class_reference_two_step_failure
  rw [hFmass] at h
  norm_num [hc, radius, Finset.prod_range_succ] at h
  exact h

/-- A genuine nontrivial joint witness: non-exact compression, actual product
sampling, a measurable event of probability at least 3/4, and microscopic
two-step failure bound 143/256 < 1 all belong to the same controlled model. -/
theorem joint_statistical_microscopic_risk_witness :
    ¬ UEOT.V3.FiniteStablePartition.Stable model partition ∧
    (143 / 256 : ℝ) < 1 ∧
    ∃ good : Set SampleSpace, MeasurableSet good ∧
      (3 / 4 : ℝ) ≤ trainingLaw.real good ∧
      ∀ ω ∈ good,
        (actualMicroLaw 2).toMeasure.real
          {h | riskEverFailure (fun x : State => coarse x = true) 2 h} ≤ 143 / 256 := by
  refine ⟨partition_not_stable, by norm_num, {ω | Good ω}, measurable_good,
    training_good_probability_ge, ?_⟩
  exact fun ω hω => microscopic_two_step_risk_on_good ω hω

end HiddenBitModel

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskWitness
