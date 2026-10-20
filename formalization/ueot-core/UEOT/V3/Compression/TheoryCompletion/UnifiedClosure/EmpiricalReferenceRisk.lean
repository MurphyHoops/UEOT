import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StatisticalRiskCalibration
import UEOT.V3.FiniteAlphabetSampling
import UEOT.V3.TransportDefect

/-!
# A data-built reference model for actual finite-time risk

The reference rows are normalized empirical PMFs formed from the observed
samples, rather than unknown true rows at chosen representatives. The fixed
test family contains all finite events of the microscopic alphabet. One
simultaneous calibration event therefore controls the true-to-empirical TV
error for every row, before any coarse map, prototype or policy is selected.

Measurable data processing and the empirically checked coarse row mismatch
give the budget `min 1 (rho + eta)`. Only one statistical error appears:
the reference row itself is empirical. The price of the fixed all-event
library is its explicit cardinality `2 ^ card X` in the confidence budget.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

noncomputable section

open MeasureTheory ProbabilityTheory
open UEOT.V3.BoundedLossSampling
open UEOT.V3.FiniteAlphabetSampling UEOT.V3.FiniteAlphabetConcentration
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.PathError UEOT.V3.TotalVariation
open scoped BigOperators Classical

universe u uΩ

/-- The observed sample multiset defines an actual normalized probability
row, including repeated observations. -/
def empiricalResponsePMF {X : Type u} {Ω : Type uΩ} {N : ℕ} (hN : 0 < N)
    (sample : Fin N → Ω → X) (ω : Ω) : PMF X := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  exact (PMF.uniformOfFintype (Fin N)).map (fun k => sample k ω)

/-- The empirical PMF is the same empirical measure already used by P-STAT-01. -/
theorem empiricalResponsePMF_toMeasure
    {X : Type u} {Ω : Type uΩ} [MeasurableSpace X] [MeasurableSingletonClass X]
    {N : ℕ} (hN : 0 < N) (sample : Fin N → Ω → X) (ω : Ω) :
    (empiricalResponsePMF hN sample ω).toMeasure = empiricalMeasure hN sample ω := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  letI : MeasurableSpace (Fin N) := ⊤
  unfold empiricalResponsePMF empiricalMeasure
  exact (PMF.toMeasure_map _ _ (measurable_of_finite _)).symm

/-- Event mass is literally the empirical mean of the corresponding fixed test. -/
theorem empiricalResponsePMF_event_mean
    {X : Type u} {Ω : Type uΩ} [MeasurableSpace X] [MeasurableSingletonClass X]
    {N : ℕ} (hN : 0 < N) (sample : Fin N → Ω → X) (ω : Ω) (s : Finset X) :
    (empiricalResponsePMF hN sample ω).toMeasure.real (s : Set X) =
      empiricalRisk (eventIndicator s) sample ω := by
  letI : MeasurableSpace Ω := ⊤
  rw [empiricalResponsePMF_toMeasure]
  simpa [empiricalRisk, sampleIndicator, Function.comp_def] using
    empiricalMeasure_real_finset hN sample ω s

/-- The population mean of an event test is the source event probability. -/
theorem pmf_event_test_mean
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF X) (s : Finset X) :
    trueRisk p.toMeasure (eventIndicator s) = p.toMeasure.real (s : Set X) := by
  exact integral_indicator_one s.measurableSet

/-- Calibrating the fixed full event library controls the empirical source
row in canonical TV; no selected quotient event needs a new confidence charge. -/
theorem calibrated_full_event_row_tv
    {Ω : Type uΩ} {X A R O : Type u} [Fintype X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {N : ℕ} (hN : 0 < N)
    (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
    (sample : ℕ → A → X → Fin N → Ω → X) (rho : ℕ → ℝ) (T : ℕ)
    (ω : Ω)
    (hcal : EmpiricalTransitionCalibrated M (fun _ => eventIndicator) sample rho T ω)
    (n : ℕ) (hn : n < T) (a : A) (x : X) :
    tvDist (finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a).toMeasure
      (empiricalResponsePMF hN (sample n a x) ω).toMeasure ≤ rho n := by
  apply tvDist_le_of_finset_event_le
  intro s
  have hmean := finiteKernelRowPMF_trueRisk (M n) (eventIndicator s) a x
  rw [pmf_event_test_mean] at hmean
  rw [hmean, empiricalResponsePMF_event_mean]
  exact hcal n hn a x s

/-- Contraction and an empirical fit bound produce a true-to-learned coarse
row bound. The learned row is already a PMF, so the unit cap is justified. -/
theorem empirical_coarse_row_tv
    {X Y : Type u} [MeasurableSpace X] [MeasurableSpace Y]
    (p phat : PMF X) (q : X → Y) (hq : Measurable q) (reference : PMF Y)
    (rho eta : ℝ)
    (hcal : tvDist p.toMeasure phat.toMeasure ≤ rho)
    (hfit : tvDist (phat.map q).toMeasure reference.toMeasure ≤ eta) :
    tvDist (p.map q).toMeasure reference.toMeasure ≤ min 1 (rho + eta) := by
  apply le_min (tvDist_le_one _ _)
  have hmap := tvDist_map_le p.toMeasure phat.toMeasure q hq
  rw [PMF.toMeasure_map q p hq, PMF.toMeasure_map q phat hq] at hmap
  exact (UEOT.V3.TransportDefect.tvDist_triangle
    (p.map q).toMeasure (phat.map q).toMeasure reference.toMeasure).trans
      (add_le_add (hmap.trans hcal) hfit)

section LearnedReference

variable {Ω : Type uΩ} {X Y A R O : Type u}
variable [Fintype X] [Fintype Y] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace Y] [MeasurableSingletonClass Y]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable {N : ℕ} (hN : 0 < N)
variable (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
variable (sample : ℕ → A → X → Fin N → Ω → X) (ω : Ω)
variable (q : X → Y) (r : Y → X) (p₀ : PMF X)
variable (policy : ∀ n, CausalHistory Y (A × Y) n → PMF A)
variable (rho eta : ℕ → ℝ) (T : ℕ)

local notation "microRows" => (fun n x a => finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a)
local notation "observedRows" => (fun n x a => empiricalResponsePMF hN (sample n a x) ω)
local notation "learnedRows" => (riskRepresentativeKernel q r observedRows)
local notation "rowError" => (fun n => min 1 (rho n + eta n))

/-- The comparison process uses only the observed PMF rows and selected
coarse map/prototypes. Every clause concerns the actual source path law. -/
def EmpiricalReferenceRiskConclusion : Prop :=
  let actual := causalLaw p₀ (riskMicroControlKernel q microRows policy) T
  let projection := riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) T
  let reference := causalLaw (p₀.map q) (riskMacroControlKernel learnedRows policy) T
  let accumulated := 1 - (∏ n ∈ Finset.range T, (1 - rowError n))
  tvDist (actual.map projection).toMeasure reference.toMeasure ≤ accumulated ∧
    accumulated ≤ ∑ n ∈ Finset.range T, rowError n ∧
    ∀ E F, E ⊆ projection ⁻¹' F →
      actual.toMeasure.real E ≤ min 1 (reference.toMeasure.real F + accumulated)

/-- The empirical fit check is made against the learned PMF itself. There
is no assumed true representative kernel in this conclusion. -/
theorem empirical_reference_risk_of_calibrated
    (hcal : EmpiricalTransitionCalibrated M (fun _ => eventIndicator) sample rho T ω)
    (hrho : ∀ n, n < T → 0 ≤ rho n) (heta : ∀ n, n < T → 0 ≤ eta n)
    (hfit : ∀ n, n < T → ∀ x a,
      tvDist ((observedRows n x a).map q).toMeasure
        (learnedRows n (q x) a).toMeasure ≤ eta n) :
    EmpiricalReferenceRiskConclusion hN M sample ω q r p₀ policy rho eta T := by
  have hrows : ∀ n, n < T → ∀ x a,
      tvDist ((microRows n x a).map q).toMeasure
        (learnedRows n (q x) a).toMeasure ≤ rowError n := by
    intro n hn x a
    exact empirical_coarse_row_tv _ _ q (measurable_of_countable _) _ _ _
      (calibrated_full_event_row_tv hN M sample rho T ω hcal n hn a x)
      (hfit n hn x a)
  have h0 : ∀ n, n < T → 0 ≤ rowError n := by
    intro n hn
    exact le_min zero_le_one (add_nonneg (hrho n hn) (heta n hn))
  have h1 : ∀ n, n < T → rowError n ≤ 1 := fun _ _ => min_le_left _ _
  have hpath := same_policy_projected_path_error p₀ q microRows learnedRows policy
    rowError T h0 h1 hrows
  refine ⟨hpath.1, hpath.2, ?_⟩
  intro E F hEF
  exact same_policy_microscopic_failure_risk p₀ q microRows learnedRows policy
    rowError T h0 h1 hrows E F hEF

end LearnedReference

section StatisticalClosure

variable {Ω : Type uΩ} {X A R O : Type u}
variable [Fintype X] [Fintype A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable {N : ℕ} (hN : 0 < N)
variable (M : ℕ → UEOT.V3.FiniteStablePartition.Model X A R O)
variable (sample : ℕ → A → X → Fin N → Ω → X) (rho : ℕ → ℝ) (T : ℕ)

/-- A single fixed microscopic event library covers all subsequent finite
coarse maps, prototypes and common policies passing the empirical fit check.
Prototypes need not form a section for this estimate: the fit is checked
directly against their actual empirical row. -/
def UniformEmpiricalReferenceRisk (ω : Ω) : Prop :=
  ∀ (Y : Type u) [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (q : X → Y) (r : Y → X) (p₀ : PMF X)
    (policy : ∀ n, CausalHistory Y (A × Y) n → PMF A) (eta : ℕ → ℝ),
    (∀ n, n < T → 0 ≤ eta n) →
    (∀ n, n < T → ∀ x a,
      tvDist ((empiricalResponsePMF hN (sample n a x) ω).map q).toMeasure
        ((empiricalResponsePMF hN (sample n a (r (q x))) ω).map q).toMeasure
          ≤ eta n) →
    EmpiricalReferenceRiskConclusion hN M sample ω q r p₀ policy rho eta T

variable [MeasurableSpace Ω]

/-- The data-built reference closes the finite sampling-to-microscopic-risk
chain. Its common good event is measurable independently of later selections.
The bound is a training-data confidence statement about the selected model's
deployment law; a joint training/deployment law is a separate interface. -/
theorem statistical_empirical_reference_certificate
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hmeas : ∀ n, n < T → ∀ a x k, Measurable (sample n a x k))
    (hindep : ∀ n, n < T → ∀ a x, iIndepFun (sample n a x) μ)
    (hlaw : ∀ n, n < T → ∀ a x k,
      μ.map (sample n a x k) =
        (finiteKernelRowPMF (modelAsFiniteKernel (M n)) x a).toMeasure)
    (hrho : ∀ n, n < T → 0 ≤ rho n) :
    ∃ good : Set Ω, MeasurableSet good ∧
      μ.real goodᶜ ≤ transitionCalibrationFailureBudget X A (Finset X) N T rho ∧
      ∀ ω ∈ good, UniformEmpiricalReferenceRisk hN M sample rho T ω := by
  have htest : ∀ n : ℕ, n < T → ∀ s : Finset X, Measurable (eventIndicator s) := by
    intro _ _ s
    exact measurable_const.indicator s.measurableSet
  have hbounded : ∀ n : ℕ, n < T → ∀ (s : Finset X) x,
      eventIndicator s x ∈ Set.Icc (0 : ℝ) 1 := by
    intro _ _ s x
    by_cases hx : x ∈ s <;> simp [eventIndicator, hx]
  refine ⟨{ω | EmpiricalTransitionCalibrated M (fun _ => eventIndicator) sample rho T ω},
    measurableSet_empirical_transition_calibrated M (fun _ => eventIndicator)
      sample rho T htest hmeas, ?_, ?_⟩
  · exact measure_empirical_transition_uncalibrated_le hN μ M (fun _ => eventIndicator)
      sample rho T htest hbounded hmeas hindep hlaw hrho
  · intro ω hω Y _ _ _ q r p₀ policy eta heta hfit
    exact empirical_reference_risk_of_calibrated hN M sample ω q r p₀ policy
      rho eta T hω hrho heta hfit

end StatisticalClosure

end

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
