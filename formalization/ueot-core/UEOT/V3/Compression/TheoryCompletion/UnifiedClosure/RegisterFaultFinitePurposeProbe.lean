import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultPurposeInformation
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Function.Floor
import UEOT.V3.FiniteDiscountedSelectorValue

/-!
Original commitment: actual finite probe data support checkable purpose judgments.
Existing assumptions: SAME unknown real hazard/goal/cost source, existing write actions and birth/paid-fee readouts.
Premise reduced: no exact population means or hidden parameters enter the executable selector.
Model: fixed full two-write sample budget; rational fee-bin width and evaluation price; threshold ambiguity yields UNKNOWN.
Consumer: strict one-step repair/idle order, and positive certified SAME literal controller's original causal optimum.

Fee bins are a fixed deterministic coarse read of the already permitted paid
expenditure. They add no information, source change, installation, parent reset,
retry or selected-success sampling. Every batch coordinate remains registered.
The selector below uses only Bool/Nat/Rat arithmetic and observed data.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeProbe
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl UEOT.V3.BoundedLossSampling
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterJointRecord RegisterFaultControlModel RegisterFaultJointRecord
open VariableRegisteredSamples RowwiseProbeSampling
open scoped BigOperators ENNReal

abbrev Observation := Bool × ℕ
abbrev Coordinate (N : ℕ) := SampleCoordinate (fun _ : Bool => N)
abbrev Batch (N : ℕ) := Coordinate N → Observation

def registration (N : ℕ) : List (Coordinate N) :=
  (List.finRange N).map (fun k => ⟨false,k⟩) ++ (List.finRange N).map (fun k => ⟨true,k⟩)

inductive Verdict where
  | repair (goal : Bool)
  | idle (goal : Bool)
  | unknown
  deriving DecidableEq, Repr

/-- Read the first informative birth from the COMPLETE registered batch. -/
def firstBirth {N : ℕ} (data : Batch N) : List (Coordinate N) → Option (Bool × ℕ)
  | [] => none
  | j::js => if (data j).1 then some (j.1,(data j).2) else firstBirth data js

/-- Executable three-way judgment. True parameters, population means and the
fault mode are absent from this interface. Payload bits come only from births. -/
def select {N : ℕ} (price width : ℚ) (data : Batch N) : Verdict :=
  match firstBirth data (registration N) with
  | none => .unknown
  | some (b,k) =>
    if price * ((k+1 : ℕ) : ℚ) * width < 1 then .repair b
    else if 1 < price * (k : ℚ) * width then .idle b
    else .unknown

noncomputable section

/-- Fixed coarse measurement of an existing real paid fee. This source-law
map is outside the executable selector; the selector receives its integer readout. -/
def feeBin (width : ℚ) (fee : ℝ) : ℕ := ⌊fee / (width : ℝ)⌋₊

@[fun_prop] theorem measurable_feeBin (width : ℚ) : Measurable (feeBin width) :=
  Nat.measurable_floor.comp (measurable_id.div_const _)

def recordObservation {n : ℕ} (width : ℚ) (r : ModeRecord n) : Observation :=
  (r.transaction.child.isSome,feeBin width r.transaction.expenditure)

def feature (m : Mechanism) (width : ℚ) (bit : Bool) (z : Bool × Bool) : Observation :=
  (z.1 && decide (bit = m.goal),if z.1 then feeBin width m.writeCost else 0)

/-- The actual source record erases to exactly the declared restricted probe
observation at EVERY retained parent carrying the SAME inherited program. -/
theorem recordObservation_eq {n : ℕ} (i : Fin n) (m : Mechanism) (width : ℚ)
    (o : Organism n) (hp : o.program = m.goal) (bit mode label : Bool) :
    recordObservation width (modeRecordStep i m o (some bit) mode label) =
      feature m width bit (mode,label) := by
  cases mode <;> cases bit <;> cases hg : m.goal <;>
    simp [recordObservation,feature,modeRecordStep,recordStep,update,hp,hg,feeBin,cost]

/-- The fee bin is an interval certificate for the actual paid cost. -/
theorem feeBin_bounds (width : ℚ) (hw : 0 < width) (fee : ℝ) (hf : 0 ≤ fee) :
    (feeBin width fee : ℝ) * (width : ℝ) ≤ fee ∧
      fee < ((feeBin width fee : ℝ)+1) * (width : ℝ) := by
  have hwr : (0 : ℝ) < width := by exact_mod_cast hw
  constructor
  · exact (le_div_iff₀ hwr).mp (Nat.floor_le (div_nonneg hf hwr.le))
  · exact (div_lt_iff₀ hwr).mp (Nat.lt_floor_add_one (fee/(width:ℝ)))

/-- Same environmental mode and birth-label laws as the deployed source. -/
def primitiveLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) : PMF (Bool × Bool) :=
  (modeLaw epsilon he).bind (fun mode => noise.map (fun label => (mode,label)))

@[simp] theorem primitiveLaw_apply (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1)
    (mode label : Bool) :
    primitiveLaw noise epsilon he (mode,label) = modeLaw epsilon he mode * noise label := by
  cases mode <;> cases label <;>
    simp [primitiveLaw,PMF.bind_apply,PMF.map_apply,tsum_fintype]

def row (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (width : ℚ) (bit : Bool) : PMF Observation :=
  (primitiveLaw noise epsilon he).map (feature m width bit)

/-- Exactly two pre-registered write rows, N samples each, with no retry. -/
def rawLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) :
    Measure (Coordinate N → Bool × Bool) :=
  productRowLaw (fun _ : Bool => primitiveLaw noise epsilon he) (fun _ => N)

instance rawLaw_isProbability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) :
    IsProbabilityMeasure (rawLaw noise epsilon he N) := by unfold rawLaw; infer_instance

/-- Actual restricted observations, with the raw modes/labels hidden from select. -/
def sourceData {N : ℕ} (m : Mechanism) (width : ℚ) (ω : Coordinate N → Bool × Bool) : Batch N :=
  fun j => feature m width j.1 (ω j)

@[simp] theorem registration_length (N : ℕ) : (registration N).length = 2*N := by simp [registration]; omega

theorem mem_registration {N : ℕ} (j : Coordinate N) : j ∈ registration N := by
  rcases j with ⟨bit,k⟩
  cases bit <;> simp [registration]

/-- Literal retained-parent execution of the pre-registered probe schedule. -/
def probeTrace {n N : ℕ} (i : Fin n) (m : Mechanism) (ω : Coordinate N → Bool × Bool) :
    Organism n → List (Coordinate N) → List (ModeRecord n)
  | _,[] => []
  | o,j::js =>
      let r := modeRecordStep i m o (some j.1) (ω j).1 (ω j).2
      r :: probeTrace i m ω r.transaction.parentAfter js

/-- Every observed batch coordinate is an actual transaction of the SAME
retained-parent run. Program identity persists; no reset or installation occurs. -/
theorem actual_probe_trace_observations {n N : ℕ} (i : Fin n) (m : Mechanism) (width : ℚ)
    (ω : Coordinate N → Bool × Bool) (o : Organism n) (hp : o.program = m.goal)
    (js : List (Coordinate N)) :
    (probeTrace i m ω o js).map (recordObservation width) = js.map (sourceData m width ω) := by
  induction js generalizing o with
  | nil => rfl
  | cons j js ih =>
    simp only [probeTrace,List.map_cons]
    rw [recordObservation_eq i m width o hp]
    rw [ih _ ((step_program i m o _ _ _).trans hp)]
    rfl

/-- A successful birth certifies exactly its requested goal and its paid cost
bin. Zero-probability source tuples are not used to infer hazard positivity. -/
theorem informative_source {N : ℕ} (m : Mechanism) (width : ℚ)
    (ω : Coordinate N → Bool × Bool) (j : Coordinate N)
    (hb : (sourceData m width ω j).1 = true) :
    j.1 = m.goal ∧ (sourceData m width ω j).2 = feeBin width m.writeCost := by
  change ((ω j).1 && decide (j.1 = m.goal)) = true at hb
  have hm : (ω j).1 = true := by cases h : (ω j).1 <;> simp_all
  have hg : j.1 = m.goal := by simpa [hm] using hb
  exact ⟨hg,by simp [sourceData,feature,hm]⟩

private theorem firstBirth_source {N : ℕ} (m : Mechanism) (width : ℚ)
    (ω : Coordinate N → Bool × Bool) (js : List (Coordinate N)) (b : Bool) (k : ℕ)
    (h : firstBirth (sourceData m width ω) js = some (b,k)) :
    b = m.goal ∧ k = feeBin width m.writeCost := by
  induction js with
  | nil => simp [firstBirth] at h
  | cons j js ih =>
    by_cases hb : (sourceData m width ω j).1 = true
    · have he : (j.1,(sourceData m width ω j).2) = (b,k) := by simpa [firstBirth,hb] using h
      have hi := informative_source m width ω j hb
      exact ⟨(congrArg Prod.fst he).symm.trans hi.1,(congrArg Prod.snd he).symm.trans hi.2⟩
    · exact ih (by simpa [firstBirth,hb] using h)

/-- Strict positive fee certificate, using only observed integer bins. -/
theorem select_repair_sound {N : ℕ} (m : Mechanism) (price width : ℚ)
    (hp : 0 ≤ price) (hw : 0 < width) (ω : Coordinate N → Bool × Bool) (b : Bool)
    (hs : select price width (sourceData m width ω) = .repair b) :
    b = m.goal ∧ (price : ℝ) * (m.writeCost : ℝ) < 1 := by
  cases hx : firstBirth (sourceData m width ω) (registration N) with
  | none => simp [select,hx] at hs
  | some q =>
    rcases q with ⟨g,k⟩
    have hi := firstBirth_source m width ω _ g k hx
    simp only [select,hx] at hs
    split_ifs at hs with hc hn
    · have hg : g = b := Verdict.repair.inj hs
      refine ⟨hg.symm.trans hi.1,?_⟩
      have hcr : (price : ℝ) * ((k+1 : ℕ) : ℝ) * (width : ℝ) < 1 := by exact_mod_cast hc
      have hbox := (feeBin_bounds width hw m.writeCost m.writeCost.coe_nonneg).2
      rw [← hi.2] at hbox
      have hpr : (0 : ℝ) ≤ price := by exact_mod_cast hp
      have hm := mul_le_mul_of_nonneg_left hbox.le hpr
      push_cast at hcr
      nlinarith

theorem select_idle_sound {N : ℕ} (m : Mechanism) (price width : ℚ)
    (hp : 0 ≤ price) (hw : 0 < width) (ω : Coordinate N → Bool × Bool) (b : Bool)
    (hs : select price width (sourceData m width ω) = .idle b) :
    b = m.goal ∧ 1 < (price : ℝ) * (m.writeCost : ℝ) := by
  cases hx : firstBirth (sourceData m width ω) (registration N) with
  | none => simp [select,hx] at hs
  | some q =>
    rcases q with ⟨g,k⟩
    have hi := firstBirth_source m width ω _ g k hx
    simp only [select,hx] at hs
    split_ifs at hs with hc hn
    · have hg : g = b := Verdict.idle.inj hs
      refine ⟨hg.symm.trans hi.1,?_⟩
      have hnr : (1 : ℝ) < (price : ℝ) * (k : ℝ) * (width : ℝ) := by exact_mod_cast hn
      have hbox := (feeBin_bounds width hw m.writeCost m.writeCost.coe_nonneg).1
      rw [← hi.2] at hbox
      have hpr : (0 : ℝ) ≤ price := by exact_mod_cast hp
      have hm := mul_le_mul_of_nonneg_left hbox hpr
      nlinarith

def birthScore (z : Observation) : ℝ := if z.1 then 1 else 0

private theorem birthScore01 (z : Observation) : birthScore z ∈ Set.Icc (0 : ℝ) 1 := by
  rcases z with ⟨b,k⟩
  cases b <;> norm_num [birthScore]

private theorem noise_sum (noise : PMF Bool) : (noise true).toReal + (noise false).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe noise)
  rw [tsum_fintype,ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ b)] at h
  simpa using h

/-- Population birth means are derived from the SAME primitive/record source. -/
theorem birth_mean (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (width : ℚ) (bit : Bool) :
    trueRisk (row noise m epsilon he width bit).toMeasure birthScore =
      repairChance epsilon * (if bit = m.goal then 1 else 0) := by
  have hn := noise_sum noise
  unfold trueRisk row
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _),
    integral_map (measurable_of_finite _).aemeasurable (measurable_of_countable _).aestronglyMeasurable,
    PMF.integral_eq_sum,Fintype.sum_prod_type]
  simp_rw [primitiveLaw_apply,ENNReal.toReal_mul]
  by_cases hb : bit = m.goal <;>
    simp [birthScore,feature,hb,modeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal,
      modeProbability,← mul_add,hn]

/-- This also consumes the original exact-probe formula, without granting the
selector access to that mean. -/
theorem birth_mean_eq_original {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (theta : RegisterFaultPurposeInformation.Parameter) (width : ℚ) (bit : Bool) :
    trueRisk (row noise theta.mechanism theta.epsilon theta.epsilon_lt_one.le width bit).toMeasure birthScore =
      RegisterFaultPurposeInformation.probeBirthMean i noise theta bit := by
  rw [birth_mean,RegisterFaultPurposeInformation.probeBirthMean_eq]

def sourceSample {N : ℕ} (m : Mechanism) (width : ℚ) (bit : Bool) (k : Fin N)
    (ω : Coordinate N → Bool × Bool) : Observation := sourceData m width ω ⟨bit,k⟩

private theorem sourceSample_measurable {N : ℕ} (m : Mechanism) (width : ℚ) (bit : Bool) (k : Fin N) :
    Measurable (sourceSample m width bit k) :=
  (measurable_of_finite (feature m width bit)).comp (productRowSample_measurable (N:=fun _ : Bool => N) bit k)

private theorem sourceSample_independent (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (N : ℕ) (width : ℚ) (bit : Bool) :
    iIndepFun (sourceSample (N:=N) m width bit) (rawLaw noise epsilon he N) := by
  exact (productRowSample_independent (fun _ : Bool => primitiveLaw noise epsilon he) (fun _ => N) bit).comp
    (fun _ => feature m width bit) (fun _ => measurable_of_finite _)

private theorem sourceSample_law (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (N : ℕ) (width : ℚ) (bit : Bool) (k : Fin N) :
    (rawLaw noise epsilon he N).map (sourceSample m width bit k) =
      (row noise m epsilon he width bit).toMeasure := by
  change (productRowLaw (fun _ : Bool => primitiveLaw noise epsilon he) (fun _ => N)).map
    (feature m width bit ∘ productRowSample (N:=fun _ : Bool => N) bit k) = _
  have hf : Measurable (feature m width bit) := measurable_of_finite _
  rw [← Measure.map_map hf (productRowSample_measurable (N:=fun _ : Bool => N) bit k),productRowSample_law]
  exact PMF.toMeasure_map _ _ (measurable_of_finite _)


/-- The common calibration event contains only actual row empirical means and
actual source population means; it is an analysis event, not selector input. -/
def Good (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (N : ℕ) (width : ℚ) (u : ℝ) : Set (Coordinate N → Bool × Bool) :=
  coordinateGood (row noise m epsilon he width) (fun _ => birthScore) (sourceSample m width) u

theorem actual_probe_calibration (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (N : ℕ) (hN : 0 < N) (width : ℚ) (u : ℝ) (hu : 0 ≤ u) :
    MeasurableSet (Good noise m epsilon he N width u) ∧
      (rawLaw noise epsilon he N).real (Good noise m epsilon he N width u)ᶜ ≤
        min 1 (4 * Real.exp (-2 * (N : ℝ) * u^2)) := by
  refine ⟨coordinateGood_measurable _ _ _ _ (fun _ => measurable_of_countable _)
    (sourceSample_measurable m width),?_⟩
  have h := measure_coordinateGood_compl_le (fun _ : Bool => N) (fun _ => hN)
    (rawLaw noise epsilon he N) (row noise m epsilon he width) (fun _ => birthScore)
    (sourceSample m width) (fun _ => measurable_of_countable _) (fun _ => birthScore01)
    (sourceSample_measurable m width) (sourceSample_independent noise m epsilon he N width)
    (sourceSample_law noise m epsilon he N width) u hu
  have hbudget : scalarBudget (fun _ : Bool => N) u = 4 * Real.exp (-2 * (N : ℝ) * u^2) := by
    simp [scalarBudget]
    ring
  simpa only [Good,hbudget] using h

private theorem firstBirth_none_iff {N : ℕ} (data : Batch N) (js : List (Coordinate N)) :
    firstBirth data js = none ↔ ∀ j ∈ js, (data j).1 = false := by
  induction js with
  | nil => simp [firstBirth]
  | cons j js ih =>
    cases hb : (data j).1 <;> simp [firstBirth,hb,ih]

/-- True source separation from the fixed measurement bin. The selector itself
checks only the bin it actually observed, never this hidden-source condition. -/
def Separated (m : Mechanism) (price width : ℚ) : Prop :=
  price * ((feeBin width m.writeCost + 1 : ℕ) : ℚ) * width < 1 ∨
    1 < price * (feeBin width m.writeCost : ℚ) * width

private theorem unknown_noBirth {N : ℕ} (m : Mechanism) (price width : ℚ)
    (hsep : Separated m price width) (ω : Coordinate N → Bool × Bool)
    (hs : select price width (sourceData m width ω) = .unknown) :
    firstBirth (sourceData m width ω) (registration N) = none := by
  cases hx : firstBirth (sourceData m width ω) (registration N) with
  | none => rfl
  | some q =>
    rcases q with ⟨g,k⟩
    have hi := firstBirth_source m width ω _ g k hx
    rcases hsep with hc | hn
    · push_cast at hc
      simp [select,hx,hi.2,hc] at hs
    · by_cases hc : price * ((feeBin width m.writeCost : ℚ) + 1) * width < 1 <;>
        simp [select,hx,hi.2,hc,hn] at hs

/-- UNKNOWN outside the near-threshold source strip can occur only on the
registered calibration failure event, when u is smaller than the true repair
chance. No such lower bound is silently supplied to the selector. -/
theorem unknown_subset_bad (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (N : ℕ) (width price : ℚ) (u : ℝ)
    (hsep : Separated m price width) (hr : u < repairChance epsilon) :
    {ω | select price width (sourceData m width ω) = .unknown} ⊆ (Good noise m epsilon he N width u)ᶜ := by
  intro ω hs hg
  have hn := (firstBirth_none_iff _ _).mp (unknown_noBirth m price width hsep ω hs)
  have hsamp (k : Fin N) : birthScore (sourceSample m width m.goal k ω) = 0 := by
    have hb := hn (⟨m.goal,k⟩ : Coordinate N) (mem_registration _)
    simp [sourceSample,birthScore,hb]
  have hemp : empiricalRisk birthScore (sourceSample (N:=N) m width m.goal) ω = 0 := by
    simp [empiricalRisk,hsamp]
  have hb := hg m.goal
  change |empiricalRisk birthScore (sourceSample m width m.goal) ω -
    trueRisk (row noise m epsilon he width m.goal).toMeasure birthScore| ≤ u at hb
  rw [hemp,birth_mean,if_pos rfl,mul_one,zero_sub,abs_neg] at hb
  exact (hr.trans_le (le_abs_self _)).not_ge hb

theorem unknown_probability_le (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (N : ℕ) (hN : 0 < N) (width price : ℚ) (u : ℝ) (hu : 0 ≤ u)
    (hsep : Separated m price width) (hr : u < repairChance epsilon) :
    (rawLaw noise epsilon he N).real {ω | select price width (sourceData m width ω) = .unknown} ≤
      min 1 (4 * Real.exp (-2 * (N : ℝ) * u^2)) :=
  (measureReal_mono (unknown_subset_bad noise m epsilon he N width price u hsep hr)).trans
    (actual_probe_calibration noise m epsilon he N hN width u hu).2

/-- Fixed registered rational evaluation price, embedded in the original model. -/
def priceValue (price : ℚ) (hp : 0 ≤ price) : NNReal := ⟨(price : ℝ),by exact_mod_cast hp⟩

/-- Output only an existing allowed-action controller. This does not install
or modify the organism's inherited program. UNKNOWN returns the allowed idle controller. -/
def returnedSelector {n : ℕ} (i : Fin n) : Verdict → State n → Action
  | .repair b => (substrate i).execute b
  | .idle _ => fun _ => none
  | .unknown => fun _ => none

def returnedPolicy {n : ℕ} (i : Fin n) (v : Verdict) : CausalPolicy.{0,0,0} (State n) (fun _ => Action) :=
  selectorPolicy (returnedSelector i v)

/-- The SAME data-returned literal controller consumes the existing all-causal
optimality theorem. No real epsilon lower bound is needed for this positive
weak-optimality claim; total fault also has its original zero objective. -/
theorem returned_positive_optimal {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (ω : Coordinate N → Bool × Bool) (b : Bool)
    (hs : select price width (sourceData m width ω) = .repair b) :
    let M := model i noise m (priceValue price hp) epsilon he d hd
    (∀ x : State n, (returnedPolicy i (select price width (sourceData m width ω))).infiniteValue M (t:=0) x =
      M.optimalValue x) ∧
    (∀ (pi : CausalPolicy (State n) (fun _ => Action)) {t : ℕ} (h : pi.Memory t),
      pi.infiniteValue M h ≤ M.optimalValue (pi.current h)) := by
  have hc := select_repair_sound m price width hp hw ω b hs
  rw [hs]
  simp only [returnedPolicy,returnedSelector]
  rw [hc.1]
  have ho := compiled_optimal_against_all_causal i noise m (priceValue price hp) epsilon he d hd hc.2.le
  exact ⟨fun x => ho.1 (t:=0) x,ho.2⟩

section RecordConsumer
variable {n : ℕ}
local instance : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _ => trivial⟩

/-- Actual complete-record payoff limit of that SAME selected controller at an
arbitrary retained parent. No physical reset or code installation is assumed. -/
theorem returned_positive_actual_record_limit {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (ω : Coordinate N → Bool × Bool) (b : Bool)
    (hs : select price width (sourceData m width ω) = .repair b)
    (o : Organism n) (ho : o.program = m.goal) :
    let sigma := returnedPolicy i (select price width (sourceData m width ω))
    let M := model i noise m (priceValue price hp) epsilon he d hd
    Filter.Tendsto (fun T => ∫ rs, RegisterFaultJointRecord.discountedPayoff (priceValue price hp) d rs ∂
      (RegisterFaultJointRecord.recordLaw i noise m epsilon he sigma T (t:=0) o.physical o).toMeasure)
      Filter.atTop (nhds (M.optimalValue o.physical)) := by
  have hc := select_repair_sound m price width hp hw ω b hs
  rw [hs]
  simp only [returnedPolicy,returnedSelector]
  rw [hc.1]
  exact compiled_record_integral_tendsto_optimal i noise m epsilon he (priceValue price hp) d hd hc.2.le o ho

end RecordConsumer

/-- Exact one-step source gap, including the good-state equality boundary. -/
theorem one_step_repair_idle_gap {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1) (x : State n) :
    (selectorPolicy ((substrate i).execute m.goal)).truncatedValue (model i noise m price epsilon he d hd) 1 (t:=0) x -
      (selectorPolicy (fun _ : State n => none)).truncatedValue (model i noise m price epsilon he d hd) 1 (t:=0) x =
      repairChance epsilon * (if x i = m.goal then 0 else 1 - (price : ℝ) * m.writeCost) := by
  rw [selector_truncatedValue_succ,selector_truncatedValue_succ]
  change (expectedModePayoff i noise m price epsilon he x ((substrate i).execute m.goal x) +
      d * (∑ y, (model i noise m price epsilon he d hd).transition x ((substrate i).execute m.goal x) y * (0 : ℝ))) -
    (expectedModePayoff i noise m price epsilon he x none +
      d * (∑ y, (model i noise m price epsilon he d hd).transition x none y * (0 : ℝ))) = _
  simp only [mul_zero,Finset.sum_const_zero,add_zero]
  rw [expectedModePayoff_eq,expectedModePayoff_eq,stage,stage,expectedChildren_eq,expectedChildren_eq,execute_compiled]
  by_cases hx : x i = m.goal <;> simp [hx,update,cost]

/-- A negative certificate is strictly one-step: at a bad actual state idle
beats repair. It is NOT an assertion of infinite-horizon idle optimality. -/
theorem returned_negative_one_step {n N : ℕ} (i : Fin n) (noise : PMF Bool)
    (theta : RegisterFaultPurposeInformation.Parameter) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (ω : Coordinate N → Bool × Bool) (b : Bool)
    (hs : select price width (sourceData theta.mechanism width ω) = .idle b)
    (x : State n) (hx : x i ≠ theta.mechanism.goal) :
    let M := model i noise theta.mechanism (priceValue price hp) theta.epsilon theta.epsilon_lt_one.le d hd
    (selectorPolicy ((substrate i).execute b)).truncatedValue M 1 (t:=0) x <
      (returnedPolicy i (select price width (sourceData theta.mechanism width ω))).truncatedValue M 1 (t:=0) x := by
  have hc := select_idle_sound theta.mechanism price width hp hw ω b hs
  rw [hs]
  simp only [returnedPolicy,returnedSelector]
  rw [hc.1]
  have hg := one_step_repair_idle_gap i noise theta.mechanism (priceValue price hp)
    theta.epsilon theta.epsilon_lt_one.le d hd x
  rw [if_neg hx] at hg
  have hr := RegisterFaultPurposeInformation.repairChance_pos theta
  have hn : repairChance theta.epsilon * (1 - (priceValue price hp : ℝ) * theta.mechanism.writeCost) < 0 :=
    mul_neg_of_pos_of_neg hr (sub_neg.mpr hc.2)
  linarith

/-- Original actual-record purpose objective, consuming exactly the same
negative returned policy; the strict claim retains explicit non-total fault. -/
theorem returned_negative_actual_objective {n N : ℕ} (i : Fin n) (noise : PMF Bool)
    (theta : RegisterFaultPurposeInformation.Parameter) (history : List Bool)
    (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (ω : Coordinate N → Bool × Bool) (b : Bool)
    (hs : select price width (sourceData theta.mechanism width ω) = .idle b)
    (x : State n) (hx : x i ≠ theta.mechanism.goal) :
    RegisterFaultPurposeInformation.objective i noise history (priceValue price hp) d 1 theta
      ⟨selectorPolicy ((substrate i).execute b),x⟩ <
    RegisterFaultPurposeInformation.objective i noise history (priceValue price hp) d 1 theta
      ⟨returnedPolicy i (select price width (sourceData theta.mechanism width ω)),x⟩ := by
  rw [RegisterFaultPurposeInformation.objective_eq_actual_policy_value i noise history _ d hd,
    RegisterFaultPurposeInformation.objective_eq_actual_policy_value i noise history _ d hd]
  exact returned_negative_one_step i noise theta price width hp hw d hd ω b hs x hx

/-- Zero source-certificate error: strict fee/goal claims are never inferred
from false population-mean estimates or floating-point comparisons. -/
def Error {N : ℕ} (m : Mechanism) (price width : ℚ) : Set (Coordinate N → Bool × Bool) :=
  {ω | match select price width (sourceData m width ω) with
    | .repair b => b ≠ m.goal ∨ 1 ≤ (price : ℝ) * m.writeCost
    | .idle b => b ≠ m.goal ∨ (price : ℝ) * m.writeCost ≤ 1
    | .unknown => False}

theorem error_empty {N : ℕ} (m : Mechanism) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width) :
    Error (N:=N) m price width = ∅ := by
  ext ω
  cases hs : select price width (sourceData m width ω) with
  | unknown => simp [Error,hs]
  | repair b =>
    have h := select_repair_sound m price width hp hw ω b hs
    simp [Error,hs,h.1,h.2.not_ge]
  | idle b =>
    have h := select_idle_sound m price width hp hw ω b hs
    simp [Error,hs,h.1,h.2.not_ge]

theorem error_probability_zero (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (N : ℕ) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width) :
    (rawLaw noise epsilon he N).real (Error m price width) = 0 := by rw [error_empty m price width hp hw]; simp

/-- If a genuine birth was observed but the bin cannot order repair and idle,
the true priced cost lies within one registered bin-width of the threshold. -/
theorem informative_unknown_gap {N : ℕ} (m : Mechanism) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width)
    (ω : Coordinate N → Bool × Bool) (b : Bool) (k : ℕ)
    (hx : firstBirth (sourceData m width ω) (registration N) = some (b,k))
    (hs : select price width (sourceData m width ω) = .unknown) :
    |(price : ℝ) * (m.writeCost : ℝ) - 1| ≤ (price : ℝ) * (width : ℝ) := by
  have hi := firstBirth_source m width ω _ b k hx
  simp only [select,hx] at hs
  split_ifs at hs with hc hn
  have hlo : price * (k : ℚ) * width ≤ 1 := le_of_not_gt hn
  have hhi : 1 ≤ price * ((k+1 : ℕ) : ℚ) * width := le_of_not_gt hc
  have hlr : (price : ℝ) * (k : ℝ) * (width : ℝ) ≤ 1 := by exact_mod_cast hlo
  have hhr : (1 : ℝ) ≤ (price : ℝ) * ((k+1 : ℕ) : ℝ) * (width : ℝ) := by exact_mod_cast hhi
  have hb := feeBin_bounds width hw m.writeCost m.writeCost.coe_nonneg
  rw [← hi.2] at hb
  have hpr : (0 : ℝ) ≤ price := by exact_mod_cast hp
  have hlow := mul_le_mul_of_nonneg_left hb.1 hpr
  have hhigh := mul_le_mul_of_nonneg_left hb.2.le hpr
  push_cast at hhr
  rw [abs_le]
  constructor <;> nlinarith

@[simp] theorem empty_budget_unknown (m : Mechanism) (price width : ℚ) (ω : Coordinate 0 → Bool × Bool) :
    select price width (sourceData m width ω) = .unknown := by simp [select,registration,firstBirth]

private theorem total_fault_mode_ae (noise : PMF Bool) :
    ∀ᵐ z ∂(primitiveLaw noise 1 (by norm_num)).toMeasure, z.1 = false := by
  rw [ae_iff,PMF.toMeasure_apply_eq_zero_iff _ (Set.toFinite _).measurableSet]
  apply Set.disjoint_left.mpr
  rintro ⟨mode,label⟩ hz hn
  change primitiveLaw noise 1 (by norm_num) (mode,label) ≠ 0 at hz
  cases mode with
  | false => exact hn rfl
  | true => simp [primitiveLaw_apply,modeLaw,FiniteProbabilityRow.ofRealRow,modeProbability,repairChance] at hz

/-- Total environmental fault is retained as a probability-one boundary.
Unsupported raw tuples may contain repairs; no pointwise positivity inference
is made from those zero-mass tuples. -/
theorem total_fault_unknown_ae (noise : PMF Bool) (m : Mechanism) (N : ℕ) (price width : ℚ) :
    ∀ᵐ ω ∂rawLaw noise 1 (by norm_num) N, select price width (sourceData m width ω) = .unknown := by
  have hcoord (j : Coordinate N) : ∀ᵐ ω ∂rawLaw noise 1 (by norm_num) N, (ω j).1 = false := by
    have hrow : ∀ᵐ z ∂(rawLaw noise 1 (by norm_num) N).map
        (productRowSample (N:=fun _ : Bool => N) j.1 j.2), z.1 = false := by
      rw [show (rawLaw noise 1 (by norm_num) N).map (productRowSample j.1 j.2) =
        (primitiveLaw noise 1 (by norm_num)).toMeasure from productRowSample_law _ _ _ _]
      exact total_fault_mode_ae noise
    exact ae_of_ae_map (productRowSample_measurable (N:=fun _ : Bool => N) j.1 j.2).aemeasurable hrow
  have hall : ∀ᵐ ω ∂rawLaw noise 1 (by norm_num) N, ∀ j, (ω j).1 = false := ae_all_iff.mpr hcoord
  filter_upwards [hall] with ω hω
  have hn : firstBirth (sourceData m width ω) (registration N) = none :=
    (firstBirth_none_iff _ _).mpr (fun j _ => by simp [sourceData,feature,hω j])
  simp [select,hn]

theorem total_fault_unknown_probability (noise : PMF Bool) (m : Mechanism) (N : ℕ) (price width : ℚ) :
    (rawLaw noise 1 (by norm_num) N).real {ω | select price width (sourceData m width ω) = .unknown} = 1 := by
  have h : (rawLaw noise 1 (by norm_num) N) {ω | select price width (sourceData m width ω) = .unknown} = 1 :=
    (mem_ae_iff_prob_eq_one (Set.toFinite _).measurableSet).mp (total_fault_unknown_ae noise m N price width)
  simp [measureReal_def,h]

def allFault (N : ℕ) : Coordinate N → Bool × Bool := fun _ => (false,false)

@[simp] theorem allFault_data (N : ℕ) (m : Mechanism) (width : ℚ) :
    sourceData m width (allFault N) = fun _ => (false,0) := by funext j; simp [sourceData,allFault,feature]

/-- The indistinguishable all-fault sample has genuine positive mass for a
fixed nonzero hazard, even though both strict source orders are different. -/
theorem allFault_mass (N : ℕ) :
    rawLaw (PMF.pure false) (1/2) (by norm_num) N {allFault N} = (1/2 : ℝ≥0∞)^(2*N) := by
  rw [rawLaw,productRowLaw,Measure.pi_singleton]
  simp [allFault,primitiveLaw_apply,modeLaw,
    FiniteProbabilityRow.ofRealRow,modeProbability,SampleCoordinate,Fintype.card_sigma,two_mul]

private theorem ae_at_atom {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (x : Ω)
    (hx : 0 < μ {x}) {P : Ω → Prop} (h : ∀ᵐ y ∂μ, P y) : P x := by
  by_contra hn
  have hle : μ {x} ≤ μ {y | ¬P y} := measure_mono (by intro y hy; rcases Set.mem_singleton_iff.mp hy with rfl; exact hn)
  rw [ae_iff.mp h] at hle
  exact (ne_of_gt hx) (le_antisymm hle bot_le)

/-- Precise deterministic-data-only no-complete-exact-ranking statement.
At price one, goal true, hazard 1/2, costs 0 and 2 have opposite one-step
orders at the SAME bad state. A procedure cannot be a.e. strictly correct and
always decisive for both. No randomized-decision extension is claimed here. -/
theorem no_complete_zero_error (N : ℕ) (width : ℚ) (D : Batch N → Verdict)
    (hcheap : ∀ᵐ ω ∂rawLaw (PMF.pure false) (1/2) (by norm_num) N,
      D (sourceData ⟨true,0⟩ width ω) = .repair true)
    (hdear : ∀ᵐ ω ∂rawLaw (PMF.pure false) (1/2) (by norm_num) N,
      D (sourceData ⟨true,2⟩ width ω) = .idle true) : False := by
  have hp : 0 < rawLaw (PMF.pure false) (1/2) (by norm_num) N {allFault N} := by rw [allFault_mass]; exact ENNReal.pow_pos (by norm_num) _
  have hc := ae_at_atom _ (allFault N) hp hcheap
  have hd := ae_at_atom _ (allFault N) hp hdear
  rw [allFault_data] at hc hd
  exact Verdict.noConfusion (hc.symm.trans hd)

/-- Fixed coarse readout can itself make two different costs indistinguishable;
this is a readout-relative boundary, not a claim about the original exact-fee probe. -/
theorem same_goal_feeBin_data {N : ℕ} (m k : Mechanism) (width : ℚ)
    (hg : m.goal = k.goal) (hc : feeBin width m.writeCost = feeBin width k.writeCost)
    (ω : Coordinate N → Bool × Bool) : sourceData m width ω = sourceData k width ω := by
  funext j
  simp only [sourceData,feature,hg,hc]

/-- A real opposite-order pair within one registered width-two fee bin. -/
theorem coarse_cost_alias {N : ℕ} (ω : Coordinate N → Bool × Bool) :
    sourceData ⟨true,1/2⟩ 2 ω = sourceData ⟨true,3/2⟩ 2 ω ∧
      ((1/2 : NNReal) : ℝ) < 1 ∧ 1 < ((3/2 : NNReal) : ℝ) := by
  refine ⟨same_goal_feeBin_data (⟨true,1/2⟩ : Mechanism) ⟨true,3/2⟩ 2 rfl ?_ ω,by norm_num,by norm_num⟩
  norm_num [feeBin]

/-- The positive-mass no-completeness pair has opposite actual one-step
repair/idle values under price one, goal true and the SAME bad physical state. -/
theorem no_complete_pair_actual_orders (noise : PMF Bool) :
    let gap := fun m : Mechanism =>
      (selectorPolicy ((substrate (0 : Fin 1)).execute m.goal)).truncatedValue
        (model 0 noise m 1 (1/2) (by norm_num) (1/2) (by norm_num)) 1 (t:=0) (fun _ => false) -
      (selectorPolicy (fun _ : State 1 => none)).truncatedValue
        (model 0 noise m 1 (1/2) (by norm_num) (1/2) (by norm_num)) 1 (t:=0) (fun _ => false)
    gap ⟨true,0⟩ = 1/2 ∧ gap ⟨true,2⟩ = -(1/2) := by
  dsimp only
  constructor
  · have h := one_step_repair_idle_gap (0 : Fin 1) noise (⟨true,0⟩ : Mechanism)
      1 (1/2) (by norm_num) (1/2) (by norm_num) (fun _ => false)
    exact h.trans (by norm_num [repairChance])
  · have h := one_step_repair_idle_gap (0 : Fin 1) noise (⟨true,2⟩ : Mechanism)
      1 (1/2) (by norm_num) (1/2) (by norm_num) (fun _ => false)
    exact h.trans (by norm_num [repairChance])

private theorem quarter_le_one : (1/4 : NNReal) ≤ 1 := by
  exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)

/-- A registered finite positive-source regime has a nonvacuous UNKNOWN bound.
This is a theorem about a fixed full budget, not a newly drawn real batch. -/
theorem finite_positive_budget (noise : PMF Bool) :
    (rawLaw noise (1/4) quarter_le_one 64).real
      {ω | select (1/2) (1/4) (sourceData ⟨true,1⟩ (1/4) ω) = .unknown} < 1 := by
  have hb := unknown_probability_le noise (⟨true,1⟩ : Mechanism) (1/4) quarter_le_one
    64 (by norm_num) (1/4) (1/2) (1/4) (by norm_num)
    (by norm_num [Separated,feeBin]) (by norm_num [repairChance])
  have hb' : (rawLaw noise (1/4) quarter_le_one 64).real
      {ω | select (1/2) (1/4) (sourceData ⟨true,1⟩ (1/4) ω) = .unknown} ≤
      min 1 (4 * Real.exp (-8)) := by
    convert hb using 1
    norm_num
  have he : 4 * Real.exp (-8) < 1 := by
    have hpos := Real.exp_pos (8 : ℝ)
    have hlo := Real.add_one_le_exp (8 : ℝ)
    rw [Real.exp_neg,← div_eq_mul_inv]
    exact (div_lt_one hpos).mpr (by linarith)
  exact (hb'.trans (min_le_right _ _)).trans_lt he

/-- Compiled policy evaluation is valid without the sufficient optimality
condition λc≤1. This is its OWN value, not a claim that it is optimal. -/
theorem compiled_own_value {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1) (x : State n) :
    (selectorPolicy ((substrate i).execute m.goal)).infiniteValue
      (model i noise m price epsilon he d hd) (t:=0) x = value i m price epsilon d x := by
  rw [selector_infiniteValue_eq_selectorValue]
  have hv : (model i noise m price epsilon he d hd).selectorBellman ((substrate i).execute m.goal)
      (value i m price epsilon d) = value i m price epsilon d := by
    funext y
    exact compiled_attains_value i noise m price epsilon he d hd y
  exact (congrFun ((model i noise m price epsilon he d hd).selectorValue_unique _ hv) x).symm

private theorem idle_bad_truncated_zero {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (x : State n) (hx : x i ≠ m.goal) :
    ∀ T, (selectorPolicy (fun _ : State n => none)).truncatedValue
      (model i noise m price epsilon he d hd) T (t:=0) x = 0 := by
  have hi : (!m.goal) = x i := by cases hg : m.goal <;> cases hxi : x i <;> simp_all
  have hf : Function.update x i (!m.goal) = x := by rw [hi]; exact Function.update_eq_self i x
  intro T
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [selector_truncatedValue_succ]
    change expectedModePayoff i noise m price epsilon he x none +
      d * (model i noise m price epsilon he d hd).expect x none
        (fun y => (selectorPolicy (fun _ : State n => none)).truncatedValue
          (model i noise m price epsilon he d hd) T (t:=1) y) = 0
    rw [expectedModePayoff_eq,stage,expectedChildren_eq,model_expect_source]
    simp only [update,cost,hx,if_false,mul_zero,sub_zero,hf,zero_add]
    have ht : (selectorPolicy (fun _ : State n => none)).truncatedValue
        (model i noise m price epsilon he d hd) T (t:=1) x = 0 := by
      rw [selector_truncatedValue_eq_iterate] at ih ⊢
      exact ih
    simp [ht]

theorem idle_bad_infinite_zero {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price epsilon : NNReal) (he : epsilon ≤ 1) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (x : State n) (hx : x i ≠ m.goal) :
    (selectorPolicy (fun _ : State n => none)).infiniteValue (model i noise m price epsilon he d hd) (t:=0) x = 0 := by
  have h := CausalPolicy.truncatedValue_tendsto_infiniteValue (selectorPolicy (fun _ : State n => none))
    (model i noise m price epsilon he d hd) (t:=0) x
  simp_rw [idle_bad_truncated_zero i noise m price epsilon he d hd x hx] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Scientific scope witness: costly repair loses at one step yet has positive
own infinite value, while idle's own infinite value is zero. No c=3 compiled
optimality condition is invoked; hence a negative probe is not an infinite no-go. -/
theorem one_step_negative_not_infinite_idle_optimal (noise : PMF Bool) :
    let m : Mechanism := ⟨true,3⟩
    let M := model (0 : Fin 1) noise m (1/2) (1/4) quarter_le_one (1/2) (by norm_num)
    let x : State 1 := fun _ => false
    (selectorPolicy ((substrate 0).execute true)).truncatedValue M 1 (t:=0) x -
      (selectorPolicy (fun _ : State 1 => none)).truncatedValue M 1 (t:=0) x = -(3/8) ∧
    (selectorPolicy ((substrate 0).execute true)).infiniteValue M (t:=0) x = 3/32 ∧
    (selectorPolicy (fun _ : State 1 => none)).infiniteValue M (t:=0) x = 0 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · have h := one_step_repair_idle_gap (0 : Fin 1) noise (⟨true,3⟩ : Mechanism)
      (1/2) (1/4) quarter_le_one (1/2) (by norm_num) (fun _ => false)
    exact h.trans (by norm_num [repairChance])
  · have h := compiled_own_value (0 : Fin 1) noise (⟨true,3⟩ : Mechanism)
      (1/2) (1/4) quarter_le_one (1/2) (by norm_num) (fun _ => false)
    exact h.trans (by norm_num [value,goodValue,badValue,repairChance])
  · exact idle_bad_infinite_zero (0 : Fin 1) noise (⟨true,3⟩ : Mechanism)
      (1/2) (1/4) quarter_le_one (1/2) (by norm_num) (fun _ => false) (by decide)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeProbe
