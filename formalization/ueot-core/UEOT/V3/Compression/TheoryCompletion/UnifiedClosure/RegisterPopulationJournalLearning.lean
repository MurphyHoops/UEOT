import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationHistorySource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredSamples
import UEOT.V3.BoundedLossTwoSided
import Mathlib.Data.List.MinMax

/-!
Original commitment: P12 parent discovery must follow actual registered observations and an executable learner.
Existing premise: actual population journal supplies the parent bridge, but its Good/calibration contract is external.
Premise reduced: derive majority Good and vanishing parent risk from an actual finite noisy-read product experiment.
Models: NEW marked-journal observation permission; fixed complete N reads, hidden target, correct probability 1-eta>1/2.
Consumer: original population P12 journal discovery, plus same-law/different-parent obstruction at eta=1/2.

The executed population episode is retained unchanged. Its finite event registry
is readable; a separate sensor queries one hidden target event's observed child
ID. A latent correct bit returns that real ID, otherwise a confuser draws an
event from the declared finite episode. The confuser PMF is arbitrary, unknown,
and may differ between source hypotheses. Sensor flags/target/eta/Good are NOT
selector inputs. This is a newly registered observation channel, not information
recovered from bare physics or old A-F data. Reads do not mutate the journal;
physical sensor costs are not derived from the old controlled-write account.
None denotes an offspring failure class: parent=None here is NOT recovery of a
failed transaction's attempted dispatch actor. Empty reads use fixed fallback.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationJournalLearning
open MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.BoundedLossSampling UEOT.V3.BoundedLossTwoSided
open VariableRegisteredSamples RegisterFaultControlModel
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open scoped BigOperators ENNReal

abbrev Observation := Option ℕ
abbrev Data (N : ℕ) := SampleCoordinate (fun _ : Unit => N) → Observation

local instance : MeasurableSpace Observation := ⊤
local instance : MeasurableSingletonClass Observation := ⟨fun _ => trivial⟩

/-- Actual computable counts over ALL pre-registered readouts. -/
def score {N : ℕ} (data : Data N) (id : Observation) : ℕ :=
  (Finset.univ.filter (fun k : Fin N => data ⟨(),k⟩ = id)).card

/-- Finite ordered argmax, with a registered zero-budget fallback. Duplicate
registry IDs, including None, are compared as observation CLASSES. -/
def select {J : Type*} {N : ℕ} (registry : List J) (key : J → Observation) (fallback : J) (data : Data N) : J :=
  if N = 0 then fallback else (registry.argmax (fun j => score data (key j))).getD fallback

@[simp] theorem select_zero {J : Type*} (registry : List J) (key : J → Observation)
    (fallback : J) (data : Data 0) : select registry key fallback data = fallback := rfl

private theorem score_disjoint_sum_le {N : ℕ} (data : Data N) (a b : Observation) (hne : a ≠ b) :
    score data a + score data b ≤ N := by
  have hd : Disjoint (Finset.univ.filter (fun k : Fin N => data ⟨(),k⟩ = a))
      (Finset.univ.filter (fun k : Fin N => data ⟨(),k⟩ = b)) := by
    apply Finset.disjoint_left.mpr
    intro k ha hb
    exact hne ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  rw [score,score,← Finset.card_union_of_disjoint hd]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

/-- A strict majority identifies the actual ID class, not an arbitrary choice
of event within a duplicated class. No injectivity hypothesis on key is used. -/
theorem select_eq_class {J : Type*} {N : ℕ} (registry : List J) (key : J → Observation)
    (fallback truth : J) (ht : truth ∈ registry) (data : Data N)
    (hmajority : N < 2 * score data (key truth)) :
    key (select registry key fallback data) = key truth := by
  have hN : N ≠ 0 := by
    intro hz
    subst N
    simp [score] at hmajority
  unfold select
  rw [if_neg hN]
  cases harg : registry.argmax (fun j => score data (key j)) with
  | none =>
    have hnil := (List.argmax_eq_none.mp harg)
    simp [hnil] at ht
  | some chosen =>
    simp only [Option.getD_some]
    have hmax := List.le_of_mem_argmax ht (show chosen ∈ registry.argmax (fun j => score data (key j)) from harg)
    by_contra hne
    have hsum := score_disjoint_sum_le data (key chosen) (key truth) hne
    omega

noncomputable section
universe u
variable {J : Type u} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

/-- Actual declared read-noise mode law, paired with an arbitrary declared confuser.
Every primitive read is retained, including incorrect flags/confuser draws. -/
def primitive (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J) : PMF (Bool × J) :=
  (modeLaw eta he).bind (fun correct => confuser.map (fun j => (correct,j)))

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
@[simp] theorem primitive_apply (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J) (b : Bool) (j : J) :
    primitive eta he confuser (b,j) = modeLaw eta he b * confuser j := by
  classical
  cases b <;> simp [primitive,PMF.bind_apply,PMF.map_apply,tsum_fintype]

abbrev Raw (J : Type u) (N : ℕ) := SampleCoordinate (fun _ : Unit => N) → Bool × J

def rawLaw (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J) (N : ℕ) : Measure (Raw J N) :=
  productRowLaw (fun _ : Unit => primitive eta he confuser) (fun _ => N)

instance rawLaw_isProbability (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J) (N : ℕ) :
    IsProbabilityMeasure (rawLaw eta he confuser N) := by unfold rawLaw; infer_instance

/-- The new permitted physical readout. Target is a source parameter, not a
learner input. A confuser may itself have the same real ID as the truth. -/
def decode (key : J → Observation) (truth : J) (z : Bool × J) : Observation :=
  key (if z.1 then truth else z.2)

def readout {N : ℕ} (key : J → Observation) (truth : J) (omega : Raw J N) : Data N :=
  fun j => decode key truth (omega j)

def correctScore (z : Bool × J) : ℝ := if z.1 then 1 else 0

def correctCount {N : ℕ} (omega : Raw J N) : ℕ :=
  (Finset.univ.filter (fun k : Fin N => (omega ⟨(),k⟩).1 = true)).card

/-- Derived latent source event, never queried by the executable selector. -/
def Good (N : ℕ) : Set (Raw J N) := {omega | N < 2 * correctCount omega}

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
private theorem pmf_sum_real (p : PMF J) : ∑ j, (p j).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [tsum_fintype,ENNReal.toReal_sum (fun j _ => PMF.apply_ne_top _ j)] at h
  exact h

/-- The latent correct flags have the actual mean 1-eta under the primitive
source. This mean is proved by integration, not supplied to the selector. -/
theorem correct_mean (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J) :
    trueRisk (primitive eta he confuser).toMeasure correctScore = repairChance eta := by
  unfold trueRisk
  rw [PMF.integral_eq_sum]
  simp only [Fintype.sum_prod_type,primitive_apply,ENNReal.toReal_mul,smul_eq_mul]
  simp only [Fintype.sum_bool,correctScore,Bool.false_eq_true,if_false,mul_zero,Finset.sum_const_zero,
    if_true,mul_one]
  rw [← Finset.mul_sum,pmf_sum_real,mul_one]
  simp [modeLaw,UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal,modeProbability]

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
private theorem empirical_correct {N : ℕ} (omega : Raw J N) :
    empiricalRisk correctScore (productRowSample (N:=fun _ : Unit => N) ()) omega = (correctCount omega : ℝ) / N := by
  unfold empiricalRisk correctScore correctCount productRowSample
  rw [Finset.sum_boole]

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
/-- Every actual correct primitive becomes an actual target-ID readout. Thus
the source Good event implies the executable selected EVENT CLASS is correct. -/
theorem good_selected_class {N : ℕ} (registry : List J) (key : J → Observation)
    (fallback truth : J) (ht : truth ∈ registry) (omega : Raw J N) (hg : omega ∈ Good (J:=J) N) :
    key (select registry key fallback (readout key truth omega)) = key truth := by
  apply select_eq_class registry key fallback truth ht
  have hcount : correctCount omega ≤ score (readout key truth omega) (key truth) := by
    apply Finset.card_le_card
    intro k hk
    have hb := (Finset.mem_filter.mp hk).2
    simp [Finset.mem_filter,readout,decode,hb]
  change N < 2 * correctCount omega at hg
  omega


/-- Strict source noise gap. It is used only in the proof/risk schedule. -/
def gap (eta : NNReal) : ℝ := 1/2 - (eta : ℝ)

/-- The actual primitive product discharges every sampling/independence/mean
premise of the existing one-sided Hoeffding theorem. -/
theorem bad_good_probability_le (eta : NNReal) (he : eta ≤ 1) (heta : (eta : ℝ) < 1/2)
    (confuser : PMF J) (N : ℕ) :
    (rawLaw eta he confuser N).real (Good (J:=J) N)ᶜ ≤ Real.exp (-2 * (N : ℝ) * gap eta ^ 2) := by
  by_cases hN : N = 0
  · subst N
    simp only [Nat.cast_zero,mul_zero,zero_mul,Real.exp_zero]
    exact measureReal_le_one
  · have hNp : 0 < N := Nat.pos_of_ne_zero hN
    have hgap : 0 ≤ gap eta := by unfold gap; linarith
    have htail := measure_empiricalRisk_lower_le hNp (rawLaw eta he confuser N)
      (primitive eta he confuser).toMeasure correctScore (measurable_of_finite _)
      (by rintro ⟨b,j⟩; cases b <;> norm_num [correctScore])
      (productRowSample (N:=fun _ : Unit => N) ())
      (fun k => VariableRegisteredSamples.productRowSample_measurable (X:=Bool × J) (N:=fun _ : Unit => N) () k)
      (productRowSample_independent (fun _ : Unit => primitive eta he confuser) (fun _ => N) ())
      (fun k => productRowSample_law (fun _ : Unit => primitive eta he confuser) (fun _ => N) () k) hgap
    apply (measureReal_mono ?_).trans htail
    intro omega homega
    change ¬ N < 2 * correctCount omega at homega
    have hcount : 2 * correctCount omega ≤ N := Nat.le_of_not_gt homega
    have hreal : 2 * (correctCount omega : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcount
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNp
    have hfrac : (correctCount omega : ℝ) / (N : ℝ) ≤ 1/2 :=
      (div_le_iff₀ hNreal).mpr (by linarith)
    change empiricalRisk correctScore (productRowSample (N:=fun _ : Unit => N) ()) omega + gap eta ≤ _
    rw [empirical_correct,correct_mean]
    unfold gap repairChance
    linarith

/-- Actual exponentially vanishing risk, including the honest N=0 bound 1.
Radius zero denotes exact EVENT CLASS recovery on the derived Good event. -/
def learningSchedule (eta : NNReal) (heta : (eta : ℝ) < 1/2) : StatisticalConsistency.ConfidenceSchedule where
  failure N := Real.exp (-2 * (N : ℝ) * gap eta ^ 2)
  radius _ := 0
  failure_pos _ := Real.exp_pos _
  failure_le_one N := Real.exp_le_one_iff.mpr (by
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith [sq_nonneg (gap eta)])
  radius_nonneg _ := le_refl 0
  failure_tendsto_zero := by
    have hg : 0 < gap eta := by unfold gap; linarith
    have hlin : Tendsto (fun N : ℕ => (2 * gap eta ^ 2) * (N : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
    have hlim := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
    convert hlim using 1
    ext N
    dsimp only [Function.comp_apply]
    congr 1
    ring
  radius_tendsto_zero := tendsto_const_nhds

/-- Previously external C.good/bad bound is now constructed from the SAME
actual noisy-read product law. No desired discovery-correctness field is used. -/
def eventContract (eta : NNReal) (he : eta ≤ 1) (heta : (eta : ℝ) < 1/2) (confuser : PMF J) :
    StatisticalConsistency.ChangingSampleEventContract (Raw J) where
  schedule := learningSchedule eta heta
  μ N := rawLaw eta he confuser N
  probability _ := inferInstance
  good N := Good N
  bad_le_failure N := bad_good_probability_le eta he heta confuser N

/-- Readout row is computed from the declared sensor interpreter. -/
def sensorLaw (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J) (key : J → Observation) (truth : J) : PMF Observation :=
  (primitive eta he confuser).map (decode key truth)

def observedLaw (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J) (key : J → Observation) (truth : J) (N : ℕ) :
    Measure (Data N) := (rawLaw eta he confuser N).map (readout key truth)

/-- Complete actual observation law, not a supplied IID observation contract. -/
theorem observedLaw_product (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J)
    (key : J → Observation) (truth : J) (N : ℕ) :
    observedLaw eta he confuser key truth N =
      productRowLaw (fun _ : Unit => sensorLaw eta he confuser key truth) (fun _ => N) := by
  unfold observedLaw rawLaw productRowLaw readout
  rw [Measure.pi_map_pi (fun _ => (measurable_of_finite (decode key truth)).aemeasurable)]
  simp_rw [PMF.toMeasure_map _ _ (measurable_of_finite _)]
  rfl

/-- Same actual finite population journal and the actual selected event.
Previously supplied hgood is derived by the product/majority theorem. -/
theorem actual_parent_risk_le {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List RegisterPopulationHistorySource.Request)
    (registry : List (Fin es.length)) (fallback truth : Fin es.length) (ht : truth ∈ registry)
    (eta : NNReal) (he : eta ≤ 1) (heta : (eta : ℝ) < 1/2) (confuser : PMF (Fin es.length)) (N : ℕ) :
    (rawLaw eta he confuser N).real {omega |
      RegisterPopulationHistorySource.actualParent i m os es
        (select registry (RegisterPopulationHistorySource.observedChildID i m os es) fallback
          (readout (RegisterPopulationHistorySource.observedChildID i m os es) truth omega)) ≠
      RegisterPopulationHistorySource.actualParent i m os es truth} ≤ Real.exp (-2 * (N : ℝ) * gap eta ^ 2) := by
  apply (measureReal_mono ?_).trans (bad_good_probability_le eta he heta confuser N)
  intro omega herr hgood
  apply herr
  exact RegisterPopulationHistorySource.parent_eq_of_childID i m os es _ truth
    (good_selected_class registry _ fallback truth ht omega hgood)

/-- The ORIGINAL P12 parent-discovery consumer receives the actual product
confidence contract and actual argmax decoder; C.good and hgood are discharged.
No physical-only ancestry or unregistered target is inferred. -/
theorem actual_journal_discovery_consumes_p12 {n : ℕ} (i : Fin n) (m : Mechanism)
    (os : List (Organism n)) (es : List RegisterPopulationHistorySource.Request)
    (registry : List (Fin es.length)) (fallback truth : Fin es.length) (ht : truth ∈ registry)
    (eta : NNReal) (he : eta ≤ 1) (heta : (eta : ℝ) < 1/2) (confuser : PMF (Fin es.length)) :
    Tendsto (fun N => (rawLaw eta he confuser N).real {omega |
      RegisterPopulationHistorySource.actualParent i m os es
        (select registry (RegisterPopulationHistorySource.observedChildID i m os es) fallback
          (readout (RegisterPopulationHistorySource.observedChildID i m os es) truth omega)) ≠
      RegisterPopulationHistorySource.actualParent i m os es truth}) atTop (𝓝 0) := by
  exact RegisterPopulationHistorySource.journal_discovery_consumes_p12 i m os es
    (eventContract eta he heta confuser) truth
    (fun _ omega => select registry (RegisterPopulationHistorySource.observedChildID i m os es) fallback
      (readout (RegisterPopulationHistorySource.observedChildID i m os es) truth omega))
    (fun _ omega hgood => good_selected_class registry _ fallback truth ht omega hgood)


omit [MeasurableSpace J] [MeasurableSingletonClass J] in
/-- Exact actual channel formula, including arbitrary confuser collisions with
the true ID. The new read permission has correctness probability AT LEAST 1-eta. -/
theorem sensorLaw_apply (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J)
    (key : J → Observation) (truth : J) (id : Observation) :
    sensorLaw eta he confuser key truth id =
      modeLaw eta he true * PMF.pure (key truth) id + modeLaw eta he false * (confuser.map key) id := by
  classical
  have hs : ∑ j, confuser j = 1 := by simpa only [tsum_fintype] using PMF.tsum_coe confuser
  simp [sensorLaw,primitive,PMF.map_bind,PMF.map_comp,Function.comp_def,decode,
    PMF.bind_apply,tsum_fintype,hs]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem actual_correct_read_probability_ge (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J)
    (key : J → Observation) (truth : J) :
    repairChance eta ≤ (sensorLaw eta he confuser key truth).toMeasure.real {key truth} := by
  have hge : modeLaw eta he true ≤ sensorLaw eta he confuser key truth (key truth) := by
    rw [sensorLaw_apply,PMF.pure_apply_self,mul_one]
    exact le_add_of_nonneg_right (by positivity)
  have h := ENNReal.toReal_mono (PMF.apply_ne_top _ _) hge
  simpa [Measure.real,PMF.toMeasure_apply_singleton,modeLaw,
    UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal,modeProbability] using h

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
/-- At eta=1/2 two legal unknown-confuser hypotheses can have exactly the SAME
observed row, although their hidden targets differ. Confusers are swapped here;
this is not a no-go under an additional fixed-known-confuser assumption. -/
theorem half_noise_sensor_swap (key : J → Observation) (a b : J) :
    sensorLaw (1/2) (by norm_num) (PMF.pure b) key a =
      sensorLaw (1/2) (by norm_num) (PMF.pure a) key b := by
  have hm : modeLaw (1/2) (by norm_num) true = modeLaw (1/2) (by norm_num) false := by
    norm_num [modeLaw,UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow,modeProbability,repairChance]
  ext id
  rw [sensorLaw_apply,sensorLaw_apply]
  simp only [PMF.pure_map]
  rw [hm]
  exact add_comm _ _

/-- Equality is for the entire fixed-budget actual readout law, not merely
one marginal or one moment. Every estimator sees the same full N-record law. -/
theorem half_noise_observed_swap (key : J → Observation) (a b : J) (N : ℕ) :
    observedLaw (1/2) (by norm_num) (PMF.pure b) key a N =
      observedLaw (1/2) (by norm_num) (PMF.pure a) key b N := by
  rw [observedLaw_product,observedLaw_product,half_noise_sensor_swap key a b]


instance observedLaw_isProbability (eta : NNReal) (he : eta ≤ 1) (confuser : PMF J)
    (key : J → Observation) (truth : J) (N : ℕ) :
    IsProbabilityMeasure (observedLaw eta he confuser key truth N) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

private theorem common_data_parent_errors (N : ℕ) (mu : Measure (Data N)) [IsProbabilityMeasure mu]
    (estimate : Data N → Observation) (pa pb : Observation) (hne : pa ≠ pb) :
    1 ≤ mu.real {data | estimate data ≠ pa} + mu.real {data | estimate data ≠ pb} := by
  let A : Set (Data N) := {data | estimate data = pa}
  let B : Set (Data N) := {data | estimate data = pb}
  have hA : MeasurableSet A := (Set.to_countable _).measurableSet
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro data ha hb
    exact hne (ha.symm.trans hb)
  have hsum : mu.real A + mu.real B ≤ 1 := by
    rw [← measureReal_union hd hB]
    exact measureReal_le_one
  have hca : mu.real A + mu.real Aᶜ = 1 := by simpa using measureReal_add_measureReal_compl (μ:=mu) hA
  have hcb : mu.real B + mu.real Bᶜ = 1 := by simpa using measureReal_add_measureReal_compl (μ:=mu) hB
  change 1 ≤ mu.real Aᶜ + mu.real Bᶜ
  linarith

/-- Strict η=1/2 impossibility for EVERY deterministic readout-only parent
estimator (including abstention None): the two legal source risks sum to >=1.
No randomized-estimator impossibility is claimed by this statement. -/
theorem half_noise_parent_risk_sum (key : J → Observation) (a b : J) (pa pb : Observation)
    (hne : pa ≠ pb) (N : ℕ) (estimate : Data N → Observation) :
    1 ≤ (observedLaw (1/2) (by norm_num) (PMF.pure b) key a N).real {data | estimate data ≠ pa} +
      (observedLaw (1/2) (by norm_num) (PMF.pure a) key b N).real {data | estimate data ≠ pb} := by
  rw [← half_noise_observed_swap key a b N]
  exact common_data_parent_errors N _ estimate pa pb hne

/-- Consequently no one readout-only deterministic estimator family can have
vanishing parent error under both indistinguishable half-noise hypotheses. -/
theorem half_noise_no_joint_consistency (key : J → Observation) (a b : J) (pa pb : Observation)
    (hne : pa ≠ pb) (estimate : ∀ N, Data N → Observation) :
    ¬ (Tendsto (fun N => (observedLaw (1/2) (by norm_num) (PMF.pure b) key a N).real
          {data | estimate N data ≠ pa}) atTop (𝓝 0) ∧
        Tendsto (fun N => (observedLaw (1/2) (by norm_num) (PMF.pure a) key b N).real
          {data | estimate N data ≠ pb}) atTop (𝓝 0)) := by
  rintro ⟨ha,hb⟩
  have hs : Tendsto (fun N =>
      (observedLaw (1/2) (by norm_num) (PMF.pure b) key a N).real {data | estimate N data ≠ pa} +
      (observedLaw (1/2) (by norm_num) (PMF.pure a) key b N).real {data | estimate N data ≠ pb}) atTop (𝓝 (0 : ℝ)) := by
    simpa using ha.add hb
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hs
    (Filter.Eventually.of_forall (fun N => half_noise_parent_risk_sum key a b pa pb hne N (estimate N)))
  norm_num at hbad

/-- Fixed original two-founder episode; the same actual mixed-program journal
is used for both learning and the information boundary. No P5 assertion is made
for all its mixed programs under a single globally fixed mechanism goal. -/
abbrev WitnessEvent := Fin 4

def witnessKey : WitnessEvent → Observation :=
  RegisterPopulationHistorySource.observedChildID (0 : Fin 1) ⟨true,1⟩
    RegisterPopulationHistorySource.witnessFounders RegisterPopulationHistorySource.witnessRequests

def witnessParent : WitnessEvent → Observation :=
  RegisterPopulationHistorySource.actualParent (0 : Fin 1) ⟨true,1⟩
    RegisterPopulationHistorySource.witnessFounders RegisterPopulationHistorySource.witnessRequests

theorem two_founder_key_parent_witness :
    witnessKey 0 = some 2 ∧ witnessKey 1 = some 3 ∧ witnessKey 2 = none ∧ witnessKey 3 = some 5 ∧
      witnessParent 0 = some 0 ∧ witnessParent 1 = some 1 ∧ witnessParent 2 = none ∧ witnessParent 3 = some 3 := by
  norm_num [witnessKey,witnessParent,RegisterPopulationHistorySource.observedChildID,
    RegisterPopulationHistorySource.actualParent,RegisterPopulationHistorySource.childID,RegisterPopulationHistorySource.parentID,
    RegisterPopulationHistorySource.storeBefore,RegisterPopulationHistorySource.requestAt,
    RegisterPopulationHistorySource.run,RegisterPopulationHistorySource.founders,
    RegisterPopulationHistorySource.witnessFounders,RegisterPopulationHistorySource.witnessRequests,
    RegisterPopulationHistorySource.child,RegisterPopulationHistorySource.transaction,RegisterPopulationHistorySource.lookup,
    RegisterPopulationHistorySource.next,RegisterTimestampedBirthSource.step,RegisterFaultJointRecord.modeRecordStep,
    RegisterJointRecord.recordStep,birthEvent,repairEvent,execute_compiled,update]

private theorem quarter_le_one : (1/4 : NNReal) ≤ 1 := by
  exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)

/-- Nondegenerate actual-source P12 consumer, uniform over arbitrary confuser
rows on the same four-event registry. No sensor truth is read by select. -/
theorem two_founder_parent_risk_le (confuser : PMF WitnessEvent) (truth fallback : WitnessEvent) (N : ℕ) :
    (rawLaw (1/4) quarter_le_one confuser N).real {omega |
      witnessParent (select (List.finRange 4) witnessKey fallback (readout witnessKey truth omega)) ≠ witnessParent truth} ≤
      Real.exp (-(N : ℝ)/8) := by
  have h := actual_parent_risk_le (0 : Fin 1) ⟨true,1⟩
    RegisterPopulationHistorySource.witnessFounders RegisterPopulationHistorySource.witnessRequests
    (List.finRange 4) fallback truth (List.mem_finRange truth) (1/4) quarter_le_one (by norm_num) confuser N
  calc
    _ ≤ Real.exp (-2 * (N : ℝ) * gap (1/4) ^ 2) := h
    _ = _ := by congr 1; norm_num [gap]; ring

theorem two_founder_p12_consumer (confuser : PMF WitnessEvent) (truth fallback : WitnessEvent) :
    Tendsto (fun N => (rawLaw (1/4) quarter_le_one confuser N).real {omega |
      witnessParent (select (List.finRange 4) witnessKey fallback (readout witnessKey truth omega)) ≠ witnessParent truth})
      atTop (𝓝 0) :=
  actual_journal_discovery_consumes_p12 (0 : Fin 1) ⟨true,1⟩
    RegisterPopulationHistorySource.witnessFounders RegisterPopulationHistorySource.witnessRequests
    (List.finRange 4) fallback truth (List.mem_finRange truth) (1/4) quarter_le_one (by norm_num) confuser

/-- Same retained population, distinct actual birth parents, identical complete
readout laws at half noise. Every deterministic parent estimator has >=1/2 risk
in at least one of the two worlds; UNKNOWN is counted as an error here. -/
theorem two_founder_half_noise_obstruction (N : ℕ) (estimate : Data N → Observation) :
    observedLaw (1/2) (by norm_num) (PMF.pure (1 : WitnessEvent)) witnessKey 0 N =
      observedLaw (1/2) (by norm_num) (PMF.pure (0 : WitnessEvent)) witnessKey 1 N ∧
    witnessParent 0 ≠ witnessParent 1 ∧
    ((1/2 : ℝ) ≤ (observedLaw (1/2) (by norm_num) (PMF.pure (1 : WitnessEvent)) witnessKey 0 N).real
        {data | estimate data ≠ witnessParent 0} ∨
      (1/2 : ℝ) ≤ (observedLaw (1/2) (by norm_num) (PMF.pure (0 : WitnessEvent)) witnessKey 1 N).real
        {data | estimate data ≠ witnessParent 1}) := by
  have hp : witnessParent 0 ≠ witnessParent 1 := by
    rw [two_founder_key_parent_witness.2.2.2.2.1,two_founder_key_parent_witness.2.2.2.2.2.1]
    decide
  refine ⟨half_noise_observed_swap witnessKey 0 1 N,hp,?_⟩
  have h := half_noise_parent_risk_sum witnessKey 0 1 (witnessParent 0) (witnessParent 1) hp N estimate
  by_cases ha : (1/2 : ℝ) ≤ (observedLaw (1/2) (by norm_num) (PMF.pure (1 : WitnessEvent)) witnessKey 0 N).real
      {data | estimate data ≠ witnessParent 0}
  · exact Or.inl ha
  · right; linarith

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationJournalLearning
