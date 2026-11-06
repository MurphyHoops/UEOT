import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismTableLaw
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentZero
import UEOT.V3.PathError
import UEOT.V3.BinaryTesting

/-!
# Exact source experiment distance and classification limits

The comparison uses one fixed independent private law and one shared table
selector. Mechanism labels occur only in the world. The private seed is retained
in the output when bounding TV, so a terminal test cannot gain an omitted side
channel from its own randomness. Raw real-randomized causal policies have the
same history law by the sampled-table theorem.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentLaw

open scoped BigOperators
open MeasureTheory
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterMechanismDecisionSource
open RegisterMechanismExperimentPaths RegisterMechanismExperimentZero RegisterMechanismTableLaw
open FiniteJointDecisionSolver (Table Model)
open FiniteJointDecisionSupportedPolicy (RawCausalPolicy)
open UEOT.V3.TotalVariation UEOT.V3.PathError UEOT.V3.BinaryTesting

local instance noiseMeasurable : MeasurableSpace Noise := ⊤
local instance noiseSingleton : MeasurableSingletonClass Noise := by infer_instance
local instance historyMeasurable : MeasurableSpace (List (Act × Obs)) := ⊤
local instance historySingleton : MeasurableSingletonClass (List (Act × Obs)) := by infer_instance
local instance tableMeasurable (H : ℕ) : MeasurableSpace (Table Act Obs H) := ⊤
local instance tableSingleton (H : ℕ) : MeasurableSingletonClass (Table Act Obs H) := by infer_instance

/-- Existing TV coupling theorem, specialized to a finite independent input.
The bad event is derived from the source, not supplied as a value bound. -/
theorem tv_map_le_event {Ω X : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [Countable X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : PMF Ω) (f g : Ω → X) (bad : Set Ω)
    (hsame : ∀ x, x ∉ bad → f x = g x) :
    tvDist (p.map f).toMeasure (p.map g).toMeasure ≤ p.toMeasure.real bad := by
  classical
  let γ := (p.map (fun x => (f x,g x))).toMeasure
  have hfst : γ.map Prod.fst = (p.map f).toMeasure := by
    rw [PMF.toMeasure_map _ measurable_fst, PMF.map_comp]
    rfl
  have hsnd : γ.map Prod.snd = (p.map g).toMeasure := by
    rw [PMF.toMeasure_map _ measurable_snd, PMF.map_comp]
    rfl
  have hcouple := tvDist_le_coupling_mismatch (p.map f).toMeasure (p.map g).toMeasure γ hfst hsnd
  have hpre : γ.real {y : X × X | y.1 ≠ y.2} = p.toMeasure.real {x | f x ≠ g x} := by
    unfold γ Measure.real
    rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _)
      (Set.to_countable _).measurableSet]
    rfl
  rw [hpre] at hcouple
  refine hcouple.trans (measureReal_mono ?_)
  intro x hx
  by_contra hn
  exact hx (hsame x hn)

noncomputable def commonInput {Seed : Type*} (μ : PMF Seed) {H : ℕ} (ν : PMF (Fin H → Noise)) :
    PMF (Seed × (Fin H → Noise)) := μ.bind fun s => ν.map fun z => (s,z)

theorem commonInput_snd {Seed : Type*} (μ : PMF Seed) {H : ℕ} (ν : PMF (Fin H → Noise)) :
    (commonInput μ ν).map Prod.snd = ν := by
  simp [commonInput, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.map_id]

theorem commonInput_event {Seed : Type*} [Fintype Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    (μ : PMF Seed) {H : ℕ} (ν : PMF (Fin H → Noise)) (A : Set (Fin H → Noise)) :
    (commonInput μ ν).toMeasure.real {x | x.2 ∈ A} = ν.toMeasure.real A := by
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have hm := PMF.toMeasure_map_apply Prod.snd (commonInput μ ν) A measurable_snd hA
  change ENNReal.toReal ((commonInput μ ν).toMeasure (Prod.snd ⁻¹' A)) = _
  rw [← hm, commonInput_snd]
  rfl

/-- Independent same-seed same-noise experiment. The seed remains available
for terminal classification, while the hidden mechanism and tape do not. -/
def seedOutput {Seed : Type*} (goal : Bool) {H : ℕ}
    (choose : Seed → Table Act Obs H) (m : FaultMechanism) (x : Seed × (Fin H → Noise)) :
    Seed × List (Act × Obs) :=
  (x.1, (packedExecute goal (choose x.1) (initialWorld goal m) x.2).history)

noncomputable def seededLaw {Seed : Type*} (P : Parameters) {H : ℕ}
    (μ : PMF Seed) (choose : Seed → Table Act Obs H) (m : FaultMechanism) :
    PMF (Seed × List (Act × Obs)) :=
  (commonInput μ (tapeLaw (noiseLaw P) H)).map (seedOutput P.goal choose m)

/-- Real finite sum form for a finite PMF event. -/
theorem event_real_sum {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (p : PMF X) (A : Set X) :
    p.toMeasure.real A = ∑ x, if x ∈ A then (p x).toReal else 0 := by
  classical
  unfold Measure.real
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro x hx
    by_cases h : x ∈ A <;> simp [Set.indicator,h]
  · intro x hx
    by_cases h : x ∈ A <;> simp [Set.indicator,h,PMF.apply_ne_top]

theorem bind_real_event {X Y : Type*} [Fintype X] [Fintype Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : PMF X) (q : X → PMF Y) (A : Set Y) :
    (p.bind q).toMeasure.real A = ∑ x, (p x).toReal * (q x).toMeasure.real A := by
  classical
  unfold Measure.real
  rw [PMF.toMeasure_bind_apply _ _ _ (Set.toFinite A).measurableSet,
    tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro x hx
    exact ENNReal.mul_ne_top (PMF.apply_ne_top p x) (measure_ne_top (q x).toMeasure A)

theorem map_real_event {X Y : Type*} [Fintype X] [Fintype Y]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (p : PMF X) (f : X → Y) (A : Set Y) :
    (p.map f).toMeasure.real A = p.toMeasure.real (f ⁻¹' A) := by
  unfold Measure.real
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) (Set.toFinite A).measurableSet]

def modeWord {H : ℕ} (b : Fin H → Bool) : Set (Fin H → Noise) :=
  {z | ∀ j, (z j).1 = b j}

def modeChance (P : Parameters) (b : Bool) : ℝ := if b then P.normal else 1 - (P.normal : ℝ)

@[simp] theorem noise_real_mode (P : Parameters) (z : Noise) :
    (noiseLaw P z).toReal = modeChance P z.1 / 2 := by
  simp [noiseLaw, UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal,
    modeChance, RegisterJointDecisionSource.primitiveWeight]

theorem noise_mode_mass (P : Parameters) (b : Bool) :
    (noiseLaw P).toMeasure.real {z : Noise | z.1 = b} = modeChance P b := by
  rw [event_real_sum]
  cases b <;>
    simp [Fintype.sum_prod_type, Fintype.sum_bool, noise_real_mode, modeChance] <;> ring

/-- Exact probability of a prescribed mode word, integrating ALL labels. -/
theorem modeWord_mass (P : Parameters) : ∀ (H : ℕ) (b : Fin H → Bool),
    (tapeLaw (noiseLaw P) H).toMeasure.real (modeWord b) = ∏ j, modeChance P (b j) := by
  classical
  intro H
  induction H with
  | zero =>
      intro b
      simp [tapeLaw,modeWord,Measure.real,PMF.toMeasure_pure_apply]
  | succ H ih =>
      intro b
      rw [tapeLaw,bind_real_event]
      have hpre (z : Noise) : (Fin.cases z) ⁻¹' modeWord b =
          if z.1 = b 0 then modeWord (fun j => b j.succ) else ∅ := by
        ext zs
        simp only [Set.mem_preimage,modeWord,Set.mem_setOf_eq,Fin.forall_fin_succ,
          Fin.cases_zero,Fin.cases_succ]
        by_cases hb : z.1 = b 0 <;> simp [hb]
      simp_rw [map_real_event, hpre]
      simp_rw [apply_ite (fun A => (tapeLaw (noiseLaw P) H).toMeasure.real A)]
      simp only [measureReal_empty, ih, mul_ite, mul_zero]
      rw [← Finset.sum_mul]
      have hsum : (∑ z : Noise, if z.1 = b 0 then (noiseLaw P z).toReal else 0) =
          modeChance P (b 0) := by
        simpa only [event_real_sum,Set.mem_setOf_eq] using noise_mode_mass P (b 0)
      rw [hsum,Fin.prod_univ_succ]

/-- NFN is exactly the only three-tick mismatch opportunity. -/
def NFN : Set (Fin 3 → Noise) := {z | (z 0).1 = true ∧ (z 1).1 = false ∧ (z 2).1 = true}

theorem NFN_mass (P : Parameters) :
    (tapeLaw (noiseLaw P) 3).toMeasure.real NFN = (P.normal : ℝ)^2 * (1-P.normal) := by
  have hset : NFN = modeWord ![true,false,true] := by
    ext z
    simp [NFN,modeWord,Fin.forall_fin_succ]
  rw [hset,modeWord_mass]
  norm_num [Fin.prod_univ_succ,modeChance]
  ring

/-- All allowed finite-horizon real-randomized experiments obey this upper
bound. No feasibility restriction or selected-policy-only check is needed. -/
theorem seeded_H3_TV_upper {Seed : Type*} [Fintype Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    (P : Parameters) (μ : PMF Seed) (choose : Seed → Table Act Obs 3) :
    tvDist (seededLaw P μ choose .S).toMeasure (seededLaw P μ choose .G).toMeasure ≤
      (P.normal : ℝ)^2 * (1-P.normal) := by
  have hbound := tv_map_le_event (commonInput μ (tapeLaw (noiseLaw P) 3))
    (seedOutput P.goal choose .S) (seedOutput P.goal choose .G) {x | x.2 ∈ NFN} (by
      intro x hx
      apply Prod.ext rfl
      exact history_three_eq_unless_NFN P.goal (choose x.1) x.2 hx)
  rw [commonInput_event, NFN_mass] at hbound
  exact hbound

/-- Short experiments, including ALL private contingent choices, have equal
joint seed/history laws. -/
theorem seeded_H2_eq {Seed : Type*} (P : Parameters) (μ : PMF Seed)
    (choose : Seed → Table Act Obs 2) : seededLaw P μ choose .S = seededLaw P μ choose .G := by
  unfold seededLaw
  apply congrArg (PMF.map · (commonInput μ (tapeLaw (noiseLaw P) 2)))
  funext x
  exact Prod.ext rfl (history_two_eq P.goal (choose x.1) x.2)

theorem seeded_H1_eq {Seed : Type*} (P : Parameters) (μ : PMF Seed)
    (choose : Seed → Table Act Obs 1) : seededLaw P μ choose .S = seededLaw P μ choose .G := by
  unfold seededLaw
  apply congrArg (PMF.map · (commonInput μ (tapeLaw (noiseLaw P) 1)))
  funext x
  exact Prod.ext rfl (history_one_eq P.goal (choose x.1) x.2)

theorem seeded_root_only_eq {Seed : Type*} (P : Parameters) {H : ℕ} (μ : PMF Seed)
    (choose : Seed → Table Act Obs H) (hr : ∀ s, RootOnly false (choose s)) :
    seededLaw P μ choose .S = seededLaw P μ choose .G := by
  unfold seededLaw
  apply congrArg (PMF.map · (commonInput μ (tapeLaw (noiseLaw P) H)))
  funext x
  exact Prod.ext rfl (root_only_initial_history P.goal (choose x.1) x.2 (hr x.1))

/-- Zero-probability private rows have no observable force. -/
theorem map_eq_of_support {X Y : Type*} (p : PMF X) (f g : X → Y)
    (h : ∀ x ∈ p.support, f x = g x) : p.map f = p.map g := by
  classical
  apply PMF.ext
  intro y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · simp [hx]
  · rw [h x ((PMF.mem_support_iff _ _).mpr hx)]

theorem commonInput_support {Seed : Type*} (μ : PMF Seed) {H : ℕ}
    (ν : PMF (Fin H → Noise)) (x : Seed × (Fin H → Noise))
    (hx : x ∈ (commonInput μ ν).support) : x.1 ∈ μ.support ∧ x.2 ∈ ν.support := by
  obtain ⟨s,hs,ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
  rcases (PMF.mem_support_map_iff _ _ _).mp ht with ⟨z,hz,heq⟩
  cases heq
  exact ⟨hs,hz⟩

/-- Actual root-only restriction on positive-probability executions is enough;
there is no extra requirement on impossible receipt rows. -/
theorem seeded_root_history_eq {Seed : Type*} (P : Parameters) {H : ℕ} (μ : PMF Seed)
    (choose : Seed → Table Act Obs H)
    (hr : ∀ s ∈ μ.support, ∀ z ∈ (tapeLaw (noiseLaw P) H).support,
      RootHistory false (packedExecute P.goal (choose s) (initialWorld P.goal .S) z).history) :
    seededLaw P μ choose .S = seededLaw P μ choose .G := by
  apply map_eq_of_support
  intro x hx
  obtain ⟨hs,hz⟩ := commonInput_support μ _ x hx
  apply Prod.ext rfl
  exact root_history_same P.goal (choose x.1) _ _ x.2 ⟨rfl,rfl⟩ (hr x.1 hs x.2 hz)

/-- A shared small wallet supplies a source-derived zero-information regime.
Legality is checked only on positive primitive/seed paths in each fixed model. -/
theorem seeded_insufficient_wallet_eq {Seed : Type*} (P : Parameters) {H : ℕ}
    (μ : PMF Seed) (choose : Seed → Table Act Obs H) (B : ℚ) (hB : B < P.tariff)
    (hp : ∀ m s, s ∈ μ.support → ∀ z, z ∈ (tapeLaw (noiseLaw P) H).support →
      PrepaidHistory P.tariff B
        (packedExecute P.goal (choose s) (initialWorld P.goal m) z).history) :
    seededLaw P μ choose .S = seededLaw P μ choose .G := by
  apply map_eq_of_support
  intro x hx
  obtain ⟨hs,hz⟩ := commonInput_support μ _ x hx
  apply Prod.ext rfl
  rw [insufficient_wallet_zero_history P.goal P.tariff _ _ x.2 B
      (RegisterJointDecisionValueBounds.allDamaged_initial P.goal) hB (hp .S x.1 hs x.2 hz),
    insufficient_wallet_zero_history P.goal P.tariff _ _ x.2 B
      (RegisterJointDecisionValueBounds.allDamaged_initial P.goal) hB (hp .G x.1 hs x.2 hz)]

/-- Constant mode-word mass. The private seed is still independent of this
physical tape, and the fixed mechanism is chosen before that seed is drawn. -/
theorem constant_modes_mass (P : Parameters) (H : ℕ) (b : Bool) :
    (tapeLaw (noiseLaw P) H).toMeasure.real (modeWord (fun _ => b)) = (modeChance P b)^H := by
  rw [modeWord_mass]
  simp

/-- Finite positive overlap is a classification obstruction, not a payoff or
regret obstruction. The bound holds even when the classifier retains its seed. -/
theorem seeded_TV_all_fault_bound {Seed : Type*} [Fintype Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    (P : Parameters) {H : ℕ} (μ : PMF Seed) (choose : Seed → Table Act Obs H) :
    tvDist (seededLaw P μ choose .S).toMeasure (seededLaw P μ choose .G).toMeasure ≤
      1 - (1-(P.normal : ℝ))^H := by
  let A : Set (Fin H → Noise) := modeWord (fun _ => false)
  have hbound := tv_map_le_event (commonInput μ (tapeLaw (noiseLaw P) H))
    (seedOutput P.goal choose .S) (seedOutput P.goal choose .G) {x | x.2 ∈ Aᶜ} (by
      intro x hx
      have hz : ∀ j, (x.2 j).1 = false := by simpa only [Set.mem_setOf_eq,
        Set.mem_compl_iff,not_not,A,modeWord] using hx
      apply Prod.ext rfl
      rw [all_fault_history P.goal _ _ _ hz,all_fault_history P.goal _ _ _ hz])
  rw [commonInput_event] at hbound
  have hm := constant_modes_mass P H false
  have hc := probReal_add_probReal_compl
    (μ := (tapeLaw (noiseLaw P) H).toMeasure) (Set.toFinite A).measurableSet
  change (tapeLaw (noiseLaw P) H).toMeasure.real A = (1-(P.normal : ℝ))^H at hm
  change tvDist _ _ ≤ _ at hbound
  linarith

theorem seeded_TV_all_normal_bound {Seed : Type*} [Fintype Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    (P : Parameters) {H : ℕ} (μ : PMF Seed) (choose : Seed → Table Act Obs H) :
    tvDist (seededLaw P μ choose .S).toMeasure (seededLaw P μ choose .G).toMeasure ≤
      1 - (P.normal : ℝ)^H := by
  let A : Set (Fin H → Noise) := modeWord (fun _ => true)
  have hbound := tv_map_le_event (commonInput μ (tapeLaw (noiseLaw P) H))
    (seedOutput P.goal choose .S) (seedOutput P.goal choose .G) {x | x.2 ∈ Aᶜ} (by
      intro x hx
      have hz : ∀ j, (x.2 j).1 = true := by simpa only [Set.mem_setOf_eq,
        Set.mem_compl_iff,not_not,A,modeWord] using hx
      exact Prod.ext rfl (all_normal_same_history P.goal _ _ _ _ ⟨rfl,rfl⟩ hz))
  rw [commonInput_event] at hbound
  have hm := constant_modes_mass P H true
  have hc := probReal_add_probReal_compl
    (μ := (tapeLaw (noiseLaw P) H).toMeasure) (Set.toFinite A).measurableSet
  change (tapeLaw (noiseLaw P) H).toMeasure.real A = (P.normal : ℝ)^H at hm
  change tvDist _ _ ≤ _ at hbound
  linarith

theorem classification_finite_lower {Seed : Type*} [Fintype Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    (P : Parameters) {H : ℕ} (μ : PMF Seed) (choose : Seed → Table Act Obs H)
    (A : Set (Seed × List (Act × Obs))) (hA : MeasurableSet A) :
    (1/2:ℝ) * (1-(P.normal : ℝ))^H ≤
      binaryRisk (seededLaw P μ choose .S).toMeasure (seededLaw P μ choose .G).toMeasure A := by
  have htv := seeded_TV_all_fault_bound P μ choose
  have he := binaryRisk_lower_bound (seededLaw P μ choose .S).toMeasure
    (seededLaw P μ choose .G).toMeasure A hA
  linarith

theorem classification_finite_positive {Seed : Type*} [Fintype Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    (P : Parameters) (hr : P.normal < 1) {H : ℕ}
    (μ : PMF Seed) (choose : Seed → Table Act Obs H)
    (A : Set (Seed × List (Act × Obs))) (hA : MeasurableSet A) :
    0 < binaryRisk (seededLaw P μ choose .S).toMeasure (seededLaw P μ choose .G).toMeasure A := by
  have hr' : (P.normal : ℝ) < 1 := by exact_mod_cast hr
  have hp : 0 < (1/2:ℝ) * (1-(P.normal : ℝ))^H := by positivity
  exact hp.trans_le (classification_finite_lower P μ choose A hA)

/-- Endpoint rates give zero TV at every finite horizon. -/
theorem endpoint_TV_zero {Seed : Type*} [Fintype Seed]
    [MeasurableSpace Seed] [MeasurableSingletonClass Seed]
    (P : Parameters) (hr : P.normal = 0 ∨ P.normal = 1) {H : ℕ}
    (μ : PMF Seed) (choose : Seed → Table Act Obs H) :
    tvDist (seededLaw P μ choose .S).toMeasure (seededLaw P μ choose .G).toMeasure = 0 := by
  apply le_antisymm
  · rcases hr with hr | hr
    · have h := seeded_TV_all_fault_bound P μ choose
      simpa [hr] using h
    · have h := seeded_TV_all_normal_bound P μ choose
      simpa [hr] using h
  · exact tvDist_nonneg _ _

noncomputable def separationLaw (P : Parameters) (m : FaultMechanism) : PMF (List (Act × Obs)) :=
  tableHistoryLaw P.goal (noiseLaw P) (separationTable P.goal) (initialWorld P.goal m)

/-- Actual exclusive terminal receipt, with no extra diagnostic tick. -/
theorem separation_event_mass_S (P : Parameters) :
    (separationLaw P .S).toMeasure.real {separationHistory P.goal} =
      (P.normal : ℝ)^2 * (1-P.normal) := by
  rw [separationLaw,tableHistoryLaw_eq_tape]
  unfold Measure.real
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) (measurableSet_singleton _)]
  have hset : (fun z : Fin 3 → Noise =>
      (packedExecute P.goal (separationTable P.goal) (initialWorld P.goal .S) z).history) ⁻¹'
      {separationHistory P.goal} = NFN := by
    ext z
    exact separation_event_S P.goal z
  rw [hset]
  exact NFN_mass P

theorem separation_event_mass_G (P : Parameters) :
    (separationLaw P .G).toMeasure.real {separationHistory P.goal} = 0 := by
  rw [separationLaw,tableHistoryLaw_eq_tape]
  unfold Measure.real
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_countable _) (measurableSet_singleton _)]
  have hset : (fun z : Fin 3 → Noise =>
      (packedExecute P.goal (separationTable P.goal) (initialWorld P.goal .G) z).history) ⁻¹'
      {separationHistory P.goal} = ∅ := by
    ext z
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_empty_iff_false,iff_false]
    exact separation_event_G P.goal z
  rw [hset]
  simp

/-- Exact TV, rather than merely a nonzero distinguishing event. -/
theorem separation_TV_exact (P : Parameters) :
    tvDist (separationLaw P .S).toMeasure (separationLaw P .G).toMeasure =
      (P.normal : ℝ)^2 * (1-P.normal) := by
  apply le_antisymm
  · rw [separationLaw,separationLaw,tableHistoryLaw_eq_tape,tableHistoryLaw_eq_tape]
    have h := tv_map_le_event (tapeLaw (noiseLaw P) 3)
      (fun z => (packedExecute P.goal (separationTable P.goal) (initialWorld P.goal .S) z).history)
      (fun z => (packedExecute P.goal (separationTable P.goal) (initialWorld P.goal .G) z).history)
      NFN (fun z hz => history_three_eq_unless_NFN P.goal _ z hz)
    rw [NFN_mass] at h
    exact h
  · have h := tvEvent_le (separationLaw P .S).toMeasure (separationLaw P .G).toMeasure
      {separationHistory P.goal} (measurableSet_singleton _)
    rw [separation_event_mass_S,separation_event_mass_G,sub_zero] at h
    have hq : 0 ≤ (P.normal : ℝ)^2 * (1-P.normal) := by
      have hr : (P.normal : ℝ) ≤ 1 := by exact_mod_cast P.normal_bounds.2
      positivity
    rwa [abs_of_nonneg hq] at h

/-- On the same H3 protocol the best equal-prior test has risk 7/16 at r=1/2.
This is finite classification, not a claim of learning-before-action benefit. -/
theorem separation_half_optimal_test (P : Parameters) (hr : P.normal = 1/2) :
    ∃ A : Set (List (Act × Obs)), MeasurableSet A ∧
      binaryRisk (separationLaw P .S).toMeasure (separationLaw P .G).toMeasure A = 7/16 ∧
      ∀ B, MeasurableSet B →
        binaryRisk (separationLaw P .S).toMeasure (separationLaw P .G).toMeasure A ≤
          binaryRisk (separationLaw P .S).toMeasure (separationLaw P .G).toMeasure B := by
  obtain ⟨A,hA,hv,ho⟩ := p_inv_01 (separationLaw P .S).toMeasure (separationLaw P .G).toMeasure
  refine ⟨A,hA,?_,ho⟩
  rw [separation_TV_exact,hr] at hv
  norm_num at hv
  exact hv

/-- All real causal kernels, with arbitrary permitted memory, inherit the
same source upper bound from one mechanism-independent sampled table law. -/
theorem raw_H3_TV_upper {I : Type*} {M : Model I Act Obs}
    (P : Parameters) (pi : RawCausalPolicy M) (h : pi.Memory) :
    tvDist (rawHistoryLaw P.goal (noiseLaw P) pi 3 h (initialWorld P.goal .S)).toMeasure
      (rawHistoryLaw P.goal (noiseLaw P) pi 3 h (initialWorld P.goal .G)).toMeasure ≤
      (P.normal : ℝ)^2 * (1-P.normal) := by
  let μ := sampleTable pi 3 h
  let ν := tapeLaw (noiseLaw P) 3
  have he (m : FaultMechanism) : rawHistoryLaw P.goal (noiseLaw P) pi 3 h (initialWorld P.goal m) =
      (commonInput μ ν).map (fun x =>
        (packedExecute P.goal x.1 (initialWorld P.goal m) x.2).history) := by
    rw [rawHistoryLaw_eq_seed_tape]
    simp [commonInput,PMF.map_bind,PMF.map_comp,Function.comp_def,μ,ν]
  rw [he .S,he .G]
  have ht := tv_map_le_event (commonInput μ ν)
    (fun x => (packedExecute P.goal x.1 (initialWorld P.goal .S) x.2).history)
    (fun x => (packedExecute P.goal x.1 (initialWorld P.goal .G) x.2).history)
    {x | x.2 ∈ NFN} (fun x hx => history_three_eq_unless_NFN P.goal x.1 x.2 hx)
  rw [commonInput_event,NFN_mass] at ht
  exact ht

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentLaw
