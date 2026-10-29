import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeInfinite
import UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceAccounting

/-!
Original commitment: resource payment follows from the SAME actual repair mechanism and a declared resource source.
Existing assumption: RegisterResourceSource supplied every step with at least one write cost; P12 separately used expected accounting.
Premise reduced: derive realized balances from compiled feedback, one initial reserve and one channel-rate bound.
Models: NEW open idle-request resource channel; original closed zero-inflow source remains a separate obstruction case.
Consumer: P6 ResourceViable on the SAME actual complete-record policy paths, without a desired funding field.

The new external port delivers g accounting units whenever the requested action
is idle, including a tick whose physical execution is preempted by environmental
fault. This protected request-triggered channel is a new open-environment model.
Its source is registered externally; the original closed source produces no
resource. Costs, physical transitions, births, program and allowed actions keep
the original projections. P6 units retain their original abstract accounting
meaning; no thermodynamic interpretation is inferred here.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFeedbackResource
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultControlModel RegisterFaultJointRecord RegisterFaultInfiniteRecord
open scoped BigOperators ENNReal
noncomputable section

/-- Computed inflow from the declared NEW external request-triggered idle port. -/
def idleInflow {n : ℕ} (g : ℝ) (r : ModeRecord n) : ℝ :=
  if r.transaction.action = none then g else 0

/-- State-dependent reserve cushion derived from the compiled repair program. -/
def cushion {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) : ℝ :=
  if x i = m.goal then 0 else m.writeCost

private theorem cushion_nonneg {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) :
    0 ≤ cushion i m x := by unfold cushion; split_ifs <;> positivity

/-- One actual transition preserves the reserve cushion. Supply is ZERO at a
paid write; affordability is therefore not a renamed pointwise cost≤supply premise. -/
theorem actual_step_funded {n : ℕ} (i : Fin n) (m : Mechanism) (g reserve : ℝ)
    (hg : (m.writeCost : ℝ) ≤ g) (o : Organism n)
    (hr : cushion i m o.physical ≤ reserve) (mode label : Bool) :
    let r := modeRecordStep i m o ((substrate i).execute m.goal o.physical) mode label
    cushion i m r.transaction.parentAfter.physical ≤ reserve + idleInflow g r - r.transaction.expenditure := by
  dsimp only
  have hc := m.writeCost.coe_nonneg
  by_cases hx : o.physical i = m.goal <;> cases mode <;>
    simp [cushion,execute_compiled,hx,modeRecordStep,RegisterJointRecord.recordStep,update,cost,idleInflow] at * <;>
      linarith

/-- Executed repair puts the real target in the legitimate state; the SAME
compiled controller consequently requests idle next. No feedback field is assumed. -/
theorem executed_repair_next_idle {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n) (label : Bool) :
    (substrate i).execute m.goal
      (modeRecordStep i m o ((substrate i).execute m.goal o.physical) true label).transaction.parentAfter.physical = none := by
  by_cases hx : o.physical i = m.goal <;>
    simp [execute_compiled,hx,modeRecordStep,RegisterJointRecord.recordStep,update]

/-- Resource balance of the actual finite complete transaction list. -/
def listBalance {n : ℕ} (reserve g : ℝ) (rs : List (ModeRecord n)) : ℝ :=
  reserve + (rs.map (idleInflow g)).sum - (rs.map (fun r => r.transaction.expenditure)).sum

private theorem listBalance_cons {n : ℕ} (reserve g : ℝ) (r : ModeRecord n) (rs : List (ModeRecord n)) :
    listBalance reserve g (r::rs) = listBalance (reserve+idleInflow g r-r.transaction.expenditure) g rs := by
  simp only [listBalance,List.map_cons,List.sum_cons]
  ring

variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
variable (epsilon : NNReal) (he : epsilon ≤ 1)

private theorem weight_head {k t : ℕ} (h : State n) (o : Organism n)
    (a : Action) (mode label : Bool) (rest : Tape k)
    (hw : 0 < weight i noise m epsilon he (selectorPolicy ((substrate i).execute m.goal)) (k+1) (t:=t) h o
      (a,mode,label,rest)) :
    a = (substrate i).execute m.goal h ∧
      0 < weight i noise m epsilon he (selectorPolicy ((substrate i).execute m.goal)) k (t:=t+1)
        (modeRecordStep i m o a mode label).transaction.parentAfter.physical
        (modeRecordStep i m o a mode label).transaction.parentAfter rest := by
  classical
  simp only [weight,selectorPolicy_actionProb,selectorPolicy_advance] at hw
  have ha : a = (substrate i).execute m.goal h := by
    by_contra hn
    rw [if_neg hn,zero_mul,zero_mul,zero_mul] at hw
    exact (lt_irrefl 0) hw
  refine ⟨ha,?_⟩
  by_contra hn
  have hz := le_antisymm (le_of_not_gt hn)
    (weight_nonneg i noise m epsilon he (selectorPolicy ((substrate i).execute m.goal)) k (t:=t+1) _ _ rest)
  rw [hz,mul_zero] at hw
  exact (lt_irrefl 0) hw

/-- Every supported finite source run pays its actual fees from this feedback
channel and reserve. Support/action consistency is derived from the original
policy probability, not supplied as an independent execution certificate. -/
theorem supported_record_balance (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g) :
    ∀ k {t : ℕ} (h : State n) (o : Organism n) (w : Tape k),
      o.physical = h → cushion i m o.physical ≤ reserve →
      0 < weight i noise m epsilon he (selectorPolicy ((substrate i).execute m.goal)) k (t:=t) h o w →
      0 ≤ listBalance reserve g (records i m (selectorPolicy ((substrate i).execute m.goal)) k (t:=t) h o w) := by
  intro k
  induction k generalizing reserve with
  | zero =>
    intro t h o w hx hr hw
    simpa [records,listBalance] using (cushion_nonneg i m o.physical).trans hr
  | succ k ih =>
    rintro t h o ⟨a,mode,label,rest⟩ hx hr hw
    have hh := weight_head i noise m epsilon he h o a mode label rest hw
    have ha : a = (substrate i).execute m.goal o.physical := by rw [hx]; exact hh.1
    have hs := actual_step_funded i m g reserve hg o hr mode label
    rw [← ha] at hs
    change 0 ≤ listBalance reserve g ((modeRecordStep i m o a mode label) ::
      records i m (selectorPolicy ((substrate i).execute m.goal)) k (t:=t+1)
        (modeRecordStep i m o a mode label).transaction.parentAfter.physical
        (modeRecordStep i m o a mode label).transaction.parentAfter rest)
    rw [listBalance_cons]
    exact ih _ _ _ _ rfl hs hh.2

local instance tapeSpace (k : ℕ) : MeasurableSpace (Tape k) := ⊤
local instance tapeSingleton (k : ℕ) : MeasurableSingletonClass (Tape k) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (ModeRecord n) := ⊤
local instance : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _ => trivial⟩

private theorem cushion_le_cost (x : State n) : cushion i m x ≤ m.writeCost := by
  unfold cushion
  split_ifs <;> simp [m.writeCost.coe_nonneg]

/-- The original finite recordLaw itself is funded; no arbitrary tape's zero
probability actions are promoted to an actually executed program. -/
theorem actual_finite_balance_ae (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g)
    (hr : (m.writeCost : ℝ) ≤ reserve) (o : Organism n) (k : ℕ) :
    ∀ᵐ rs ∂(recordLaw i noise m epsilon he (selectorPolicy ((substrate i).execute m.goal))
      k (t:=0) o.physical o).toMeasure, 0 ≤ listBalance reserve g rs := by
  let sigma := selectorPolicy ((substrate i).execute m.goal)
  let q := tapeLaw i noise m epsilon he sigma k (t:=0) o.physical o
  have hsupp : ∀ᵐ w ∂q.toMeasure, q w ≠ 0 := by
    rw [ae_iff,PMF.toMeasure_apply_eq_zero_iff _ (by trivial)]
    exact Set.disjoint_left.mpr (fun w hw hn => hn hw)
  let f : Tape k → List (ModeRecord n) := records i m sigma k (t:=0) o.physical o
  change ∀ᵐ rs ∂(q.map f).toMeasure, 0 ≤ listBalance reserve g rs
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite f)]
  apply (ae_map_iff (measurable_of_finite f).aemeasurable (by trivial)).mpr
  filter_upwards [hsupp] with w hw
  have hwpos := ENNReal.toReal_pos hw (PMF.apply_ne_top _ _)
  change 0 < (tapeLaw i noise m epsilon he sigma k (t:=0) o.physical o w).toReal at hwpos
  simp only [tapeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal] at hwpos
  exact supported_record_balance i noise m epsilon he g reserve hg k o.physical o w rfl
    ((cushion_le_cost i m o.physical).trans hr) hwpos

private theorem listBalance_append_one (reserve g : ℝ) (rs : List (ModeRecord n)) (r : ModeRecord n) :
    listBalance reserve g (rs++[r]) = listBalance reserve g rs + idleInflow g r - r.transaction.expenditure := by
  simp only [listBalance,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem listBalance_ofFn (reserve g : ℝ) (rs : ℕ → ModeRecord n) : ∀ k,
    listBalance reserve g (List.ofFn (fun j : Fin k => rs j)) =
      cumulativeResourceBalance reserve (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) k := by
  intro k
  induction k with
  | zero => simp [listBalance,cumulativeResourceBalance]
  | succ k ih =>
    rw [List.ofFn_succ',List.concat_eq_append,listBalance_append_one]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih]
    unfold cumulativeResourceBalance
    simp only [Finset.sum_range_succ]
    ring

@[fun_prop] private theorem measurable_idleInflow (g : ℝ) : Measurable (idleInflow (n:=n) g) := by intro s hs; trivial
@[fun_prop] private theorem measurable_expenditure : Measurable (fun r : ModeRecord n => r.transaction.expenditure) := by intro s hs; trivial

private theorem measurable_viable (reserve g : ℝ) :
    MeasurableSet {rs : ℕ → ModeRecord n | ResourceViable reserve
      (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)} := by
  have heq : {rs : ℕ → ModeRecord n | ResourceViable reserve
      (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)} =
      ⋂ k : ℕ, {rs | 0 ≤ cumulativeResourceBalance reserve
        (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) k} := by
    ext rs
    simp [ResourceViable]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le measurable_const
  unfold cumulativeResourceBalance
  have hgain (t : ℕ) : Measurable (fun rs : ℕ → ModeRecord n => idleInflow g (rs t)) :=
    (measurable_idleInflow g).comp (measurable_pi_apply t)
  have hcost (t : ℕ) : Measurable (fun rs : ℕ → ModeRecord n => (rs t).transaction.expenditure) :=
    measurable_expenditure.comp (measurable_pi_apply t)
  exact (measurable_const.add (Finset.measurable_sum (Finset.range k) (fun t _ => hgain t))).sub
    (Finset.measurable_sum (Finset.range k) (fun t _ => hcost t))

set_option maxHeartbeats 1000000 in
/-- P6 pathwise accounting for the SAME genuine infinite complete-record law.
The replenishment schedule is computed from actual requested idle transactions;
it can be zero exactly when an actual repair is paid. -/
theorem actual_recordPath_resource_viable (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g)
    (hr : (m.writeCost : ℝ) ≤ reserve) (o : Organism n) :
    let sigma := selectorPolicy ((substrate i).execute m.goal)
    ∀ᵐ rs ∂recordPathLaw i noise m epsilon he sigma ⟨0,o.physical,o⟩,
      ResourceViable reserve (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) := by
  let sigma := selectorPolicy ((substrate i).execute m.goal)
  let c : Config sigma := ⟨0,o.physical,o⟩
  have hfinite (k : ℕ) : ∀ᵐ z ∂wordPathLaw i noise m epsilon he sigma c,
      0 ≤ listBalance reserve g (trace i m sigma c (z k)) := by
    have hf := actual_finite_balance_ae i noise m epsilon he g reserve hg hr o k
    rw [← actual_record_prefix_law i noise m epsilon he sigma o.physical o k] at hf
    exact ae_of_ae_map ((measurable_of_countable _).comp (measurable_pi_apply k)).aemeasurable hf
  have hall : ∀ᵐ z ∂wordPathLaw i noise m epsilon he sigma c,
      ∀ k, 0 ≤ listBalance reserve g (trace i m sigma c (z k)) := ae_all_iff.mpr hfinite
  change ∀ᵐ rs ∂(wordPathLaw i noise m epsilon he sigma c).map (fun z k => recordAt i m sigma c z k),
    ResourceViable reserve (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)
  apply (ae_map_iff (measurable_recordStream i m sigma c).aemeasurable (measurable_viable reserve g)).mpr
  filter_upwards [hall,wordPathLaw_ae_coherent i noise m epsilon he sigma c] with z hz hc
  intro k
  have h := hz k
  rw [coherent_trace_eq_stream i m sigma c z hc.1 hc.2 k,listBalance_ofFn] at h
  exact h

/-- Open environment augmentation is only a computed extra resource coordinate;
erasing it leaves the original complete transaction law literally unchanged. -/
def openResourcePathLaw (g : ℝ) (o : Organism n) : Measure (ℕ → ModeRecord n × ℝ) :=
  (recordPathLaw i noise m epsilon he (selectorPolicy ((substrate i).execute m.goal)) ⟨0,o.physical,o⟩).map
    (fun rs t => (rs t,idleInflow g (rs t)))

theorem openResourcePath_erasure (g : ℝ) (o : Organism n) :
    (openResourcePathLaw i noise m epsilon he g o).map (fun rs t => (rs t).1) =
      recordPathLaw i noise m epsilon he (selectorPolicy ((substrate i).execute m.goal)) ⟨0,o.physical,o⟩ := by
  rw [openResourcePathLaw,Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id


/-- A concrete closed-source obstruction family: no inflow, a retained one-bit
parent, the same compiled repair program, and nondegenerate environmental faults.
The finite tape alternates a paid executed repair and a failed idle transaction. -/
def cycleHorizon : ℕ → ℕ
  | 0 => 0
  | k+1 => cycleHorizon k + 2

def cycleTape : (k : ℕ) → Tape (cycleHorizon k)
  | 0 => ()
  | k+1 => (some true,true,false,none,false,false,cycleTape k)

def closedParent (history : List Bool) : Organism 1 := ⟨history,fun _ => false,true⟩

private theorem closed_pair_parent (c : NNReal) (history : List Bool) :
    let m : Mechanism := ⟨true,c⟩
    let o := closedParent history
    (modeRecordStep 0 m (modeRecordStep 0 m o (some true) true false).transaction.parentAfter
      none false false).transaction.parentAfter = o := by
  dsimp [closedParent,modeRecordStep,RegisterJointRecord.recordStep,update]
  congr 1
  funext j
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  simp

/-- The registered alternating words have strictly positive mass whenever both
actual modes do. The action choices are evaluated by the original policy weight. -/
theorem cycle_weight (c epsilon : NNReal) (he : epsilon ≤ 1) (history : List Bool) :
    ∀ k {t : ℕ},
      weight (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he
        (selectorPolicy ((substrate (0 : Fin 1)).execute true)) (cycleHorizon k) (t:=t)
        (closedParent history).physical (closedParent history) (cycleTape k) =
        (repairChance epsilon * (epsilon : ℝ)) ^ k := by
  intro k
  induction k with
  | zero => intro t; rfl
  | succ k ih =>
    intro t
    have hp := closed_pair_parent c history
    dsimp only at hp
    have h0 : (selectorPolicy ((substrate (0 : Fin 1)).execute true)).actionProb (t:=t)
        (closedParent history).physical (some true) = 1 := by
      simp [selectorPolicy_actionProb,execute_compiled,closedParent]
    have h1 : (selectorPolicy ((substrate (0 : Fin 1)).execute true)).actionProb (t:=t+1)
        (modeRecordStep (0 : Fin 1) ⟨true,c⟩ (closedParent history)
          (some true) true false).transaction.parentAfter.physical none = 1 := by
      simp [selectorPolicy_actionProb,execute_compiled,modeRecordStep,RegisterJointRecord.recordStep,update]
    simp only [cycleHorizon,cycleTape,weight,selectorPolicy_advance]
    rw [h0,h1,hp,ih]
    simp [modeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal,modeProbability,pow_succ]
    ring

/-- The same actual words really pay k write charges; failed idle transactions
are retained and charged zero. No independent desired cost sequence is used. -/
theorem cycle_balance (c : NNReal) (history : List Bool) (reserve : ℝ) :
    ∀ k {t : ℕ},
      listBalance reserve 0
        (records (0 : Fin 1) ⟨true,c⟩
          (selectorPolicy ((substrate (0 : Fin 1)).execute true)) (cycleHorizon k) (t:=t)
          (closedParent history).physical (closedParent history) (cycleTape k)) = reserve - k * (c : ℝ) := by
  intro k
  induction k generalizing reserve with
  | zero => intro t; simp [cycleHorizon,cycleTape,records,listBalance]
  | succ k ih =>
    intro t
    change listBalance reserve 0
      (modeRecordStep (0 : Fin 1) ⟨true,c⟩ (closedParent history) (some true) true false ::
       modeRecordStep (0 : Fin 1) ⟨true,c⟩
         (modeRecordStep 0 ⟨true,c⟩ (closedParent history) (some true) true false).transaction.parentAfter
         none false false ::
       records 0 ⟨true,c⟩ (selectorPolicy ((substrate (0 : Fin 1)).execute true)) (cycleHorizon k) (t:=t+2)
         _ _ (cycleTape k)) = _
    rw [listBalance_cons,listBalance_cons]
    have hp := closed_pair_parent c history
    dsimp only at hp
    rw [hp]
    simp only [selectorPolicy_advance]
    rw [ih]
    simp [idleInflow,modeRecordStep,RegisterJointRecord.recordStep,cost]
    ring


/-- Every finite closed-source reserve has a genuine positive-probability
failure prefix. This is a failure of sure/pathwise funding, NOT an almost-sure
ruin theorem. Both actual modes and a positive write fee are essential here. -/
theorem closed_finite_reserve_failure (c epsilon : NNReal) (he : epsilon ≤ 1)
    (hc : 0 < c) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (history : List Bool) (reserve : ℝ) :
    ∃ k : ℕ, 0 <
      (recordLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he
        (selectorPolicy ((substrate (0 : Fin 1)).execute true)) (cycleHorizon k) (t:=0)
        (closedParent history).physical (closedParent history)).toMeasure
        {rs | listBalance reserve 0 rs < 0} := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  obtain ⟨k,hk⟩ := exists_nat_gt (reserve / (c : ℝ))
  have hover : reserve < (k : ℝ) * c := (div_lt_iff₀ hc').mp hk
  let sigma := selectorPolicy ((substrate (0 : Fin 1)).execute true)
  let q := tapeLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma
    (cycleHorizon k) (t:=0) (closedParent history).physical (closedParent history)
  let f := records (0 : Fin 1) ⟨true,c⟩ sigma (cycleHorizon k) (t:=0)
    (closedParent history).physical (closedParent history)
  have hwpos : 0 < (q (cycleTape k)).toReal := by
    change 0 < (tapeLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma
      (cycleHorizon k) (t:=0) (closedParent history).physical (closedParent history) (cycleTape k)).toReal
    simp only [tapeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal]
    rw [cycle_weight]
    have he' : (0 : ℝ) < epsilon := by exact_mod_cast he0
    have hr : 0 < repairChance epsilon := by
      unfold repairChance
      have : (epsilon : ℝ) < 1 := by exact_mod_cast he1
      linarith
    exact pow_pos (mul_pos hr he') k
  have hw : cycleTape k ∈ q.support := by
    change q (cycleTape k) ≠ 0
    intro hz
    simp [hz] at hwpos
  have hrecord : f (cycleTape k) ∈ (q.map f).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨cycleTape k,hw,rfl⟩
  have hbad : listBalance reserve 0 (f (cycleTape k)) < 0 := by
    change listBalance reserve 0 (records (0 : Fin 1) ⟨true,c⟩ sigma (cycleHorizon k) (t:=0)
      (closedParent history).physical (closedParent history) (cycleTape k)) < 0
    rw [cycle_balance]
    linarith
  refine ⟨k,?_⟩
  change 0 < (q.map f).toMeasure {rs | listBalance reserve 0 rs < 0}
  apply pos_iff_ne_zero.mpr
  intro hz
  exact (Set.disjoint_left.mp ((PMF.toMeasure_apply_eq_zero_iff (q.map f) (by trivial)).mp hz))
    hrecord hbad

set_option maxHeartbeats 1000000 in
/-- The closed original infinite source cannot fund this compiled repair
controller surely from any finite reserve. No claim of almost-sure ruin is made. -/
theorem closed_not_ae_infinite_viable (c epsilon : NNReal) (he : epsilon ≤ 1)
    (hc : 0 < c) (he0 : 0 < epsilon) (he1 : epsilon < 1)
    (history : List Bool) (reserve : ℝ) :
    let sigma := selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let o := closedParent history
    ¬ ∀ᵐ rs ∂recordPathLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma ⟨0,o.physical,o⟩,
      ResourceViable reserve (fun t => idleInflow 0 (rs t)) (fun t => (rs t).transaction.expenditure) := by
  dsimp only
  let sigma := selectorPolicy ((substrate (0 : Fin 1)).execute true)
  let o := closedParent history
  let cfg : Config sigma := ⟨0,o.physical,o⟩
  obtain ⟨k,hpositive⟩ := closed_finite_reserve_failure c epsilon he hc he0 he1 history reserve
  intro hviable
  have hv : ∀ᵐ z ∂wordPathLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma cfg,
      ResourceViable reserve (fun t => idleInflow 0 (recordAt 0 ⟨true,c⟩ sigma cfg z t))
        (fun t => (recordAt 0 ⟨true,c⟩ sigma cfg z t).transaction.expenditure) :=
    ae_of_ae_map (measurable_recordStream (0 : Fin 1) ⟨true,c⟩ sigma cfg).aemeasurable hviable
  have ht : ∀ᵐ z ∂wordPathLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma cfg,
      0 ≤ listBalance reserve 0 (trace 0 ⟨true,c⟩ sigma cfg (z (cycleHorizon k))) := by
    filter_upwards [hv,wordPathLaw_ae_coherent (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma cfg]
      with z hz hzcoh
    rw [coherent_trace_eq_stream (0 : Fin 1) ⟨true,c⟩ sigma cfg z hzcoh.1 hzcoh.2,
      listBalance_ofFn]
    exact hz _
  have hmeas : Measurable (fun z : ℕ → List Event => trace 0 ⟨true,c⟩ sigma cfg (z (cycleHorizon k))) :=
    (measurable_of_countable _).comp (measurable_pi_apply _)
  have hf : ∀ᵐ rs ∂(wordPathLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma cfg).map
      (fun z => trace 0 ⟨true,c⟩ sigma cfg (z (cycleHorizon k))),
      0 ≤ listBalance reserve 0 rs := (ae_map_iff hmeas.aemeasurable (by trivial)).mpr ht
  have heq : (wordPathLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma cfg).map
      (fun z => trace 0 ⟨true,c⟩ sigma cfg (z (cycleHorizon k))) =
      (recordLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma
        (cycleHorizon k) (t:=0) o.physical o).toMeasure :=
    actual_record_prefix_law (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma o.physical o (cycleHorizon k)
  rw [heq] at hf
  have hzero : (recordLaw (0 : Fin 1) (PMF.pure false) ⟨true,c⟩ epsilon he sigma
      (cycleHorizon k) (t:=0) o.physical o).toMeasure {rs | listBalance reserve 0 rs < 0} = 0 := by
    simpa only [not_le] using ae_iff.mp hf
  exact (ne_of_gt hpositive) hzero

/-- One common deployment consumer: the finite-data-selected literal policy
retains the actual post-probe parent, achieves its original infinite optimum,
and its SAME actual complete record law is resource-viable under the explicitly
new open idle-request channel. Past probe acquisition costs are not erased or
included in this deployment-origin reserve theorem. -/
theorem returned_positive_funded_actual_infinite {N : ℕ}
    (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (omega : RegisterFaultFinitePurposeProbe.Coordinate N → Bool × Bool) (b : Bool)
    (hs : RegisterFaultFinitePurposeProbe.select price width
      (RegisterFaultFinitePurposeProbe.sourceData m width omega) = .repair b)
    (o : Organism n) (ho : o.program = m.goal)
    (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g) (hr : (m.writeCost : ℝ) ≤ reserve) :
    let parent := RegisterFaultFinitePurposeInfinite.postProbeParent i m omega o
    let sigma := RegisterFaultFinitePurposeProbe.returnedPolicy i
      (RegisterFaultFinitePurposeProbe.select price width (RegisterFaultFinitePurposeProbe.sourceData m width omega))
    let mu := recordPathLaw i noise m epsilon he sigma ⟨0,parent.physical,parent⟩
    let p := RegisterFaultFinitePurposeProbe.priceValue price hp
    let M := RegisterFaultControlModel.model i noise m p epsilon he d hd
    Integrable (streamPayoff p d) mu ∧
      (∫ rs, streamPayoff p d rs ∂mu) = M.optimalValue parent.physical ∧
      ∀ᵐ rs ∂mu, ResourceViable reserve (fun t => idleInflow g (rs t))
        (fun t => (rs t).transaction.expenditure) := by
  have h := RegisterFaultFinitePurposeInfinite.returned_positive_actual_infinite_record
    i noise m epsilon he price width hp hw d hd omega b hs o ho
  refine ⟨h.2.1,h.2.2.2,?_⟩
  have hsnd := RegisterFaultFinitePurposeProbe.select_repair_sound m price width hp hw omega b hs
  rw [hs]
  simp only [RegisterFaultFinitePurposeProbe.returnedPolicy,RegisterFaultFinitePurposeProbe.returnedSelector]
  rw [hsnd.1]
  exact actual_recordPath_resource_viable i noise m epsilon he g reserve hg hr _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFeedbackResource
