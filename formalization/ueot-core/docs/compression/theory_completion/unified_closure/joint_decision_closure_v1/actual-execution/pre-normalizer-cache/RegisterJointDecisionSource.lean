import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationHistorySource

/-!
# Same-source finite-wallet population decisions

The computational world stores the hidden register bits of the actual finite
population. The controller sees only the registered prefix receipt
(birth occurred, a controlled write was charged), together with its own requests.
This is a declared prefix-receipt protocol, not the old whole-batch protocol.
Neither the protected resident program nor population existence, source mode,
birth label, true parent or owner is an observation.

The source-to-code theorem below justifies erasing metadata for this known-goal
family: every resident program equals that goal, and all three register actions
use the old primitive. Actual addresses, histories, owners, clocks and children
remain in the same original Store replay. The fresh source parameter is sampled
only during initialization and is copied unchanged by every transition.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionSource

open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open scoped BigOperators

/-- None commits to root-idle for this and every remaining decision tick.
Some addresses root0/child1 and emits one old register action. -/
abbrev Act := Option (Bool × RegisterRepairSource.Action)
abbrev Obs := Bool × Bool
abbrev Noise := Bool × Bool
abbrev PackedStore := List (Option Bool)

structure World (Theta : Type*) where
  theta : Theta
  store : PackedStore
  stopped : Bool
  deriving DecidableEq, Repr

def address (b : Bool) : ℕ := if b then 1 else 0

def effective (stopped : Bool) (a : Act) : Bool × RegisterRepairSource.Action :=
  if stopped then (false, none) else a.getD (false, none)

def request (stopped : Bool) (a : Act) (z : Noise) :
    RegisterPopulationHistorySource.Request :=
  let q := effective stopped a
  ⟨address q.1, q.2, z.1, z.2⟩

def packedLookup (s : PackedStore) (j : ℕ) : Option Bool := (s[j]?).join

def postBit (goal bit : Bool) (a : RegisterRepairSource.Action) (mode : Bool) : Bool :=
  if mode then a.getD bit else !goal

def childBit (goal bit : Bool) (a : RegisterRepairSource.Action) (mode : Bool) : Option Bool :=
  if mode && (a.getD bit == goal) then some (a.getD bit) else none

def packedNext (goal : Bool) (s : PackedStore) (j : ℕ)
    (a : RegisterRepairSource.Action) (mode : Bool) : PackedStore :=
  match packedLookup s j with
  | none => s ++ [none]
  | some bit => s.set j (some (postBit goal bit a mode)) ++ [childBit goal bit a mode]

/-- Both receipt fields are computed from the same literal transaction branch.
An invalid address cannot charge or produce a child, and still consumes a tick. -/
def packedObserve (goal : Bool) (s : PackedStore) (j : ℕ)
    (a : RegisterRepairSource.Action) (mode : Bool) : Obs :=
  match packedLookup s j with
  | none => (false, false)
  | some bit => ((childBit goal bit a mode).isSome, mode && a.isSome)

def step {Theta : Type*} (goal : Bool) (w : World Theta) (a : Act) (z : Noise) : World Theta :=
  let q := effective w.stopped a
  ⟨w.theta, packedNext goal w.store (address q.1) q.2 z.1,
    w.stopped || a.isNone⟩

def observe {Theta : Type*} (goal : Bool) (w : World Theta) (a : Act) (z : Noise) : Obs :=
  let q := effective w.stopped a
  packedObserve goal w.store (address q.1) q.2 z.1

def feeUnit {Theta : Type*} (goal : Bool) (w : World Theta) (a : Act) (z : Noise) : ℚ :=
  if (observe goal w a z).2 then 1 else 0

def birthUnit {Theta : Type*} (goal : Bool) (w : World Theta) (a : Act) (z : Noise) : ℚ :=
  if (observe goal w a z).1 then 1 else 0

/-- Public pre-outcome write commitment. No future fault/None result is used. -/
def cap (a : Act) : ℚ := if (effective false a).2.isSome then 1 else 0

/-- A fair independent birth label is recorded by the world but not exposed.
The SAME theta supplies every mode probability. -/
def primitiveWeight {Theta : Type*} (r : Theta → ℚ) (w : World Theta) (z : Noise) : ℚ :=
  (if z.1 then r w.theta else 1 - r w.theta) / 2

@[simp] theorem theta_preserved {Theta : Type*} (goal : Bool) (w : World Theta)
    (a : Act) (z : Noise) : (step goal w a z).theta = w.theta := rfl

@[simp] theorem stopped_preserved {Theta : Type*} (goal : Bool) (w : World Theta)
    (a : Act) (z : Noise) (h : w.stopped = true) :
    (step goal w a z).stopped = true := by simp [step, h]

@[simp] theorem stop_commits {Theta : Type*} (goal : Bool) (w : World Theta) (z : Noise) :
    (step goal w none z).stopped = true := by simp [step]

theorem stop_is_actual_root_idle {Theta : Type*} (w : World Theta) (z : Noise) :
    request w.stopped none z = ⟨0, none, z.1, z.2⟩ := by
  cases h : w.stopped <;> rfl

theorem stopped_is_actual_root_idle {Theta : Type*} (w : World Theta) (a : Act) (z : Noise)
    (h : w.stopped = true) : request w.stopped a z = ⟨0, none, z.1, z.2⟩ := by
  simp [request, effective, h, address]

theorem packedNext_length (goal : Bool) (s : PackedStore) (j : ℕ)
    (a : RegisterRepairSource.Action) (mode : Bool) :
    (packedNext goal s j a mode).length = s.length + 1 := by
  unfold packedNext
  split <;> simp

@[simp] theorem step_length {Theta : Type*} (goal : Bool) (w : World Theta)
    (a : Act) (z : Noise) : (step goal w a z).store.length = w.store.length + 1 :=
  packedNext_length _ _ _ _ _

theorem feeUnit_nonneg {Theta : Type*} (goal : Bool) (w : World Theta) (a : Act) (z : Noise) :
    0 ≤ feeUnit goal w a z := by unfold feeUnit; split <;> norm_num

theorem feeUnit_le_cap {Theta : Type*} (goal : Bool) (w : World Theta) (a : Act) (z : Noise) :
    feeUnit goal w a z ≤ cap a := by
  rcases w with ⟨theta, s, stopped⟩
  rcases z with ⟨mode, label⟩
  cases stopped <;> cases a with
  | none =>
      simp only [feeUnit, observe, effective, cap, Bool.false_eq_true, if_false,
        Option.getD_none, Option.isSome_none, if_true]
      unfold packedObserve
      split <;> simp
  | some a =>
      rcases a with ⟨j, action⟩
      cases action <;>
        simp only [feeUnit, observe, effective, cap, Bool.false_eq_true, if_false,
          Option.getD_some, Option.isSome_none, Option.isSome_some, if_true] <;>
        unfold packedObserve
      all_goals split <;> cases mode <;> simp

theorem primitiveWeight_nonneg {Theta : Type*} (r : Theta → ℚ)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (w : World Theta) (z : Noise) :
    0 ≤ primitiveWeight r w z := by
  unfold primitiveWeight
  split
  · exact div_nonneg (hr w.theta).1 (by norm_num)
  · exact div_nonneg (sub_nonneg.mpr (hr w.theta).2) (by norm_num)

theorem primitiveWeight_sum_one {Theta : Type*} (r : Theta → ℚ) (w : World Theta) :
    ∑ z : Noise, primitiveWeight r w z = 1 := by
  simp [primitiveWeight, Fintype.sum_prod_type]

/-- World projection only. It is NOT an observation granted to a policy. -/
def project {n : ℕ} (i : Fin n) (s : RegisterPopulationHistorySource.Store n) : PackedStore :=
  s.map (Option.map (fun p => p.organism.physical i))

def Aligned {n : ℕ} (goal : Bool) (s : RegisterPopulationHistorySource.Store n) : Prop :=
  ∀ p, some p ∈ s → p.organism.program = goal


theorem project_lookup {n : ℕ} (i : Fin n) (s : RegisterPopulationHistorySource.Store n) (j : ℕ) :
    packedLookup (project i s) j =
      (RegisterPopulationHistorySource.lookup s j).map (fun p => p.organism.physical i) := by
  simp only [packedLookup, project, List.getElem?_map, RegisterPopulationHistorySource.lookup]
  cases h : s[j]? with
  | none => simp [h]
  | some op => cases op <;> simp [h]

theorem project_set {n : ℕ} (i : Fin n) (s : RegisterPopulationHistorySource.Store n)
    (j : ℕ) (p : ClockedOrganism n) :
    project i (s.set j (some p)) = (project i s).set j (some (p.organism.physical i)) := by
  simp [project, List.map_set]

theorem aligned_lookup {n : ℕ} (goal : Bool) (s : RegisterPopulationHistorySource.Store n)
    (h : Aligned goal s) (j : ℕ) (p : ClockedOrganism n)
    (hp : RegisterPopulationHistorySource.lookup s j = some p) : p.organism.program = goal := by
  unfold RegisterPopulationHistorySource.lookup at hp
  cases hj : s[j]? with
  | none => simp [hj] at hp
  | some op =>
    cases op with
    | none => simp [hj] at hp
    | some q =>
      have hq : q = p := by simpa [hj] using hp
      subst q
      exact h p (List.mem_of_getElem? hj)

theorem primitive_parent_bit {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (a : RegisterRepairSource.Action) (mode label : Bool) :
    (RegisterTimestampedBirthSource.step i m p a mode label).parentAfter.organism.physical i =
      postBit m.goal (p.organism.physical i) a mode := by
  cases mode <;> cases a <;>
    simp [RegisterTimestampedBirthSource.step, modeRecordStep, RegisterJointRecord.recordStep,
      postBit, update]

theorem primitive_child_bit {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : ClockedOrganism n) (a : RegisterRepairSource.Action) (mode label : Bool)
    (hp : p.organism.program = m.goal) :
    (RegisterTimestampedBirthSource.step i m p a mode label).child.map
      (fun c => c.organism.physical i) =
      childBit m.goal (p.organism.physical i) a mode := by
  cases mode with
  | false => rfl
  | true =>
    cases a with
    | none =>
      by_cases hb : p.organism.physical i = m.goal
      · simp [RegisterTimestampedBirthSource.step, modeRecordStep, RegisterJointRecord.recordStep,
          childBit, birthEvent, repairEvent, execute_compiled, update, hp, hb]
      · simp [RegisterTimestampedBirthSource.step, modeRecordStep, RegisterJointRecord.recordStep,
          childBit, update, hp, hb]
    | some b =>
      by_cases hb : b = m.goal
      · simp [RegisterTimestampedBirthSource.step, modeRecordStep, RegisterJointRecord.recordStep,
          childBit, birthEvent, repairEvent, execute_compiled, update, hp, hb]
      · simp [RegisterTimestampedBirthSource.step, modeRecordStep, RegisterJointRecord.recordStep,
          childBit, update, hp, hb]

/-- One actual Store transition commutes with the computational projection.
The hypothesis is only the known resident-program family, not a next-state,
value, funding or optimality certificate. -/
theorem next_project {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RegisterPopulationHistorySource.Store n) (q : RegisterPopulationHistorySource.Request)
    (hs : Aligned m.goal s) :
    project i (RegisterPopulationHistorySource.next i m s q) =
      packedNext m.goal (project i s) q.parent q.action q.mode := by
  unfold packedNext
  rw [project_lookup]
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none =>
    simp [hp, RegisterPopulationHistorySource.next, RegisterPopulationHistorySource.transaction,
      RegisterPopulationHistorySource.child, project]
  | some p =>
    have hg := aligned_lookup m.goal s hs q.parent p hp
    simp only [Option.map_some]
    simp only [RegisterPopulationHistorySource.next, RegisterPopulationHistorySource.child,
      RegisterPopulationHistorySource.transaction, hp, Option.map_some, Option.bind_some]
    simp only [project, List.map_append, List.map_cons, List.map_nil]
    change project i (s.set q.parent (some _)) ++ [_] = _
    rw [project_set, primitive_parent_bit, primitive_child_bit i m {p with clock := s.length} q.action q.mode q.label hg]
    rfl

private theorem aligned_set {n : ℕ} (goal : Bool) (s : RegisterPopulationHistorySource.Store n)
    (hs : Aligned goal s) (j : ℕ) (p : ClockedOrganism n) (hp : p.organism.program = goal) :
    Aligned goal (s.set j (some p)) := by
  induction s generalizing j with
  | nil => simp [Aligned]
  | cons op s ih =>
    cases j with
    | zero =>
      intro q hq
      simp only [List.set_cons_zero, List.mem_cons] at hq
      rcases hq with heq | hq
      · exact (Option.some.inj heq).symm ▸ hp
      · exact hs q (by simp [hq])
    | succ j =>
      intro q hq
      simp only [List.set_cons_succ, List.mem_cons] at hq
      rcases hq with hq | hq
      · exact hs q (by simp [hq])
      · exact ih (fun q hq => hs q (by simp [hq])) j q hq

/-- All actual retained parents and actual newborns preserve the known program
invariant, including faults, failed births and invalid addresses. -/
theorem aligned_next {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RegisterPopulationHistorySource.Store n) (q : RegisterPopulationHistorySource.Request)
    (hs : Aligned m.goal s) :
    Aligned m.goal (RegisterPopulationHistorySource.next i m s q) := by
  have hc : ∀ c, RegisterPopulationHistorySource.child i m s q = some c →
      c.organism.program = m.goal := by
    intro c hc
    obtain ⟨p, hp, _, hprog, _⟩ :=
      RegisterPopulationHistorySource.actual_child_source i m s q c hc
    exact hprog.trans (aligned_lookup m.goal s hs q.parent p hp)
  have happ : ∀ t : RegisterPopulationHistorySource.Store n,
      Aligned m.goal t → Aligned m.goal (t ++ [RegisterPopulationHistorySource.child i m s q]) := by
    intro t ht p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | hp
    · exact ht p hp
    · exact hc p hp.symm
  unfold RegisterPopulationHistorySource.next
  cases ht : RegisterPopulationHistorySource.transaction i m s q with
  | none => exact happ s hs
  | some r =>
    have hparent : r.parentAfter.organism.program = m.goal := by
      unfold RegisterPopulationHistorySource.transaction at ht
      obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp ht
      subst r
      exact (step_program i m p.organism q.action q.mode q.label).trans
        (aligned_lookup m.goal s hs q.parent p hp)
    exact happ _ (aligned_set m.goal s hs q.parent r.parentAfter hparent)

noncomputable def nativeFee {n : ℕ} (r : Option (ClockedRecord n)) : ℝ :=
  (r.map ClockedRecord.expenditure).getD 0

def nativeObs {n : ℕ} (r : Option (ClockedRecord n)) : Obs :=
  ((r.bind ClockedRecord.child).isSome,
    (r.map (fun t => t.repairMode && t.action.isSome)).getD false)

theorem primitive_obs {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (a : RegisterRepairSource.Action) (mode label : Bool) (hp : p.organism.program = m.goal) :
    nativeObs (some (RegisterTimestampedBirthSource.step i m p a mode label)) =
      ((childBit m.goal (p.organism.physical i) a mode).isSome, mode && a.isSome) := by
  have hb := congrArg Option.isSome (primitive_child_bit i m p a mode label hp)
  simp only [Option.isSome_map] at hb
  apply Prod.ext
  · exact hb
  · cases mode <;> rfl

theorem observation_project {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RegisterPopulationHistorySource.Store n) (q : RegisterPopulationHistorySource.Request)
    (hs : Aligned m.goal s) :
    nativeObs (RegisterPopulationHistorySource.transaction i m s q) =
      packedObserve m.goal (project i s) q.parent q.action q.mode := by
  unfold packedObserve
  rw [project_lookup]
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none => simp [RegisterPopulationHistorySource.transaction, hp, nativeObs]
  | some p =>
    simpa only [RegisterPopulationHistorySource.transaction, hp, Option.map_some] using
      primitive_obs i m {p with clock := s.length} q.action q.mode q.label
        (aligned_lookup m.goal s hs q.parent p hp)

/-- Exact zero/c tariff from the SAME original transaction. The paid-write
flag is equivalent to a nonzero fee when the registered tariff is positive. -/
theorem primitive_fee {n : ℕ} (i : Fin n) (m : Mechanism) (p : ClockedOrganism n)
    (a : RegisterRepairSource.Action) (mode label : Bool) :
    nativeFee (some (RegisterTimestampedBirthSource.step i m p a mode label)) =
      (if mode && a.isSome then 1 else 0 : ℝ) * m.writeCost := by
  cases mode <;> cases a <;>
    simp [nativeFee, RegisterTimestampedBirthSource.step, modeRecordStep,
      RegisterJointRecord.recordStep, cost]

theorem fee_project {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RegisterPopulationHistorySource.Store n) (q : RegisterPopulationHistorySource.Request) :
    nativeFee (RegisterPopulationHistorySource.transaction i m s q) =
      (if (packedObserve m.goal (project i s) q.parent q.action q.mode).2 then 1 else 0 : ℝ) *
        m.writeCost := by
  unfold packedObserve
  rw [project_lookup]
  cases hp : RegisterPopulationHistorySource.lookup s q.parent with
  | none => simp [RegisterPopulationHistorySource.transaction, hp, nativeFee]
  | some p =>
    simpa only [RegisterPopulationHistorySource.transaction, hp, Option.map_some] using
      primitive_fee i m {p with clock := s.length} q.action q.mode q.label


structure NativeWorld (Theta : Type*) (n : ℕ) where
  theta : Theta
  store : RegisterPopulationHistorySource.Store n
  stopped : Bool

def projectWorld {Theta : Type*} {n : ℕ} (i : Fin n) (w : NativeWorld Theta n) : World Theta :=
  ⟨w.theta, project i w.store, w.stopped⟩

noncomputable def nativeStep {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) : NativeWorld Theta n :=
  ⟨w.theta, RegisterPopulationHistorySource.next i m w.store (request w.stopped a z),
    w.stopped || a.isNone⟩

noncomputable def nativeTransaction {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) : Option (ClockedRecord n) :=
  RegisterPopulationHistorySource.transaction i m w.store (request w.stopped a z)

theorem nativeStep_project {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    projectWorld i (nativeStep i m w a z) = step m.goal (projectWorld i w) a z := by
  unfold projectWorld nativeStep step request
  congr 1
  exact next_project i m w.store _ hw

theorem nativeStep_aligned {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    Aligned m.goal (nativeStep i m w a z).store :=
  aligned_next i m w.store _ hw

theorem nativeObservation_project {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) (hw : Aligned m.goal w.store) :
    nativeObs (nativeTransaction i m w a z) = observe m.goal (projectWorld i w) a z :=
  observation_project i m w.store _ hw

theorem nativeFee_project {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) :
    nativeFee (nativeTransaction i m w a z) =
      (feeUnit m.goal (projectWorld i w) a z : ℝ) * m.writeCost := by
  rw [nativeTransaction, fee_project]
  change (if (observe m.goal (projectWorld i w) a z).2 then 1 else 0 : ℝ) * m.writeCost =
    (feeUnit m.goal (projectWorld i w) a z : ℝ) * m.writeCost
  unfold feeUnit
  cases h : (observe m.goal (projectWorld i w) a z).2 <;> simp

noncomputable def nativePayoff {n : ℕ} (price : ℚ) (r : Option (ClockedRecord n)) : ℝ :=
  (if (nativeObs r).1 then 1 else 0) - (price : ℝ) * nativeFee r

/-- Literal full-cost payoff, obtained from the SAME transaction as the
observation and successor. No independent reward or fee kernel is supplied. -/
theorem nativePayoff_project {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (price : ℚ) (w : NativeWorld Theta n) (a : Act) (z : Noise)
    (hw : Aligned m.goal w.store) :
    nativePayoff price (nativeTransaction i m w a z) =
      (birthUnit m.goal (projectWorld i w) a z : ℝ) -
        (price : ℝ) * (m.writeCost : ℝ) * (feeUnit m.goal (projectWorld i w) a z : ℝ) := by
  rw [nativePayoff, nativeObservation_project i m w a z hw, nativeFee_project]
  cases h : (observe m.goal (projectWorld i w) a z).1 <;>
    simp [birthUnit, h] <;> ring

/-- A positive public tariff makes the charged-write receipt exactly the
information in the real nonzero payment; a zero-tariff mode oracle is excluded. -/
theorem charged_iff_nonzero_fee {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise)
    (hc : 0 < (m.writeCost : ℝ)) :
    (observe m.goal (projectWorld i w) a z).2 = true ↔
      nativeFee (nativeTransaction i m w a z) ≠ 0 := by
  rw [nativeFee_project]
  unfold feeUnit
  cases h : (observe m.goal (projectWorld i w) a z).2 <;> simp [hc.ne']

/-- Initialization protects resident programs. This known-goal family does
not leak an unknown goal by supplying its program to the optimizer. -/
def initialStore (goal initialBit : Bool) : RegisterPopulationHistorySource.Store 1 :=
  RegisterPopulationHistorySource.founders
    [⟨[], fun _ => initialBit, goal⟩]

theorem initial_aligned (goal initialBit : Bool) : Aligned goal (initialStore goal initialBit) := by
  intro p hp
  simp only [initialStore, RegisterPopulationHistorySource.founders, List.mapIdx_cons,
    List.mapIdx_nil, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq] at hp
  subst p
  rfl

@[simp] theorem initial_project (goal initialBit : Bool) :
    project (0 : Fin 1) (initialStore goal initialBit) = [some initialBit] := by
  rfl

/-- The same original population allocator supplies the complete child,
including physical source, owner extension, parent address and fresh ID. -/
theorem native_child_is_actual {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) (c : ClockedOrganism n)
    (hc : (nativeTransaction i m w a z).bind ClockedRecord.child = some c) :
    ∃ p : ClockedOrganism n,
      RegisterPopulationHistorySource.lookup w.store (request w.stopped a z).parent = some p ∧
      (modeRecordStep i m p.organism (request w.stopped a z).action z.1 z.2).transaction.child =
        some c.organism ∧
      c.organism.program = p.organism.program ∧
      (request w.stopped a z).parent < w.store.length := by
  exact RegisterPopulationHistorySource.actual_child_source i m w.store
    (request w.stopped a z) c hc

theorem native_child_fresh {Theta : Type*} {n : ℕ} (i : Fin n) (m : Mechanism)
    (w : NativeWorld Theta n) (a : Act) (z : Noise) (c : ClockedOrganism n)
    (hc : (nativeTransaction i m w a z).bind ClockedRecord.child = some c) :
    RegisterPopulationHistorySource.childID i m w.store (request w.stopped a z) = some w.store.length ∧
      RegisterPopulationHistorySource.lookup w.store w.store.length = none ∧
      (request w.stopped a z).parent < w.store.length :=
  RegisterPopulationHistorySource.actual_child_fresh i m w.store (request w.stopped a z) c hc

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionSource
