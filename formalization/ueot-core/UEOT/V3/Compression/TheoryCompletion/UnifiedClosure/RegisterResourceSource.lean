import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismPurpose
import UEOT.V3.Compression.Objecthood.ResourceClosure.StateCostEnvelope

/-! Literal register-write expenditure supplies P6 affordability. The resource
unit is the same registered write unit as the reproductive objective. Constant
supply covering one write is a sufficient design condition, not a claim of
minimal supply, thermodynamic closure, or survival with an empty budget. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterResourceSource
open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterFaultSource RegisterMechanismPurpose
noncomputable section

/-- The runtime rebinds its controller from the retained stored program before
selecting the action; this is precisely safeRepairKernel's executed action. -/
def actualCost {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RepairOrganizationState (State n) Action Bool) : ℝ :=
  cost m ((canonicalizeRepairOrganization (substrate i) codec s).controller s.physical)

theorem actualCost_eq {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RepairOrganizationState (State n) Action Bool) :
    actualCost i m s = if s.physical i = s.repairProgram then (0 : ℝ) else (m.writeCost : ℝ) := by
  simp [actualCost, canonicalizeRepairOrganization, canonicalRepairOrganizationState,
    codec, execute_compiled, cost]
  split_ifs <;> rfl

/-- Every allowed write has the same registered ceiling; idle is free. -/
theorem actionCost_bounds (m : Mechanism) (a : Action) :
    0 ≤ cost m a ∧ cost m a ≤ m.writeCost := by
  cases a <;> simp [cost, m.writeCost.coe_nonneg]

theorem actualCost_bounds {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RepairOrganizationState (State n) Action Bool) :
    0 ≤ actualCost i m s ∧ actualCost i m s ≤ m.writeCost := by
  exact actionCost_bounds m _

/-- A genuine fault incurs the registered write charge; legitimacy makes it idle. -/
theorem damaged_cost {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RepairOrganizationState (State n) Action Bool) :
    actualCost i m (damage i s) = m.writeCost := by
  rw [actualCost_eq]
  simp [damage]

def accounting (m : Mechanism) : ResourceCostModel where
  maintenance := 0
  repair := m.writeCost
  reconstruction := 0
  maintenance_nonneg := le_rfl
  repair_nonneg := m.writeCost.coe_nonneg
  reconstruction_nonneg := le_rfl

/-- The old P6 state-cost envelope dominates this literal runtime cost.
No state-cost correctness premise is supplied by the caller. -/
theorem actualCost_le_p6 {n : ℕ} (i : Fin n) (m : Mechanism)
    (s : RepairOrganizationState (State n) Action Bool) :
    actualCost i m s ≤ stateResourceCost (accounting m)
      (fun z => z ∈ jointLegitimate (substrate i) codec (target i m.goal) m.goal)
      (jointProgramMismatch (substrate i) codec m.goal) s := by
  classical
  by_cases hs : s ∈ jointLegitimate (substrate i) codec (target i m.goal) m.goal
  · have hz : actualCost i m s = 0 := by
      obtain ⟨x, hx, rfl⟩ := hs
      rw [actualCost_eq]
      change (if x i = m.goal then (0 : ℝ) else (m.writeCost : ℝ)) = 0
      exact if_pos hx
    rw [hz]
    exact stateResourceCost_nonneg _ _ _ _
  · simpa [stateResourceCost, accounting, realIndicator, hs] using (actualCost_bounds i m s).2

/-- On the P5 source carrier this is the very same program/action tariff as
registered reproduction, rather than the cost of a substituted controller. -/
theorem actualCost_on_carrier {n : ℕ} [MeasurableSpace (State n)]
    [MeasurableSingletonClass (State n)] (i : Fin n) (m : Mechanism)
    (s : RepairOrganizationState (State n) Action Bool)
    (hs : s ∈ finiteJointRepairCarrier (physical i) (target i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal) :
    actualCost i m s = cost m ((substrate i).execute m.goal s.physical) := by
  have hp := (carrier_iff_program i m.goal s).mp hs
  simp [actualCost, canonicalizeRepairOrganization, canonicalRepairOrganizationState, codec, hp]

/-- In the P5 fault/repair mixture, only a scheduled repair executes the
controlled write. Environmental damage is not charged as a repair action. -/
def realizedStepCost {n : ℕ} (i : Fin n) (m : Mechanism) (repairNow : Bool)
    (s : RepairOrganizationState (State n) Action Bool) : ℝ :=
  if repairNow then actualCost i m s else 0

theorem realizedStepCost_bounds {n : ℕ} (i : Fin n) (m : Mechanism) (mode : Bool)
    (s : RepairOrganizationState (State n) Action Bool) :
    0 ≤ realizedStepCost i m mode s ∧ realizedStepCost i m mode s ≤ m.writeCost := by
  cases mode
  · simp [realizedStepCost, m.writeCost.coe_nonneg]
  · exact actualCost_bounds i m s

/-- The same nonnegative reserve and literal per-write supply work for every
realized source trace, including all fault/repair sequences. Affordability is
proved from instruction cost, not passed as an independent hrealized field. -/
theorem actual_trace_resource_viable {n : ℕ} (i : Fin n) (m : Mechanism)
    (trace : ℕ → RepairOrganizationState (State n) Action Bool) (repairNow : ℕ → Bool)
    (initial supply : ℝ) (hi : 0 ≤ initial) (hc : (m.writeCost : ℝ) ≤ supply) :
    ResourceViable initial (fun _ => supply) (fun t => realizedStepCost i m (repairNow t) (trace t)) := by
  apply resourceViable_of_pointwise_cost_le_replenish _ _ _ hi
  intro t
  exact (realizedStepCost_bounds i m (repairNow t) (trace t)).2.trans hc

/-- The same budget also covers arbitrary actual causal action records, not
only maintenance-program actions. This quantifies over every action/mode word,
so no success selection or path-support assumption is used. -/
theorem action_schedule_resource_viable (m : Mechanism)
    (actions : ℕ → Action) (repairNow : ℕ → Bool)
    (initial supply : ℝ) (hi : 0 ≤ initial) (hc : (m.writeCost : ℝ) ≤ supply) :
    ResourceViable initial (fun _ => supply)
      (fun t => if repairNow t then cost m (actions t) else 0) := by
  apply resourceViable_of_pointwise_cost_le_replenish _ _ _ hi
  intro t
  cases h : repairNow t
  · simpa only [h, Bool.false_eq_true, if_false] using m.writeCost.coe_nonneg.trans hc
  · simpa only [h, if_true] using (actionCost_bounds m (actions t)).2.trans hc

/-- The resource balance has the actual source accounting recurrence. -/
theorem actual_balance_step {n : ℕ} (i : Fin n) (m : Mechanism)
    (trace : ℕ → RepairOrganizationState (State n) Action Bool) (repairNow : ℕ → Bool)
    (initial supply : ℝ) (t : ℕ) :
    cumulativeResourceBalance initial (fun _ => supply) (fun k => realizedStepCost i m (repairNow k) (trace k)) (t+1) =
      cumulativeResourceBalance initial (fun _ => supply) (fun k => realizedStepCost i m (repairNow k) (trace k)) t +
        supply - realizedStepCost i m (repairNow t) (trace t) := by
  simp only [cumulativeResourceBalance, Finset.sum_range_succ]
  ring

/-- Nonconstant costs and real damage coexist in a nonempty source instance. -/
theorem nontrivial_cost_instance :
    let m : Mechanism := ⟨true, 1⟩
    let healthy := canonicalRepairOrganizationState (substrate (0 : Fin 1)) codec true (fun _ => true)
    actualCost 0 m healthy = 0 ∧ actualCost 0 m (damage 0 healthy) = 1 := by
  constructor
  · rw [actualCost_eq]
    rfl
  · exact damaged_cost 0 _ _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterResourceSource
