import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource

/-!
# Paid recovery of the actual code and execution component

This file applies the existing strong-repair/rank construction to the actual
pre-outcome repair phase of `CoreRegenerativeSource.step`.  It does not assert
that the subsequent survival/birth experiment cannot kill the organism.
Recovery spends the local resource state; it is not a cost-free abstract reset.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource

open UEOT.V3.Compression.Objecthood UEOT.V3.ViabilityKernel

structure RepairState where
  body : Body
  balance : Fin 7
  deriving DecidableEq, Fintype, Repr

/-- The finite bootstrap has only a physical body and a real finite balance. -/
def paidRepair (s : RepairState) : RepairState :=
  if (s.body.bootstrap = true ∨ repairCost s.body = 0) ∧
      repairCost s.body ≤ s.balance.val then
    ⟨restore s.body, ⟨s.balance.val - repairCost s.body,
      lt_of_le_of_lt (Nat.sub_le _ _) s.balance.isLt⟩⟩
  else s

def startState (theta i tag : Bool) : RepairState :=
  ⟨programBody theta i tag, 6⟩

def afterRepairState (theta i tag : Bool) : RepairState :=
  ⟨encode theta false tag, ⟨if i then 3 else 6, by cases i <;> decide⟩⟩

theorem paidRepair_start (theta i tag : Bool) :
    paidRepair (startState theta i tag) = afterRepairState theta i tag := by
  cases theta <;> cases i <;> cases tag <;> decide

theorem paidRepair_start_account (theta i tag : Bool) :
    (paidRepair (startState theta i tag)).balance.val +
      repairCost (startState theta i tag).body = 1 + 5 := by
  cases theta <;> cases i <;> cases tag <;> decide

theorem paidRepair_damaged_costs_three (theta tag : Bool) :
    (paidRepair (startState theta true tag)).body = encode theta false tag ∧
    (paidRepair (startState theta true tag)).balance.val = 3 ∧
    repairCost (startState theta true tag).body = 3 := by
  cases theta <;> cases tag <;> decide

theorem restored_remainder_funds_care_and_two_outputs (theta tag : Bool) :
    (paidRepair (startState theta true tag)).balance.val = operationCost .care + 2 := by
  cases theta <;> cases tag <;> decide

/-- The paid repair object is exactly the physical first phase used by the source. -/
theorem paidRepair_body_is_source_restore (theta i tag : Bool) :
    (paidRepair (startState theta i tag)).body = restore (programBody theta i tag) := by
  cases theta <;> cases i <;> cases tag <;> decide

theorem programStep_uses_paid_repair (theta i tag : Bool) (z : Noise) :
    (programStep (programBody theta i tag) z).retained =
      (if retains (programAction theta i) z then
        some (damageBody (paidRepair (startState theta i tag)).body z.2.1) else none) ∧
    (programStep (programBody theta i tag) z).newborn =
      (if births (programAction theta i) z then
        some (damageBody (paidRepair (startState theta i tag)).body z.2.2) else none) ∧
    (programStep (programBody theta i tag) z).repairPaid +
      (paidRepair (startState theta i tag)).balance.val = 1 + 5 := by
  rw [program_step_executes, paidRepair_body_is_source_restore]
  refine ⟨rfl, rfl, ?_⟩
  have h := paidRepair_start_account theta i tag
  simpa [executedResult, startState, Nat.add_comm] using h

noncomputable def repairKernel (s : RepairState) (_ : Unit) : PMF RepairState :=
  PMF.pure (paidRepair s)

def recoveredSet (theta tag : Bool) : Set RepairState :=
  {s | s.body = encode theta false tag}

/-- A nonempty basin containing healthy and genuinely damaged instances of both programs. -/
theorem source_mem_repairIter_one (theta i tag : Bool) :
    startState theta i tag ∈ repairIter repairKernel (recoveredSet theta tag) 1 := by
  change startState theta i tag ∈ recoveredSet theta tag ∪
    {s | ∃ a : Unit, StaysIn (repairKernel s a) (recoveredSet theta tag)}
  right
  refine ⟨(), ?_⟩
  simp [StaysIn, repairKernel, paidRepair_start, recoveredSet, afterRepairState]

theorem source_strongRepairable (theta i tag : Bool) :
    StrongRepairable repairKernel (recoveredSet theta tag) (startState theta i tag) :=
  ⟨1, source_mem_repairIter_one theta i tag⟩

theorem source_repairRank_le_one (theta i tag : Bool) :
    repairRank repairKernel (recoveredSet theta tag) (startState theta i tag)
      (source_strongRepairable theta i tag) ≤ 1 :=
  repairRank_le_of_mem repairKernel (recoveredSet theta tag) (startState theta i tag)
    (source_strongRepairable theta i tag) (source_mem_repairIter_one theta i tag)

theorem healthy_repairRank_zero (theta tag : Bool) :
    repairRank repairKernel (recoveredSet theta tag) (startState theta false tag)
      (source_strongRepairable theta false tag) = 0 := by
  apply (repairRank_eq_zero_iff_mem _ _ _ _).2
  rfl

theorem damaged_not_recovered (theta tag : Bool) :
    startState theta true tag ∉ recoveredSet theta tag := by
  cases theta <;> cases tag <;> decide

theorem damaged_repairRank_one (theta tag : Bool) :
    repairRank repairKernel (recoveredSet theta tag) (startState theta true tag)
      (source_strongRepairable theta true tag) = 1 := by
  have hle := source_repairRank_le_one theta true tag
  have hn : repairRank repairKernel (recoveredSet theta tag) (startState theta true tag)
      (source_strongRepairable theta true tag) ≠ 0 := by
    intro h
    exact damaged_not_recovered theta tag ((repairRank_eq_zero_iff_mem _ _ _ _).1 h)
  omega

/-- A physical self-loop outside the target has no strong-repair certificate. -/
theorem fixed_unrecovered_not_strongRepairable (s : RepairState) (K : Set RepairState)
    (hfix : paidRepair s = s) (hK : s ∉ K) :
    ¬ StrongRepairable repairKernel K s := by
  have hn : ∀ n, s ∉ repairIter repairKernel K n := by
    intro n
    induction n with
    | zero => exact hK
    | succ n ih =>
        intro hs
        change s ∈ repairIter repairKernel K n ∪
          {x | ∃ a : Unit, StaysIn (repairKernel x a) (repairIter repairKernel K n)} at hs
        rcases hs with hp | ⟨a, ha⟩
        · exact ih hp
        · have hs' : s ∈ repairIter repairKernel K n := by
            simpa [StaysIn, repairKernel, hfix] using ha
          exact ih hs'
  rintro ⟨n, h⟩
  exact hn n h

def bootCutState (theta tag : Bool) : RepairState :=
  ⟨{ programBody theta true tag with bootstrap := false }, 6⟩

theorem paidRepair_bootCut_fixed (theta tag : Bool) :
    paidRepair (bootCutState theta tag) = bootCutState theta tag := by
  cases theta <;> cases tag <;> decide

theorem bootstrap_cut_not_repairable (theta tag : Bool) :
    ¬ StrongRepairable repairKernel (recoveredSet theta tag) (bootCutState theta tag) := by
  apply fixed_unrecovered_not_strongRepairable _ _ (paidRepair_bootCut_fixed theta tag)
  cases theta <;> cases tag <;> decide

def underfundedState (theta tag : Bool) : RepairState :=
  ⟨programBody theta true tag, 2⟩

theorem paidRepair_underfunded_fixed (theta tag : Bool) :
    paidRepair (underfundedState theta tag) = underfundedState theta tag := by
  cases theta <;> cases tag <;> decide

theorem underfunded_not_repairable (theta tag : Bool) :
    ¬ StrongRepairable repairKernel (recoveredSet theta tag) (underfundedState theta tag) := by
  apply fixed_unrecovered_not_strongRepairable _ _ (paidRepair_underfunded_fixed theta tag)
  cases theta <;> cases tag <;> decide

/-- Less than the declared supply may permit writes but cannot prepay the real continuation. -/
theorem damaged_care_needs_full_supply (theta tag : Bool) :
    requestCap (programBody theta true tag) .care = 6 ∧
      ¬ requestCap (programBody theta true tag) .care ≤ 1 + 4 := by
  simp

/-- Same program, same damaged initial state, same six resource units. -/
theorem same_program_restores_then_reads (theta tag : Bool) :
    (paidRepair (startState theta true tag)).body = encode theta false tag ∧
    rawExecute (paidRepair (startState theta true tag)).body true = some .care ∧
    (paidRepair (startState theta true tag)).balance.val = 3 := by
  cases theta <;> cases tag <;> decide

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource
