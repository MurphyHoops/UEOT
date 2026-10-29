import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointRecord
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultSource

/-! Actual successful births supply the physical component and inherited
program of the next P5 seed. They are not externally replaced by a valid seed.
This is one-generation maintenance entry; unique concurrent lineage identifiers
and an indefinitely reproducing population remain separate obligations. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBirthMaintenance
open Set MeasureTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterJointRecord RegisterFaultSource
noncomputable section

theorem actual_child_ready {n : ℕ} (i : Fin n) (m : Mechanism) (parent child : Organism n)
    (a : Action) (label : Bool) (hp : parent.program = m.goal)
    (hc : (recordStep i m parent a label).child = some child) :
    child.program = m.goal ∧ child.physical ∈ target i m.goal ∧
      (lineage i).OffspringOf (recordStep i m parent a label).parentAfter child := by
  have hsrc := record_child_source i m parent a label child hc
  have hgood : update i parent.physical a i = parent.program := by
    by_contra hn
    simp [recordStep, hn] at hc
  refine ⟨hsrc.2.2.trans hp, ?_, hsrc.2.1⟩
  rw [record_child_physical i m parent a label child hc]
  exact hgood.trans hp

section Maintenance
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- P5 consumes the literal child's inherited program and physical state.
Caller-supplied validity, target-membership and fault-success certificates have
all been discharged by birth execution and the source mechanism. -/
theorem actual_birth_enters_maintenance (i : Fin n) (m : Mechanism)
    (parent child : Organism n) (a : Action) (label : Bool)
    (hp : parent.program = m.goal)
    (hc : (recordStep i m parent a label).child = some child)
    (epsilon : NNReal) (he : epsilon ≤ 1) :
    let seed : OntogeneticSeed (State n) Bool := ⟨child.physical, child.program⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  have hready := actual_child_ready i m parent child a label hp hc
  dsimp only
  rw [hready.1]
  exact assembled_enters_actual_fault_system i m.goal child.physical hready.2.1 epsilon he

end Maintenance
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBirthMaintenance
