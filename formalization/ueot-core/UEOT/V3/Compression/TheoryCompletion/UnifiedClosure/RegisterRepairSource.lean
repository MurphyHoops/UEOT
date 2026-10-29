import UEOT.V3.Compression.Objecthood.OntogeneticConstruction.MaintenanceEntry

/-! # Register repair from executable syntax
The source is a finite register bank and a designated write port. Instructions
read registers and emit allowed actions. Compiler correctness and the physical
update supply P5's implementation premise. Reliable writing is a model
condition; environmental faults, budgets and program acquisition are separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairSource
open Set MeasureTheory
open UEOT.V3.ViabilityKernel UEOT.V3.ViabilityTrajectory
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open scoped ENNReal

abbrev State (n : ℕ) := Fin n → Bool
abbrev Action := Option Bool

inductive Instruction (n : ℕ) where
  | emit : Action → Instruction n
  | test : Fin n → Bool → Instruction n → Instruction n → Instruction n

def interpret {n : ℕ} : Instruction n → State n → Action
  | .emit a, _ => a
  | .test j b yes no, x => if x j = b then interpret yes x else interpret no x

def compile {n : ℕ} (i : Fin n) (b : Bool) : Instruction n :=
  .test i b (.emit none) (.emit (some b))

def substrate {n : ℕ} (i : Fin n) : TrustedRepairSubstrate Bool (State n) Action :=
  ⟨fun b x => interpret (compile i b) x⟩

def update {n : ℕ} (i : Fin n) (x : State n) : Action → State n
  | none => x
  | some b => Function.update x i b

noncomputable def physical {n : ℕ} (i : Fin n) (x : State n) (a : Action) : PMF (State n) :=
  PMF.pure (update i x a)

def target {n : ℕ} (i : Fin n) (b : Bool) : Set (State n) := {x | x i = b}

def repair {n : ℕ} (_i : Fin n) (b : Bool) : State n → Action := fun _ => some b

@[simp] theorem execute_compiled {n : ℕ} (i : Fin n) (b : Bool) (x : State n) :
    (substrate i).execute b x = if x i = b then none else some b := rfl

theorem other_register_unchanged {n : ℕ} (i j : Fin n) (hji : j ≠ i)
    (x : State n) (a : Action) : update i x a j = x j := by
  cases a <;> simp [update, hji]

theorem target_fixed {n : ℕ} (i : Fin n) (b : Bool) :
    viabilityStep (physical i) (target i b) = target i b := by
  apply Set.Subset.antisymm (viabilityStep_subset _ _)
  intro x hx
  refine ⟨hx, none, ?_⟩
  simpa [StaysIn, physical, update] using hx

/-- A target-preserving action at a target state is physically idle on the
entire state. This compares with, but does not execute, the old chosen policy. -/
theorem preserving_action_idle {n : ℕ} (i : Fin n) (b : Bool)
    (x : State n) (hx : x ∈ target i b) (a : Action)
    (ha : StaysIn (physical i x a) (target i b)) :
    update i x a = x := by
  cases a with
  | none => rfl
  | some c =>
      have hc : c = b := by simpa [StaysIn, physical, update, target] using ha
      subst c
      change x i = b at hx
      simp [update, ← hx]

/-- Full-state dynamics of this particular interpreted program implement the
existing repair/preserve law, without an existential replacement program. -/
theorem compiled_dynamics_implements {n : ℕ} (i : Fin n) (b : Bool) :
    RepairProgramDynamicsImplementsPolicy (substrate i) (physical i) b
      (repairThenPreservePolicy (physical i) (target i b) (target_fixed i b)
        (repair i b)) := by
  intro x
  by_cases hx : x ∈ target i b
  · have hp := canonicalPreservingController_preserving
      (physical i) (target i b) (target_fixed i b) x hx
    have hi := preserving_action_idle i b x hx _ hp
    simp only [repairThenPreservePolicy, if_pos hx]
    have hx' : x i = b := hx
    simp only [physical, execute_compiled, if_pos hx']
    rw [hi]
    rfl
  · have hx' : x i ≠ b := hx
    simp [repairThenPreservePolicy, hx, physical, execute_compiled, hx', repair]

section Maintenance
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

noncomputable def certificate (i : Fin n) (b : Bool) :
    PhysicalRepairCertificate (physical i) (target i b) where
  repairPolicy := repair i b
  potential := fun x => if x i = b then 0 else 1
  drift := 1
  target_measurable := (Set.toFinite _).measurableSet
  potential_measurable := measurable_of_finite _
  drift_ne_zero := one_ne_zero
  drift_ne_top := ENNReal.one_ne_top
  drift_condition := by
    intro x hx
    change x i ≠ b at hx
    simp [stationaryKernel_apply, physical, repair, update, PMF.toMeasure_pure, hx]

/-- Existing P5 entry with `himpl` and `hvalid` discharged by the source.
Fault-envelope and hazard assumptions remain explicit. -/
theorem compiled_enters_p5 (i : Fin n) (b : Bool) (x : State n)
    (hx : x ∈ target i b)
    (F : RepairOrganizationState (State n) Action Bool →
      PMF (RepairOrganizationState (State n) Action Bool))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : FiniteJointFaultEnvelope (physical i) (target i b) (certificate i b)
      (substrate i) (⟨id, id, fun _ => rfl⟩ : TrustedRepairCodec Bool Bool) b F) :
    let codec : TrustedRepairCodec Bool Bool := ⟨id, id, fun _ => rfl⟩
    let seed : OntogeneticSeed (State n) Bool := ⟨x, b⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i b) (target_fixed i b) (certificate i b)
      (substrate i) codec b (compiled_dynamics_implements i b)
      F epsilon hepsilon hF
    StaysIn (PMF.pure (assembleRepairOrganization (substrate i) codec seed)) S.carrier := by
  exact pure_assembled_stays_p5MaintenanceSystem
    (physical i) (target i b) (target_fixed i b) (certificate i b)
    (substrate i) ⟨id, id, fun _ => rfl⟩ ⟨x, b⟩
    (compiled_dynamics_implements i b) F epsilon hepsilon hF hx
end Maintenance

theorem opposite_programs_distinct (n : ℕ) (i : Fin n) :
    physical i (fun _ => false) ((substrate i).execute false (fun _ => false)) ≠
      physical i (fun _ => false) ((substrate i).execute true (fun _ => false)) := by
  simp only [execute_compiled, Bool.false_eq_true, if_true, if_false]
  intro h
  have hs : (fun _ : Fin n => false) ∈
      (physical i (fun _ => false) (some true)).support := by
    rw [← h]
    simp [physical, update]
  have hstate : (fun _ : Fin n => false) = Function.update (fun _ => false) i true := by
    simpa only [physical, PMF.support_pure, Set.mem_singleton_iff, update] using hs
  have hbit := congrFun hstate i
  simp at hbit

/-- A wrong target program is not a valid repair law for the original target. -/
theorem wrong_target_not_valid (n : ℕ) (i : Fin n) :
    ¬ RepairProgramValid (substrate i) (physical i) (target i false) true := by
  intro hv
  have hh : Function.update (fun _ : Fin n => false) i true ∈ target i false :=
    hv (fun _ => false) rfl (by simp [physical, update])
  simp [target] at hh

/-- Explicit nonempty proper one-register instance, including a real outside
state and its one-step repair. No empty address type witnesses the family. -/
theorem one_register_witness :
    (∃ x : State 1, x ∈ target 0 true) ∧
    (∃ x : State 1, x ∉ target 0 true ∧
      update 0 x (some true) ∈ target 0 true) ∧
    ¬ RepairProgramValid (substrate (0 : Fin 1)) (physical 0) (target 0 false) true := by
  refine ⟨⟨fun _ => true, rfl⟩, ⟨fun _ => false, ?_, ?_⟩,
    wrong_target_not_valid 1 0⟩ <;> simp [target, update]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairSource
