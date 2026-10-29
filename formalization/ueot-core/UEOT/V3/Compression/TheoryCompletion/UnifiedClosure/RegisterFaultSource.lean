import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRepairSource

/-! A physical fault writes the opposite of the retained target (flipping a
correct register), while retaining the
stored source program and controller. This explicit protected-code fault class
supplies the old P5 fault envelope; arbitrary code corruption is not asserted. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultSource
open Set MeasureTheory
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterRepairSource
open scoped ENNReal
noncomputable section
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

def codec : TrustedRepairCodec Bool Bool := ⟨id, id, fun _ => rfl⟩

/-- The fault reads the retained source bit; it does not synthesize a program. -/
def damage (i : Fin n) (s : RepairOrganizationState (State n) Action Bool) :
    RepairOrganizationState (State n) Action Bool :=
  { s with physical := Function.update s.physical i (!s.repairProgram) }

def fault (i : Fin n) (s : RepairOrganizationState (State n) Action Bool) :
    PMF (RepairOrganizationState (State n) Action Bool) := PMF.pure (damage i s)

theorem potential_finite (i : Fin n) (b : Bool)
    (s : RepairOrganizationState (State n) Action Bool) :
    jointRepairPotential (physical i) (target i b) (certificate i b) (substrate i) codec b s ≠ ∞ := by
  classical
  have h := autonomousRepairPotential_le_W_add_d
    (physical i) (target i b) (certificate i b) (s.physical, s.controller)
  have hf : autonomousRepairPotential (physical i) (target i b) (certificate i b)
      (s.physical, s.controller) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ h
    simp only [certificate]
    split_ifs <;> simp
  unfold jointRepairPotential
  apply ENNReal.add_ne_top.mpr
  refine ⟨hf, ?_⟩
  unfold organizationMismatchPenalty
  split_ifs <;> simp [certificate]

theorem carrier_iff_program (i : Fin n) (b : Bool)
    (s : RepairOrganizationState (State n) Action Bool) :
    s ∈ finiteJointRepairCarrier (physical i) (target i b) (certificate i b)
      (substrate i) codec b ↔ s.repairProgram = b := by
  constructor
  · intro h
    exact h.1.2
  · intro hs
    refine ⟨⟨?_, hs⟩, potential_finite i b s⟩
    have hx : s.physical ∈ (certificate i b).basin := by
      change (if s.physical i = b then (0 : ℝ≥0∞) else 1) ≠ ∞
      split_ifs <;> simp
    have hrec := repairProgramRecoverableAt_of_dynamicsImplements_repairThenPreserve
      (substrate i) (physical i) (target i b) (target_fixed i b) (repair i b) b
      (compiled_dynamics_implements i b)
      ((certificate i b).expectedHittingTime_ne_top_of_mem_basin hx)
    exact (repairProgramRecoverableAt_iff _ _ _ _ _).mp hrec

/-- No independent fault-envelope success hypothesis is supplied. -/
theorem actual_fault_envelope (i : Fin n) (b : Bool) :
    FiniteJointFaultEnvelope (physical i) (target i b) (certificate i b)
      (substrate i) codec b (fault i) where
  fault_stays_finite_carrier := by
    intro s hs
    have hp := (carrier_iff_program i b s).mp hs
    intro z hz
    have he : z = damage i s := by simpa [fault] using hz
    subst z
    exact (carrier_iff_program i b (damage i s)).mpr hp

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
/-- Every such fault really damages the original physical target. -/
theorem actual_fault_outside_target (i : Fin n) (b : Bool)
    (s : RepairOrganizationState (State n) Action Bool) (hs : s.repairProgram = b) :
    (damage i s).physical ∉ target i b := by
  simp [damage, target, hs]

/-- The actual existing P5 consumer now needs neither an implementation
certificate nor an independent successful fault envelope from the caller. -/
theorem assembled_enters_actual_fault_system (i : Fin n) (b : Bool) (x : State n)
    (hx : x ∈ target i b) (epsilon : NNReal) (he : epsilon ≤ 1) :
    let seed : OntogeneticConstruction.OntogeneticSeed (State n) Bool := ⟨x,b⟩
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i b) (target_fixed i b) (certificate i b)
      (substrate i) codec b (compiled_dynamics_implements i b)
      (fault i) epsilon he (actual_fault_envelope i b)
    UEOT.V3.ViabilityKernel.StaysIn
      (PMF.pure (OntogeneticConstruction.assembleRepairOrganization (substrate i) codec seed))
      S.carrier := by
  exact compiled_enters_p5 i b x hx (fault i) epsilon he (actual_fault_envelope i b)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultSource
