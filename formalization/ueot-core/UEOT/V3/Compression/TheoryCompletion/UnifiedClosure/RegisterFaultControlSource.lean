import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterResourceSource

/-! The controlled physical source including the actual P5 fault alternative.
This identifies its physical shadow; it does not silently transfer the old
fault-free control objective or its optimality theorem to this different law. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultControlSource
open Set MeasureTheory
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open RegisterRepairSource RegisterFaultSource RegisterMechanismPurpose RegisterResourceSource
open scoped ENNReal
noncomputable section

private theorem map_mix {X Y : Type*} [Fintype X] [Fintype Y]
    (f : X → Y) (Q F : PMF X) (epsilon : NNReal) (he : epsilon ≤ 1) :
    (recurrentFaultMix Q F epsilon he).map f =
      recurrentFaultMix (Q.map f) (F.map f) epsilon he := by
  classical
  ext y
  simp only [PMF.map_apply, recurrentFaultMix_apply, tsum_fintype]
  have hp : ∀ x, (if y = f x then ((1-epsilon : NNReal) : ℝ≥0∞) * Q x +
      (epsilon : ℝ≥0∞) * F x else 0) =
    ((1-epsilon : NNReal) : ℝ≥0∞) * (if y = f x then Q x else 0) +
      (epsilon : ℝ≥0∞) * (if y = f x then F x else 0) := by
    intro x
    split_ifs <;> simp
  simp_rw [hp]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Same allowed actuator, with the source's explicit environment-damage branch.
The hazard is fixed before action selection, and fault damage retains code. -/
def physicalSource {n : ℕ} (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (x : State n) (a : Action) : PMF (State n) :=
  recurrentFaultMix (physical i x a)
    (PMF.pure (Function.update x i (!m.goal))) epsilon he

private theorem repair_shadow {n : ℕ} (i : Fin n) (b : Bool)
    (s : RepairOrganizationState (State n) Action Bool) (hp : s.repairProgram = b) :
    (safeRepairKernel (substrate i) codec (physical i) s).map
      (fun z => z.physical) = physical i s.physical ((substrate i).execute b s.physical) := by
  simp [safeRepairKernel, canonicalizeRepairOrganization, canonicalRepairOrganizationState,
    codec, physical, hp, PMF.pure_map]

section ActualP5
variable {n : ℕ} [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- Actual P5 row projected to physical state, for this SAME compiled program.
Neither a kernel-identification field nor an external fault envelope is input. -/
theorem actual_P5_physical_shadow (i : Fin n) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1)
    (s : RepairOrganizationState (State n) Action Bool)
    (hs : s ∈ finiteJointRepairCarrier (physical i) (target i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal) :
    let S := finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    (S.mixedKernel s).map (fun z => z.physical) =
      physicalSource i m epsilon he s.physical ((substrate i).execute m.goal s.physical) := by
  have hp := (carrier_iff_program i m.goal s).mp hs
  dsimp only
  change (recurrentFaultMix (safeRepairKernel (substrate i) codec (physical i) s)
    (fault i s) epsilon he).map (fun z => z.physical) = _
  rw [map_mix, repair_shadow i m.goal s hp]
  simp [physicalSource, fault, damage, hp, PMF.pure_map]

end ActualP5
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultControlSource
