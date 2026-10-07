import UEOT.V3.Compression.Objecthood.JointHomeostasis.JointPotential
import UEOT.V3.Compression.Objecthood.Homeostasis.MixedHomeostaticDrift

/-!
# Theory Completion P5.3 — recurrent joint fault system

The older RLSR recurrent-fault path law deliberately models a macro-step that
starts on the canonical recovered manifold, applies organizational damage that
leaves physical state fixed, and then repairs before the next physical step.
P5 needs the stronger recurrent-homeostasis interface: a fault row may also
move physical state, provided the entire successor remains inside the declared
joint repair carrier.

The envelope below therefore allows simultaneously:

* physical faults anywhere inside the finite expected-return basin;
* arbitrary stored-controller corruption;
* arbitrary repair-program representation changes that still decode to the
  same intended program.

No fault outside that carrier is hidden by the positive theorem.
-/

namespace UEOT.V3.Compression.Objecthood.JointHomeostasis

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal

universe uX uA uP uR

noncomputable section

/-- Full P5 fault envelope on the mutable joint organization state.  Controller
corruption is intentionally unconstrained. -/
structure JointFaultEnvelope
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X) (r : Program)
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation)) : Prop where
  physical_repairable :
    ∀ s, s ∈ jointRepairCarrier T codec P K r →
      ∀ w ∈ (F s).support,
        w.physical ∈ StationaryRepairBasin P K (T.execute r)
  decode_preserved :
    ∀ s, s ∈ jointRepairCarrier T codec P K r →
      ∀ w ∈ (F s).support,
        codec.decode w.repairProgram = r

namespace JointFaultEnvelope

/-- The explicit physical/decode clauses are exactly sufficient for RH carrier
support closure. -/
theorem stays_jointRepairCarrier
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    {T : TrustedRepairSubstrate Program X A}
    {codec : TrustedRepairCodec Program Representation}
    {P : X → A → PMF X} {K : Set X} {r : Program}
    {F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation)}
    (E : JointFaultEnvelope T codec P K r F)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ jointRepairCarrier T codec P K r) :
    StaysIn (F s) (jointRepairCarrier T codec P K r) := by
  intro w hw
  exact ⟨E.physical_repairable s hs w hw,
    E.decode_preserved s hs w hw⟩

end JointFaultEnvelope

/-- The P5 joint system is a direct instantiation of the already proved generic
RH state machine.  Its repair kernel is RLSR's mode-free safe kernel; its
potential is the minimal P5 joint potential; only the fault envelope is new. -/
noncomputable def jointRecurrentHomeostasisSystem
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Nonempty A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P r
      (repairThenPreservePolicy P K hfix R.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : JointFaultEnvelope T codec P K r F) :
    RecurrentHomeostasisSystem
      (RepairOrganizationState X A Representation) := by
  have hvalid : RepairProgramValid T P K r :=
    repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P K hfix R.repairPolicy r himpl
  exact
    { legitimate := jointLegitimate T codec K r
      carrier := jointRepairCarrier T codec P K r
      repairKernel := safeRepairKernel T codec P
      faultKernel := F
      faultHazard := epsilon
      faultHazard_le_one := hepsilon
      potential := jointRepairPotential P K R T codec r
      repairDrift := R.drift
      repairDrift_ne_zero := R.drift_ne_zero
      repairDrift_ne_top := R.drift_ne_top
      legitimate_subset_carrier :=
        jointLegitimate_subset_jointRepairCarrier
          T codec P K r hvalid
      repair_stays_carrier := by
        intro s hs
        exact safeRepairKernel_stays_jointRepairCarrier
          T codec P K r hvalid hs
      fault_stays_carrier := by
        intro s hs
        exact hF.stays_jointRepairCarrier hs }

/-- On exact joint legitimacy, the safe repair kernel has zero expected joint
potential. -/
theorem safeRepairKernel_jointRepairPotential_zero_of_jointLegitimate
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (hvalid : RepairProgramValid T P K r)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ jointLegitimate T codec K r) :
    (∫⁻ w, jointRepairPotential P K R T codec r w
      ∂(safeRepairKernel T codec P s).toMeasure) = 0 := by
  classical
  rcases hs with ⟨x, hxK, rfl⟩
  rw [safeRepairKernel_canonical]
  let f : X → RepairOrganizationState X A Representation :=
    canonicalRepairOrganizationState T codec r
  have hf : Measurable f := measurable_of_finite f
  have hInt : Measurable (jointRepairPotential P K R T codec r) :=
    measurable_of_finite _
  have hm :
      (P x (T.execute r x)).toMeasure.map f =
        ((P x (T.execute r x)).map f).toMeasure :=
    PMF.toMeasure_map f (P x (T.execute r x)) hf
  rw [← hm, lintegral_map hInt hf, lintegral_fintype]
  apply Finset.sum_eq_zero
  intro y hyuniv
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton y)]
  by_cases hy0 : P x (T.execute r x) y = 0
  · simp [hy0]
  · have hys : y ∈ (P x (T.execute r x)).support :=
      (PMF.mem_support_iff _ _).2 hy0
    have hyK : y ∈ K := hvalid x hxK hys
    have hpot0 := jointRepairPotential_canonical_eq_zero_of_mem_target
      P K R T codec r hvalid hyK
    simp [f, hpot0]

/-- The concrete P5 system satisfies exactly the repair-side budget expected by
RH2: damaged states pay one existing repair-drift unit; legitimate states have
zero potential before and after the safe step. -/
theorem jointRecurrentHomeostasisSystem_repair_budget
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Nonempty A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P r
      (repairThenPreservePolicy P K hfix R.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : JointFaultEnvelope T codec P K r F)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ jointRepairCarrier T codec P K r) :
    let S := jointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    (∫⁻ w, S.potential w ∂(S.repairKernel s).toMeasure) +
        S.damagePenalty s ≤ S.potential s := by
  dsimp only
  let S := jointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  have hvalid : RepairProgramValid T P K r :=
    repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P K hfix R.repairPolicy r himpl
  by_cases hleg : s ∈ jointLegitimate T codec K r
  · have hzero :=
      safeRepairKernel_jointRepairPotential_zero_of_jointLegitimate
        P K R T codec r hvalid hleg
    have hpot0 : jointRepairPotential P K R T codec r s = 0 := by
      rcases hleg with ⟨x, hxK, rfl⟩
      exact jointRepairPotential_canonical_eq_zero_of_mem_target
        P K R T codec r hvalid hxK
    simpa [S, jointRecurrentHomeostasisSystem,
      RecurrentHomeostasisSystem.damagePenalty, hleg, hpot0] using hzero
  · have hdrift := safeRepairKernel_jointRepairPotential_drift
      P K hfix R T codec r himpl hs hleg
    simpa [S, jointRecurrentHomeostasisSystem,
      RecurrentHomeostasisSystem.damagePenalty, hleg] using hdrift

end
end UEOT.V3.Compression.Objecthood.JointHomeostasis
