import UEOT.V3.Compression.Objecthood.JointHomeostasis.JointFaultSystem
import UEOT.V3.Compression.Objecthood.Homeostasis.CanonicalBurden.CanonicalFaultBurden

namespace UEOT.V3.Compression.Objecthood.JointHomeostasis

open Set MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal BigOperators

universe uX uA uP uR
noncomputable section

/-- Quantitative refinement of the broad P5.1 repair carrier: the joint
Lyapunov potential itself is finite. -/
def finiteJointRepairCarrier
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program) : Set (RepairOrganizationState X A Representation) :=
  {s | s ∈ jointRepairCarrier T codec P K r ∧
    jointRepairPotential P K R T codec r s ≠ ∞}

/-- Exact joint legitimacy lies in the finite-potential carrier. -/
theorem jointLegitimate_subset_finiteJointRepairCarrier
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (hvalid : RepairProgramValid T P K r) :
    jointLegitimate T codec K r ⊆
      finiteJointRepairCarrier P K R T codec r := by
  intro s hs
  refine ⟨jointLegitimate_subset_jointRepairCarrier
      T codec P K r hvalid hs, ?_⟩
  rcases hs with ⟨x, hxK, rfl⟩
  rw [jointRepairPotential_canonical_eq_zero_of_mem_target
    P K R T codec r hvalid hxK]
  simp

private theorem support_potential_ne_top_of_lintegral_ne_top
    {Z : Type*} [Fintype Z]
    [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (Q : PMF Z) (W : Z → ENNReal)
    (hInt : (∫⁻ z, W z ∂Q.toMeasure) ≠ ∞)
    {w : Z} (hw : w ∈ Q.support) :
    W w ≠ ∞ := by
  have hterm : W w * Q w ≤ (∫⁻ z, W z ∂Q.toMeasure) := by
    rw [lintegral_fintype]
    simp_rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
    exact Finset.single_le_sum
      (fun z _ => (show (0 : ENNReal) ≤ W z * Q z from bot_le))
      (Finset.mem_univ w)
  have hprod : W w * Q w ≠ ∞ := ne_top_of_le_ne_top hInt hterm
  intro hW
  have hQ0 : Q w ≠ 0 := (PMF.mem_support_iff Q w).1 hw
  apply hprod
  exact (ENNReal.mul_eq_top).2 (Or.inr ⟨hW, hQ0⟩)

/-- The safe repair kernel also preserves the finite-potential refinement. -/
theorem safeRepairKernel_stays_finiteJointRepairCarrier
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
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ finiteJointRepairCarrier P K R T codec r) :
    StaysIn (safeRepairKernel T codec P s)
      (finiteJointRepairCarrier P K R T codec r) := by
  have hvalid : RepairProgramValid T P K r :=
    repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P K hfix R.repairPolicy r himpl
  intro w hw
  refine ⟨safeRepairKernel_stays_jointRepairCarrier
      T codec P K r hvalid hs.1 hw, ?_⟩
  by_cases hleg : s ∈ jointLegitimate T codec K r
  · have hstay : StaysIn (safeRepairKernel T codec P s)
        (jointLegitimate T codec K r) := by
      rcases hleg with ⟨x, hxK, rfl⟩
      exact safeRepairKernel_staysIn_recoveredTarget
        T codec P K hvalid hxK
    have hwLeg := hstay hw
    rcases hwLeg with ⟨x, hxK, rfl⟩
    rw [jointRepairPotential_canonical_eq_zero_of_mem_target
      P K R T codec r hvalid hxK]
    simp
  · have hdrift := safeRepairKernel_jointRepairPotential_drift
      P K hfix R T codec r himpl hs.1 hleg
    have hIntLe :
        (∫⁻ z, jointRepairPotential P K R T codec r z
          ∂(safeRepairKernel T codec P s).toMeasure) ≤
        jointRepairPotential P K R T codec r s :=
      le_trans (le_add_right le_rfl) hdrift
    have hInt :
        (∫⁻ z, jointRepairPotential P K R T codec r z
          ∂(safeRepairKernel T codec P s).toMeasure) ≠ ∞ :=
      ne_top_of_le_ne_top hs.2 hIntLe
    exact support_potential_ne_top_of_lintegral_ne_top
      (safeRepairKernel T codec P s)
      (jointRepairPotential P K R T codec r) hInt hw

/-- Stronger P5 fault envelope required for quantitative finite-burden RH:
fault successors remain in the finite-potential subcarrier. -/
structure FiniteJointFaultEnvelope
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (K : Set X)
    (R : PhysicalRepairCertificate P K)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation)) : Prop where
  fault_stays_finite_carrier :
    ∀ s, s ∈ finiteJointRepairCarrier P K R T codec r →
      StaysIn (F s) (finiteJointRepairCarrier P K R T codec r)

/-- Quantitative P5 recurrent-homeostasis system on the finite-potential carrier. -/
noncomputable def finiteJointRecurrentHomeostasisSystem
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
    (hF : FiniteJointFaultEnvelope P K R T codec r F) :
    RecurrentHomeostasisSystem
      (RepairOrganizationState X A Representation) := by
  have hvalid : RepairProgramValid T P K r :=
    repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P K hfix R.repairPolicy r himpl
  exact
    { legitimate := jointLegitimate T codec K r
      carrier := finiteJointRepairCarrier P K R T codec r
      repairKernel := safeRepairKernel T codec P
      faultKernel := F
      faultHazard := epsilon
      faultHazard_le_one := hepsilon
      potential := jointRepairPotential P K R T codec r
      repairDrift := R.drift
      repairDrift_ne_zero := R.drift_ne_zero
      repairDrift_ne_top := R.drift_ne_top
      legitimate_subset_carrier :=
        jointLegitimate_subset_finiteJointRepairCarrier
          P K R T codec r hvalid
      repair_stays_carrier := by
        intro s hs
        exact safeRepairKernel_stays_finiteJointRepairCarrier
          P K hfix R T codec r himpl hs
      fault_stays_carrier := by
        intro s hs
        exact hF.fault_stays_finite_carrier s hs }

/-- Carrier-potential finiteness is now definitional, not an extra theorem
assumption supplied by users of P5. -/
theorem finiteJointRecurrentHomeostasisSystem_potential_ne_top
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
    (hF : FiniteJointFaultEnvelope P K R T codec r F) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    ∀ s, s ∈ S.carrier → S.potential s ≠ ∞ := by
  dsimp only
  intro s hs
  exact hs.2


/-- The finite-potential refinement satisfies the same repair-side RH2 budget
as the broad P5.3 system. -/
theorem finiteJointRecurrentHomeostasisSystem_repair_budget
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
    (hF : FiniteJointFaultEnvelope P K R T codec r F)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ finiteJointRepairCarrier P K R T codec r) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    (∫⁻ w, S.potential w ∂(S.repairKernel s).toMeasure) +
        S.damagePenalty s ≤ S.potential s := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
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
    simpa [S, finiteJointRecurrentHomeostasisSystem,
      RecurrentHomeostasisSystem.damagePenalty, hleg, hpot0] using hzero
  · have hdrift := safeRepairKernel_jointRepairPotential_drift
      P K hfix R T codec r himpl hs.1 hleg
    simpa [S, finiteJointRecurrentHomeostasisSystem,
      RecurrentHomeostasisSystem.damagePenalty, hleg] using hdrift

/-- Canonical least finite fault-burden certificate for the quantitative joint
system.  Finiteness is derived from the carrier definition rather than supplied
as an external burden hypothesis. -/
noncomputable def finiteJointCanonicalFaultBurdenCertificate
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
    (hF : FiniteJointFaultEnvelope P K R T codec r F) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    FaultBurdenCertificate S := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  exact canonicalFaultBurdenCertificate S
    (finiteJointRecurrentHomeostasisSystem_potential_ne_top
      P K hfix R T codec r himpl F epsilon hepsilon hF)

/-- **P5.4 canonical mixed joint drift.**  The new organizational layer now
consumes the generic RH2 algebra unchanged.  Repair capacity is the original
P-REC drift; fault load is the canonical least burden of the full joint fault
kernel on the finite-potential carrier. -/
theorem finiteJoint_mixedHomeostaticDrift_canonical
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
    (hF : FiniteJointFaultEnvelope P K R T codec r F)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ finiteJointRepairCarrier P K R T codec r) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    (∫⁻ w, S.potential w ∂(S.mixedKernel s).toMeasure) +
        ((1 - epsilon : NNReal) : ENNReal) * S.damagePenalty s ≤
      S.potential s +
        (epsilon : ENNReal) * canonicalFaultBurden S := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  let C : FaultBurdenCertificate S :=
    finiteJointCanonicalFaultBurdenCertificate
      P K hfix R T codec r himpl F epsilon hepsilon hF
  have hrepair := finiteJointRecurrentHomeostasisSystem_repair_budget
    P K hfix R T codec r himpl F epsilon hepsilon hF hs
  have hmixed := mixedHomeostaticDrift S C hs hrepair
  change
    (∫⁻ w, S.potential w ∂(S.mixedKernel s).toMeasure) +
        ((1 - S.faultHazard : NNReal) : ENNReal) * S.damagePenalty s ≤
      S.potential s + (S.faultHazard : ENNReal) * C.burden
  exact hmixed

end
end UEOT.V3.Compression.Objecthood.JointHomeostasis
