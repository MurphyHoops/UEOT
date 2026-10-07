import UEOT.V3.Compression.Objecthood.JointHomeostasis.FiniteBurden
import UEOT.V3.Compression.Objecthood.Homeostasis.HomeostasisSemantics
import UEOT.V3.Compression.Objecthood.Homeostasis.CesaroHomeostasis
import UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction.TightenedSameParentRestoration

namespace UEOT.V3.Compression.Objecthood.JointHomeostasis

open Set Filter Topology MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal BigOperators

universe uX uA uP uR
noncomputable section


noncomputable local instance p55SemanticDecidableEq {Ssem : Type*} :
    DecidableEq Ssem := Classical.decEq _
noncomputable local instance jointHomeostasisDecidableEq
    {X : Type uX} {A : Type uA} {Representation : Type uR} :
    DecidableEq (RepairOrganizationState X A Representation) :=
  Classical.decEq _

/-- P5.5 finite-horizon occupation bound for the full joint organizational state.
This is exactly RH3 specialized to the P5 finite-potential joint carrier and its
canonical least fault burden. -/
theorem finiteJoint_finiteHorizonDamagedOccupation
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
    (mu0 : PMF (RepairOrganizationState X A Representation))
    (hmu0 : StaysIn mu0 (finiteJointRepairCarrier P K R T codec r))
    (N : ℕ) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift) *
        (∑ n ∈ Finset.range N,
          (homeostaticMarginal S.mixedKernel mu0 n).toMeasure
            S.legitimateᶜ) ≤
      homeostaticENNExpectation mu0 S.potential +
        (N : ENNReal) *
          ((epsilon : ENNReal) *
            canonicalFaultBurden S) := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  let C : FaultBurdenCertificate S :=
    finiteJointCanonicalFaultBurdenCertificate
      P K hfix R T codec r himpl F epsilon hepsilon hF
  apply S.finiteHorizonDamagedOccupation C mu0 hmu0
  intro s hs
  exact finiteJointRecurrentHomeostasisSystem_repair_budget
    P K hfix R T codec r himpl F epsilon hepsilon hF hs

/-- P5.5 asymptotic mean joint-homeostasis certificate.  The bound controls the
Cesaro average probability of not being in exact same-program joint legitimacy.
It is a mean-occupation statement, not a pathwise recurrence theorem. -/
theorem finiteJoint_meanHomeostasis
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
    (mu0 : PMF (RepairOrganizationState X A Representation))
    (hmu0 : StaysIn mu0 (finiteJointRepairCarrier P K R T codec r))
    (hhazard : epsilon < 1) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let kappa : ENNReal :=
      ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal :=
      (epsilon : ENNReal) * canonicalFaultBurden S
    MeanHomeostasis (fun n => (D n).toReal)
      (lambda.toReal / kappa.toReal) := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  let C : FaultBurdenCertificate S :=
    finiteJointCanonicalFaultBurdenCertificate
      P K hfix R T codec r himpl F epsilon hepsilon hF
  apply S.meanHomeostasis C mu0 hmu0
  · intro s hs
    exact finiteJointRecurrentHomeostasisSystem_repair_budget
      P K hfix R T codec r himpl F epsilon hepsilon hF hs
  · intro s hs
    exact finiteJointRecurrentHomeostasisSystem_potential_ne_top
      P K hfix R T codec r himpl F epsilon hepsilon hF s hs
  · simpa [S, finiteJointRecurrentHomeostasisSystem] using hhazard

/-- P5.5 invariant/Cesaro form: at least one Cesaro subsequential limit of the
joint mixed dynamics is invariant and inherits the certified damaged-mass and
legitimate-mass bounds. -/
theorem finiteJoint_exists_invariant_cesaro_limit_with_damage_bound
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
    (mu0 : PMF (RepairOrganizationState X A Representation))
    (hmu0 : StaysIn mu0 (finiteJointRepairCarrier P K R T codec r))
    (hhazard : epsilon < 1) :
    let S := finiteJointRecurrentHomeostasisSystem
      P K hfix R T codec r himpl F epsilon hepsilon hF
    ∃ nu : stdSimplex ℝ (RepairOrganizationState X A Representation),
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧
        Tendsto
          (cesaroRow (pmfKernelMatrix S.mixedKernel)
            (pmfKernelMatrix_rowStochastic S.mixedKernel)
            (pmfSimplex mu0) ∘ phi)
          atTop (𝓝 nu) ∧
        Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
        simplexDamagedMass S.legitimate nu ≤
          ((epsilon : ENNReal) * canonicalFaultBurden S).toReal /
            (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift).toReal ∧
        1 - ((epsilon : ENNReal) * canonicalFaultBurden S).toReal /
            (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift).toReal ≤
          simplexLegitimateMass S.legitimate nu := by
  dsimp only
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  let C : FaultBurdenCertificate S :=
    finiteJointCanonicalFaultBurdenCertificate
      P K hfix R T codec r himpl F epsilon hepsilon hF
  exact S.exists_invariant_cesaro_limit_with_damage_bound
    C mu0 hmu0
    (by
      intro s hs
      exact finiteJointRecurrentHomeostasisSystem_repair_budget
        P K hfix R T codec r himpl F epsilon hepsilon hF hs)
    (by
      intro s hs
      exact finiteJointRecurrentHomeostasisSystem_potential_ne_top
        P K hfix R T codec r himpl F epsilon hepsilon hF s hs)
    (by simpa [S, finiteJointRecurrentHomeostasisSystem] using hhazard)

/-- Exact P5 joint legitimacy projects to the established constitutive
legitimacy of the same intended internal program.  This is the semantic bridge
needed to interpret the long-run joint damaged mass as same-parent Objecthood
damage rather than an unrelated state label. -/
theorem jointLegitimate_projects_to_constitutiveLegitimate
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (P : X → A → PMF X) (K : Set X)
    {r : Program}
    (hvalid : RepairProgramValid T P K r)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ jointLegitimate T codec K r) :
    repairOrganizationConstitutiveProjection s ∈
      legitimateConstitutiveDomain P K := by
  exact safeRecoveredTarget_projects_to_legitimate
    T codec P K hvalid hs


/-- Same-parent semantic interpretation of P5 joint legitimacy.  The joint state
projects to the selected parent's constitutive legitimate domain, while the
parent's pre-existing Track-X semantic-fibre bound remains available unchanged.
No semantic kernel is reconstructed by P5. -/
theorem jointLegitimate_sameParent_semantic_certificate
    {V : Type*} {Child : Type*} [Fintype Child]
    {H : Type*} {Probe : Type*}
    {Rout : Type*} {Y : Type*} [MeasurableSpace Y]
    {E : Type*} {Z : Type*} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    {Program : Type uP} {Representation : Type uR}
    {Csem : Type*}
    {Ssem : Type*} [Fintype Ssem] [Nonempty Ssem]
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ U e, IsProbabilityMeasure (response U e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (hvalid : RepairProgramValid T
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K r)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = C.semantic.child)
    {s : RepairOrganizationState X A Representation}
    (hs : s ∈ jointLegitimate T codec
      C.repairing.operational.persistence.K r) :
    repairOrganizationConstitutiveProjection s ∈
        legitimateConstitutiveDomain
          (dynamics C.repairing.operational.parent)
          C.repairing.operational.persistence.K ∧
      lawTV
        (C.semantic.invariantLaw C.repairing.operational.parent)
        (C.semantic.invariantLaw q) ≤
          C.semantic.epsilon / C.semantic.kappaMin := by
  constructor
  · exact jointLegitimate_projects_to_constitutiveLegitimate
      T codec (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K hvalid hs
  · exact C.selected_parent_pairwise_semantic_bound hcard hq


end
end UEOT.V3.Compression.Objecthood.JointHomeostasis
