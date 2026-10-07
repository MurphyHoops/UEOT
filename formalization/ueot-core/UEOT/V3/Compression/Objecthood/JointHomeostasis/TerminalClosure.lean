import UEOT.V3.Compression.Objecthood.JointHomeostasis.LongRunHomeostasis
import UEOT.V3.Compression.Objecthood.JointHomeostasis.Boundaries

/-!
# Theory Completion P5.7 — terminal joint-homeostasis closure

The terminal theorem binds the quantitative joint recurrent-homeostasis system
to one already certified semantic/self-repairing parent.  It composes only
previously proved P5/RH/RLSR/Track-X surfaces:

* canonical mixed drift on the finite joint repair carrier;
* asymptotic mean damaged-organizational occupation;
* existence of an invariant Cesaro subsequential limit with damage/legitimacy
  bounds;
* projection of exact joint legitimacy back to the same parent's constitutive
  legitimate domain and retention of its independent Track-X semantic bound.

It does not claim pathwise perpetual legitimacy, arbitrary program corruption,
resource closure, ontogenetic self-construction, or semantic-kernel repair.
-/

namespace UEOT.V3.Compression.Objecthood.JointHomeostasis

open Set Filter Topology MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.FiniteCesaroInvariant
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal BigOperators

universe uV uChild uH uProbe uRout uY uE uZ
universe uX uA uP uRep uC uS
noncomputable section

noncomputable local instance p57SemanticDecidableEq {Ssem : Type uS} :
    DecidableEq Ssem := Classical.decEq _

noncomputable local instance p57JointDecidableEq
    {X : Type uX} {A : Type uA} {Representation : Type uRep} :
    DecidableEq (RepairOrganizationState X A Representation) :=
  Classical.decEq _

/-- **P5 terminal finite joint-homeostasis closure for one same parent.**

The recurrent fault row may corrupt physical state, stored controller and repair
program simultaneously, but every fault successor must remain in the declared
finite-potential same-program carrier.  The repaired program implements the
selected parent's existing repair-then-preserve policy.

Under those explicit conditions, the same parent obtains a canonical joint
mixed-drift certificate, RH mean/invariant homeostasis bounds, constitutive
legitimacy on exact joint recovery, and its pre-existing Track-X semantic
stability bound. -/
theorem p5_terminal_sameParent_joint_homeostasis
    {V : Type uV} {Child : Type uChild} [Fintype Child]
    {H : Type uH} {Probe : Type uProbe}
    {Rout : Type uRout} {Y : Type uY} [MeasurableSpace Y]
    {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    {Program : Type uP} {Representation : Type uRep}
    [Fintype Representation]
    {Csem : Type uC}
    {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
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
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics C.repairing.operational.parent) r
      (repairThenPreservePolicy
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K
        C.repairing.operational.persistence.source_fixed
        C.repairing.physicalRepair.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : FiniteJointFaultEnvelope
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K
      C.repairing.physicalRepair T codec r F)
    (mu0 : PMF (RepairOrganizationState X A Representation))
    (hmu0 : StaysIn mu0
      (finiteJointRepairCarrier
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K
        C.repairing.physicalRepair T codec r))
    (hhazard : epsilon < 1)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = C.semantic.child) :
    let P := dynamics C.repairing.operational.parent
    let K := C.repairing.operational.persistence.K
    let R := C.repairing.physicalRepair
    let S := finiteJointRecurrentHomeostasisSystem
      P K C.repairing.operational.persistence.source_fixed R
      T codec r himpl F epsilon hepsilon hF
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let kappa : ENNReal :=
      ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal :=
      (epsilon : ENNReal) * canonicalFaultBurden S
    (∀ s, s ∈ S.carrier →
      (∫⁻ w, S.potential w ∂(S.mixedKernel s).toMeasure) +
          ((1 - epsilon : NNReal) : ENNReal) * S.damagePenalty s ≤
        S.potential s +
          (epsilon : ENNReal) * canonicalFaultBurden S) ∧
    MeanHomeostasis (fun n => (D n).toReal)
      (lambda.toReal / kappa.toReal) ∧
    (∃ nu : stdSimplex ℝ (RepairOrganizationState X A Representation),
      ∃ phi : ℕ → ℕ,
        StrictMono phi ∧
        Tendsto
          (cesaroRow (pmfKernelMatrix S.mixedKernel)
            (pmfKernelMatrix_rowStochastic S.mixedKernel)
            (pmfSimplex mu0) ∘ phi)
          atTop (𝓝 nu) ∧
        Matrix.vecMul nu.1 (pmfKernelMatrix S.mixedKernel) = nu.1 ∧
        simplexDamagedMass S.legitimate nu ≤
          lambda.toReal / kappa.toReal ∧
        1 - lambda.toReal / kappa.toReal ≤
          simplexLegitimateMass S.legitimate nu) ∧
    (∀ s, s ∈ S.legitimate →
      repairOrganizationConstitutiveProjection s ∈
        legitimateConstitutiveDomain P K) ∧
    lawTV
      (C.semantic.invariantLaw C.repairing.operational.parent)
      (C.semantic.invariantLaw q) ≤
        C.semantic.epsilon / C.semantic.kappaMin := by
  dsimp only
  let P := dynamics C.repairing.operational.parent
  let K := C.repairing.operational.persistence.K
  let R := C.repairing.physicalRepair
  let hfix := C.repairing.operational.persistence.source_fixed
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  have hvalid : RepairProgramValid T P K r :=
    repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P K hfix R.repairPolicy r himpl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    change s ∈ finiteJointRepairCarrier P K R T codec r at hs
    exact finiteJoint_mixedHomeostaticDrift_canonical
      P K hfix R T codec r himpl F epsilon hepsilon hF hs
  · exact finiteJoint_meanHomeostasis
      P K hfix R T codec r himpl F epsilon hepsilon hF
      mu0 hmu0 hhazard
  · exact finiteJoint_exists_invariant_cesaro_limit_with_damage_bound
      P K hfix R T codec r himpl F epsilon hepsilon hF
      mu0 hmu0 hhazard
  · intro s hs
    change s ∈ jointLegitimate T codec K r at hs
    exact jointLegitimate_projects_to_constitutiveLegitimate
      T codec P K hvalid hs
  · exact C.selected_parent_pairwise_semantic_bound hcard hq

end
end UEOT.V3.Compression.Objecthood.JointHomeostasis
