import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.TerminalClosure
import UEOT.V3.Compression.Objecthood.OntogeneticConstruction
import UEOT.V3.Compression.Objecthood.ResourceClosure.FiniteReserve
import UEOT.V3.Compression.TheoryCompletion.LineageEvolution
import UEOT.V3.Compression.TheoryCompletion.ObjectScaleCalculus
import UEOT.V3.Compression.TheoryCompletion.GeneralStateObjecthood
import UEOT.V3.Compression.TheoryCompletion.StochasticSubstrate

/-!
# Theory Completion P12 — final autopoiesis integration and boundary

P12 composes only previously proved components.  It does not define a structure
whose fields are the desired conclusions.  The finite lifecycle theorem below
uses P7/P8/P9 directly.  P4 remains an epistemic discovery/certification lane;
P10/P11 remain generalization substrates with their own explicit boundaries.

A separate no-go proves that the current P7 construction cannot be promoted to
full autonomous synthesis from the physical seed alone: if the same physical
component can carry two distinct repair-program sources, no function of that
physical component alone recovers both.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory Filter Topology
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.EvolutionPrice
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction
open UEOT.V3.Compression.Objecthood.ResourceClosure
open UEOT.V3.Compression.TheoryCompletion.InverseObjecthood

universe uX uA uP uR uO uI uXF uXC uOF uOC uOmega uCandidate

/-- P4 remains a certification input, not a constitutive field of an object. -/
theorem p12_inverseObjecthood_certification_input
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate) :
    Tendsto
      (fun n => (D.mu n).real
        {omega | ¬ D.objectClass.r (D.estimate n omega) D.truth})
      atTop (𝓝 0) :=
  D.classFailure_tendsto_zero

/-- A program synthesizer that is allowed to inspect only the physical seed
component.  This deliberately excludes the explicit program-source information
that P7 currently requires. -/
def PhysicalOnlyProgramSynthesizer
    (X : Type uX) (Program : Type uP) := X → Program

/-- Full autonomous recovery from the physical component alone is impossible on
any seed family containing the same physical component with two distinct
program sources.  The conclusion is information-theoretic, not a limitation of
one decoder implementation. -/
theorem no_physicalOnly_synthesizer_for_distinct_sources
    {X : Type uX} {Program : Type uP}
    (x : X) {r₁ r₂ : Program} (hne : r₁ ≠ r₂) :
    ¬ ∃ synth : PhysicalOnlyProgramSynthesizer X Program,
        synth x = r₁ ∧ synth x = r₂ := by
  rintro ⟨synth, h₁, h₂⟩
  apply hne
  calc
    r₁ = synth x := h₁.symm
    _ = r₂ := h₂

/-- Seed-level version of the same blocker. -/
theorem no_physicalOnly_synthesizer_for_samePhysical_distinctSeeds
    {X : Type uX} {Program : Type uP}
    (s₁ s₂ : OntogeneticSeed X Program)
    (hphysical : s₁.physicalComponent = s₂.physicalComponent)
    (hprogram : s₁.repairProgramSource ≠ s₂.repairProgramSource) :
    ¬ ∃ synth : PhysicalOnlyProgramSynthesizer X Program,
        synth s₁.physicalComponent = s₁.repairProgramSource ∧
        synth s₂.physicalComponent = s₂.repairProgramSource := by
  rintro ⟨synth, h₁, h₂⟩
  apply hprogram
  calc
    s₁.repairProgramSource = synth s₁.physicalComponent := h₁.symm
    _ = synth s₂.physicalComponent := congrArg synth hphysical
    _ = s₂.repairProgramSource := h₂

/-- Explicit maps tying the organizational, lineage and fine-scale views of one
lifecycle object.  The maps carry no success theorem; compatibility with a
particular constructed parent is a separate premise below. -/
structure LifecycleObjectBridge
    (Organization : Type*) (Object : Type*) (FineObject : Type*) where
  organizationObject : Organization → Object
  fineObject : Object → FineObject

/-- If every state in a recurrent-homeostasis carrier represents the same
lineage identity as `parent`, then every finite-time maintained marginal also
represents that same parent identity.  This is the missing bridge between
organizational state maintenance and lifecycle-object identity. -/
theorem homeostaticMarginals_preserve_lifecycleParent
    {Organization : Type*} [Fintype Organization]
    [MeasurableSpace Organization] [MeasurableSingletonClass Organization]
    {Object : Type uO} {Identity : Type uI}
    (L : LineageSemantics Object Identity)
    (organizationObject : Organization → Object)
    (parent : Object)
    (S : RecurrentHomeostasisSystem Organization)
    (mu0 : PMF Organization)
    (hmu0 : StaysIn mu0 S.carrier)
    (hcarrierParent :
      ∀ s, s ∈ S.carrier → L.SameObject (organizationObject s) parent) :
    ∀ n s,
      s ∈ (homeostaticMarginal S.mixedKernel mu0 n).support →
        L.SameObject (organizationObject s) parent := by
  have hstay : ∀ n,
      StaysIn (homeostaticMarginal S.mixedKernel mu0 n) S.carrier :=
    homeostaticMarginal_staysIn S.mixedKernel mu0 S.carrier hmu0
      (by
        intro s hs
        exact S.mixed_stays_carrier hs)
  intro n s hs
  exact hcarrierParent s (hstay n hs)

/-- P4's recovered object class can be connected to the same lifecycle parent
only through the already-required explicit parent bridge. -/
theorem p12_discovered_parent_tendsto_lifecycleParent
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    {Object : Type uO}
    (candidateParent : Candidate → Object)
    (Bparent : ObjectClassParentBridge D.objectClass candidateParent)
    (lifecycleParent : Object)
    (htruth : candidateParent D.truth = lifecycleParent) :
    Tendsto
      (fun n => (D.mu n).real
        {omega | candidateParent (D.estimate n omega) ≠ lifecycleParent})
      atTop (𝓝 0) := by
  simpa [htruth] using
    parentIdentityFailure_tendsto_zero D candidateParent Bparent

/-- **P12 structural finite lifecycle bridge.**

Unlike a mere conjunction of unrelated subsystem theorems, this statement
contains explicit bridges tying all three constitutive views to the *same*
parent:

1. P4 candidate discovery is mapped to the lifecycle parent through an
   `ObjectClassParentBridge`;
2. P7's assembled repair organization is explicitly identified with that same
   lineage parent;
3. P9 starts from the fine-scale representation of that same parent.

P8 then certifies that the declared child is a distinct offspring and supplies
the exact Price decomposition.  No bridge is inferred from type coincidence.
This theorem deliberately stops at finite-carrier entry.  The stronger terminal
theorem below additionally threads the complete P5 recurrent-maintenance and P6
resource-accounting premises. -/
theorem p12_conditional_finite_lifecycle
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (Kphysical : Set X)
    (R : PhysicalRepairCertificate P Kphysical)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program)
    (hvalid : RepairProgramValid T P Kphysical seed.repairProgramSource)
    (hx : seed.physicalComponent ∈ Kphysical)
    {Object : Type uO} {Identity : Type uI} [Fintype Object]
    (L : LineageSemantics Object Identity)
    {parent child : Object} (hoff : L.OffspringOf parent child)
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    (candidateParent : Candidate → Object)
    (Bparent : ObjectClassParentBridge D.objectClass candidateParent)
    (htruth : candidateParent D.truth = parent)
    (p b z : Object → ℝ) (Klineage : Object → Object → ℝ)
    (z' : Object → ℝ)
    (hlineage : L.ReproductiveTransmission Klineage)
    (hp0 : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hb0 : ∀ i, 0 ≤ b i)
    (hK0 : ∀ i j, 0 ≤ Klineage i j)
    (hKsum : ∀ i, ∑ j, Klineage i j = 1)
    (hbar : 0 < weightedMean p b)
    {FineState : Type uXF} {CoarseState : Type uXC}
    {FineObject : Type uOF} {CoarseObject : Type uOC}
    (B : LifecycleObjectBridge
      (RepairOrganizationState X A Representation) Object FineObject)
    (hassembledParent :
      B.organizationObject (assembleRepairOrganization T codec seed) = parent)
    (M : ObjectScaleMap FineState CoarseState FineObject CoarseObject)
    (FineProperty : FineObject → Prop) (CoarseProperty : CoarseObject → Prop)
    {coarse : CoarseObject}
    (htransport : ObjectScaleTransport M (B.fineObject parent) coarse)
    (hpreserve : PreservesObjectPredicate M FineProperty CoarseProperty)
    (hfine : FineProperty (B.fineObject parent)) :
    Tendsto
      (fun n => (D.mu n).real
        {omega | candidateParent (D.estimate n omega) ≠ parent})
      atTop (𝓝 0) ∧
    StaysIn (PMF.pure (assembleRepairOrganization T codec seed))
      (finiteJointRepairCarrier P Kphysical R T codec
        seed.repairProgramSource) ∧
    B.organizationObject (assembleRepairOrganization T codec seed) = parent ∧
    ¬ L.SameObject parent child ∧
    (offspringTraitMean (nextFrequency p b Klineage) z' - weightedMean p z =
      weightedCov p b z / weightedMean p b +
      weightedMean p
        (fun i => b i * (transmittedTrait Klineage z' i - z i)) /
        weightedMean p b) ∧
    CoarseProperty coarse := by
  have hdiscover := p12_discovered_parent_tendsto_lifecycleParent
    D candidateParent Bparent parent htruth
  have hconstruct := pure_assembled_stays_finiteMaintenanceCarrier
    P Kphysical R T codec seed hvalid hx
  have hevolution := p8_terminal_lineage_evolution L hoff p b z Klineage z'
    hlineage hp0 hpsum hb0 hK0 hKsum hbar
  have hscale := transport_object_property M FineProperty CoarseProperty
    htransport hpreserve hfine
  exact ⟨hdiscover, hconstruct, hassembledParent,
    hevolution.1, hevolution.2, hscale⟩

/-- **P12 terminal finite conditional lifecycle.**

This strengthens the structural bridge above by requiring the exact P5
recurrent-homeostasis premises and the P6 expected-accounting resource premises.
The constructed organization is therefore not merely in a finite carrier: its
Dirac initial law is admitted to the instantiated P5 system, the corresponding
mean-homeostasis bound is obtained, and the P6 expected resource schedule is
viable.  Discovery, lineage/evolution and scale transport are tied to the same
lifecycle parent through the same explicit bridges as above.

The theorem is still conditional and finite.  It does not synthesize the repair
program, codec/interpreter, fault model, resource model, lineage relation or
scale-preservation law. -/
theorem p12_terminal_conditional_finite_lifecycle
    {X : Type uX} {A : Type uA}
    {Program : Type uP} {Representation : Type uR}
    [Fintype X] [Fintype A] [Nonempty A] [Fintype Representation]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : X → A → PMF X) (Kphysical : Set X)
    (hfix : viabilityStep P Kphysical = Kphysical)
    (R : PhysicalRepairCertificate P Kphysical)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (seed : OntogeneticSeed X Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T P
      seed.repairProgramSource
      (repairThenPreservePolicy P Kphysical hfix R.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : FiniteJointFaultEnvelope P Kphysical R T codec
      seed.repairProgramSource F)
    (hhazard : epsilon < 1)
    (hx : seed.physicalComponent ∈ Kphysical)
    (Cresource : ResourceCostModel) (initial supply : ℝ)
    (hreserve :
      let S := finiteJointRecurrentHomeostasisSystem
        P Kphysical hfix R T codec seed.repairProgramSource himpl
        F epsilon hepsilon hF
      let mu0 := PMF.pure (assembleRepairOrganization T codec seed)
      let kappa : ENNReal :=
        ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
      let V0 := homeostaticENNExpectation mu0 S.potential
      Cresource.variableCost * (V0.toReal / kappa.toReal) ≤ initial)
    (hsupply :
      let S := finiteJointRecurrentHomeostasisSystem
        P Kphysical hfix R T codec seed.repairProgramSource himpl
        F epsilon hepsilon hF
      let kappa : ENNReal :=
        ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
      let lambda : ENNReal :=
        (epsilon : ENNReal) * canonicalFaultBurden S
      Cresource.maintenance +
          Cresource.variableCost * (lambda.toReal / kappa.toReal) ≤ supply)
    {Object : Type uO} {Identity : Type uI} [Fintype Object]
    (L : LineageSemantics Object Identity)
    {parent child : Object} (hoff : L.OffspringOf parent child)
    {Omega : ℕ → Type uOmega} [∀ n, MeasurableSpace (Omega n)]
    {Candidate : Type uCandidate}
    (D : ChangingObjectClassDiscoveryContract Omega Candidate)
    (candidateParent : Candidate → Object)
    (Bparent : ObjectClassParentBridge D.objectClass candidateParent)
    (htruth : candidateParent D.truth = parent)
    (p b z : Object → ℝ) (Klineage : Object → Object → ℝ)
    (z' : Object → ℝ)
    (hlineage : L.ReproductiveTransmission Klineage)
    (hp0 : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hb0 : ∀ i, 0 ≤ b i)
    (hK0 : ∀ i j, 0 ≤ Klineage i j)
    (hKsum : ∀ i, ∑ j, Klineage i j = 1)
    (hbar : 0 < weightedMean p b)
    {FineState : Type uXF} {CoarseState : Type uXC}
    {FineObject : Type uOF} {CoarseObject : Type uOC}
    (B : LifecycleObjectBridge
      (RepairOrganizationState X A Representation) Object FineObject)
    (hassembledParent :
      B.organizationObject (assembleRepairOrganization T codec seed) = parent)
    (hcarrierSameParent :
      ∀ s,
        s ∈ finiteJointRepairCarrier P Kphysical R T codec
          seed.repairProgramSource →
        L.SameObject (B.organizationObject s) parent)
    (M : ObjectScaleMap FineState CoarseState FineObject CoarseObject)
    (FineProperty : FineObject → Prop) (CoarseProperty : CoarseObject → Prop)
    {coarse : CoarseObject}
    (htransport : ObjectScaleTransport M (B.fineObject parent) coarse)
    (hpreserve : PreservesObjectPredicate M FineProperty CoarseProperty)
    (hfine : FineProperty (B.fineObject parent)) :
    let S := finiteJointRecurrentHomeostasisSystem
      P Kphysical hfix R T codec seed.repairProgramSource himpl
      F epsilon hepsilon hF
    let mu0 := PMF.pure (assembleRepairOrganization T codec seed)
    let Ddamage : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let kappa : ENNReal :=
      ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let lambda : ENNReal :=
      (epsilon : ENNReal) * canonicalFaultBurden S
    let actualCost : ℕ → ℝ := fun n =>
      pmfRealExpectation (homeostaticMarginal S.mixedKernel mu0 n)
        (stateResourceCost Cresource
          (fun s => s ∈ jointLegitimate T codec Kphysical seed.repairProgramSource)
          (jointProgramMismatch T codec seed.repairProgramSource))
    Tendsto
      (fun n => (D.mu n).real
        {omega | candidateParent (D.estimate n omega) ≠ parent})
      atTop (𝓝 0) ∧
    StaysIn mu0 S.carrier ∧
    (∀ n s,
      s ∈ (homeostaticMarginal S.mixedKernel mu0 n).support →
        L.SameObject (B.organizationObject s) parent) ∧
    MeanHomeostasis (fun n => (Ddamage n).toReal)
      (lambda.toReal / kappa.toReal) ∧
    ResourceViable initial (fun _ => supply) actualCost ∧
    B.organizationObject (assembleRepairOrganization T codec seed) = parent ∧
    ¬ L.SameObject parent child ∧
    (offspringTraitMean (nextFrequency p b Klineage) z' - weightedMean p z =
      weightedCov p b z / weightedMean p b +
      weightedMean p
        (fun i => b i * (transmittedTrait Klineage z' i - z i)) /
        weightedMean p b) ∧
    CoarseProperty coarse := by
  dsimp only
  let mu0 : PMF (RepairOrganizationState X A Representation) :=
    PMF.pure (assembleRepairOrganization T codec seed)
  have hentrySystem :=
    pure_assembled_stays_p5MaintenanceSystem
      P Kphysical hfix R T codec seed himpl F epsilon hepsilon hF hx
  have hentry : StaysIn mu0
      (finiteJointRepairCarrier P Kphysical R T codec seed.repairProgramSource) := by
    change StaysIn (PMF.pure (assembleRepairOrganization T codec seed))
      (finiteJointRepairCarrier P Kphysical R T codec seed.repairProgramSource)
      at hentrySystem
    simpa [mu0] using hentrySystem
  have hmean := finiteJoint_meanHomeostasis
    P Kphysical hfix R T codec seed.repairProgramSource himpl
    F epsilon hepsilon hF mu0 hentry hhazard
  have hresource := finiteJoint_expectedAccountingResourceViable
    P Kphysical hfix R T codec seed.repairProgramSource himpl
    F epsilon hepsilon hF mu0 hentry hhazard
    Cresource initial supply
    (by simpa [mu0] using hreserve)
    (by simpa using hsupply)
  have hsameParent :=
    homeostaticMarginals_preserve_lifecycleParent
      L B.organizationObject parent
      (finiteJointRecurrentHomeostasisSystem
        P Kphysical hfix R T codec seed.repairProgramSource himpl
        F epsilon hepsilon hF)
      mu0 hentry
      (by
        intro s hs
        exact hcarrierSameParent s hs)
  have hstructural := p12_conditional_finite_lifecycle
    P Kphysical R T codec seed
    (repairProgramValid_of_dynamicsImplements_repairThenPreserve
      T P Kphysical hfix R.repairPolicy seed.repairProgramSource himpl)
    hx L hoff D candidateParent Bparent htruth p b z Klineage z'
    hlineage hp0 hpsum hb0 hK0 hKsum hbar B hassembledParent
    M FineProperty CoarseProperty htransport hpreserve hfine
  rcases hstructural with
    ⟨hdiscover, _hcarrier, hparent, hdistinct, hprice, hscale⟩
  refine ⟨hdiscover, ?_, ?_, ?_, ?_, hparent, hdistinct, hprice, hscale⟩
  · change StaysIn mu0
      (finiteJointRepairCarrier P Kphysical R T codec seed.repairProgramSource)
    exact hentry
  · simpa [mu0] using hsameParent
  · simpa [mu0] using hmean
  · simpa [mu0] using hresource

end UEOT.V3.Compression.TheoryCompletion
