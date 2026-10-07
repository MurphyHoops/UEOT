import UEOT.V3.Compression.Objecthood.ResourceClosure.FiniteReserve
import UEOT.V3.Compression.Objecthood.JointHomeostasis.TerminalClosure

namespace UEOT.V3.Compression.Objecthood.ResourceClosure

open Set Filter Topology MeasureTheory ProbabilityTheory
open UEOT.V3.ViabilityKernel
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open scoped ENNReal BigOperators

universe uV uChild uH uProbe uRout uY uE uZ
universe uX uA uP uRep uC uS
noncomputable section

noncomputable local instance p66SemanticDecidableEq {Ssem : Type uS} :
    DecidableEq Ssem := Classical.decEq _

/-- **P6.6 same-parent resource-maintenance synthesis.**

P5 supplies same-parent joint homeostasis and semantic/constitutive meaning.
P6 adds explicit abstract accounting costs.  Under one strict steady-load margin
and one transient-reserve inequality, the same certified parent has both an
asymptotic mean resource bound and finite-horizon viability of the schedule of
expected state costs.  Realized/pathwise viability remains a separate
pointwise-accounting implication and is not inferred from those average laws. -/
theorem p6_sameParent_resourceMaintenance_synthesis
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
    (Cparent : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)
    (T : TrustedRepairSubstrate Program X A)
    (codec : TrustedRepairCodec Program Representation)
    (r : Program)
    (himpl : RepairProgramDynamicsImplementsPolicy T
      (dynamics Cparent.repairing.operational.parent) r
      (repairThenPreservePolicy
        (dynamics Cparent.repairing.operational.parent)
        Cparent.repairing.operational.persistence.K
        Cparent.repairing.operational.persistence.source_fixed
        Cparent.repairing.physicalRepair.repairPolicy))
    (F : RepairOrganizationState X A Representation →
      PMF (RepairOrganizationState X A Representation))
    (epsilon : NNReal) (hepsilon : epsilon ≤ 1)
    (hF : FiniteJointFaultEnvelope
      (dynamics Cparent.repairing.operational.parent)
      Cparent.repairing.operational.persistence.K
      Cparent.repairing.physicalRepair T codec r F)
    (mu0 : PMF (RepairOrganizationState X A Representation))
    (hmu0 : StaysIn mu0
      (finiteJointRepairCarrier
        (dynamics Cparent.repairing.operational.parent)
        Cparent.repairing.operational.persistence.K
        Cparent.repairing.physicalRepair T codec r))
    (hhazard : epsilon < 1)
    (cost : ResourceCostModel) (initial supply : ℝ)
    (hreserve :
      let P := dynamics Cparent.repairing.operational.parent
      let K := Cparent.repairing.operational.persistence.K
      let R := Cparent.repairing.physicalRepair
      let S := finiteJointRecurrentHomeostasisSystem
        P K Cparent.repairing.operational.persistence.source_fixed R
        T codec r himpl F epsilon hepsilon hF
      let kappa : ENNReal :=
        ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
      let V0 := homeostaticENNExpectation mu0 S.potential
      cost.variableCost * (V0.toReal / kappa.toReal) ≤ initial)
    (hmargin :
      let P := dynamics Cparent.repairing.operational.parent
      let K := Cparent.repairing.operational.persistence.K
      let R := Cparent.repairing.physicalRepair
      let S := finiteJointRecurrentHomeostasisSystem
        P K Cparent.repairing.operational.persistence.source_fixed R
        T codec r himpl F epsilon hepsilon hF
      let rho :=
        ((epsilon : ENNReal) * canonicalFaultBurden S).toReal /
          (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift).toReal
      cost.maintenance + cost.variableCost * rho < supply)
    (hcard : 1 < Fintype.card Ssem)
    {q : FormedCandidate readout p regions}
    (hq : pi q = Cparent.semantic.child) :
    let P := dynamics Cparent.repairing.operational.parent
    let K := Cparent.repairing.operational.persistence.K
    let R := Cparent.repairing.physicalRepair
    let S := finiteJointRecurrentHomeostasisSystem
      P K Cparent.repairing.operational.persistence.source_fixed R
      T codec r himpl F epsilon hepsilon hF
    let D : ℕ → ENNReal := fun n =>
      (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
    let rho : ℝ :=
      ((epsilon : ENNReal) * canonicalFaultBurden S).toReal /
        (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift).toReal
    let actual : ℕ → ℝ := fun n =>
      pmfRealExpectation (homeostaticMarginal S.mixedKernel mu0 n)
        (stateResourceCost cost
          (fun s => s ∈ jointLegitimate T codec K r)
          (jointProgramMismatch T codec r))
    MeanHomeostasis (fun n => (D n).toReal) rho ∧
    (∀ s, s ∈ S.legitimate →
      repairOrganizationConstitutiveProjection s ∈
        legitimateConstitutiveDomain P K) ∧
    lawTV
      (Cparent.semantic.invariantLaw Cparent.repairing.operational.parent)
      (Cparent.semantic.invariantLaw q) ≤
        Cparent.semantic.epsilon / Cparent.semantic.kappaMin ∧
    (∀ᶠ n in atTop, meanRealSchedule actual n < supply) ∧
    ResourceViable initial (fun _ => supply) actual := by
  dsimp only
  let P := dynamics Cparent.repairing.operational.parent
  let K := Cparent.repairing.operational.persistence.K
  let R := Cparent.repairing.physicalRepair
  let hfix := Cparent.repairing.operational.persistence.source_fixed
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  let D : ℕ → ENNReal := fun n =>
    (homeostaticMarginal S.mixedKernel mu0 n).toMeasure S.legitimateᶜ
  let rho : ℝ :=
    ((epsilon : ENNReal) * canonicalFaultBurden S).toReal /
      (((1 - epsilon : NNReal) : ENNReal) * S.repairDrift).toReal
  let actual : ℕ → ℝ := fun n =>
    pmfRealExpectation (homeostaticMarginal S.mixedKernel mu0 n)
      (stateResourceCost cost
        (fun s => s ∈ jointLegitimate T codec K r)
        (jointProgramMismatch T codec r))
  have hp5 := p5_terminal_sameParent_joint_homeostasis
    Cparent T codec r himpl F epsilon hepsilon hF mu0 hmu0 hhazard hcard hq
  rcases hp5 with ⟨_hdrift, hmean, _hinvariant, hprojection, hsemantic⟩
  have hmeanResource := finiteJoint_eventually_meanActualResourceCost_lt_supply
    P K hfix R T codec r himpl F epsilon hepsilon hF mu0 hmu0 hhazard
    cost supply (by simpa [P, K, R, S, rho] using hmargin)
  have hexpected := finiteJoint_expectedAccountingResourceViable
    P K hfix R T codec r himpl F epsilon hepsilon hF mu0 hmu0 hhazard
    cost initial supply
    (by simpa [P, K, R, S] using hreserve)
    (by
      have hm : cost.maintenance + cost.variableCost * rho < supply := by
        simpa [P, K, R, S, rho] using hmargin
      simpa [P, K, R, S, rho] using le_of_lt hm)
  refine ⟨?_, ?_, hsemantic, ?_, ?_⟩
  · simpa [P, K, R, S, D, rho] using hmean
  · simpa [P, K, R, S] using hprojection
  · simpa [P, K, R, S, actual] using hmeanResource
  · simpa [P, K, R, S, actual] using hexpected

end
end UEOT.V3.Compression.Objecthood.ResourceClosure
