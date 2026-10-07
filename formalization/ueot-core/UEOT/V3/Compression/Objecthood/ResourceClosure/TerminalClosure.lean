import UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceMaintenanceSynthesis

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

noncomputable local instance p67SemanticDecidableEq {Ssem : Type uS} :
    DecidableEq Ssem := Classical.decEq _

/-- **P6 terminal same-parent resource closure.**

P6.6 supplies same-parent joint homeostasis plus mean and expected-accounting
resource closure.  The terminal theorem adds one realized-cost schedule only
under an explicit pointwise affordability hypothesis.  Pathwise viability is
therefore strengthened by a new realized-cost premise, never inferred from the
mean or expected conclusions. -/
theorem p6_terminal_sameParent_resourceClosure
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
    (realizedCost : ℕ → ℝ)
    (hrealized : ∀ n, realizedCost n ≤ supply)
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
    ResourceViable initial (fun _ => supply) actual ∧
    ResourceViable initial (fun _ => supply) realizedCost := by
  dsimp only
  let P := dynamics Cparent.repairing.operational.parent
  let K := Cparent.repairing.operational.persistence.K
  let R := Cparent.repairing.physicalRepair
  let hfix := Cparent.repairing.operational.persistence.source_fixed
  let S := finiteJointRecurrentHomeostasisSystem
    P K hfix R T codec r himpl F epsilon hepsilon hF
  have hsynth := p6_sameParent_resourceMaintenance_synthesis
    Cparent T codec r himpl F epsilon hepsilon hF mu0 hmu0 hhazard
    cost initial supply hreserve hmargin hcard hq
  rcases hsynth with ⟨hmean, hprojection, hsemantic, hmeanResource, hexpected⟩
  have hinit : 0 ≤ initial := by
    let kappa : ENNReal :=
      ((1 - epsilon : NNReal) : ENNReal) * S.repairDrift
    let V0 : ENNReal := homeostaticENNExpectation mu0 S.potential
    have hterm : 0 ≤ cost.variableCost * (V0.toReal / kappa.toReal) := by
      exact mul_nonneg cost.variableCost_nonneg
        (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    exact hterm.trans (by simpa [P, K, R, S, kappa, V0] using hreserve)
  have hpath : ResourceViable initial (fun _ => supply) realizedCost :=
    resourceViable_of_pointwise_cost_le_replenish
      initial (fun _ => supply) realizedCost hinit hrealized
  exact ⟨hmean, hprojection, hsemantic, hmeanResource, hexpected, hpath⟩

end
end UEOT.V3.Compression.Objecthood.ResourceClosure
