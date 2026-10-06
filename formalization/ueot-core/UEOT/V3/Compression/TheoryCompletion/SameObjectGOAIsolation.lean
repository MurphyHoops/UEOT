import UEOT.V3.Compression.TheoryCompletion.SameObjectViableGOA
import UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

/-!
# P2 audit hardening — GOA uniqueness below global mixing

The P2.6 Dobrushin theorem is intentionally strong because it supplies both
uniqueness and geometric global mixing.  Uniqueness itself needs less.

For a nontrivial finite state space, positivity of the canonical direct-L1
residual conorm is exactly equivalent to uniqueness of the invariant law.
This module specializes that weaker isolation certificate to the same
Objecthood-selected greedy closed loop.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood

universe uV uChild uH uProbe uR uY uE uZ uX uA uC uS uF

noncomputable section

variable {V : Type uV} {Child : Type uChild}
variable {H : Type uH} {Probe : Type uProbe}
variable {Rout : Type uR} {Y : Type uY} [MeasurableSpace Y]
variable {E : Type uE} {Z : Type uZ} [MeasurableSpace Z]
variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Nonempty X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace (ConstitutiveState X A)]
variable [MeasurableSingletonClass (ConstitutiveState X A)]
variable {Csem : Type uC}
variable {Ssem : Type uS} [Fintype Ssem] [Nonempty Ssem]
variable {Future : Type uF}
noncomputable local instance sameObjectGoaIsolationSemanticDecidableEq :
    DecidableEq Ssem :=
  Classical.decEq Ssem

namespace ObjecthoodTeleologicalControlSpec

variable [Fintype Child]
variable
    {readout : Finset V → H → Rout}
    {p : H → Probe → Measure Y}
    {regions : Child → Finset V}
    {response : Finset Child → E → Measure Z}
    {hprob : ∀ S e, IsProbabilityMeasure (response S e)}
    {probes : Finset E}
    {dynamics : FormedCandidate readout p regions → X → A → PMF X}
    {persistenceDomain : FormedCandidate readout p regions → Set X}
    {pi : FormedCandidate readout p regions → Csem}
    {semanticKernel : FormedCandidate readout p regions → Matrix Ssem Ssem ℝ}
    {hSemanticKernel : ∀ q, semanticKernel q ∈ Matrix.rowStochastic ℝ Ssem}
    (C : SemanticallyStableSelfRepairingOperationalParent
      readout p regions response hprob probes dynamics persistenceDomain
      pi semanticKernel hSemanticKernel)

/-- Weaker P2.6 uniqueness gate: positive direct-L1 residual conorm of the
exact same-object greedy closed loop gives a unique invariant-law GOA.

No Dobrushin contraction or geometric mixing conclusion is claimed. -/
theorem existsUnique_greedyGOA_of_l1ResidualConorm_pos
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hcard : 1 < Fintype.card X)
    (hisolation :
      0 <
        UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm.l1ResidualConorm
          (UEOT.V3.Compression.AgencyGodGoaAssembly.greedyClosedLoopMatrix
            ((R.toParentRealization C).toControlModel dynamics))) :
    ∃! mu : stdSimplex ℝ X, mu ∈ R.greedyGOASet C := by
  classical
  let M := (R.toParentRealization C).toControlModel dynamics
  let P : Matrix X X ℝ :=
    UEOT.V3.Compression.AgencyGodGoaAssembly.greedyClosedLoopMatrix M
  let hP : P ∈ Matrix.rowStochastic ℝ X :=
    UEOT.V3.Compression.AgencyGodGoaAssembly.greedyClosedLoopMatrix_rowStochastic M
  have hisolation' :
      0 <
        UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm.l1ResidualConorm
          (S := X) P := by
    simpa [P, M] using hisolation
  have hunique :
      ∃! mu : stdSimplex ℝ X,
        mu ∈ UEOT.V3.Compression.InvariantSetGaugeInvariance.invariantLawSet P hP :=
    (UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation.l1ResidualConorm_pos_iff_unique_invariant_law
        (S := X) P hP hcard).1 hisolation'
  change ∃! mu : stdSimplex ℝ X,
    mu ∈ UEOT.V3.Compression.InvariantSetGaugeInvariance.invariantLawSet P hP
  exact hunique

/-- Combining the weaker residual uniqueness certificate with P2.7 viability
shows that the unique greedy GOA is supported inside the same Objecthood
persistence kernel, still without assuming global mixing. -/
theorem existsUnique_persistenceSupportedGreedyGOA_of_l1ResidualConorm_pos
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    (hcard : 1 < Fintype.card X)
    (hisolation :
      0 <
        UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm.l1ResidualConorm
          (UEOT.V3.Compression.AgencyGodGoaAssembly.greedyClosedLoopMatrix
            ((R.toParentRealization C).toControlModel dynamics))) :
    ∃ mustar : stdSimplex ℝ X,
      mustar ∈ R.persistenceSupportedGreedyGOASet C ∧
      ∀ mu : stdSimplex ℝ X,
        mu ∈ R.greedyGOASet C → mu = mustar := by
  rcases
      R.existsUnique_greedyGOA_of_l1ResidualConorm_pos C hcard hisolation with
    ⟨mustar, hmustar, hunique⟩
  rcases R.persistenceSupportedGreedyGOASet_nonempty C hviable with
    ⟨nu, hnu⟩
  have hnugoa : nu ∈ R.greedyGOASet C :=
    R.persistenceSupportedGreedyGOASet_subset_greedyGOASet C hnu
  have hnuEq : nu = mustar := hunique nu hnugoa
  refine ⟨mustar, ?_, hunique⟩
  simpa [hnuEq] using hnu

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
