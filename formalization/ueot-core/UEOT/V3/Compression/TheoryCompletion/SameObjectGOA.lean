import UEOT.V3.Compression.TheoryCompletion.SameObjectObjecthoodAnchor
import UEOT.V3.Compression.TheoryCompletion.GOA

/-!
# P2.5 — GOA existence for the same canonical Objecthood parent

This stage proves existence only. It does not add uniqueness, irreducibility,
mixing, or policy-level teleological faithfulness.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.Compression.AgencyGodGoaAssembly
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
noncomputable local instance sameObjectGoaSemanticDecidableEq :
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

/-- The invariant-law GOA set of the Bellman-greedy closed loop induced from
the exact selected Objecthood parent. -/
def greedyGOASet
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    Set (stdSimplex ℝ X) :=
  GreedyInvariantGOASet
    ((R.toParentRealization C).toControlModel dynamics)

/-- P2.5: the same selected Objecthood parent has at least one invariant-law
GOA under the greedy closed loop of its induced control model.

No uniqueness, irreducibility, Dobrushin contraction or global mixing is used. -/
theorem greedyGOASet_nonempty
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    (R.greedyGOASet C).Nonempty := by
  exact greedyInvariantGOASet_nonempty
    ((R.toParentRealization C).toControlModel dynamics)

/-- Membership in the object-specialized GOA set is exactly invariant-law GOA
membership for the induced greedy closed-loop kernel. -/
theorem mem_greedyGOASet_iff
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (mu : stdSimplex ℝ X) :
    mu ∈ R.greedyGOASet C ↔
      InvariantLawGOA
        (greedyClosedLoopMatrix
          ((R.toParentRealization C).toControlModel dynamics))
        (greedyClosedLoopMatrix_rowStochastic
          ((R.toParentRealization C).toControlModel dynamics))
        mu := by
  rfl

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
