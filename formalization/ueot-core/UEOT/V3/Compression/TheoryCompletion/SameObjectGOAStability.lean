import UEOT.V3.Compression.TheoryCompletion.SameObjectGOA
import UEOT.V3.Compression.ContractiveFixedPoint

/-!
# P2.6 — Conditional uniqueness and geometric stability of the same-object GOA

The stronger conclusions in this module require an explicit Dobrushin margin.
They are not consequences of GOA existence alone.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.FiniteDobrushin
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
noncomputable local instance sameObjectGoaStabilitySemanticDecidableEq :
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

/-- P2.6: under an explicit Dobrushin margin, the greedy closed loop of the
same canonical Objecthood parent has one unique invariant-law GOA and every
initial law converges to it at the canonical geometric TV rate. -/
theorem existsUnique_stable_greedyGOA
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (halpha :
      dobrushinAlpha
        (greedyClosedLoopMatrix
          ((R.toParentRealization C).toControlModel dynamics))
        (greedyClosedLoopMatrix_rowStochastic
          ((R.toParentRealization C).toControlModel dynamics)) < 1) :
    ∃ mustar : stdSimplex ℝ X,
      mustar ∈ R.greedyGOASet C ∧
      (∀ mu : stdSimplex ℝ X,
        mu ∈ R.greedyGOASet C → mu = mustar) ∧
      ∀ (mu : stdSimplex ℝ X) (n : ℕ),
        lawTV
            (((step
              (greedyClosedLoopMatrix
                ((R.toParentRealization C).toControlModel dynamics))
              (greedyClosedLoopMatrix_rowStochastic
                ((R.toParentRealization C).toControlModel dynamics)))^[n]) mu)
            mustar ≤
          dobrushinAlpha
              (greedyClosedLoopMatrix
                ((R.toParentRealization C).toControlModel dynamics))
              (greedyClosedLoopMatrix_rowStochastic
                ((R.toParentRealization C).toControlModel dynamics)) ^ n *
            lawTV mu mustar := by
  let M := (R.toParentRealization C).toControlModel dynamics
  let P : Matrix X X ℝ := greedyClosedLoopMatrix M
  let hP : P ∈ Matrix.rowStochastic ℝ X := by
    simpa [P, M] using greedyClosedLoopMatrix_rowStochastic M
  have halpha' : dobrushinAlpha P hP < 1 := by
    simpa [P, hP, M] using halpha
  rcases
      (UEOT.V3.Compression.ContractiveFixedPoint.p_goa_02_via_mcf
        P hP halpha').1 with
    ⟨mustar, hmustar, hunique⟩
  refine ⟨mustar, ?_, ?_, ?_⟩
  · simpa [greedyGOASet, GreedyInvariantGOASet, P, hP, M] using hmustar
  · intro mu hmu
    apply hunique mu
    simpa [greedyGOASet, GreedyInvariantGOASet, P, hP, M] using hmu
  · intro mu n
    have hmix :=
      UEOT.V3.Compression.ContractiveFixedPoint.dobrushin_iterate_to_invariant_le_via_mcf
        P hP halpha' mu mustar hmustar n
    simpa [P, hP, M] using hmix

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
