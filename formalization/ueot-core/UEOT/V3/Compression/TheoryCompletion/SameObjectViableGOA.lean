import UEOT.V3.Compression.TheoryCompletion.SameObjectViability
import UEOT.V3.Compression.TopologyChangingGoaSemantics

/-!
# P2 audit hardening — persistence-supported same-object GOA

P2.7 originally established only one-step preservation of the canonical
Objecthood persistence kernel by the Bellman-greedy action.  This module closes
the long-run semantic gap: because that persistence kernel is nonempty and
closed under the same greedy closed-loop dynamics, finite Cesaro semantics
supplies an invariant-law GOA whose support remains inside the persistence
kernel.

No irreducibility, recurrent-class label, Dobrushin contraction, or uniqueness
assumption is added.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set MeasureTheory ProbabilityTheory
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.FiniteDobrushin
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.AgencyGodGoaAssembly
open UEOT.V3.Compression.CrossTrack
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.RecurrentClassGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSemantics

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
noncomputable local instance sameObjectViableGoaSemanticDecidableEq :
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

/-- The exact greedy closed-loop row equals the selected parent's physical PMF
under its Bellman-greedy action. -/
@[simp] theorem greedyClosedLoopMatrix_apply_selectedParent
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (x y : X) :
    greedyClosedLoopMatrix
        ((R.toParentRealization C).toControlModel dynamics) x y =
      ((dynamics C.repairing.operational.parent x
        (((R.toParentRealization C).toControlModel dynamics).greedyAction x)) y).toReal := by
  classical
  rw [greedyClosedLoopMatrix, greedyStationaryPolicy]
  simp [UEOT.V3.CoreOperationalAssembly.policyMatrix,
    Model.policyTransition, StationaryPolicy.ofSelector]

/-- P2.7 strengthened: the exact Objecthood persistence kernel is a closed
carrier of the Bellman-greedy closed-loop Markov matrix whenever the explicit
greedy-viability gate holds. -/
theorem persistence_closedCarrier_of_greedyPreserves
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C) :
    ClosedCarrier
      (greedyClosedLoopMatrix
        ((R.toParentRealization C).toControlModel dynamics))
      C.repairing.operational.persistence.K := by
  intro x hx y hxy
  have hypos :
      0 <
        ((dynamics C.repairing.operational.parent x
          (((R.toParentRealization C).toControlModel dynamics).greedyAction x)) y).toReal := by
    simpa using hxy
  have hyne :
      (dynamics C.repairing.operational.parent x
        (((R.toParentRealization C).toControlModel dynamics).greedyAction x)) y ≠ 0 := by
    intro hyzero
    rw [hyzero] at hypos
    simp at hypos
  exact
    hviable x hx
      ((PMF.mem_support_iff _ _).2 hyne)

/-- The P2.7 viability gate says exactly that the Bellman-greedy selector is a
functionally legitimate preserving controller for the same Objecthood kernel.
Objecthood legitimacy is behavioral, not equality to one arbitrary stored
selector. -/
theorem greedyAction_preservingController
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C) :
    PreservingController
      (dynamics C.repairing.operational.parent)
      C.repairing.operational.persistence.K
      ((R.toParentRealization C).toControlModel dynamics).greedyAction :=
  hviable

/-- Consequently the greedy controller can be internalized as a reflexive
constitutive state in the same Objecthood legitimate class. -/
theorem greedyConstitutiveState_mem_legitimate
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    (x, ((R.toParentRealization C).toControlModel dynamics).greedyAction) ∈
      legitimateConstitutiveDomain
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K :=
  ⟨hx, R.greedyAction_preservingController C hviable⟩

/-- The autonomous constitutive lift therefore preserves functional legitimacy
when initialized with the Bellman-greedy controller. This is the explicit
internalization bridge from P2 agency to Objecthood's reflexive-state semantics. -/
theorem greedyConstitutiveLift_staysIn_legitimate
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    {x : X} (hx : x ∈ C.repairing.operational.persistence.K) :
    StaysIn
      (constitutiveLift
        (dynamics C.repairing.operational.parent)
        (x, ((R.toParentRealization C).toControlModel dynamics).greedyAction) ())
      (legitimateConstitutiveDomain
        (dynamics C.repairing.operational.parent)
        C.repairing.operational.persistence.K) :=
  constitutiveLift_staysIn_legitimate
    (dynamics C.repairing.operational.parent)
    C.repairing.operational.persistence.K
    (R.greedyConstitutiveState_mem_legitimate C hviable hx)

/-- Long-run same-object viability semantics: invariant laws of the greedy
closed loop whose support stays in the exact Objecthood persistence kernel. -/
def persistenceSupportedGreedyGOASet
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    Set (stdSimplex ℝ X) :=
  carrierInvariantLawSet
    (greedyClosedLoopMatrix
      ((R.toParentRealization C).toControlModel dynamics))
    (greedyClosedLoopMatrix_rowStochastic
      ((R.toParentRealization C).toControlModel dynamics))
    C.repairing.operational.persistence.K

/-- Audit hardening: once greedy actions preserve the exact persistence kernel,
there exists an invariant-law GOA supported inside that kernel.

The witness is obtained from a Cesaro subsequential limit started at the
Objecthood certificate's own nonvacuous persistence seed. -/
theorem persistenceSupportedGreedyGOASet_nonempty
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C) :
    (R.persistenceSupportedGreedyGOASet C).Nonempty := by
  let M := (R.toParentRealization C).toControlModel dynamics
  let P : Matrix X X ℝ := greedyClosedLoopMatrix M
  let hP : P ∈ Matrix.rowStochastic ℝ X := by
    simpa [P, M] using greedyClosedLoopMatrix_rowStochastic M
  let K : Set X := C.repairing.operational.persistence.K
  let x0 : X := C.repairing.operational.persistence.seed
  have hx0 : x0 ∈ K := by
    simpa [x0, K] using C.repairing.operational.persistence.seed_mem
  have hclosed : ClosedCarrier P K := by
    simpa [P, M, K] using R.persistence_closedCarrier_of_greedyPreserves C hviable
  let mu0 : stdSimplex ℝ X := pureSimplex x0
  have hmu0 : SupportedOn mu0 K := by
    simpa [mu0] using pureSimplex_supportedOn K x0 hx0
  rcases cesaroLimitSet_nonempty P hP mu0 with ⟨nu, hnu⟩
  refine ⟨nu, ?_⟩
  have hcarrier :
      nu ∈ carrierInvariantLawSet P hP K :=
    cesaroLimitSet_subset_carrierInvariantLawSet_of_closed
      P hP K hclosed mu0 hmu0 hnu
  simpa [persistenceSupportedGreedyGOASet, P, hP, M, K] using hcarrier

/-- Forgetting the support certificate embeds every persistence-supported GOA
into the ordinary greedy invariant-GOA set. -/
theorem persistenceSupportedGreedyGOASet_subset_greedyGOASet
    (R : ObjecthoodTeleologicalControlSpec C Future) :
    R.persistenceSupportedGreedyGOASet C ⊆ R.greedyGOASet C := by
  intro mu hmu
  exact hmu.1

/-- Combined P2.6/P2.7 hardening: if greedy dynamics preserve the same
Objecthood persistence kernel and the greedy closed loop has a strict
Dobrushin margin, then its unique globally attracting GOA is itself supported
inside that persistence kernel. -/
theorem existsUnique_stable_persistenceSupportedGreedyGOA
    (R : ObjecthoodTeleologicalControlSpec C Future)
    (hviable : R.GreedyPreservesObjectPersistence C)
    (halpha :
      dobrushinAlpha
        (greedyClosedLoopMatrix
          ((R.toParentRealization C).toControlModel dynamics))
        (greedyClosedLoopMatrix_rowStochastic
          ((R.toParentRealization C).toControlModel dynamics)) < 1) :
    ∃ mustar : stdSimplex ℝ X,
      mustar ∈ R.persistenceSupportedGreedyGOASet C ∧
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
  rcases R.existsUnique_stable_greedyGOA C halpha with
    ⟨mustar, hmustar, hunique, hmix⟩
  rcases R.persistenceSupportedGreedyGOASet_nonempty C hviable with
    ⟨nu, hnu⟩
  have hnugoa : nu ∈ R.greedyGOASet C :=
    R.persistenceSupportedGreedyGOASet_subset_greedyGOASet C hnu
  have hnuEq : nu = mustar := hunique nu hnugoa
  refine ⟨mustar, ?_, hunique, hmix⟩
  simpa [hnuEq] using hnu

end ObjecthoodTeleologicalControlSpec

end

end UEOT.V3.Compression.TheoryCompletion
