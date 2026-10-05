import UEOT.V3.Compression.TheoryCompletion.Purpose
import UEOT.V3.DualDriveGauge

/-!
# P1.5 — Teleological objective classes

A teleological objective is not identified with one scalar representative.
This stage packages the weak-order representation class and proves the expected
equivalence-class laws. Pi/Phi gauge structure is added only in P1.6.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set
open UEOT.V3.Compression.TeleologicalEquivalence

universe uP

/-- The teleological class of J is the set of numerical objectives that induce
exactly the same weak ordering. -/
def TeleologicalObjectiveClass {P : Type uP}
    (J : NumericalObjective P) : Set (NumericalObjective P) :=
  {K | PolicyOrderingEquivalent J K}

@[simp] theorem mem_teleologicalObjectiveClass
    {P : Type uP} (J K : NumericalObjective P) :
    K ∈ TeleologicalObjectiveClass J ↔ PolicyOrderingEquivalent J K := by
  rfl

theorem policyOrderingEquivalent_refl
    {P : Type uP} (J : NumericalObjective P) :
    PolicyOrderingEquivalent J J := by
  intro p q
  rfl

theorem policyOrderingEquivalent_symm
    {P : Type uP} {J K : NumericalObjective P}
    (h : PolicyOrderingEquivalent J K) :
    PolicyOrderingEquivalent K J := by
  intro p q
  exact (h p q).symm

theorem policyOrderingEquivalent_trans
    {P : Type uP} {J K L : NumericalObjective P}
    (hJK : PolicyOrderingEquivalent J K)
    (hKL : PolicyOrderingEquivalent K L) :
    PolicyOrderingEquivalent J L := by
  intro p q
  exact (hJK p q).trans (hKL p q)

theorem teleologicalObjectiveClass_eq_of_equivalent
    {P : Type uP} {J K : NumericalObjective P}
    (h : PolicyOrderingEquivalent J K) :
    TeleologicalObjectiveClass J = TeleologicalObjectiveClass K := by
  ext L
  constructor
  · intro hJL
    exact policyOrderingEquivalent_trans
      (policyOrderingEquivalent_symm h) hJL
  · intro hKL
    exact policyOrderingEquivalent_trans h hKL

/-- One Pi/Phi representation at fixed tradeoff parameter lambda. -/
structure DualDriveRepresentation (P : Type uP) where
  piVal : P → ℝ
  phiVal : P → ℝ

@[ext] theorem DualDriveRepresentation.ext
    {P : Type uP} {R S : DualDriveRepresentation P}
    (hPi : ∀ p, R.piVal p = S.piVal p)
    (hPhi : ∀ p, R.phiVal p = S.phiVal p) :
    R = S := by
  cases R with
  | mk rPi rPhi =>
      cases S with
      | mk sPi sPhi =>
          congr
          · funext p
            exact hPi p
          · funext p
            exact hPhi p

def DualDriveRepresentation.combinedObjective
    {P : Type uP} (lambdaVal : ℝ)
    (R : DualDriveRepresentation P) : NumericalObjective P :=
  fun p => R.piVal p - lambdaVal * R.phiVal p

/-- Canonical DDH gauge action. -/
def DualDriveRepresentation.gaugeTransform
    {P : Type uP} (lambdaVal : ℝ) (chiVal : P → ℝ)
    (R : DualDriveRepresentation P) : DualDriveRepresentation P where
  piVal := fun p => R.piVal p + lambdaVal * chiVal p
  phiVal := fun p => R.phiVal p + chiVal p

/-- P1.6 gauge orbit of a Pi/Phi representation. -/
def DualDriveGaugeClass
    {P : Type uP} (lambdaVal : ℝ)
    (R : DualDriveRepresentation P) :
    Set (DualDriveRepresentation P) :=
  Set.range (fun chiVal => R.gaugeTransform lambdaVal chiVal)

theorem mem_own_dualDriveGaugeClass
    {P : Type uP} (lambdaVal : ℝ)
    (R : DualDriveRepresentation P) :
    R ∈ DualDriveGaugeClass lambdaVal R := by
  refine ⟨fun _ => 0, ?_⟩
  ext p <;>
    simp [DualDriveRepresentation.gaugeTransform]

theorem dualDriveGaugeClass_symm
    {P : Type uP} {lambdaVal : ℝ}
    {R S : DualDriveRepresentation P}
    (hS : S ∈ DualDriveGaugeClass lambdaVal R) :
    R ∈ DualDriveGaugeClass lambdaVal S := by
  rcases hS with ⟨chiVal, rfl⟩
  refine ⟨fun p => -chiVal p, ?_⟩
  ext p <;>
    simp [DualDriveRepresentation.gaugeTransform]

theorem dualDriveGaugeClass_trans
    {P : Type uP} {lambdaVal : ℝ}
    {R S T : DualDriveRepresentation P}
    (hS : S ∈ DualDriveGaugeClass lambdaVal R)
    (hT : T ∈ DualDriveGaugeClass lambdaVal S) :
    T ∈ DualDriveGaugeClass lambdaVal R := by
  rcases hS with ⟨chiVal, rfl⟩
  rcases hT with ⟨psiVal, rfl⟩
  refine ⟨fun p => chiVal p + psiVal p, ?_⟩
  ext p <;>
    simp [DualDriveRepresentation.gaugeTransform] <;>
    ring

theorem dualDriveGaugeClass_eq_of_mem
    {P : Type uP} {lambdaVal : ℝ}
    {R S : DualDriveRepresentation P}
    (hS : S ∈ DualDriveGaugeClass lambdaVal R) :
    DualDriveGaugeClass lambdaVal S =
      DualDriveGaugeClass lambdaVal R := by
  ext T
  constructor
  · intro hT
    exact dualDriveGaugeClass_trans hS hT
  · intro hT
    exact dualDriveGaugeClass_trans
      (dualDriveGaugeClass_symm hS) hT

/-- DDH gauge transformations preserve the combined objective pointwise. -/
theorem gaugeTransform_valueEqual
    {P : Type uP} (lambdaVal : ℝ) (chiVal : P → ℝ)
    (R : DualDriveRepresentation P) :
    ValueEqual
      (R.combinedObjective lambdaVal)
      ((R.gaugeTransform lambdaVal chiVal).combinedObjective lambdaVal) := by
  intro p
  exact UEOT.V3.DualDriveGauge.p_ddh_01_pointwise
    R.piVal R.phiVal chiVal lambdaVal p

/-- P1.7 easy direction: every valid DDH gauge representative lies in the
same teleological weak-order class. -/
theorem gaugeClass_to_teleologicalClass
    {P : Type uP} (lambdaVal : ℝ)
    (R S : DualDriveRepresentation P)
    (hS : S ∈ DualDriveGaugeClass lambdaVal R) :
    S.combinedObjective lambdaVal ∈
      TeleologicalObjectiveClass (R.combinedObjective lambdaVal) := by
  rcases hS with ⟨chiVal, rfl⟩
  exact positiveAffineEquivalent_to_policyOrderingEquivalent
    (valueEqual_to_positiveAffineEquivalent
      (gaugeTransform_valueEqual lambdaVal chiVal R))

end UEOT.V3.Compression.TheoryCompletion
