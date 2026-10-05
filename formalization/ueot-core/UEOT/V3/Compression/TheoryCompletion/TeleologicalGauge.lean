import UEOT.V3.Compression.TheoryCompletion.Purpose
import UEOT.V3.Compression.TheoryCompletion.TeleologicalContract
import UEOT.V3.DualDriveGauge

/-!
# P1.5-P1.8 — Teleological classes and dual-drive gauge semantics

A bare Pi/Phi pair is algebraic data only. It becomes a valid teleological
representation only after its combined objective represents the declared
TeleologicalContract and both axes satisfy an explicit domain-supplied
admissibility specification. This keeps DDH gauge algebra separate from
semantic anchoring.
-/

namespace UEOT.V3.Compression.TheoryCompletion

open Set
open UEOT.V3.Compression.TeleologicalEquivalence

universe uP uF

/-- The teleological class of a numerical objective is the set of numerical
objectives inducing exactly the same weak ordering. -/
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

/-- A numerical objective represents a declared teleological contract exactly
when it induces the contract's weak preference relation on admissible futures. -/
def ObjectiveRepresentsContract
    {Future : Type uF} (C : TeleologicalContract Future)
    (J : NumericalObjective (AdmissibleFuture C.admissible)) : Prop :=
  ∀ x y, InducedPreference J x y ↔ C.prefers x y

/-- The contract-relative teleological objective class. -/
def ContractObjectiveClass
    {Future : Type uF} (C : TeleologicalContract Future) :
    Set (NumericalObjective (AdmissibleFuture C.admissible)) :=
  {J | ObjectiveRepresentsContract C J}

theorem objectives_representing_same_contract_are_orderEquivalent
    {Future : Type uF} {C : TeleologicalContract Future}
    {J K : NumericalObjective (AdmissibleFuture C.admissible)}
    (hJ : ObjectiveRepresentsContract C J)
    (hK : ObjectiveRepresentsContract C K) :
    PolicyOrderingEquivalent J K := by
  intro x y
  exact (hJ x y).trans (hK x y).symm

/-- Bare algebraic Pi/Phi data. This type by itself makes no claim that either
axis is semantically meaningful or that the combined objective represents a
TeleologicalContract. -/
structure DualDrivePair (P : Type uP) where
  piVal : P → ℝ
  phiVal : P → ℝ

@[ext] theorem DualDrivePair.ext
    {P : Type uP} {R S : DualDrivePair P}
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

def DualDrivePair.combinedObjective
    {P : Type uP} (lambdaVal : ℝ)
    (R : DualDrivePair P) : NumericalObjective P :=
  fun p => R.piVal p - lambdaVal * R.phiVal p

/-- Domain-supplied semantic admissibility for the two drives.

P1 does not invent universal meanings for Pi or Phi; a concrete domain must
supply these predicates. -/
structure DualDriveAdmissibilitySpec (P : Type uP) where
  piAdmissible : (P → ℝ) → Prop
  phiAdmissible : (P → ℝ) → Prop

/-- A semantically valid Pi/Phi representation of one declared contract. -/
def ValidDualDriveRepresentation
    {Future : Type uF} (C : TeleologicalContract Future)
    (spec : DualDriveAdmissibilitySpec (AdmissibleFuture C.admissible))
    (lambdaVal : ℝ)
    (R : DualDrivePair (AdmissibleFuture C.admissible)) : Prop :=
  spec.piAdmissible R.piVal ∧
    spec.phiAdmissible R.phiVal ∧
      ObjectiveRepresentsContract C (R.combinedObjective lambdaVal)

/-- Existence of a semantically valid Pi/Phi representation is therefore a
contract-plus-domain question, not a consequence of teleological order alone. -/
def HasValidDualDriveRepresentation
    {Future : Type uF} (C : TeleologicalContract Future)
    (spec : DualDriveAdmissibilitySpec (AdmissibleFuture C.admissible))
    (lambdaVal : ℝ) : Prop :=
  ∃ R, ValidDualDriveRepresentation C spec lambdaVal R

/-- Canonical DDH gauge action on the algebraic pair. -/
def DualDrivePair.gaugeTransform
    {P : Type uP} (lambdaVal : ℝ) (chiVal : P → ℝ)
    (R : DualDrivePair P) : DualDrivePair P where
  piVal := fun p => R.piVal p + lambdaVal * chiVal p
  phiVal := fun p => R.phiVal p + chiVal p

/-- Algebraic DDH gauge orbit. Membership alone does not assert semantic axis
admissibility. -/
def DualDriveGaugeClass
    {P : Type uP} (lambdaVal : ℝ)
    (R : DualDrivePair P) :
    Set (DualDrivePair P) :=
  Set.range (fun chiVal => R.gaugeTransform lambdaVal chiVal)

theorem mem_own_dualDriveGaugeClass
    {P : Type uP} (lambdaVal : ℝ)
    (R : DualDrivePair P) :
    R ∈ DualDriveGaugeClass lambdaVal R := by
  refine ⟨fun _ => 0, ?_⟩
  ext p <;>
    simp [DualDrivePair.gaugeTransform]

theorem dualDriveGaugeClass_symm
    {P : Type uP} {lambdaVal : ℝ}
    {R S : DualDrivePair P}
    (hS : S ∈ DualDriveGaugeClass lambdaVal R) :
    R ∈ DualDriveGaugeClass lambdaVal S := by
  rcases hS with ⟨chiVal, rfl⟩
  refine ⟨fun p => -chiVal p, ?_⟩
  ext p <;>
    simp [DualDrivePair.gaugeTransform]

theorem dualDriveGaugeClass_trans
    {P : Type uP} {lambdaVal : ℝ}
    {R S T : DualDrivePair P}
    (hS : S ∈ DualDriveGaugeClass lambdaVal R)
    (hT : T ∈ DualDriveGaugeClass lambdaVal S) :
    T ∈ DualDriveGaugeClass lambdaVal R := by
  rcases hS with ⟨chiVal, rfl⟩
  rcases hT with ⟨psiVal, rfl⟩
  refine ⟨fun p => chiVal p + psiVal p, ?_⟩
  ext p <;>
    simp [DualDrivePair.gaugeTransform] <;>
    ring

theorem dualDriveGaugeClass_eq_of_mem
    {P : Type uP} {lambdaVal : ℝ}
    {R S : DualDrivePair P}
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
    (R : DualDrivePair P) :
    ValueEqual
      (R.combinedObjective lambdaVal)
      ((R.gaugeTransform lambdaVal chiVal).combinedObjective lambdaVal) := by
  intro p
  exact UEOT.V3.DualDriveGauge.p_ddh_01_pointwise
    R.piVal R.phiVal chiVal lambdaVal p

/-- A domain specification is gauge-closed when admissible axes remain
admissible under every DDH gauge transformation. -/
def DualDriveAdmissibilitySpec.GaugeClosed
    {P : Type uP} (spec : DualDriveAdmissibilitySpec P)
    (lambdaVal : ℝ) : Prop :=
  ∀ (R : DualDrivePair P) (chiVal : P → ℝ),
    spec.piAdmissible R.piVal →
    spec.phiAdmissible R.phiVal →
      spec.piAdmissible (R.gaugeTransform lambdaVal chiVal).piVal ∧
      spec.phiAdmissible (R.gaugeTransform lambdaVal chiVal).phiVal

/-- P1.7: every algebraic gauge representative of a valid Pi/Phi
representation has a combined objective representing the same declared
TeleologicalContract. -/
theorem gaugeClass_of_validRepresentation_representsContract
    {Future : Type uF} (C : TeleologicalContract Future)
    (spec : DualDriveAdmissibilitySpec (AdmissibleFuture C.admissible))
    (lambdaVal : ℝ)
    (R S : DualDrivePair (AdmissibleFuture C.admissible))
    (hR : ValidDualDriveRepresentation C spec lambdaVal R)
    (hS : S ∈ DualDriveGaugeClass lambdaVal R) :
    ObjectiveRepresentsContract C (S.combinedObjective lambdaVal) := by
  rcases hS with ⟨chiVal, rfl⟩
  have hOrder :
      PolicyOrderingEquivalent
        (R.combinedObjective lambdaVal)
        ((R.gaugeTransform lambdaVal chiVal).combinedObjective lambdaVal) :=
    positiveAffineEquivalent_to_policyOrderingEquivalent
      (valueEqual_to_positiveAffineEquivalent
        (gaugeTransform_valueEqual lambdaVal chiVal R))
  intro x y
  exact (hOrder x y).symm.trans (hR.2.2 x y)

/-- If the domain's axis semantics is itself gauge-closed, a gauge transform of
a valid representation remains a valid representation, not merely an
order-equivalent combined objective. -/
theorem gaugeTransform_preserves_validRepresentation
    {Future : Type uF} (C : TeleologicalContract Future)
    (spec : DualDriveAdmissibilitySpec (AdmissibleFuture C.admissible))
    (lambdaVal : ℝ)
    (hClosed : spec.GaugeClosed lambdaVal)
    (R : DualDrivePair (AdmissibleFuture C.admissible))
    (hR : ValidDualDriveRepresentation C spec lambdaVal R)
    (chiVal : AdmissibleFuture C.admissible → ℝ) :
    ValidDualDriveRepresentation C spec lambdaVal
      (R.gaugeTransform lambdaVal chiVal) := by
  have hAxes := hClosed R chiVal hR.1 hR.2.1
  exact ⟨hAxes.1, hAxes.2,
    gaugeClass_of_validRepresentation_representsContract
      C spec lambdaVal R (R.gaugeTransform lambdaVal chiVal)
      hR ⟨chiVal, rfl⟩⟩

/-- Every valid representation's combined objective lies in the
contract-relative teleological class. -/
theorem validDualDriveRepresentation_mem_contractObjectiveClass
    {Future : Type uF} (C : TeleologicalContract Future)
    (spec : DualDriveAdmissibilitySpec (AdmissibleFuture C.admissible))
    (lambdaVal : ℝ)
    (R : DualDrivePair (AdmissibleFuture C.admissible))
    (hR : ValidDualDriveRepresentation C spec lambdaVal R) :
    R.combinedObjective lambdaVal ∈ ContractObjectiveClass C :=
  hR.2.2

/-- P1.8 algebraic boundary: weak-order equivalence of combined objectives does
not imply membership in the same fixed-lambda DDH gauge orbit. -/
theorem teleologicalEquivalent_not_imply_sameAlgebraicGaugeOrbit :
    ∃ R S : DualDrivePair Bool,
      S.combinedObjective 1 ∈
          TeleologicalObjectiveClass (R.combinedObjective 1) ∧
        S ∉ DualDriveGaugeClass 1 R := by
  let R : DualDrivePair Bool :=
    { piVal := fun b => if b then 1 else 0
      phiVal := fun _ => 0 }
  let S : DualDrivePair Bool :=
    { piVal := fun b => if b then 2 else 0
      phiVal := fun _ => 0 }
  refine ⟨R, S, ?_, ?_⟩
  · apply positiveAffineEquivalent_to_policyOrderingEquivalent
    refine ⟨2, 0, by norm_num, ?_⟩
    intro b
    cases b <;>
      norm_num [R, S, DualDrivePair.combinedObjective]
  · intro hGauge
    rcases hGauge with ⟨chiVal, hchi⟩
    have hValue :
        ValueEqual
          (R.combinedObjective 1)
          (S.combinedObjective 1) := by
      rw [← hchi]
      exact gaugeTransform_valueEqual 1 chiVal R
    have hTrue := hValue true
    norm_num [R, S, DualDrivePair.combinedObjective] at hTrue

/-- A legal teleological contract with two admissible futures that are
incomparable except with themselves. -/
def incomparableBoolContract : TeleologicalContract Bool where
  admissible := Set.univ
  admissible_nonempty := ⟨false, by simp⟩
  prefers := fun x y => x.1 = y.1
  preference_preorder := by
    constructor
    · intro x
      rfl
    · intro x y z hxy hyz
      exact hxy.trans hyz

private def incomparableFalse :
    AdmissibleFuture incomparableBoolContract.admissible :=
  ⟨false, by simp [incomparableBoolContract]⟩

private def incomparableTrue :
    AdmissibleFuture incomparableBoolContract.admissible :=
  ⟨true, by simp [incomparableBoolContract]⟩

/-- P1.8 semantic boundary: a general teleological contract need not possess a
real-valued numerical representation, because the contract need not be total
while every real-valued objective induces a total weak order. -/
theorem incomparableBoolContract_has_no_numerical_representation :
    ¬ ∃ J : NumericalObjective
        (AdmissibleFuture incomparableBoolContract.admissible),
      ObjectiveRepresentsContract incomparableBoolContract J := by
  rintro ⟨J, hJ⟩
  rcases le_total (J incomparableFalse) (J incomparableTrue) with hle | hle
  · have hpref := (hJ incomparableFalse incomparableTrue).1 hle
    have hEq : false = true := hpref
    cases hEq
  · have hpref := (hJ incomparableTrue incomparableFalse).1 hle
    have hEq : true = false := hpref
    cases hEq

/-- Consequently the general TeleologicalContract interface alone does not
imply a valid Pi/Phi representation, for any domain axis specification or
tradeoff parameter. -/
theorem incomparableBoolContract_has_no_validDualDriveRepresentation
    (spec : DualDriveAdmissibilitySpec
      (AdmissibleFuture incomparableBoolContract.admissible))
    (lambdaVal : ℝ) :
    ¬ HasValidDualDriveRepresentation
      incomparableBoolContract spec lambdaVal := by
  rintro ⟨R, hR⟩
  exact incomparableBoolContract_has_no_numerical_representation
    ⟨R.combinedObjective lambdaVal, hR.2.2⟩

end UEOT.V3.Compression.TheoryCompletion
