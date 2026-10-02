import UEOT.V3.CompositionCarrierLift
import UEOT.V3.Compression.CrossTrack.RobustParentSemanticCertificate

/-!
# Track X — X6 P-COMP out-of-sample parent semantics

The frozen P-COMP family does not contain a universal parent constructor.
P-COMP-06 is the clean carrier-assembly surface: supplied physical minimal
carriers induce the canonical family of minimal child coalitions.

This module consumes that actual source contract without strengthening it.  A
domain assembly certificate states which richer parent completions realize
those P-COMP-06-valid coalitions and bind to one child-evidence value.  Track X
then combines the separately supplied dynamics defect and Track-S isolation
margin to obtain robust long-run semantics.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.CompositionCarrierLift

universe uP uC uS uI uV

noncomputable section

variable {P : Type uP} {C : Type uC}
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {I : Type uI}
variable {V : Type uV}
noncomputable local instance pcompParentSemanticDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- A domain-level P-COMP-06 parent-assembly certificate.

Nothing here reconstructs parent data from child marginals.  The physical
minimal-carrier semantics, the richer parent-to-coalition realization, and the
binding to one child-evidence value are explicit supplied obligations. -/
structure PCompCarrierAssemblyCertificate
    (pi : P → C) where
  child : C
  regions : I → Finset V
  physicalMin : Set (Finset V)
  coalition : P → Finset I
  admissible : P → Prop
  admissible_iff_childMinimal : ∀ p,
    admissible p ↔
      coalition p ∈ childMinimalFamily regions physicalMin
  child_binding : ∀ p, admissible p → pi p = child
  nonempty : ∃ p, admissible p

/-- P-COMP-06 converts the certificate's child-minimal validity criterion into
the canonical two-stage lifted physical-cover criterion. -/
theorem PCompCarrierAssemblyCertificate.admissible_iff_lifted
    [Fintype I]
    (pi : P → C)
    (A : PCompCarrierAssemblyCertificate (P := P) (C := C)
      (I := I) (V := V) pi)
    (p : P) :
    A.admissible p ↔
      A.coalition p ∈
        liftedMinimalCoverFamily A.regions A.physicalMin := by
  rw [A.admissible_iff_childMinimal p]
  rw [p_comp_06 A.regions A.physicalMin]

/-- Semantic distances among the P-COMP-valid richer parent completions. -/
def pcompSemanticDistances
    (A : PCompCarrierAssemblyCertificate (P := P) (C := C)
      (I := I) (V := V) pi)
    (mu : P → stdSimplex ℝ S) : Set ℝ :=
  {d | ∃ p q, A.admissible p ∧ A.admissible q ∧
    d = lawTV (mu p) (mu q)}

/-- Supremal long-run semantic diameter among P-COMP-valid parent
completions. -/
noncomputable def pcompSemanticDiameter
    (A : PCompCarrierAssemblyCertificate (P := P) (C := C)
      (I := I) (V := V) pi)
    (mu : P → stdSimplex ℝ S) : ℝ :=
  sSup (pcompSemanticDistances A mu)

/-- **X6 — P-COMP out-of-sample robust parent semantics, pairwise form.**

Valid P-COMP-06 assembly plus an explicit assembly-induced row-dynamics defect
and a positive parent residual-isolation floor imply robust long-run semantics.
The theorem preserves H3 separations because it mentions neither objectives,
maximizers, fitness, nor selection semantics. -/
theorem x6_pcomp_pairwiseRobustParentSemantics
    (pi : P → C)
    (A : PCompCarrierAssemblyCertificate (P := P) (C := C)
      (I := I) (V := V) pi)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (epsilon kappaMin : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hrow : ∀ p q, A.admissible p → A.admissible q → ∀ x,
      crossRowTV (K p) (hK p) (K q) (hK q) x ≤ epsilon)
    (hisolationFloor : ∀ p, A.admissible p →
      kappaMin ≤ l1ResidualConorm (K p))
    {p q : P}
    (hp : A.admissible p) (hq : A.admissible q) :
    lawTV (mu p) (mu q) ≤ epsilon / kappaMin := by
  have hsourceIsolation : 0 < l1ResidualConorm (K p) :=
    lt_of_lt_of_le hkappaMin (hisolationFloor p hp)
  have hsame : pi q = pi p := by
    rw [A.child_binding q hq, A.child_binding p hp]
  have htrack :
      lawTV (mu p) (mu q) ≤ epsilon / l1ResidualConorm (K p) := by
    exact x3_parentSemanticTracking
      pi K hK mu hmu p q hsame epsilon hcard hsourceIsolation
      (hrow p q hp hq)
  have hradius :
      epsilon / l1ResidualConorm (K p) ≤ epsilon / kappaMin :=
    div_le_div_of_nonneg_left hepsilon hkappaMin
      (hisolationFloor p hp)
  exact htrack.trans hradius

/-- **X6 — P-COMP out-of-sample robust parent semantics, fibre-diameter
form.** -/
theorem x6_pcompSemanticDiameter
    (pi : P → C)
    (A : PCompCarrierAssemblyCertificate (P := P) (C := C)
      (I := I) (V := V) pi)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (epsilon kappaMin : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hrow : ∀ p q, A.admissible p → A.admissible q → ∀ x,
      crossRowTV (K p) (hK p) (K q) (hK q) x ≤ epsilon)
    (hisolationFloor : ∀ p, A.admissible p →
      kappaMin ≤ l1ResidualConorm (K p)) :
    pcompSemanticDiameter A mu ≤ epsilon / kappaMin := by
  unfold pcompSemanticDiameter
  apply csSup_le
  · rcases A.nonempty with ⟨p, hp⟩
    exact ⟨lawTV (mu p) (mu p), p, p, hp, hp, rfl⟩
  · intro d hd
    rcases hd with ⟨p, q, hp, hq, rfl⟩
    exact x6_pcomp_pairwiseRobustParentSemantics
      pi A K hK mu hmu epsilon kappaMin
      hepsilon hkappaMin hcard hrow hisolationFloor hp hq

end

end UEOT.V3.Compression.CrossTrack
