import UEOT.V3.Compression.CrossTrack.ParentBindingStatic
import UEOT.V3.Compression.CrossTrack.PCompParentSemantic

/-!
# Parent Binding Mechanism — PB6 P-COMP specialization

Track X required an explicit row-kernel defect on P-COMP-valid parent
completions.  PB6 replaces that premise by two more primitive domain inputs:

1. a metric bound on the P-COMP-valid richer parent realizations;
2. row-TV Lipschitz regularity of the parent-dynamics realization map.

P-COMP-06 still does not create either input.  The theorem makes that boundary
explicit while removing the ad-hoc row-defect assumption from the final
semantic bound.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uP uC uA uS uI uV

noncomputable section

variable {P : Type uP} {C : Type uC} {A : Type uA}
variable [PseudoMetricSpace A]
variable {S : Type uS} [Fintype S] [Nonempty S]
variable {I : Type uI} {V : Type uV}
noncomputable local instance parentBindingPCompDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- **PB6 pairwise form.**

Two P-COMP-valid parent completions are semantically close when their
domain-level assembly realizations are close, the parent-dynamics realization
is row-TV Lipschitz, and the source completion has positive Track-S residual
isolation. -/
theorem pcomp_pairwiseSemanticBound_of_binding
    (pi : P → C)
    (Acomp : PCompCarrierAssemblyCertificate
      (P := P) (C := C) (I := I) (V := V) pi)
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (delta kappaMin : ℝ)
    (hdelta : 0 ≤ delta)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hassembly : ∀ p q,
      Acomp.admissible p → Acomp.admissible q →
      dist (repr p) (repr q) ≤ delta)
    (hisolationFloor : ∀ p, Acomp.admissible p →
      kappaMin ≤ l1ResidualConorm (K p))
    {p q : P}
    (hp : Acomp.admissible p)
    (hq : Acomp.admissible q) :
    lawTV (mu p) (mu q) ≤ bind.L * delta / kappaMin := by
  have hsourceIsolation : 0 < l1ResidualConorm (K p) :=
    lt_of_lt_of_le hkappaMin (hisolationFloor p hp)
  have hsame : pi q = pi p := by
    rw [Acomp.child_binding q hq, Acomp.child_binding p hp]
  have hrow : ∀ x,
      crossRowTV (K p) (hK p) (K q) (hK q) x ≤ bind.L * delta := by
    intro x
    calc
      crossRowTV (K p) (hK p) (K q) (hK q) x
          ≤ bind.L * dist (repr p) (repr q) :=
        bind.row_lipschitz p q x
      _ ≤ bind.L * delta :=
        mul_le_mul_of_nonneg_left (hassembly p q hp hq) bind.L_nonneg
  have htrack := x3_parentSemanticTracking
    pi K hK mu hmu p q hsame
    (bind.L * delta) hcard hsourceIsolation hrow
  have hnum0 : 0 ≤ bind.L * delta :=
    mul_nonneg bind.L_nonneg hdelta
  exact htrack.trans
    (div_le_div_of_nonneg_left hnum0 hkappaMin (hisolationFloor p hp))

/-- **PB6 fibre-diameter form.**

For all P-COMP-valid richer parent completions, a domain assembly diameter
`delta`, binding sensitivity `L`, and uniform residual-isolation floor
`kappaMin` imply

`pcompSemanticDiameter <= L * delta / kappaMin`.

Unlike Track-X X6, no row-TV defect is supplied directly. -/
theorem pcompSemanticDiameter_of_binding
    (pi : P → C)
    (Acomp : PCompCarrierAssemblyCertificate
      (P := P) (C := C) (I := I) (V := V) pi)
    (repr : P → A)
    (K : P → Matrix S S ℝ)
    (hK : ∀ p, K p ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz repr K hK)
    (mu : P → stdSimplex ℝ S)
    (hmu : ∀ p, mu p ∈ invariantLawSet (K p) (hK p))
    (delta kappaMin : ℝ)
    (hdelta : 0 ≤ delta)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hassembly : ∀ p q,
      Acomp.admissible p → Acomp.admissible q →
      dist (repr p) (repr q) ≤ delta)
    (hisolationFloor : ∀ p, Acomp.admissible p →
      kappaMin ≤ l1ResidualConorm (K p)) :
    pcompSemanticDiameter Acomp mu ≤ bind.L * delta / kappaMin := by
  unfold pcompSemanticDiameter
  apply csSup_le
  · rcases Acomp.nonempty with ⟨p, hp⟩
    exact ⟨lawTV (mu p) (mu p), p, p, hp, hp, rfl⟩
  · intro d hd
    rcases hd with ⟨p, q, hp, hq, rfl⟩
    exact pcomp_pairwiseSemanticBound_of_binding
      pi Acomp repr K hK bind mu hmu
      delta kappaMin hdelta hkappaMin hcard
      hassembly hisolationFloor hp hq

end

end UEOT.V3.Compression.CrossTrack
