import UEOT.Core.Finite

/-!
# P-COMP-06 — lifting physical carriers to child coalitions

The frozen Core 3 source considers finitely many certified children with
physical regions `R i`.  A child coalition `S` covers a physical carrier `M`
when `M ⊆ ⋃ i ∈ S, R i`.  If coalition sufficiency is defined exactly by the
existence of a covered physical minimal carrier, then the minimal sufficient
child coalitions are obtained in two stages:

1. for each physical minimal carrier, take its inclusion-minimal covering
   coalitions;
2. take the inclusion-minimal elements of the union of all those local cover
   families.

The second minimization is essential: a coalition can be minimal for covering
one physical carrier while still containing a smaller coalition that covers a
different physical minimal carrier.
-/

namespace UEOT.V3.CompositionCarrierLift

universe uV uI

variable {V : Type uV} {I : Type uI} [Fintype I]

/-- `S` covers physical carrier `M` through the declared child regions.  This
is the finite-set spelling of `M ⊆ V(S) = ⋃ i∈S, V_i`. -/
def coalitionCovers (R : I → Finset V) (M : Finset V) (S : Finset I) : Prop := by
  classical
  exact ∀ v ∈ M, ∃ i ∈ S, v ∈ R i

/-- Source assumption that child-coalition sufficiency is exactly induced by
covering at least one physical minimal carrier. -/
def childSufficient
    (R : I → Finset V) (physicalMin : Set (Finset V)) (S : Finset I) : Prop :=
  ∃ M, M ∈ physicalMin ∧ coalitionCovers R M S

/-- Membership in the union, over physical minimal carriers `M`, of the
inclusion-minimal coalitions covering `M`. -/
def locallyMinimalCover
    (R : I → Finset V) (physicalMin : Set (Finset V)) (S : Finset I) : Prop :=
  ∃ M, M ∈ physicalMin ∧ UEOT.Finite.Minimal (coalitionCovers R M) S

/-- Left-hand side of P-COMP-06: the minimal sufficient child coalitions. -/
def childMinimalFamily
    (R : I → Finset V) (physicalMin : Set (Finset V)) : Set (Finset I) :=
  {S | UEOT.Finite.Minimal (childSufficient R physicalMin) S}

/-- Right-hand side of P-COMP-06: the outer inclusion-minimum of the union of
all per-carrier minimal-cover families. -/
def liftedMinimalCoverFamily
    (R : I → Finset V) (physicalMin : Set (Finset V)) : Set (Finset I) :=
  {S | UEOT.Finite.Minimal (locallyMinimalCover R physicalMin) S}

/-- A locally minimal cover is, in particular, a sufficient child coalition. -/
theorem locallyMinimalCover_childSufficient
    (R : I → Finset V) (physicalMin : Set (Finset V)) {S : Finset I}
    (hS : locallyMinimalCover R physicalMin S) :
    childSufficient R physicalMin S := by
  rcases hS with ⟨M, hM, hmin⟩
  exact ⟨M, hM, hmin.1⟩

/-- Every sufficient coalition contains a locally minimal cover of one of the
physical minimal carriers that it covers. -/
theorem sufficient_contains_locallyMinimalCover
    (R : I → Finset V) (physicalMin : Set (Finset V)) {S : Finset I}
    (hS : childSufficient R physicalMin S) :
    ∃ N, N ⊆ S ∧ locallyMinimalCover R physicalMin N := by
  rcases hS with ⟨M, hM, hcover⟩
  obtain ⟨N, hNS, hNmin⟩ :=
    UEOT.Finite.exists_minimal_subset (coalitionCovers R M) S hcover
  exact ⟨N, hNS, M, hM, hNmin⟩

/-- **P-COMP-06: physical carrier to child-coalition lift.**

Under the source identification of coalition sufficiency with union-region
coverage of some physical minimal carrier, the child minimal-carrier family is
exactly the outer inclusion-minimum of the union of the per-physical-carrier
minimal covering coalitions.
-/
theorem p_comp_06
    (R : I → Finset V) (physicalMin : Set (Finset V)) :
    childMinimalFamily R physicalMin =
      liftedMinimalCoverFamily R physicalMin := by
  ext S
  simp only [childMinimalFamily, liftedMinimalCoverFamily, Set.mem_setOf_eq]
  constructor
  · intro hS
    rcases hS.1 with ⟨M, hM, hcover⟩
    obtain ⟨N, hNS, hNmin⟩ :=
      UEOT.Finite.exists_minimal_subset (coalitionCovers R M) S hcover
    have hNchild : childSufficient R physicalMin N :=
      ⟨M, hM, hNmin.1⟩
    have hNS_eq : N = S := hS.2 N hNS hNchild
    have hSlocal : locallyMinimalCover R physicalMin S := by
      refine ⟨M, hM, ?_⟩
      simpa [hNS_eq] using hNmin
    refine ⟨hSlocal, ?_⟩
    intro T hTS hTlocal
    exact hS.2 T hTS
      (locallyMinimalCover_childSufficient R physicalMin hTlocal)
  · intro hS
    have hSchild : childSufficient R physicalMin S :=
      locallyMinimalCover_childSufficient R physicalMin hS.1
    refine ⟨hSchild, ?_⟩
    intro T hTS hTchild
    rcases hTchild with ⟨M, hM, hcover⟩
    obtain ⟨N, hNT, hNmin⟩ :=
      UEOT.Finite.exists_minimal_subset (coalitionCovers R M) T hcover
    have hNlocal : locallyMinimalCover R physicalMin N :=
      ⟨M, hM, hNmin⟩
    have hNS : N ⊆ S := hNT.trans hTS
    have hNS_eq : N = S := hS.2 N hNS hNlocal
    have hST : S ⊆ T := by
      rw [← hNS_eq]
      exact hNT
    exact Finset.Subset.antisymm hTS hST

end UEOT.V3.CompositionCarrierLift
