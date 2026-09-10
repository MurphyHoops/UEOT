import Mathlib.Dynamics.OmegaLimit

/-!
# P-PER-01 foundation — omega-limit persistence core

This module formalizes the compactness/nonemptiness/closed-domain/forward
invariance part of the source omega-limit theorem.  The source requires the
strong equality phi_s(omega)=omega; the reverse inclusion is deliberately kept
as a separate obligation and is not claimed here.
-/

namespace UEOT.V3.PersistenceOmega

open Set Function Filter Topology
open omegaLimit

universe uT uX

variable {τ : Type uT} {X : Type uX}
variable [TopologicalSpace τ] [AddMonoid τ]
variable [TopologicalSpace X] [T2Space X]

/-- If one tail closure of a trajectory is contained in a compact set, the
omega-limit is compact.  This is the exact compact-absorbing formulation of
precompactness used by Mathlib's omega-limit API. -/
theorem isCompact_omegaLimit_of_compact_tail
    (f : Filter τ) (φ : Flow τ X) (x : X)
    {K : Set X} (hK : IsCompact K)
    (habs : ∃ v ∈ f,
      closure (image2 φ v ({x} : Set X)) ⊆ K) :
    IsCompact (ω f φ ({x} : Set X)) := by
  rcases habs with ⟨v, hv, hsub⟩
  exact hK.of_isClosed_subset
    (isClosed_omegaLimit f φ ({x} : Set X))
    ((omegaLimit_subset_closure_image2 f φ ({x} : Set X) hv).trans hsub)

/-- Eventual residence in a closed persistence domain forces the omega-limit
to lie in that domain. -/
theorem omegaLimit_subset_closed_of_eventually_mem
    (f : Filter τ) (φ : Flow τ X) (x : X)
    {V : Set X} (hV : IsClosed V)
    (hstay : ∀ᶠ t in f, φ t x ∈ V) :
    ω f φ ({x} : Set X) ⊆ V := by
  let v : Set τ := {t | φ t x ∈ V}
  have hv : v ∈ f := hstay
  refine (omegaLimit_subset_closure_image2 f φ ({x} : Set X) hv).trans ?_
  apply closure_minimal
  · rintro y ⟨t, ht, z, hz, rfl⟩
    simp only [mem_singleton_iff] at hz
    subst z
    exact ht
  · exact hV

/-- Machine-checked persistence core behind P-PER-01.  A nontrivial time
filter, one compact absorbing tail, eventual residence in a closed domain, and
translation stability of the time filter imply a nonempty compact omega-limit
inside the domain, with forward invariance under the continuous semiflow. -/
theorem omegaLimit_persistence_core
    (f : Filter τ) [NeBot f]
    (φ : Flow τ X) (x : X)
    {V K : Set X}
    (hV : IsClosed V)
    (hstay : ∀ᶠ t in f, φ t x ∈ V)
    (hK : IsCompact K)
    (habs : ∃ v ∈ f,
      closure (image2 φ v ({x} : Set X)) ⊆ K)
    (htrans : ∀ s : τ, Tendsto (s + ·) f f) :
    (ω f φ ({x} : Set X)).Nonempty ∧
      IsCompact (ω f φ ({x} : Set X)) ∧
      ω f φ ({x} : Set X) ⊆ V ∧
      IsInvariant φ (ω f φ ({x} : Set X)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nonempty_omegaLimit_of_isCompact_absorbing
      f φ ({x} : Set X) hK habs (singleton_nonempty x)
  · exact isCompact_omegaLimit_of_compact_tail f φ x hK habs
  · exact omegaLimit_subset_closed_of_eventually_mem f φ x hV hstay
  · exact Flow.isInvariant_omegaLimit f φ ({x} : Set X) htrans

/-- Forward invariance upgrades to exact set invariance at a time `s` whenever
that time has a right inverse `r` in the acting time monoid.  This isolates the
precise algebraic ingredient missing from a genuinely one-sided semiflow. -/
theorem image_eq_of_isInvariant_of_rightInverseTime
    (φ : Flow τ X) {S : Set X}
    (hS : IsInvariant φ S)
    (s r : τ) (hsr : s + r = 0) :
    φ s '' S = S := by
  apply Set.Subset.antisymm
  · exact (isInvariant_iff_image φ S).1 hS s
  · intro y hy
    refine ⟨φ r y, hS r hy, ?_⟩
    rw [← φ.map_add s r y, hsr]
    exact φ.map_zero_apply y

/-- Exact omega-limit invariance for any time monoid in which every time has a
right inverse.  In particular this applies to two-sided additive-group flows;
it intentionally does not assert the reverse inclusion for a merely positive
semiflow. -/
theorem omegaLimit_exact_invariant_of_rightInverseTimes
    (f : Filter τ) (φ : Flow τ X) (x : X)
    (htrans : ∀ s : τ, Tendsto (s + ·) f f)
    (hinv : ∀ s : τ, ∃ r : τ, s + r = 0) :
    ∀ s : τ, φ s '' ω f φ ({x} : Set X) = ω f φ ({x} : Set X) := by
  have hω : IsInvariant φ (ω f φ ({x} : Set X)) :=
    Flow.isInvariant_omegaLimit f φ ({x} : Set X) htrans
  intro s
  obtain ⟨r, hsr⟩ := hinv s
  exact image_eq_of_isInvariant_of_rightInverseTime φ hω s r hsr

end UEOT.V3.PersistenceOmega
