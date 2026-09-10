import Mathlib.Dynamics.OmegaLimit

/-!
# P-PER-01 foundation — omega-limit persistence core

This clean module contains only source-compatible ingredients. It proves
nonemptiness, compactness, persistence-domain containment, and forward
invariance of the omega-limit from compact-tail and eventual-residence
hypotheses. The remaining source obligation is the reverse inclusion needed
for exact image equality under a genuinely one-sided semiflow; no right-inverse
or negative-time assumption is introduced here.
-/

namespace UEOT.V3.PersistenceOmega

open Set Function Filter Topology
open omegaLimit

universe uT uX

variable {τ : Type uT} {X : Type uX}
variable [TopologicalSpace τ] [AddMonoid τ]
variable [TopologicalSpace X] [T2Space X]

/-- If one tail closure of a trajectory is contained in a compact set, the
omega-limit is compact. -/
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

/-- Machine-checked persistence core behind P-PER-01. -/
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

end UEOT.V3.PersistenceOmega
