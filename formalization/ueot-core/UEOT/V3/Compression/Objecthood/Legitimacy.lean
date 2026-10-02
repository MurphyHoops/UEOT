import UEOT.V3.Compression.CrossTrack.EndogenousConstitutivePersistence

/-!
# Track O / O1 — functional constitutive legitimacy

The Track-X constitutive lift embeds one particular preserving controller
`pi : X → A` into reflexive state.  For Objecthood/self-repair that target is
too syntactic: P-PER generally need not make the preserving controller unique.

O1 therefore defines the legitimate organization as the entire class of
controllers that preserve the same viability kernel.  It proves two facts:

1. this functional legitimate domain is nonempty whenever a nonempty fixed
   viability kernel exists, and it is closed under the current constitutive
   lift;
2. the current lift cannot repair a non-preserving controller, because that
   controller coordinate is copied exactly forever.

The second result is the formal boundary between constitutive persistence and
self-stabilization.  No new counted generator is introduced.
-/

namespace UEOT.V3.Compression.Objecthood

open Set
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack

universe uX uA

noncomputable section

/-- A controller is functionally legitimate for `K` when every transition it
selects from a state in `K` is supported inside `K`.  Object identity is thus
defined by preservation semantics rather than equality to one arbitrary
stationary selector. -/
def PreservingController
    {X : Type uX} {A : Type uA}
    (P : X → A → PMF X) (K : Set X) (c : X → A) : Prop :=
  ∀ x ∈ K, StaysIn (P x (c x)) K

/-- Functional legitimate constitutive states: the physical coordinate lies in
the declared viability kernel and the internal controller preserves that
kernel. -/
def legitimateConstitutiveDomain
    {X : Type uX} {A : Type uA}
    (P : X → A → PMF X) (K : Set X) :
    Set (ConstitutiveState X A) :=
  {z | z.1 ∈ K ∧ PreservingController P K z.2}

/-- States whose internal controller is not functionally preserving. -/
def nonPreservingControllerDomain
    {X : Type uX} {A : Type uA}
    (P : X → A → PMF X) (K : Set X) :
    Set (ConstitutiveState X A) :=
  {z | ¬ PreservingController P K z.2}

/-- Every old singleton-controller constitutive domain embeds into the new
functional legitimate class when that controller is preserving. -/
theorem constitutiveDomain_subset_legitimate
    {X : Type uX} {A : Type uA}
    (P : X → A → PMF X) (K : Set X) (pi : X → A)
    (hpi : PreservingController P K pi) :
    constitutiveDomain K pi ⊆ legitimateConstitutiveDomain P K := by
  rintro ⟨x, c⟩ ⟨hx, hc⟩
  change x ∈ K at hx
  change c = pi at hc
  subst c
  exact ⟨hx, hpi⟩

/-- A nonempty fixed viability kernel always yields at least one legitimate
constitutive state, by the stationary preserving selector already provided by
P-PER's finite viability machinery. -/
theorem legitimateConstitutiveDomain_nonempty_of_fixed
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) {K : Set X}
    (hK : K.Nonempty)
    (hfix : viabilityStep P K = K) :
    (legitimateConstitutiveDomain P K).Nonempty := by
  obtain ⟨pi, hpi⟩ := exists_stationary_policy_of_fixed P hfix
  rcases hK with ⟨x, hx⟩
  exact ⟨(x, pi), hx, hpi⟩

/-- The current Track-X constitutive lift is closed on the functional
legitimate domain.  It therefore already proves the *closure* half of finite
self-stabilization. -/
theorem constitutiveLift_staysIn_legitimate
    {X : Type uX} {A : Type uA}
    (P : X → A → PMF X) (K : Set X)
    {z : ConstitutiveState X A}
    (hz : z ∈ legitimateConstitutiveDomain P K) :
    StaysIn (constitutiveLift P z ())
      (legitimateConstitutiveDomain P K) := by
  rcases z with ⟨x, c⟩
  rcases hz with ⟨hx, hc⟩
  intro y hy
  rcases y with ⟨y, c'⟩
  have hy' : y ∈ (P x (c x)).support ∧ c' = c := by
    simpa [constitutiveLift] using hy
  have hc' : c' = c := hy'.2
  subst c'
  change y ∈ K ∧ PreservingController P K c
  exact ⟨hc x hx hy'.1, hc⟩

/-- Functional legitimacy and controller corruption are disjoint by
construction. -/
theorem not_mem_legitimate_of_nonpreserving
    {X : Type uX} {A : Type uA}
    (P : X → A → PMF X) (K : Set X)
    {z : ConstitutiveState X A}
    (hz : z ∈ nonPreservingControllerDomain P K) :
    z ∉ legitimateConstitutiveDomain P K := by
  intro hlegit
  exact hz hlegit.2

/-- **O1 self-repair boundary.**  A non-preserving controller remains
non-preserving after one step of the current constitutive lift, because the
controller coordinate is copied exactly. -/
theorem constitutiveLift_staysIn_nonPreserving
    {X : Type uX} {A : Type uA}
    (P : X → A → PMF X) (K : Set X)
    {z : ConstitutiveState X A}
    (hz : z ∈ nonPreservingControllerDomain P K) :
    StaysIn (constitutiveLift P z ())
      (nonPreservingControllerDomain P K) := by
  rcases z with ⟨x, controller⟩
  change ¬ PreservingController P K controller at hz
  intro y hy
  rcases y with ⟨y, controller'⟩
  have hy' :
      y ∈ (P x (controller x)).support ∧ controller' = controller := by
    simpa [constitutiveLift] using hy
  change ¬ PreservingController P K controller'
  simpa [hy'.2] using hz

/-- The no-repair boundary propagates to every finite-time marginal of the
actual autonomous recursion.  Thus the old lift has closure but lacks the
convergence half of self-stabilization. -/
theorem constitutiveLift_nonpreserving_all_marginals
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A]
    (P : X → A → PMF X) (K : Set X)
    {z : ConstitutiveState X A}
    (hz : z ∈ nonPreservingControllerDomain P K) :
    ∀ n : ℕ,
      StaysIn
        (stationaryStateLaw
          (constitutiveLift P) noExternalControl (PMF.pure z) n)
        (nonPreservingControllerDomain P K) := by
  apply stationaryStateLaw_staysIn
    (constitutiveLift P) noExternalControl
    (nonPreservingControllerDomain P K) (PMF.pure z)
  · simpa [StaysIn] using hz
  · intro w hw
    simpa [noExternalControl] using
      constitutiveLift_staysIn_nonPreserving P K hw

end

end UEOT.V3.Compression.Objecthood
