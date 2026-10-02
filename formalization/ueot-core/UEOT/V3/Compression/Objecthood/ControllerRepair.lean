import UEOT.V3.Compression.Objecthood.Legitimacy

/-!
# Track O / O2 — autonomous controller repair

O1 showed that the merged constitutive lift has closure on the functional
legitimate domain but no convergence from a corrupted controller.  O2 adds the
smallest finite repair mechanism that closes precisely that gap.

The repair controller is not supplied as a runtime input.  It is selected once
from the fixed viability-kernel witness already guaranteed by P-PER.  At each
step the constitutive dynamics keeps an already preserving internal controller,
but replaces a non-preserving one by that canonical preserving witness *before*
the physical transition is executed.

This establishes controller-level self-stabilization while the physical state
is still inside `K`.  Recovery from physical states outside `K` is deliberately
reserved for O4.
-/

namespace UEOT.V3.Compression.Objecthood

open Set
open UEOT.V3.ViabilityKernel
open UEOT.V3.Compression.CrossTrack

universe uX uA

noncomputable section

/-- A canonical preserving controller extracted from the fixed-kernel P-PER
witness.  The choice is a construction witness, not an informative runtime
control channel. -/
noncomputable def canonicalPreservingController
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K) : X → A :=
  Classical.choose (exists_stationary_policy_of_fixed P hfix)

/-- The canonical P-PER controller really preserves the fixed kernel. -/
theorem canonicalPreservingController_preserving
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K) :
    PreservingController P K
      (canonicalPreservingController P K hfix) :=
  Classical.choose_spec (exists_stationary_policy_of_fixed P hfix)

/-- Repair only when necessary.  Legitimate controller variants are preserved
rather than canonicalized away. -/
noncomputable def repairedController
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (c : X → A) : X → A := by
  classical
  exact if PreservingController P K c then c
    else canonicalPreservingController P K hfix

/-- Already legitimate controllers are left unchanged. -/
theorem repairedController_eq_self_of_preserving
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (c : X → A) (hc : PreservingController P K c) :
    repairedController P K hfix c = c := by
  simp [repairedController, hc]

/-- Corrupted controllers are replaced by the canonical preserving witness. -/
theorem repairedController_eq_canonical_of_nonpreserving
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (c : X → A) (hc : ¬ PreservingController P K c) :
    repairedController P K hfix c =
      canonicalPreservingController P K hfix := by
  simp [repairedController, hc]

/-- Every repaired controller is functionally legitimate. -/
theorem repairedController_preserving
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (c : X → A) :
    PreservingController P K (repairedController P K hfix c) := by
  classical
  by_cases hc : PreservingController P K c
  · simpa [repairedController, hc] using hc
  · simpa [repairedController, hc] using
      canonicalPreservingController_preserving P K hfix

/-- Autonomous controller-repair dynamics.  Repair is performed before the
physical action is selected, so a corrupt controller cannot eject a state from
`K` during the repair step.  The only external action remains `Unit`. -/
noncomputable def controllerRepairLift
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K) :
    ConstitutiveState X A → Unit → PMF (ConstitutiveState X A) :=
  fun z _ =>
    let c' := repairedController P K hfix z.2
    (P z.1 (c' z.1)).bind fun y => PMF.pure (y, c')

/-- No informative external action can alter the controller-repair dynamics. -/
theorem controllerRepairLift_external_action_irrelevant
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    (z : ConstitutiveState X A) (u v : Unit) :
    controllerRepairLift P K hfix z u =
      controllerRepairLift P K hfix z v := by
  cases u
  cases v
  rfl

/-- On an already legitimate state, O2 repair dynamics is exactly the merged
Track-X constitutive dynamics: no legitimate controller variant is rewritten. -/
theorem controllerRepairLift_eq_constitutiveLift_of_legitimate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hz : z ∈ legitimateConstitutiveDomain P K) :
    controllerRepairLift P K hfix z () = constitutiveLift P z () := by
  rcases z with ⟨x, c⟩
  have hc : PreservingController P K c := hz.2
  simp [controllerRepairLift, repairedController, hc, constitutiveLift]

/-- **O2 controller convergence.**  From any physical state already in `K`,
one autonomous step enters the functional legitimate constitutive domain,
regardless of the stored controller. -/
theorem controllerRepairLift_enters_legitimate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hx : z.1 ∈ K) :
    StaysIn (controllerRepairLift P K hfix z ())
      (legitimateConstitutiveDomain P K) := by
  rcases z with ⟨x, c⟩
  let c' := repairedController P K hfix c
  have hc' : PreservingController P K c' :=
    repairedController_preserving P K hfix c
  intro w hw
  rcases w with ⟨y, d⟩
  have hw' : y ∈ (P x (c' x)).support ∧ d = c' := by
    simpa [controllerRepairLift, c'] using hw
  change y ∈ K ∧ PreservingController P K d
  refine ⟨hc' x hx hw'.1, ?_⟩
  simpa [hw'.2] using hc'

/-- The legitimate domain is closed under O2 repair dynamics. -/
theorem controllerRepairLift_staysIn_legitimate
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hz : z ∈ legitimateConstitutiveDomain P K) :
    StaysIn (controllerRepairLift P K hfix z ())
      (legitimateConstitutiveDomain P K) :=
  controllerRepairLift_enters_legitimate P K hfix hz.1

/-- After the first repair step, every finite-time marginal remains in the
functional legitimate domain.  This is controller-level closure + convergence
without yet invoking path-measure machinery. -/
theorem controllerRepairLift_all_marginals_after_one
    {X : Type uX} {A : Type uA}
    [Fintype X] [Fintype A] [Nonempty A]
    (P : X → A → PMF X) (K : Set X)
    (hfix : viabilityStep P K = K)
    {z : ConstitutiveState X A}
    (hx : z.1 ∈ K) :
    ∀ n : ℕ,
      StaysIn
        (stationaryStateLaw
          (controllerRepairLift P K hfix)
          noExternalControl (PMF.pure z) (n + 1))
        (legitimateConstitutiveDomain P K) := by
  intro n
  induction n with
  | zero =>
      rw [stationaryStateLaw_succ, stationaryStateLaw_zero]
      simpa [noExternalControl] using
        controllerRepairLift_enters_legitimate P K hfix hx
  | succ n ih =>
      rw [stationaryStateLaw_succ]
      unfold StaysIn at ih ⊢
      rw [PMF.support_bind]
      refine iUnion_subset fun w => ?_
      refine iUnion_subset fun hw => ?_
      have hwL : w ∈ legitimateConstitutiveDomain P K := ih hw
      exact controllerRepairLift_staysIn_legitimate P K hfix hwL

end

end UEOT.V3.Compression.Objecthood
