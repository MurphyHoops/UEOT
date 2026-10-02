import UEOT.V3.ViabilitySource
import UEOT.V3.ReflexiveStateAugmentation

/-!
# Endogenous constitutive persistence lift

P-PER-03 already constructs a deterministic stationary preserving selector for
every fixed finite viability kernel.  Its source statement is nevertheless a
controlled-system theorem: the selector is presented outside the state.

This module closes that specific residual by storing the selector inside the
reflexive state and executing the selected action internally.  The resulting
lift has `Unit` as its only external action.  Once initialized, its physical
state transition is exactly the policy-induced source transition and its
controller coordinate is preserved exactly.

This is a positive endogenous-persistence construction, but deliberately not a
full UEOT Objecthood theorem: the controller is synthesized from the viability
kernel and then embedded.  Self-construction, repair/replacement of the
controller, energetic closure, and a full Omega-loop certificate remain
separate obligations.
-/

namespace UEOT.V3.Compression.CrossTrack

open Set
open UEOT.V3
open UEOT.V3.ViabilityKernel
open UEOT.V3.ViabilityTrajectory

universe uX uA

noncomputable section

variable {X : Type uX} {A : Type uA}
variable [Fintype X] [Fintype A]

/-- Reflexive constitutive state: physical state together with the stationary
controller that maps physical states to actions. -/
abbrev ConstitutiveState (X : Type uX) (A : Type uA) :=
  UEOT.V3.ReflexiveStateAugmentation.ReflexiveState X (X → A)

noncomputable instance constitutiveStateFintype :
    Fintype (ConstitutiveState X A) :=
  Fintype.ofFinite (ConstitutiveState X A)

/-- Autonomous closed-loop lift.  The external action type is `Unit`; the
action applied to the physical transition is read from the controller stored
inside the current reflexive state.  The same controller is carried forward. -/
noncomputable def constitutiveLift
    (P : X → A → PMF X) :
    ConstitutiveState X A → Unit → PMF (ConstitutiveState X A) :=
  fun z _ =>
    (P z.1 (z.2 z.1)).bind (fun y => PMF.pure (y, z.2))

/-- The external action argument carries no information at all: every external
`Unit` action induces the same constitutive transition.  Runtime control is
therefore entirely supplied by the controller stored in reflexive state. -/
theorem constitutiveLift_external_action_irrelevant
    (P : X → A → PMF X)
    (z : ConstitutiveState X A) (u v : Unit) :
    constitutiveLift P z u = constitutiveLift P z v := by
  cases u
  cases v
  rfl

/-- Constitutive persistence domain: the physical state lies in `K` and the
internal controller is the selected preserving controller `pi`. -/
def constitutiveDomain (K : Set X) (pi : X → A) :
    Set (ConstitutiveState X A) :=
  {z | z.1 ∈ K ∧ z.2 = pi}

/-- The physical marginal of one constitutive step is exactly the original
source transition under the internally stored controller. -/
theorem constitutiveLift_state_projection
    (P : X → A → PMF X) (x : X) (pi : X → A) :
    (constitutiveLift P (x, pi) ()).bind (fun z => PMF.pure z.1) =
      P x (pi x) := by
  ext y
  simp [constitutiveLift]

/-- The controller coordinate is copied exactly through every constitutive
step. -/
theorem constitutiveLift_controller_projection
    (P : X → A → PMF X) (x : X) (pi : X → A) :
    (constitutiveLift P (x, pi) ()).bind (fun z => PMF.pure z.2) =
      PMF.pure pi := by
  ext controller
  simp [constitutiveLift]

/-- **Self-repair boundary.**  The present constitutive lift preserves whatever
controller it was initialized with.  Consequently a controller distinct from
the target `pi` stays distinct after every one-step support transition.  This
formally separates runtime-autonomous persistence from a stronger Omega-loop
claim that would repair or reconstruct a corrupted controller. -/
theorem constitutiveLift_wrong_controller_stays_wrong
    (P : X → A → PMF X) (x : X)
    (controller pi : X → A) (hne : controller ≠ pi) :
    StaysIn (constitutiveLift P (x, controller) ())
      {z : ConstitutiveState X A | z.2 ≠ pi} := by
  intro z hz
  rcases z with ⟨y, nextController⟩
  have hz' : y ∈ (P x (controller x)).support ∧
      nextController = controller := by
    simpa [constitutiveLift] using hz
  simpa [hz'.2] using hne

/-- Any source policy that preserves `K` makes the corresponding reflexive
constitutive domain invariant under the autonomous lift. -/
theorem constitutiveLift_staysIn
    (P : X → A → PMF X) {K : Set X} (pi : X → A)
    (hpi : ∀ x ∈ K, StaysIn (P x (pi x)) K)
    {z : ConstitutiveState X A}
    (hz : z ∈ constitutiveDomain K pi) :
    StaysIn (constitutiveLift P z ()) (constitutiveDomain K pi) := by
  rcases z with ⟨x, controller⟩
  rcases hz with ⟨hx, hc⟩
  have hx' : x ∈ K := by simpa using hx
  have hc' : controller = pi := by simpa using hc
  subst controller
  intro y hy
  rcases y with ⟨y, c⟩
  have hy' : y ∈ (P x (pi x)).support ∧ c = pi := by
    simpa [constitutiveLift] using hy
  exact ⟨hpi x hx' hy'.1, hy'.2⟩

/-- Under a preserving internal controller, the constitutive domain is itself
a fixed finite viability kernel of a system with no informative external
action channel. -/
theorem constitutiveDomain_fixed
    (P : X → A → PMF X) {K : Set X} (pi : X → A)
    (hpi : ∀ x ∈ K, StaysIn (P x (pi x)) K) :
    viabilityStep (constitutiveLift P) (constitutiveDomain K pi) =
      constitutiveDomain K pi := by
  apply Set.Subset.antisymm
  · exact viabilityStep_subset _ _
  · intro z hz
    exact ⟨hz, (), constitutiveLift_staysIn P pi hpi hz⟩

/-- There is only one external policy for the constitutive lift in any
information-bearing sense: every state is mapped to the unique `Unit` action. -/
def noExternalControl : ConstitutiveState X A → Unit := fun _ => ()

/-- A *given* preserving internal controller, rather than a separately
re-selected existential policy, keeps the genuine constitutive trajectory in
its constitutive domain at every discrete time with probability one. -/
theorem constitutive_all_times_safe_of_preserving
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) {K : Set X} (pi : X → A)
    (hpi : ∀ x ∈ K, StaysIn (P x (pi x)) K)
    (x : X) (hx : x ∈ K) :
    stationaryTrajMeasure
      (constitutiveLift P) noExternalControl
      (PMF.pure (x, pi))
      {omega | ∀ n : ℕ, omega n ∈ constitutiveDomain K pi} = 1 := by
  have hmu : StaysIn (PMF.pure (x, pi)) (constitutiveDomain K pi) := by
    simp [StaysIn, constitutiveDomain, hx]
  have hstep : ∀ z ∈ constitutiveDomain K pi,
      StaysIn (constitutiveLift P z (noExternalControl z))
        (constitutiveDomain K pi) := by
    intro z hz
    simpa [noExternalControl] using constitutiveLift_staysIn P pi hpi hz
  have hmarg : ∀ n : ℕ,
      StaysIn
        (stationaryStateLaw (constitutiveLift P) noExternalControl
          (PMF.pure (x, pi)) n)
        (constitutiveDomain K pi) :=
    stationaryStateLaw_staysIn
      (constitutiveLift P) noExternalControl
      (constitutiveDomain K pi) (PMF.pure (x, pi)) hmu hstep
  apply all_times_safe_of_coordinate_one
    (constitutiveLift P) noExternalControl (PMF.pure (x, pi))
    (constitutiveDomain K pi)
  intro n
  have hmeas : MeasurableSet (constitutiveDomain K pi) :=
    (Set.toFinite (constitutiveDomain K pi)).measurableSet
  have hcoord :
      (stationaryTrajMeasure
        (constitutiveLift P) noExternalControl (PMF.pure (x, pi))).map
        (fun z : ℕ → ConstitutiveState X A => z n)
        (constitutiveDomain K pi) = 1 := by
    rw [stationaryTrajMeasure_coordinate]
    exact (staysIn_iff_toMeasure_eq_one _ hmeas).1 (hmarg n)
  rw [MeasureTheory.Measure.map_apply (measurable_pi_apply n) hmeas] at hcoord
  exact hcoord

/-- Nonvacuous operational persistence certificate.  Unlike a bare fixed-set
statement, this certificate contains an actual physical seed inside the
stabilized viability kernel and one internal controller witnessing both
autonomous one-step closure and genuine all-times persistence. -/
structure ConstitutivePersistenceCertificate
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (V : Set X) where
  K : Set X
  controller : X → A
  seed : X
  kernel_sub_domain : K ⊆ V
  seed_mem : seed ∈ K
  source_fixed : viabilityStep P K = K
  source_winning :
    K = UEOT.V3.ViabilityStrategy.winningSet P V
  constitutive_fixed :
    viabilityStep (constitutiveLift P) (constitutiveDomain K controller) =
      constitutiveDomain K controller
  all_times_safe :
    stationaryTrajMeasure
      (constitutiveLift P) noExternalControl
      (PMF.pure (seed, controller))
      {omega | ∀ n : ℕ, omega n ∈ constitutiveDomain K controller} = 1

/-- **Nonvacuous endogenous constitutive persistence.**

If the source P-PER-03 winning set contains at least one actual state, the
stabilized viability kernel is nonempty and admits one controller that is
embedded in reflexive state, closes the autonomous constitutive dynamics, and
keeps the genuine infinite trajectory safe with probability one. -/
theorem exists_constitutivePersistenceCertificate_of_nonempty_winningSet
    [Nonempty A]
    [MeasurableSpace X]
    [MeasurableSingletonClass X]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) (V : Set X)
    (hwin : (UEOT.V3.ViabilityStrategy.winningSet P V).Nonempty) :
    Nonempty (ConstitutivePersistenceCertificate P V) := by
  obtain ⟨n, K, _hKiter, hKV, hfix, hKwin, hpolicy, _hall⟩ :=
    UEOT.V3.ViabilitySource.p_per_03 P V
  rcases hpolicy with ⟨pi, hpi⟩
  rcases hwin with ⟨x, hxwin⟩
  have hxK : x ∈ K := by
    rw [hKwin]
    exact hxwin
  refine ⟨{
    K := K
    controller := pi
    seed := x
    kernel_sub_domain := hKV
    seed_mem := hxK
    source_fixed := hfix
    source_winning := hKwin
    constitutive_fixed := constitutiveDomain_fixed P pi hpi
    all_times_safe := constitutive_all_times_safe_of_preserving P pi hpi x hxK
  }⟩

/-- **Fixed-kernel endogenous closure.**

P-PER-03's stationary-selector construction is enough to build a reflexive
closed-loop realization in which the preserving controller is internal state
and no nontrivial external action remains. -/
theorem exists_endogenous_constitutive_closure_of_fixed
    [Nonempty A]
    (P : X → A → PMF X) {K : Set X}
    (hfix : viabilityStep P K = K) :
    ∃ pi : X → A,
      viabilityStep (constitutiveLift P) (constitutiveDomain K pi) =
        constitutiveDomain K pi := by
  obtain ⟨pi, hpi⟩ := exists_stationary_policy_of_fixed P hfix
  exact ⟨pi, constitutiveDomain_fixed P pi hpi⟩

/-- **Finite endogenous persistence synthesis.**

Every finite controlled persistence problem reaches a stabilized viability
kernel; that kernel admits a stationary preserving selector; embedding that
selector into reflexive state produces an autonomous constitutive fixed set. -/
theorem exists_endogenous_constitutive_closure
    [Nonempty A]
    (P : X → A → PMF X) (V : Set X) :
    ∃ (n : ℕ) (K : Set X) (pi : X → A),
      K = viabilityIter P V n ∧
      K ⊆ V ∧
      viabilityStep P K = K ∧
      viabilityStep (constitutiveLift P) (constitutiveDomain K pi) =
        constitutiveDomain K pi := by
  obtain ⟨n, hfixed⟩ := exists_viabilityIter_fixed P V
  have hfix : viabilityStep P (viabilityIter P V n) =
      viabilityIter P V n := by
    simpa using hfixed
  have hsub : viabilityIter P V n ⊆ V := by
    simpa using viabilityIter_antitone P V (Nat.zero_le n)
  obtain ⟨pi, hpi⟩ := exists_stationary_policy_of_fixed P hfix
  exact ⟨n, viabilityIter P V n, pi, rfl, hsub, hfix,
    constitutiveDomain_fixed P pi hpi⟩

/-- **Path-level endogenous persistence.**

For any state in a fixed source viability kernel, one can synthesize an
internal controller such that the genuine Ionescu--Tulcea trajectory of the
constitutive lift, under the unique external `Unit` controller, remains in the
constitutive domain at every discrete time with probability one. -/
theorem exists_constitutive_all_times_safe_of_fixed
    [Nonempty A]
    [MeasurableSpace (ConstitutiveState X A)]
    [MeasurableSingletonClass (ConstitutiveState X A)]
    (P : X → A → PMF X) {K : Set X}
    (hfix : viabilityStep P K = K)
    (x : X) (hx : x ∈ K) :
    ∃ pi : X → A,
      stationaryTrajMeasure
        (constitutiveLift P) noExternalControl
        (PMF.pure (x, pi))
        {omega | ∀ n : ℕ, omega n ∈ constitutiveDomain K pi} = 1 := by
  obtain ⟨pi, hpi⟩ := exists_stationary_policy_of_fixed P hfix
  have hlift : viabilityStep (constitutiveLift P) (constitutiveDomain K pi) =
      constitutiveDomain K pi :=
    constitutiveDomain_fixed P pi hpi
  have hmu : StaysIn (PMF.pure (x, pi)) (constitutiveDomain K pi) := by
    simp [StaysIn, constitutiveDomain, hx]
  have hmeas : MeasurableSet (constitutiveDomain K pi) :=
    (Set.toFinite (constitutiveDomain K pi)).measurableSet
  obtain ⟨external, hsafe⟩ :=
    exists_stationary_policy_all_times_of_fixed
      (constitutiveLift P) hlift (PMF.pure (x, pi)) hmu hmeas
  have hext : external = noExternalControl := by
    funext z
    exact Subsingleton.elim _ _
  subst external
  exact ⟨pi, hsafe⟩

end

end UEOT.V3.Compression.CrossTrack
