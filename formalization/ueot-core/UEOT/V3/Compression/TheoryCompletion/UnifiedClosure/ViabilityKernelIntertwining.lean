import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictiveViabilityTransport
import Mathlib.Tactic

/-!
# UMC: endogenous finite-horizon viable-action existence commutes with exact quotients

Unlike a prescribed safe policy, this module derives the EXISTENCE of an
action preserving a registered region directly from the same source kernel.
The finite-horizon controlled viability predicate is built by backward
induction on actual transition support and includes states whose chosen
action can keep all possible successors viable. An exact stochastic control
quotient transports this existential predecessor, not just a supplied
controller's individual positive-probability paths.

This is an operational viability result, not endogenous purpose, repair,
long-run ergodicity, biological self-construction or physical parenthood.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uY uA uI

/-- Actual supported micro successors stay inside the pullback of a macro
predicate iff the corresponding macro-kernel row puts zero mass outside it. -/
theorem macro_zero_outside_iff_micro_zero_outside
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (good : Y → Prop) (x : X) (a : A) :
    (∀ d : Y, ¬ good d →
       Q.macroModel.transition (Q.f x) a d = 0) ↔
    (∀ z : X, ¬ good (Q.f z) →
       Q.micro.transition x a z = 0) := by
  classical
  constructor
  · intro hmacro z hz
    have hbound := micro_transition_mass_le_macro_class_mass Q x z a
    have hzero := hmacro (Q.f z) hz
    have hnonneg := Q.micro.transition_nonneg x a z
    linarith
  · intro hmicro d hd
    rw [← Q.transition_closed x a d]
    unfold fiberMass
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hclass : Q.f z = d
    · have hbad : ¬ good (Q.f z) := by simpa [hclass] using hd
      simp [hclass, hmicro z hbad]
    · simp [hclass]

/-- Finite-horizon feedback viability in the macro state space. At each
step the controller may choose an action depending on the CURRENT state. -/
def macroViable
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) : ℕ → Y → Prop
  | 0, c => safe c
  | n+1, c =>
      safe c ∧ ∃ a : A, ∀ d : Y,
        ¬ macroViable Q safe n d →
          Q.macroModel.transition c a d = 0

/-- The same finite-horizon feedback viability problem on the actual
microscopic source, with the SAME registered safety observable. -/
def microViable
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) : ℕ → X → Prop
  | 0, x => safe (Q.f x)
  | n+1, x =>
      safe (Q.f x) ∧ ∃ a : A, ∀ z : X,
        ¬ microViable Q safe n z →
          Q.micro.transition x a z = 0

/-- A NEW crossed existential consequence: exactly the states which have
a finite-horizon, supported-successor-safe feedback policy upstairs also
have one downstairs, even though no fixed policy was given as an input.
The equivalence is relative to a saturated registered safety set. -/
theorem micro_viability_iff_macro_viability
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) :
    ∀ n : ℕ, ∀ x : X,
      microViable Q safe n x ↔ macroViable Q safe n (Q.f x) := by
  classical
  intro n
  induction n with
  | zero =>
      intro x
      rfl
  | succ n ih =>
      intro x
      change (safe (Q.f x) ∧
          ∃ a : A, ∀ z : X,
            ¬ microViable Q safe n z →
              Q.micro.transition x a z = 0) ↔
        (safe (Q.f x) ∧
          ∃ a : A, ∀ d : Y,
            ¬ macroViable Q safe n d →
              Q.macroModel.transition (Q.f x) a d = 0)
      constructor
      · rintro ⟨hsafe, a, hstep⟩
        refine ⟨hsafe, a, ?_⟩
        apply (macro_zero_outside_iff_micro_zero_outside
          Q (macroViable Q safe n) x a).2
        intro z hz
        exact hstep z ((ih z).not.mpr hz)
      · rintro ⟨hsafe, a, hstep⟩
        refine ⟨hsafe, a, ?_⟩
        have hmicro := (macro_zero_outside_iff_micro_zero_outside
          Q (macroViable Q safe n) x a).1 hstep
        intro z hz
        exact hmicro z ((ih z).not.mp hz)

/-- The operationally maximal n-step viable macro region has an exact
microphysical pullback, including all registered states and actions. -/
theorem micro_viable_region_is_exact_preimage
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ) :
    {x : X | microViable Q safe n x} =
      Q.f ⁻¹' {c : Y | macroViable Q safe n c} := by
  ext x
  exact micro_viability_iff_macro_viability Q safe n x


/-- The finite-horizon candidate regions form a descending chain. -/
theorem macro_viable_succ_subset
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ) :
    ∀ c : Y, macroViable Q safe (n+1) c → macroViable Q safe n c := by
  induction n with
  | zero =>
      intro c h
      exact h.1
  | succ n ih =>
      intro c h
      rcases h with ⟨hsafe, a, hstep⟩
      refine ⟨hsafe, a, ?_⟩
      intro d hd
      exact hstep d (fun hnext => hd (ih d hnext))

/-- A stable horizon yields actual EXISTENCE of a controlled invariant
macro action for each viable state; no strategy is supplied. -/
theorem macro_viable_fixedpoint_has_safe_action
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ)
    (hfix : ∀ c : Y, macroViable Q safe n c ↔
      macroViable Q safe (n+1) c) :
    ∀ c : Y, macroViable Q safe n c →
      ∃ a : A, ∀ d : Y, ¬ macroViable Q safe n d →
        Q.macroModel.transition c a d = 0 := by
  intro c hc
  exact ((hfix c).mp hc).2

/-- Feedback action synthesized from the viability fixed point.
Outside the kernel the fallback is arbitrary and has no claimed safety. -/
noncomputable def controllerFromViableFixedpoint
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ)
    (hfix : ∀ c : Y, macroViable Q safe n c ↔
      macroViable Q safe (n+1) c) : Y → A := by
  classical
  intro c
  by_cases hc : macroViable Q safe n c
  · exact Classical.choose (macro_viable_fixedpoint_has_safe_action
      Q safe n hfix c hc)
  · exact Classical.choice inferInstance

/-- A derived controller, rather than a given controller, protects the
registered viable region on every actual positive-support micro path. -/
theorem derived_controller_micro_path_viability
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ)
    (hfix : ∀ c : Y, macroViable Q safe n c ↔
      macroViable Q safe (n+1) c) :
    let sigma := controllerFromViableFixedpoint Q safe n hfix
    ∀ (x : X) (path : List X),
      macroViable Q safe n (Q.f x) →
      PositivePolicyRealization Q sigma x path →
      macroViable Q safe n
        (Q.f (realizedPolicyEndpoint x path)) := by
  classical
  let sigma := controllerFromViableFixedpoint Q safe n hfix
  have hclosed : ∀ c d : Y,
      macroViable Q safe n c → ¬ macroViable Q safe n d →
        Q.macroModel.transition c (sigma c) d = 0 := by
    intro c d hc hd
    have h := Classical.choose_spec (macro_viable_fixedpoint_has_safe_action
      Q safe n hfix c hc)
    simpa [sigma, controllerFromViableFixedpoint, dif_pos hc] using h d hd
  change ∀ (x : X) (path : List X),
    macroViable Q safe n (Q.f x) →
    PositivePolicyRealization Q sigma x path →
    macroViable Q safe n (Q.f (realizedPolicyEndpoint x path))
  intro x path hx hpath
  exact macro_policy_viability_survives_every_finite_micro_path
    Q (macroViable Q safe n) sigma hclosed x path hx hpath


/-- The n-step macro viability sets are decidable finite subsets of the
finite registered model, rather than untyped external evidence objects. -/
noncomputable def macroViableFinset
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ) : Finset Y := by
  classical
  exact Finset.univ.filter (macroViable Q safe n)

theorem macroViableFinset_succ_subset
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ) :
    macroViableFinset Q safe (n+1) ⊆ macroViableFinset Q safe n := by
  classical
  intro c hc
  have hh : macroViable Q safe (n+1) c := by
    simpa [macroViableFinset] using hc
  simpa [macroViableFinset] using
    macro_viable_succ_subset Q safe n c hh

/-- Finite-state controlled viability necessarily stabilizes within at most
the number of macro states; a strict refinement removes at least one state.
This removes an externally stipulated fixed-point existence hypothesis. -/
theorem exists_finite_viability_fixedpoint
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) :
    ∃ n : ℕ, n ≤ Fintype.card Y ∧
      ∀ c : Y, macroViable Q safe n c ↔
        macroViable Q safe (n+1) c := by
  classical
  let S : ℕ → Finset Y := macroViableFinset Q safe
  by_contra hnone
  have hno : ∀ n : ℕ, n ≤ Fintype.card Y →
      ¬ (∀ c : Y, macroViable Q safe n c ↔
          macroViable Q safe (n+1) c) := by
    intro n hn hf
    exact hnone ⟨n,hn,hf⟩
  have hstep : ∀ n : ℕ, n ≤ Fintype.card Y →
      (S (n+1)).card < (S n).card := by
    intro n hn
    have hsub : S (n+1) ⊆ S n := macroViableFinset_succ_subset Q safe n
    have hneq : S (n+1) ≠ S n := by
      intro heq
      apply hno n hn
      intro c
      have hh : c ∈ S n ↔ c ∈ S (n+1) := by rw [heq]
      simpa [S, macroViableFinset] using hh
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub,hneq⟩)
  have hcost : ∀ n : ℕ, n ≤ Fintype.card Y + 1 →
      n + (S n).card ≤ Fintype.card Y := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hsubset : S 0 ⊆ (Finset.univ : Finset Y) := Finset.subset_univ _
        simpa using Finset.card_le_card hsubset
    | succ n ih =>
        intro hn
        have hne : n ≤ Fintype.card Y := by omega
        have hh := hstep n hne
        have prev := ih (by omega)
        omega
  have absurd := hcost (Fintype.card Y+1) (by omega)
  omega

/-- For EVERY finite exact-controlled quotient, a finite-iteration fixed
point can be constructed; its policy is optimal with respect to hard
survival feasibility (not an externally specified reward optimum). -/
theorem exists_derived_survival_controller
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) :
    ∃ n : ℕ, n ≤ Fintype.card Y ∧
      ∃ sigma : Y → A,
      ∀ (x : X) (path : List X),
        macroViable Q safe n (Q.f x) →
        PositivePolicyRealization Q sigma x path →
        macroViable Q safe n
          (Q.f (realizedPolicyEndpoint x path)) := by
  obtain ⟨n,hn,hfix⟩ := exists_finite_viability_fixedpoint Q safe
  refine ⟨n,hn,controllerFromViableFixedpoint Q safe n hfix,?_⟩
  exact derived_controller_micro_path_viability Q safe n hfix


/-- Any registered controlled-invariant region is included in EVERY
finite-horizon viability iterate. Thus a stabilized iterate is the
GREATEST controlled-invariant subset of the registered safety predicate,
not merely one region protected by one selected policy. -/
theorem invariant_region_subset_every_macro_viability_horizon
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe region : Y → Prop)
    (hinside : ∀ c : Y, region c → safe c)
    (hcontrol : ∀ c : Y, region c →
      ∃ a : A, ∀ d : Y, ¬ region d →
        Q.macroModel.transition c a d = 0) :
    ∀ (n : ℕ) (c : Y), region c → macroViable Q safe n c := by
  intro n
  induction n with
  | zero =>
      intro c hc
      exact hinside c hc
  | succ n ih =>
      intro c hc
      obtain ⟨a,ha⟩ := hcontrol c hc
      refine ⟨hinside c hc, a, ?_⟩
      intro d hd
      apply ha d
      intro hregion
      exact hd (ih d hregion)

/-- The stabilized region is the greatest controlled-invariant subset
of the supplied safe predicate. Controller existential quantification
is genuine and no externally fixed sigma appears in the conclusion. -/
theorem fixed_viability_is_greatest_controlled_invariant
    {X : Type uX} {Y : Type uY} {A : Type uA}
    [Fintype X] [Fintype Y] [Fintype A] [Nonempty A]
    (Q : ExactControlQuotient X Y (fun _ => A))
    (safe : Y → Prop) (n : ℕ)
    (hfix : ∀ c : Y, macroViable Q safe n c ↔
      macroViable Q safe (n+1) c) :
    (∀ c, macroViable Q safe n c → safe c) ∧
    (∀ c, macroViable Q safe n c →
      ∃ a : A, ∀ d : Y, ¬ macroViable Q safe n d →
        Q.macroModel.transition c a d = 0) ∧
    (∀ region : Y → Prop,
      (∀ c, region c → safe c) →
      (∀ c, region c →
        ∃ a : A, ∀ d, ¬ region d →
          Q.macroModel.transition c a d = 0) →
      ∀ c, region c → macroViable Q safe n c) := by
  refine ⟨?_, macro_viable_fixedpoint_has_safe_action Q safe n hfix, ?_⟩
  · intro c hc
    cases n with
    | zero => exact hc
    | succ n => exact hc.1
  · intro region hinside hcontrol c hc
    exact invariant_region_subset_every_macro_viability_horizon
      Q safe region hinside hcontrol n c hc

/-- Exact prediction identifiability now builds a source-coherent control
quotient AND a finite-step greatest viable subset with its synthesized
micro-path-preserving feedback, discharging both independent transition
closure and previously externally supplied controller existence. -/
theorem future_observability_yields_derived_survival_controller
    {X : Type uX} {A : Type uA} {O : Type uO} {I : Type uI}
    [Fintype X] [Fintype A] [Nonempty A]
    [DecidableEq O] [Fintype I]
    (K : FiniteControlledStochasticKernel X A)
    (read : X → O) (probe : I → List (A × O))
    (coeff : ReachableState (stochasticFuture K read) → I → ℝ)
    (hresolve : FutureTestsResolvePredictiveClasses K read probe coeff)
    (rbar : ReachableState (stochasticFuture K read) → A → ℝ)
    (B β : ℝ) (hr : ∀ c a, |rbar c a| ≤ B)
    (hβpos : 0 < β) (hβlt : β < 1)
    (safe : ReachableState (stochasticFuture K read) → Prop) :
    letI : Fintype (ReachableState (stochasticFuture K read)) :=
      Fintype.ofFinite _
    let Q := predictiveFutureExactControlQuotient
      K read probe coeff hresolve rbar B β hr hβpos hβlt
    ∃ n : ℕ, n ≤ Fintype.card (ReachableState (stochasticFuture K read)) ∧
      ∃ sigma : ReachableState (stochasticFuture K read) → A,
      ∀ (x : X) (path : List X),
        macroViable Q safe n (Q.f x) →
        PositivePolicyRealization Q sigma x path →
        macroViable Q safe n
          (Q.f (realizedPolicyEndpoint x path)) := by
  classical
  letI : Fintype (ReachableState (stochasticFuture K read)) :=
    Fintype.ofFinite _
  let Q := predictiveFutureExactControlQuotient
    K read probe coeff hresolve rbar B β hr hβpos hβlt
  change ∃ n : ℕ, n ≤ Fintype.card (ReachableState (stochasticFuture K read)) ∧
    ∃ sigma : ReachableState (stochasticFuture K read) → A,
    ∀ (x : X) (path : List X),
      macroViable Q safe n (Q.f x) →
      PositivePolicyRealization Q sigma x path →
      macroViable Q safe n
        (Q.f (realizedPolicyEndpoint x path))
  exact exists_derived_survival_controller Q safe

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
