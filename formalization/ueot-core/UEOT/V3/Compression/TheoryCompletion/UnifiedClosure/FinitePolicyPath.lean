import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransport

/-!
# Specified finite current-observation policies: complete-path equivalence

Equality of the entire finite state path determines the initial law and the
transition rows at precisely the target's positive-occupancy states. Conversely,
those obligations certify the SAME specified policy, with no existential choice
of another controller. The zero horizon and unoccupied rows are included.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPathCheck

open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open SourcePolicyPathBridgeCheck FiniteActionRealizabilityCheck
open SameSourceKilledExitFluxCheck ConditionedActionTransportCheck
open scoped Classical

noncomputable section
universe u

/-- Equality of full paths entails equality of every earlier prefix. This uses
the actual `causalLaw_map_prefix` projection, not terminal-state equality. -/
theorem full_path_eq_prefix
    {X : Type u} (p mu : PMF X)
    (K L : ∀ n, CausalHistory X X n → PMF X) (T : ℕ)
    (heq : causalLaw p K T = causalLaw mu L T) :
    ∀ n, n ≤ T → causalLaw p K n = causalLaw mu L n := by
  induction T with
  | zero =>
      intro n hn
      have : n = 0 := by omega
      subst n
      exact heq
  | succ T ih =>
      intro n hn
      by_cases hlast : n = T + 1
      · subst n
        exact heq
      · have hprefix : causalLaw p K T = causalLaw mu L T := by
          have hm := congrArg
            (fun law : PMF (CausalHistory X X (T + 1)) => law.map Prod.fst) heq
          exact (causalLaw_map_prefix p K T).symm.trans
            (hm.trans (causalLaw_map_prefix mu L T))
        exact ih hprefix n (by omega)

/-- Initial equality and equality on positive target histories are exactly the
obligations for a complete finite path. Cancellation uses finite positive PMF
mass; no claim is made about null histories. -/
theorem causal_path_eq_iff
    {X : Type u} [Fintype X] (p mu : PMF X)
    (K L : ∀ n, CausalHistory X X n → PMF X) (T : ℕ) :
    causalLaw p K T = causalLaw mu L T ↔
      p = mu ∧ ∀ t, t < T → ∀ h, causalLaw mu L t h ≠ 0 → K t h = L t h := by
  constructor
  · intro heq
    have hpref := full_path_eq_prefix p mu K L T heq
    refine ⟨hpref 0 (Nat.zero_le T), ?_⟩
    intro t ht h hpos
    apply PMF.ext
    intro z
    have hstep := congrArg (fun law : PMF (CausalHistory X X (t + 1)) => law (h, z))
      (hpref (t + 1) (by omega))
    change pmfExtend (causalLaw p K t) (K t) (h, z) =
      pmfExtend (causalLaw mu L t) (L t) (h, z) at hstep
    rw [pmfExtend_apply, pmfExtend_apply, hpref t (by omega)] at hstep
    exact (ENNReal.mul_right_inj hpos (PMF.apply_ne_top _ _)).mp hstep
  · rintro ⟨hp, hrow⟩
    rw [hp]
    have hprefix : ∀ n, n ≤ T → causalLaw mu K n = causalLaw mu L n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
          intro hn
          apply PMF.ext
          rintro ⟨h, z⟩
          change pmfExtend (causalLaw mu K n) (K n) (h, z) =
            pmfExtend (causalLaw mu L n) (L n) (h, z)
          rw [pmfExtend_apply, pmfExtend_apply, ih (by omega)]
          by_cases hpos : causalLaw mu L n h = 0
          · simp [hpos]
          · rw [hrow n (by omega) h hpos]
    exact hprefix T (le_refl T)

/-- Full-state-path iff for this SPECIFIED time-varying current-observation
policy. The common observation policy is retained at every occupied hidden
state; the theorem does not extend the policy's information or preparation
powers. -/
theorem specified_policy_path_iff
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : ℕ → Y → PMF A)
    (p mu : PMF X) (R : ℕ → X → PMF X) (T : ℕ) :
    (causalLaw p (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (timeObservationPolicy sigma)) T).map (eraseActionHistory T) = targetPath mu R T ↔
      p = mu ∧ ∀ t, t < T → ∀ x ∈ occupiedState mu R t,
        actionMixture (M.transitionPMF x) (sigma t (q x)) = R t x := by
  rw [time_action_state_path_eq_mixture]
  change causalLaw p (timeMixtureKernel M q sigma) T =
    causalLaw mu (fun t h => R t (currentState t h)) T ↔ _
  rw [causal_path_eq_iff]
  constructor
  · rintro ⟨hp, hrow⟩
    refine ⟨hp, ?_⟩
    intro t ht x hx
    obtain ⟨h, hpos, rfl⟩ := hx
    exact hrow t ht h hpos
  · rintro ⟨hp, hrow⟩
    refine ⟨hp, ?_⟩
    intro t ht h hpos
    exact hrow t ht (currentState t h) ⟨h, hpos, rfl⟩

/-- Direct consumer of a concrete policy table, without passing through an
existential realizability theorem. -/
theorem specified_policy_path_of_rows
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : ℕ → Y → PMF A)
    (p mu : PMF X) (R : ℕ → X → PMF X) (T : ℕ)
    (hp : p = mu)
    (hrow : ∀ t, t < T → ∀ x ∈ occupiedState mu R t,
      actionMixture (M.transitionPMF x) (sigma t (q x)) = R t x) :
    (causalLaw p (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (timeObservationPolicy sigma)) T).map (eraseActionHistory T) = targetPath mu R T :=
  (specified_policy_path_iff M q sigma p mu R T).mpr ⟨hp, hrow⟩

/-- Same-source conditional consumer of the specified policy. The target is
identified with the original survival-conditioned experiment by the existing
generated/actual theorem, rather than assumed to equal a fitted process. -/
theorem specified_policy_conditioned_path_iff
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (basePolicy : Y → PMF A)
    (p0 p : PMF X) (safe : Set X) (T : ℕ)
    (hpos : 0 < SameSourceFiniteWindowCheck.actualSurvivalMass
      M q basePolicy p0 safe T)
    (fallback : ℕ → safe → PMF safe) (outside : ℕ → X → PMF X)
    (sigma : ℕ → Y → PMF A) :
    (causalLaw p (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (timeObservationPolicy sigma)) T).map (eraseActionHistory T) =
        SameSourceFiniteWindowCheck.actualConditionedPrefix
          M q basePolicy p0 safe T 0 hpos ↔
      p = preparedInitial M q basePolicy p0 safe T hpos fallback outside ∧
      ∀ t, t < T → ∀ x ∈ occupiedState
        (preparedInitial M q basePolicy p0 safe T hpos fallback outside)
        (conditionedTargetRow M q basePolicy safe T fallback outside) t,
        actionMixture (M.transitionPMF x) (sigma t (q x)) =
          conditionedTargetRow M q basePolicy safe T fallback outside t x := by
  have htarget : targetPath
      (preparedInitial M q basePolicy p0 safe T hpos fallback outside)
      (conditionedTargetRow M q basePolicy safe T fallback outside) T =
        SameSourceFiniteWindowCheck.actualConditionedPrefix
          M q basePolicy p0 safe T 0 hpos := by
    change TotalFiniteWindowCheck.generatedAmbientPrefix
      M q basePolicy p0 safe T hpos fallback outside T = _
    exact TotalFiniteWindowCheck.generated_ambient_eq_actual
      M q basePolicy p0 safe T 0 hpos fallback outside
  rw [← htarget]
  exact specified_policy_path_iff M q sigma p _ _ T

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPathCheck
