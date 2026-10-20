import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PosteriorSupportCoverage

/-!
# Policy-prefix congruence and conditional reachable extension

Agreement before a time fixes its actual prefix, and agreement through
that time fixes its state-action law. The extension theorem retains its
explicit strong premise over every already-certified prefix; that premise
is not used by the separate exact finite support-viability equivalence.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace PolicyPrefixCongruenceCheck

open UEOT.V3.PathError

universe u

/-- The actual microscopic prefix at n depends only on policy components
strictly before n. No assumption on the current or future action law occurs. -/
theorem actual_causalLaw_congr_before
    {X Y A : Type u}
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π π' : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ)
    (hπ : ∀ j, j < n → ∀ hc, π j hc = π' j hc) :
    causalLaw p₀ (riskMicroControlKernel q P π) n =
      causalLaw p₀ (riskMicroControlKernel q P π') n := by
  apply causalLaw_congr_before
  intro j hj h
  exact congrArg
    (fun μ : PMF A => pmfExtend μ (P j (riskLastState j h)))
    (hπ j hj (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) j h))

/-- The actual state/action law at n also samples the current action, so
policy agreement is required through n, including the current component. -/
theorem deployment_rowLaw_congr_through
    {X Y A : Type u}
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π π' : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ)
    (hπ : ∀ j, j ≤ n → ∀ hc, π j hc = π' j hc) :
    coverageDeploymentRowLaw p₀ q P π n =
      coverageDeploymentRowLaw p₀ q P π' n := by
  have hprefix := actual_causalLaw_congr_before
    p₀ q P π π' n (fun j hj => hπ j (Nat.le_of_lt hj))
  have hcurrent : π n = π' n := funext (hπ n le_rfl)
  unfold coverageDeploymentRowLaw
  rw [hprefix, hcurrent]

end PolicyPrefixCongruenceCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace ReachablePolicyExtensionCheck

open MeasureTheory UEOT.V3.PathError
open scoped Classical

universe u

noncomputable section

/-- A feasible certified action at each currently supported coarse history
constructs one real policy extension. The current prefix law is preserved;
the new current state/action law has zero uncertified mass. -/
theorem extend_policy_at_reachable_histories
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A) (n : ℕ)
    (hfeasible :
      ∀ hc ∈ ((causalLaw p₀ (riskMicroControlKernel q P π) n).map
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)).support,
        ∃ a : A,
          ∀ h ∈ (causalLaw p₀ (riskMicroControlKernel q P π) n).support,
            riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h = hc →
              certified n (riskLastState n h) a) :
    ∃ π' : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      (∀ j, j < n → ∀ hc, π' j hc = π j hc) ∧
        (coverageDeploymentRowLaw p₀ q P π' n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  let D := causalLaw p₀ (riskMicroControlKernel q P π) n
  let F := riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n
  let now : CausalHistory Y (A × Y) n → PMF A := fun hc =>
    if hg : hc ∈ (D.map F).support
      then PMF.pure (Classical.choose (hfeasible hc hg))
      else π n hc
  let π' := Function.update π n now
  have hagree : ∀ j, j < n → ∀ hc, π' j hc = π j hc := by
    intro j hj hc
    dsimp only [π']
    rw [Function.update_of_ne (Nat.ne_of_lt hj)]
  have hcurrent : π' n = now := by simp [π']
  have hprefix : causalLaw p₀ (riskMicroControlKernel q P π') n = D :=
    PolicyPrefixCongruenceCheck.actual_causalLaw_congr_before p₀ q P π' π n hagree
  refine ⟨π', hagree, ?_⟩
  apply le_antisymm _ ENNReal.toReal_nonneg
  apply PosteriorSupportCoverageCheck.supported_history_actions_bound_actual_coverage
    p₀ q P π' certified n (fun _ _ => True) 0
  · intro h hh a ha _
    have hhD : h ∈ D.support := by simpa only [hprefix] using hh
    have hg : F h ∈ (D.map F).support :=
      (PMF.mem_support_map_iff F D (F h)).mpr ⟨h, hhD, rfl⟩
    have hpure : π' n (F h) = PMF.pure (Classical.choose (hfeasible (F h) hg)) := by
      rw [hcurrent]
      simp only [now, dif_pos hg]
    have haeq : a = Classical.choose (hfeasible (F h) hg) := by
      have hnonzero : (π' n (F h)) a ≠ 0 := (PMF.mem_support_iff _ _).mp ha
      rw [hpure] at hnonzero
      by_contra hne
      apply hnonzero
      simp [PMF.pure_apply]
      exact hne
    rw [haeq]
    exact (Classical.choose_spec (hfeasible (F h) hg)) h hhD rfl
  · intro hc _
    simp

/-- Under the explicit condition that every covered finite policy prefix
can be extended at every actually supported coarse history, a full policy
with zero uncertified occupancy exists up to the specified horizon. This is
a sufficient classical construction, not a weakest or executable criterion. -/
theorem exists_zero_uncovered_policy_of_extendability
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (certified : ℕ → X → A → Prop)
    (πbase : ∀ n, CausalHistory Y (A × Y) n → PMF A) (T : ℕ)
    (hExtend :
      ∀ n, n < T → ∀ π : ∀ k, CausalHistory Y (A × Y) k → PMF A,
        (∀ j, j < n →
          (coverageDeploymentRowLaw p₀ q P π j).toMeasure.real
            {xa | ¬ certified j xa.1 xa.2} = 0) →
        ∀ hc ∈ ((causalLaw p₀ (riskMicroControlKernel q P π) n).map
            (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)).support,
          ∃ a : A,
            ∀ h ∈ (causalLaw p₀ (riskMicroControlKernel q P π) n).support,
              riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h = hc →
                certified n (riskLastState n h) a) :
    ∃ π : ∀ n, CausalHistory Y (A × Y) n → PMF A,
      ∀ n, n < T →
        (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
          {xa | ¬ certified n xa.1 xa.2} = 0 := by
  have hbuild : ∀ n, n ≤ T →
      ∃ π : ∀ k, CausalHistory Y (A × Y) k → PMF A,
        ∀ j, j < n →
          (coverageDeploymentRowLaw p₀ q P π j).toMeasure.real
            {xa | ¬ certified j xa.1 xa.2} = 0 := by
    intro n
    induction n with
    | zero =>
        intro _
        refine ⟨πbase, ?_⟩
        intro j hj
        exact False.elim (Nat.not_lt_zero j hj)
    | succ n ih =>
        intro hn
        have hnT : n < T := Nat.lt_of_succ_le hn
        obtain ⟨π, hcovered⟩ := ih (Nat.le_of_lt hnT)
        obtain ⟨π', hagree, hzero⟩ := extend_policy_at_reachable_histories
          p₀ q P certified π n (hExtend n hnT π hcovered)
        refine ⟨π', ?_⟩
        intro j hj
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hjn | rfl
        · have hrow := PolicyPrefixCongruenceCheck.deployment_rowLaw_congr_through
            p₀ q P π' π j (fun k hk => hagree k (lt_of_le_of_lt hk hjn))
          rw [hrow]
          exact hcovered j hjn
        · exact hzero
  exact hbuild T le_rfl


end
end ReachablePolicyExtensionCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
