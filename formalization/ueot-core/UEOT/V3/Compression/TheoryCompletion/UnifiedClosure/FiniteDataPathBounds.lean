import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionCertificate
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage

/-!
# Finite-data path budgets for the specified action table

The initial-law error and target-occupied row errors belong to the same
specified experiment. Target-zero histories need no row bound. The source
comparison keeps the same policy in both sources, including its data-selected
literal weights; no additional selected-controller fitting hypothesis appears.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataPathBounds

open MeasureTheory UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open SourcePolicyPathBridgeCheck FiniteActionRealizabilityCheck
open ConditionedActionTransportCheck FiniteActionCertificateCheck
open scoped BigOperators Classical

noncomputable section
universe u

/-- Initial mismatch plus target-weighted finite row errors controls the whole
path. This reuses the exact weighted extension identity and the shared-kernel
TV contraction; empirical zero counts are never substituted for target support. -/
theorem causal_path_tv_le
    {X : Type u} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p mu : PMF X) (K L : ∀ n, CausalHistory X X n → PMF X)
    (T : ℕ) (delta0 : ℝ) (epsilon : ℕ → ℝ)
    (hinit : tvDist p.toMeasure mu.toMeasure ≤ delta0)
    (hrow : ∀ n, n < T → ∀ h, causalLaw mu L n h ≠ 0 →
      tvDist (K n h).toMeasure (L n h).toMeasure ≤ epsilon n) :
    tvDist (causalLaw p K T).toMeasure (causalLaw mu L T).toMeasure ≤
      min 1 (delta0 + ∑ n ∈ Finset.range T, epsilon n) := by
  apply le_min (tvDist_le_one _ _)
  have hprefix : ∀ n, n ≤ T →
      tvDist (causalLaw p K n).toMeasure (causalLaw mu L n).toMeasure ≤
        delta0 + ∑ i ∈ Finset.range n, epsilon i := by
    intro n
    induction n with
    | zero =>
        intro _
        change tvDist p.toMeasure mu.toMeasure ≤ delta0 + ∑ i ∈ Finset.range 0, epsilon i
        simpa only [Finset.range_zero, Finset.sum_empty, add_zero] using hinit
    | succ n ih =>
        intro hn
        let pn := causalLaw p K n
        let qn := causalLaw mu L n
        have hstep : tvDist (pmfExtend qn (K n)).toMeasure
            (pmfExtend qn (L n)).toMeasure ≤ epsilon n := by
          rw [coverage_tv_extend_same_initial]
          calc
            _ ≤ ∑ h, (qn h).toReal * epsilon n := by
              apply Finset.sum_le_sum
              intro h _
              by_cases hz : qn h = 0
              · simp [hz]
              · exact mul_le_mul_of_nonneg_left (hrow n (by omega) h hz)
                  ENNReal.toReal_nonneg
            _ = epsilon n := by rw [← Finset.sum_mul, coverage_sum_toReal, one_mul]
        have hcarry := coverage_tv_extend_same_kernel pn qn (K n)
        have htriangle := UEOT.V3.TransportDefect.tvDist_triangle
          (pmfExtend pn (K n)).toMeasure (pmfExtend qn (K n)).toMeasure
          (pmfExtend qn (L n)).toMeasure
        change tvDist (pmfExtend pn (K n)).toMeasure
          (pmfExtend qn (L n)).toMeasure ≤ _
        calc
          _ ≤ tvDist pn.toMeasure qn.toMeasure + epsilon n :=
            htriangle.trans (add_le_add hcarry hstep)
          _ ≤ (delta0 + ∑ i ∈ Finset.range n, epsilon i) + epsilon n :=
            add_le_add (ih (by omega)) le_rfl
          _ = _ := by rw [Finset.sum_range_succ]; ring
  exact hprefix T le_rfl

/-- Approximate whole-state-path consumer of this SAME time-dependent policy.
Only positive target-occupancy states carry a residual obligation. -/
theorem specified_policy_tv_le
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : ℕ → Y → PMF A)
    (p mu : PMF X) (R : ℕ → X → PMF X) (T : ℕ)
    (delta0 : ℝ) (epsilon : ℕ → ℝ)
    (hinit : tvDist p.toMeasure mu.toMeasure ≤ delta0)
    (hrow : ∀ t, t < T → ∀ x ∈ occupiedState mu R t,
      tvDist (actionMixture (M.transitionPMF x) (sigma t (q x))).toMeasure
        (R t x).toMeasure ≤ epsilon t) :
    tvDist
      ((causalLaw p (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (timeObservationPolicy sigma)) T).map (eraseActionHistory T)).toMeasure
      (targetPath mu R T).toMeasure ≤ min 1 (delta0 + ∑ t ∈ Finset.range T, epsilon t) := by
  rw [time_action_state_path_eq_mixture]
  apply causal_path_tv_le p mu (timeMixtureKernel M q sigma)
    (fun n h => R n (currentState n h)) T delta0 epsilon hinit
  intro n hn h hpos
  exact hrow n hn (currentState n h) ⟨h, hpos, rfl⟩

/-- Direct literal-table form: the same finite `w` supplies every action PMF;
post-horizon actions are explicit and cannot change the certified window. -/
theorem literal_table_tv_le
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (M : Model X (fun _ => A)) (q : X → Y)
    (p mu : PMF X) (R : ℕ → X → PMF X) (T : ℕ)
    (w : Fin T → Y → A → ℚ) (hw : ∀ t y, ValidRow (w t y)) (after : A)
    (delta0 : ℝ) (epsilon : ℕ → ℝ)
    (hinit : tvDist p.toMeasure mu.toMeasure ≤ delta0)
    (hrow : ∀ t (ht : t < T), ∀ x ∈ occupiedState mu R t,
      tvDist (actionMixture (M.transitionPMF x)
        (rowPMF (w ⟨t,ht⟩ (q x)) (hw ⟨t,ht⟩ (q x)))).toMeasure
        (R t x).toMeasure ≤ epsilon t) :
    tvDist
      ((causalLaw p (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (timeObservationPolicy (policy w hw after))) T).map (eraseActionHistory T)).toMeasure
      (targetPath mu R T).toMeasure ≤ min 1 (delta0 + ∑ t ∈ Finset.range T, epsilon t) := by
  apply specified_policy_tv_le M q (policy w hw after) p mu R T delta0 epsilon hinit
  intro t ht x hx
  simpa only [policy, dif_pos ht] using hrow t ht x hx

/-- A uniform all-action source bound remains valid after the SAME arbitrary
policy table is selected. The initial error includes any actual noisy preparation;
all ambient rows, including an absorbing failure state, are covered explicitly. -/
theorem same_table_source_tv_le
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (M N : Model X (fun _ => A)) (q : X → Y) (sigma : ℕ → Y → PMF A)
    (p pref : PMF X) (T : ℕ) (delta0 delta : ℝ)
    (hinit : tvDist p.toMeasure pref.toMeasure ≤ delta0)
    (hsource : ∀ x a, tvDist (M.transitionPMF x a).toMeasure
      (N.transitionPMF x a).toMeasure ≤ delta) :
    tvDist
      ((causalLaw p (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (timeObservationPolicy sigma)) T).map (eraseActionHistory T)).toMeasure
      ((causalLaw pref (riskMicroControlKernel q (fun _ => N.transitionPMF)
        (timeObservationPolicy sigma)) T).map (eraseActionHistory T)).toMeasure ≤
      min 1 (delta0 + (T : ℝ) * delta) := by
  rw [time_action_state_path_eq_mixture, time_action_state_path_eq_mixture]
  have h := causal_path_tv_le p pref (timeMixtureKernel M q sigma)
    (timeMixtureKernel N q sigma) T delta0 (fun _ => delta) hinit (by
      intro t _ h _
      exact risk_tv_bind_same_weights (sigma t (q (currentState t h)))
        (M.transitionPMF (currentState t h)) (N.transitionPMF (currentState t h)) delta
        (fun a _ => hsource (currentState t h) a))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

/-- The rank-one safe target has an initial `nu`, another `T-1` independent
`nu` draws, and one common final fair draw. This definition is used only after
the concrete source identity is proved; it is not an assumed conditioned law. -/
def rankOnePath {X : Type u} (nu fair : PMF X) (T : ℕ) :
    PMF (CausalHistory X X T) :=
  targetPath nu (fun n _ => if n+1 < T then nu else fair) T

/-- Shared final randomness contributes no additional target perturbation.
For a positive horizon the complete rank-one target costs T copies of TV(nu,nu'). -/
theorem rank_one_path_tv_le
    {X : Type u} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (nu nuhat fair : PMF X) (T : ℕ) (hT : 0 < T) :
    tvDist (rankOnePath nu fair T).toMeasure (rankOnePath nuhat fair T).toMeasure ≤
      min 1 ((T : ℝ) * tvDist nu.toMeasure nuhat.toMeasure) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  apply le_min (tvDist_le_one _ _)
  let K : ∀ t, CausalHistory X X t → PMF X :=
    fun t _ => if t+1 < n+1 then nu else fair
  let L : ∀ t, CausalHistory X X t → PMF X :=
    fun t _ => if t+1 < n+1 then nuhat else fair
  have hprefix := causal_path_tv_le nu nuhat K L n
    (tvDist nu.toMeasure nuhat.toMeasure) (fun _ => tvDist nu.toMeasure nuhat.toMeasure)
    le_rfl (by intro t ht h _; simp only [K, L, if_pos (by omega : t+1 < n+1)]; exact le_rfl)
  have hlast : tvDist (rankOnePath nu fair (n+1)).toMeasure
      (rankOnePath nuhat fair (n+1)).toMeasure ≤
      tvDist (causalLaw nu K n).toMeasure (causalLaw nuhat L n).toMeasure := by
    change tvDist (pmfExtend (causalLaw nu K n) (K n)).toMeasure
      (pmfExtend (causalLaw nuhat L n) (L n)).toMeasure ≤ _
    have hk : K n = fun _ => fair := by funext h; simp [K]
    have hl : L n = fun _ => fair := by funext h; simp [L]
    rw [hk, hl]
    exact coverage_tv_extend_same_kernel _ _ _
  have h := hlast.trans (hprefix.trans (min_le_right _ _))
  calc
    _ ≤ tvDist nu.toMeasure nuhat.toMeasure + ∑ i ∈ Finset.range n,
        tvDist nu.toMeasure nuhat.toMeasure := h
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_succ]
      ring

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataPathBounds
