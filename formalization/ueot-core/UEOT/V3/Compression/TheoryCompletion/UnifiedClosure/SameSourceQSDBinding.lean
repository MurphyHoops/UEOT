import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminal
import UEOT.V3.Compression.TheoryCompletion.GOA
import UEOT.V3.FiniteDiscountedApproxQuotient

/-!
K3: bind supplied normalized QSD data to the original action-record risk
experiment, reusing the actual conditional-terminal interface of general K2.

The real initial law below is `r.map Subtype.val`, and Q is the restriction
of that SAME model/current-observation stationary policy. No source-law or
initial-row equality is an added premise. A normalized left eigenrelation is
input; existence, uniqueness, attraction and arbitrary-policy Markovization
are not asserted. Positive-current-survival conditioning includes rho=0,n=0.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceQSDBindingCheck

open MeasureTheory
open UEOT.V3.PathError
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck
open scoped BigOperators Classical

noncomputable section
universe u

/-- The actual source initial row is derived from the chosen PMF. -/
theorem safeInitialRow_map_subtype {X : Type u} (K : Set X) (r : PMF K) :
    safeInitialRow (r.map Subtype.val) K = fun v => (r v).toReal := by
  funext v
  unfold safeInitialRow
  rw [pmf_map_injective_atom Subtype.val Subtype.val_injective r v]

section ActualSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
variable (K : Set X) (r : PMF K) (rho : ℝ)

local notation "Q" => killedMatrix M (liftedStationaryPolicy q sigma) K
local notation "rR" => (fun v : K => ENNReal.toReal (r v))
local notation "p0" => PMF.map Subtype.val r
local notation "nu" => (fun n => causalLaw p0
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n)

/-- Actual joint mass, with no positivity assumption on rho. -/
theorem actual_qsd_survival_terminal_mass
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (n : ℕ) (v : K) :
    (nu n).toMeasure.real
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h ∧ riskLastState n h = v.1} =
      rho ^ n * (r v).toReal := by
  rw [actual_survival_terminal_mass_eq_killed_pow, safeInitialRow_map_subtype]
  convert leftPerron_pow Q rR rho hleft n v using 1 <;> congr!

/-- Actual total survival, with no positivity assumption on rho. -/
theorem actual_qsd_survival_mass
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (n : ℕ) :
    (nu n).toMeasure.real
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h} = rho ^ n := by
  rw [actual_survival_mass_eq_killed_pow_sum, safeInitialRow_map_subtype]
  convert qsd_survival_mass_pow Q rR rho (coverage_sum_toReal r) hleft n using 1 <;>
    congr!

/-- The actual conditioning event has positive mass when rho is positive. -/
theorem actual_qsd_survival_pos
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (hrho : 0 < rho) (n : ℕ) :
    0 < (nu n).toMeasure.real
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h} := by
  rw [actual_qsd_survival_mass M q sigma K r rho hleft n]
  exact pow_pos hrho n

/-- A ratio of two events in the SAME original experiment. -/
theorem actual_qsd_conditional_terminal_ratio
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (hrho : 0 < rho) (n : ℕ) (v : K) :
    (nu n).toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) n h ∧ riskLastState n h = v.1} /
      (nu n).toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) n h} = (r v).toReal := by
  rw [actual_qsd_survival_terminal_mass M q sigma K r rho hleft n v,
    actual_qsd_survival_mass M q sigma K r rho hleft n]
  have hn : rho ^ n ≠ 0 := pow_ne_zero n hrho.ne'
  field_simp [hn]

/-- Construct precisely the semantic predicate already used by GOA. -/
theorem sameSource_KilledQSDGOA
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (hrho : 0 < rho) :
    KilledQSDGOA Q rR rho := by
  exact ⟨killedMatrix_nonneg M (liftedStationaryPolicy q sigma) K,
    killedMatrix_row_sum_le_one M (liftedStationaryPolicy q sigma) K,
    (fun _ => ENNReal.toReal_nonneg), coverage_sum_toReal r, hrho, hleft⟩

/-- Nonnegative normalized left data on this actual killed kernel force
rho into [0,1]; strict positivity is not inferred. -/
theorem sameSource_rho_bounds
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal) :
    0 ≤ rho ∧ rho ≤ 1 := by
  constructor
  · rw [← qsd_survival_mass Q rR rho (coverage_sum_toReal r) hleft]
    apply Finset.sum_nonneg
    intro v _
    unfold rowApply
    apply Finset.sum_nonneg
    intro w _
    exact mul_nonneg ENNReal.toReal_nonneg
      (killedMatrix_nonneg M (liftedStationaryPolicy q sigma) K w v)
  · exact perron_root_le_one_of_substochastic Q rR rho
      (fun _ => ENNReal.toReal_nonneg)
      (killedMatrix_row_sum_le_one M (liftedStationaryPolicy q sigma) K)
      (coverage_sum_toReal r) hleft

/-- Exact positive-window boundary: even a zero left eigenvalue permits
conditioning at n=0, while positive horizons require rho>0. -/
theorem actual_qsd_survival_pos_iff
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (n : ℕ) :
    0 < (nu n).toMeasure.real
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h} ↔ n = 0 ∨ 0 < rho := by
  rw [actual_qsd_survival_mass M q sigma K r rho hleft n]
  have hr0 := (sameSource_rho_bounds M q sigma K r rho hleft).1
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_ne_zero, false_or]
      constructor
      · intro hp
        by_contra hnot
        have hz : rho = 0 := le_antisymm (le_of_not_gt hnot) hr0
        simp [hz] at hp
      · intro hp
        exact pow_pos hp _

/-- General K2 specialized to the same normalized left row. Only the
current actual survival mass must be positive, not rho at every horizon. -/
theorem actual_qsd_conditioned_terminal_law_of_survival_pos
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (n : ℕ)
    (hpos : 0 < (nu n).toMeasure.real
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h}) :
    actualConditionedTerminal M q sigma p0 K n hpos = p0 := by
  have hp : 0 < rho ^ n := by
    rwa [actual_qsd_survival_mass M q sigma K r rho hleft n] at hpos
  have hnorm : normalizedKilledTerminal M q sigma p0 K n hpos = r := by
    apply PMF.ext
    intro v
    apply (ENNReal.toReal_eq_toReal_iff'
      ((normalizedKilledTerminal M q sigma p0 K n hpos).apply_ne_top v)
      (r.apply_ne_top v)).1
    rw [normalizedKilledTerminal_apply_toReal,
      ← actual_survival_terminal_mass_eq_killed_pow M q sigma p0 K n v,
      actual_qsd_survival_terminal_mass M q sigma K r rho hleft n v,
      actual_qsd_survival_mass M q sigma K r rho hleft n]
    field_simp [hp.ne']
  rw [actual_conditioned_terminal_eq_normalized_killed_map, hnorm]

/-- At a positive horizon, rho=0 yields no support witness for actual
survival conditioning. No arbitrary normalized law is assigned to it. -/
theorem actual_qsd_zero_root_no_filter_witness
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (hrho : rho = 0) (n : ℕ) (hn : n ≠ 0) :
    ¬ ∃ h ∈ {h | ¬ riskEverFailure (fun x => x ∉ K) n h},
      h ∈ (nu n).support := by
  apply actual_zero_survival_no_filter_witness M q sigma p0 K n
  rw [actual_qsd_survival_mass M q sigma K r rho hleft n, hrho, zero_pow hn]

/-- This is a consequence of positive actual mass, not a fresh hypothesis
about some separately chosen path experiment. -/
theorem actual_qsd_survival_support
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (hrho : 0 < rho) (n : ℕ) :
    ∃ h ∈ {h | ¬ riskEverFailure (fun x => x ∉ K) n h}, h ∈ (nu n).support := by
  exact (actual_survival_pos_iff_support M q sigma p0 K n).1
    (actual_qsd_survival_pos M q sigma K r rho hleft hrho n)

end ActualSource

/-- Exact conditional terminal PMF. The support certificate is constructed
internally from the same path law's positive survival mass. -/
theorem actual_qsd_conditioned_terminal_law
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (K : Set X) (r : PMF K) (rho : ℝ)
    (hleft : ∀ v, rowApply (fun w : K => (r w).toReal)
      (killedMatrix M (liftedStationaryPolicy q sigma) K) v = rho * (r v).toReal)
    (hrho : 0 < rho) (n : ℕ) :
    let nu := causalLaw (r.map Subtype.val)
      (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (observationMarkovPolicy sigma)) n
    let S : Set (CausalHistory X (A × X) n) :=
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h}
    (nu.filter S
      (actual_qsd_survival_support M q sigma K r rho hleft hrho n)).map
        (riskLastState n) = r.map Subtype.val := by
  let hpos := actual_qsd_survival_pos M q sigma K r rho hleft hrho n
  change actualConditionedTerminal M q sigma (r.map Subtype.val) K n hpos =
    r.map Subtype.val
  exact actual_qsd_conditioned_terminal_law_of_survival_pos
    M q sigma K r rho hleft n hpos

/-- A normalized nonnegative REAL left row gives the actual PMF source by
the existing ofRealRow constructor. No extra [Nonempty K] is postulated. -/
theorem actual_qsd_masses_ofRealRow
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
    (K : Set X) (r : K → ℝ) (hr : ∀ v, 0 ≤ r v) (hsum : ∑ v, r v = 1)
    (rho : ℝ)
    (hleft : ∀ v, rowApply r
      (killedMatrix M (liftedStationaryPolicy q sigma) K) v = rho * r v)
    (n : ℕ) :
    let p0 := (FiniteProbabilityRow.ofRealRow r hr hsum).map Subtype.val
    let nu := causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma)) n
    nu.toMeasure.real {h | ¬ riskEverFailure (fun x => x ∉ K) n h} = rho ^ n ∧
      ∀ v : K, nu.toMeasure.real
        {h | ¬ riskEverFailure (fun x => x ∉ K) n h ∧ riskLastState n h = v.1} =
          rho ^ n * r v := by
  let rp := FiniteProbabilityRow.ofRealRow r hr hsum
  have hleftp : ∀ v, rowApply (fun w : K => (rp w).toReal)
      (killedMatrix M (liftedStationaryPolicy q sigma) K) v = rho * (rp v).toReal := by
    simpa only [rp, FiniteProbabilityRow.ofRealRow_apply_toReal] using hleft
  constructor
  · exact actual_qsd_survival_mass M q sigma K rp rho hleftp n
  · intro v
    simpa only [rp, FiniteProbabilityRow.ofRealRow_apply_toReal] using
      actual_qsd_survival_terminal_mass M q sigma K rp rho hleftp n v

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceQSDBindingCheck
