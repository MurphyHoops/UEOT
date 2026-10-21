import SameSourceKilledPath
import UEOT.V3.Compression.TheoryCompletion.GOA
import UEOT.V3.FiniteDiscountedApproxQuotient

/-!
STATIC PROOF DRAFT — NOT COMPILED, NOT A PRODUCTION MODULE.

K2: bind normalized QSD data to the original action-record risk experiment.
`SameSourceKilledPath` is the private K1 candidate, not a production import.
The real initial law below is `r.map Subtype.val`, and Q is the restriction
of that SAME model/current-observation stationary policy. No source-law or
initial-row equality is an added premise. Perron existence is still input.

All proof bodies are proposals. There are no axioms or admitted proofs;
this does NOT constitute a Lean PASS or an axiom-closure receipt.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceQSDBindingCheck

open MeasureTheory
open UEOT.V3.PathError
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open UEOT.V3.QSDPerron
open SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open scoped BigOperators Classical

noncomputable section
universe u

private theorem map_injective_atom {S T : Type*} (f : S → T)
    (hf : Function.Injective f) (p : PMF S) (s : S) :
    (p.map f) (f s) = p s := by
  rw [PMF.map_apply]
  refine (tsum_eq_single s ?_).trans ?_
  · intro t ht
    exact if_neg (fun h => ht (hf h).symm)
  · simp

/-- The actual source initial row is derived from the chosen PMF. -/
theorem safeInitialRow_map_subtype {X : Type u} (K : Set X) (r : PMF K) :
    safeInitialRow (r.map Subtype.val) K = fun v => (r v).toReal := by
  funext v
  unfold safeInitialRow
  rw [map_injective_atom Subtype.val Subtype.val_injective r v]

section ActualSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : Model X (fun _ => A)) (q : X → Y) (sigma : Y → PMF A)
variable (K : Set X) (r : PMF K) (rho : ℝ)

local notation "Q" => killedMatrix M (liftedStationaryPolicy q sigma) K
local notation "rR" => (fun v : K => (r v).toReal)
local notation "p0" => r.map Subtype.val
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
  exact leftPerron_pow Q rR rho hleft n v

/-- Actual total survival, with no positivity assumption on rho. -/
theorem actual_qsd_survival_mass
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (n : ℕ) :
    (nu n).toMeasure.real
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h} = rho ^ n := by
  rw [actual_survival_mass_eq_killed_pow_sum, safeInitialRow_map_subtype]
  exact qsd_survival_mass_pow Q rR rho (coverage_sum_toReal r) hleft n

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

/-- This is a consequence of positive actual mass, not a fresh hypothesis
about some separately chosen path experiment. -/
theorem actual_qsd_survival_support
    (hleft : ∀ v, rowApply rR Q v = rho * (r v).toReal)
    (hrho : 0 < rho) (n : ℕ) :
    ∃ h ∈ {h | ¬ riskEverFailure (fun x => x ∉ K) n h}, h ∈ (nu n).support := by
  classical
  have hpos := actual_qsd_survival_pos M q sigma K r rho hleft hrho n
  by_contra hnone
  have hzero : (nu n).toMeasure
      {h | ¬ riskEverFailure (fun x => x ∉ K) n h} = 0 := by
    apply ((nu n).toMeasure_apply_eq_zero_iff (Set.toFinite _).measurableSet).2
    apply Set.disjoint_left.mpr
    intro h hsupp hsafe
    exact hnone ⟨h, hsafe, hsupp⟩
  change 0 < ((nu n).toMeasure
    {h | ¬ riskEverFailure (fun x => x ∉ K) n h}).toReal at hpos
  rw [hzero, ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos

end ActualSource

/-- Small finite conditioning adapter. Its conclusion is about PMF.filter
and the actual pushed-forward law, not only an algebraic normalized row. -/
private theorem filter_map_apply_real
    {H Z : Type u} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (p : PMF H) (S : Set H) (hs : ∃ h ∈ S, h ∈ p.support)
    (f : H → Z) (z : Z) :
    (((p.filter S hs).map f) z).toReal =
      p.toMeasure.real {h | h ∈ S ∧ f h = z} / p.toMeasure.real S := by
  have he : ((p.filter S hs).map f) z =
      p.toMeasure {h | h ∈ S ∧ f h = z} / p.toMeasure S := by
    rw [PMF.map_apply, tsum_fintype]
    simp only [PMF.toMeasure_apply_fintype, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro h _
    rw [PMF.filter_apply, tsum_fintype]
    by_cases hS : h ∈ S <;> by_cases hz : f h = z <;>
      simp [hS, hz, eq_comm]
  simpa only [ENNReal.toReal_div, Measure.real] using congrArg ENNReal.toReal he

private theorem survives_last_mem
    {X A : Type u} (K : Set X) (n : ℕ)
    (h : CausalHistory X (A × X) n)
    (hs : ¬ riskEverFailure (fun x => x ∉ K) n h) :
    riskLastState n h ∈ K := by
  cases n with
  | zero => simpa only [riskEverFailure, riskLastState, not_not] using hs
  | succ n =>
      change ¬ (riskEverFailure (fun x => x ∉ K) n h.1 ∨ h.2.2 ∉ K) at hs
      exact not_not.mp (not_or.mp hs).2

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
  classical
  let nu := causalLaw (r.map Subtype.val)
    (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy sigma)) n
  let S : Set (CausalHistory X (A × X) n) :=
    {h | ¬ riskEverFailure (fun x => x ∉ K) n h}
  let hs := actual_qsd_survival_support M q sigma K r rho hleft hrho n
  let cond := (nu.filter S hs).map (riskLastState n)
  change cond = r.map Subtype.val
  apply PMF.ext
  intro x
  by_cases hx : x ∈ K
  · let v : K := ⟨x, hx⟩
    apply (ENNReal.toReal_eq_toReal_iff'
      (cond.apply_ne_top x) ((r.map Subtype.val).apply_ne_top x)).1
    calc
      (cond x).toReal =
          nu.toMeasure.real {h | h ∈ S ∧ riskLastState n h = x} /
            nu.toMeasure.real S := filter_map_apply_real nu S hs (riskLastState n) x
      _ = (r v).toReal :=
        actual_qsd_conditional_terminal_ratio M q sigma K r rho hleft hrho n v
      _ = ((r.map Subtype.val) x).toReal := by
        exact (congrArg ENNReal.toReal
          (map_injective_atom Subtype.val Subtype.val_injective r v)).symm
  · have hcond : cond x = 0 := by
      apply (PMF.apply_eq_zero_iff cond x).2
      intro hmem
      rcases (PMF.mem_support_map_iff (riskLastState n) (nu.filter S hs) x).1 hmem with
        ⟨h, hh, heq⟩
      have hsafe := (PMF.mem_support_filter_iff hs).1 hh
      have hlast := survives_last_mem K n h hsafe.1
      exact hx (heq ▸ hlast)
    have hmap : (r.map Subtype.val) x = 0 := by
      apply (PMF.apply_eq_zero_iff (r.map Subtype.val) x).2
      intro hmem
      rcases (PMF.mem_support_map_iff Subtype.val r x).1 hmem with ⟨v, _, heq⟩
      exact hx (heq ▸ v.property)
    rw [hcond, hmap]

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
