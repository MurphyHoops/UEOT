import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricInfinite
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricControl
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictOrganizationalSource
import UEOT.V3.Compression.TheoryCompletion.GOA
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricStationary
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricQSD

/-! Exact common actual-record consumers for the book's theta-family.
Terminal damage, ever-exit, and damage-then-return are different events.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricCommonConsumer
open MeasureTheory
open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open ConflictParametricSource ConflictParametricPath
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : DecidableEq State := Classical.decEq State

/-- The same COMPLETE original record feeds the original stationary source;
    only actions are erased, using the already-proved production path bridge. -/
theorem full_record_stationary_source (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (law theta h0 h1 n).map (riskLastState n) =
      ConflictParametricStationary.actualMarginal theta h0 h1 (PMF.pure (true,false)) n := by
  have hh := SourcePolicyPathBridgeCheck.actual_state_path_eq_stationary_path M Prod.fst
    (fun _ : Bool => actionLaw theta h0 h1) (PMF.pure (true,false)) n
  have he := congrArg (fun p : PMF (CausalHistory State State n) => p.map (currentState n)) hh
  rw [PMF.map_comp] at he
  have hf : currentState n ∘ SourcePolicyPathBridgeCheck.eraseActionHistory (X := State) (A := Bool) n =
      riskLastState n := by
    funext h
    cases n <;> rfl
  rw [hf] at he
  change (law theta h0 h1 n).map (riskLastState n) =
    ConflictParametricStationary.actualMarginal theta h0 h1 (PMF.pure (true,false)) n at he
  exact he

theorem actual_terminal_pmf (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (law theta h0 h1 (n+1)).map (riskLastState (n+1)) = mu theta h0 h1 := by
  rw [full_record_stationary_source]
  exact ConflictParametricStationary.actual_marginal_after_one theta h0 h1 _ n

theorem terminal_damage_probability (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (n : ℕ) :
    (law theta h0 h1 (n+1)).toMeasure.real {h | (riskLastState (n+1) h).1 = false} = theta := by
  have hs : Measurable (riskLastState (n+1) : History (n+1) → State) := measurable_of_finite _
  have hset : MeasurableSet {x : State | x.1 = false} := (Set.toFinite _).measurableSet
  have hm : (law theta h0 h1 (n+1)).toMeasure.map (riskLastState (n+1)) =
      (mu theta h0 h1).toMeasure := by
    rw [PMF.toMeasure_map _ _ hs, actual_terminal_pmf]
  have he : (law theta h0 h1 (n+1)).toMeasure {h | (riskLastState (n+1) h).1 = false} =
      (mu theta h0 h1).toMeasure {x | x.1 = false} := by
    rw [← hm, Measure.map_apply hs hset]
    rfl
  rw [Measure.real,he]
  change (mu theta h0 h1).toMeasure.real {x | x.1 = false} = _
  have hb : {x : State | x.1 = false} = {x | ¬ (x.1 = true)} := by
    ext ⟨b,u⟩; cases b <;> simp
  rw [hb, ← coverage_uncovered_indicator_expectation _ (fun x : State => x.1 = true)]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,mu_real]
  norm_num

/-- Damage at step1 and return at step2 in the same full record. -/
def returned (h : History 2) : Prop := h.1.2.2.1 = false ∧ h.2.2.1 = true

theorem two_mass (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (h : History 2) :
    (law theta h0 h1 2 h).toReal =
      ((PMF.pure (true,false) : PMF State) h.1.1).toReal *
        actionWeight theta h.1.2.1 * (if h.1.2.2.1 = h.1.2.1 then (1/2 : ℝ) else 0) *
        actionWeight theta h.2.1 * (if h.2.2.1 = h.2.1 then (1/2 : ℝ) else 0) := by
  rcases h with ⟨h,a,z⟩
  rw [mass_succ]
  rcases h with ⟨x,b,y⟩
  rw [mass_succ]
  rfl

theorem two_step_return_probability (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    (law theta h0 h1 2).toMeasure.real {h | returned h} = theta*(1-theta) := by
  classical
  have hu := (coverage_uncovered_indicator_expectation (law theta h0 h1 2) (fun h => ¬ returned h)).symm
  simp only [not_not] at hu
  rw [hu]
  simp only [two_mass, returned]
  change (∑ h : (State × (Bool × State)) × (Bool × State), _) = _
  simp [Fintype.sum_prod_type,actionWeight,PMF.pure_apply]
  ring

open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.AgencyGodGoaAssembly
open UEOT.V3.Compression.InvariantSetGaugeInvariance

theorem original_greedy_matrix : greedyClosedLoopMatrix M = closedMatrix 1 := by
  funext x y
  simp only [greedyClosedLoopMatrix,greedyStationaryPolicy,policyMatrix,Model.policyTransition,
    StationaryPolicy.ofSelector,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,if_true,ConflictParametricControl.unrestricted_greedy,transition_eq]
  cases hy : y.1 <;> norm_num [closedMatrix,hy]

theorem original_greedy_normalized_step (q : stdSimplex ℝ State) (y : State) :
    Matrix.vecMul q.val (greedyClosedLoopMatrix M) y = (mu 1 (by norm_num) (by norm_num) y).toReal := by
  rw [original_greedy_matrix,mu_real]
  simp only [Matrix.vecMul,dotProduct,closedMatrix]
  have hsum : (∑ x : State, q.val x) = 1 := stdSimplex.sum_eq_one q
  rw [← Finset.sum_mul,hsum,one_mul]

/-- Original GOD -> GOA consumer for the unrestricted model, not the
    restricted model's different invariant set. -/
theorem original_unrestricted_GOA_iff (q : stdSimplex ℝ State) :
    q ∈ GreedyInvariantGOASet M ↔
      q.val = fun y => (mu 1 (by norm_num) (by norm_num) y).toReal := by
  change UEOT.V3.FiniteDobrushin.step _ _ q = q ↔ _
  constructor
  · intro h
    funext y
    have hy := congrArg (fun q : stdSimplex ℝ State => q.val y) h
    change Matrix.vecMul q.val (greedyClosedLoopMatrix M) y = q.val y at hy
    exact hy.symm.trans (original_greedy_normalized_step q y)
  · intro h
    apply Subtype.ext
    funext y
    change Matrix.vecMul q.val (greedyClosedLoopMatrix M) y = q.val y
    rw [original_greedy_normalized_step,h]

abbrev lawSimplex := ConflictParametricStationary.ofPMF

theorem original_unrestricted_GOA_mu_one :
    lawSimplex (mu 1 (by norm_num) (by norm_num)) ∈ GreedyInvariantGOASet M := by
  rw [original_unrestricted_GOA_iff]
  rfl

theorem original_unrestricted_GOA_outside_safe (x : State)
    (hx : x ∈ (mu 1 (by norm_num) (by norm_num)).support) : x.1 = false := by
  have hh := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hx) (PMF.apply_ne_top _ _)
  rw [mu_real] at hh
  cases hb : x.1 with
  | false => rfl
  | true => norm_num [hb] at hh

open Filter Topology UEOT.V3.FiniteCesaroInvariant

/-- The original CesaroLimitGOA predicate is actually instantiated from the
    explicit source average, not asserted as another certificate input. -/
theorem actual_cesaro_simplex_tendsto (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    Tendsto (cesaroRow (ConflictParametricStationary.P theta)
      (ConflictParametricStationary.matrix_stochastic theta h0 h1)
      (lawSimplex ConflictParametricStationary.initial)) atTop (𝓝 (lawSimplex (mu theta h0 h1))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro y
  have hi : Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he (n : ℕ) :
      (cesaroRow (ConflictParametricStationary.P theta)
        (ConflictParametricStationary.matrix_stochastic theta h0 h1)
        (lawSimplex ConflictParametricStationary.initial) n).val y =
      (mu theta h0 h1 y).toReal +
        ((ConflictParametricStationary.initial y).toReal-(mu theta h0 h1 y).toReal)*(((n+1 : ℕ) : ℝ))⁻¹ := by
    have hd := ConflictParametricStationary.cesaro_difference theta h0 h1 n y
    have hr : (ConflictParametricStationary.actualCesaro theta h0 h1 n y).toReal =
        (cesaroRow (ConflictParametricStationary.P theta)
          (ConflictParametricStationary.matrix_stochastic theta h0 h1)
          (lawSimplex ConflictParametricStationary.initial) n).val y :=
      by
        unfold ConflictParametricStationary.actualCesaro
        exact FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _
    rw [hr] at hd
    rw [div_eq_mul_inv] at hd
    linarith
  simp_rw [he]
  simpa only [lawSimplex,ConflictParametricStationary.ofPMF,mul_zero,add_zero] using
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hi) :
      Tendsto (fun n : ℕ => (mu theta h0 h1 y).toReal +
        ((ConflictParametricStationary.initial y).toReal-(mu theta h0 h1 y).toReal)*(((n+1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 ((mu theta h0 h1 y).toReal+_*0)))

theorem original_cesaro_limit_GOA (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    CesaroLimitGOA (ConflictParametricStationary.P theta)
      (ConflictParametricStationary.matrix_stochastic theta h0 h1)
      (lawSimplex ConflictParametricStationary.initial) (lawSimplex (mu theta h0 h1)) :=
  ⟨id, strictMono_id, actual_cesaro_simplex_tendsto theta h0 h1⟩

/-- The full-domain ORIGINAL restricted greedy matrix is the actual D. -/
theorem original_restricted_greedy_matrix :
    greedyClosedLoopMatrix ConflictParametricControl.R = ConflictParametricControl.D := rfl

theorem original_restricted_step_pmf (p : PMF State) :
    lawSimplex (p.bind ConflictParametricControl.restrictedRow) =
      UEOT.V3.FiniteDobrushin.step (greedyClosedLoopMatrix ConflictParametricControl.R)
        (greedyClosedLoopMatrix_rowStochastic ConflictParametricControl.R) (lawSimplex p) := by
  apply Subtype.ext
  funext ⟨b,u⟩
  change ((p.bind ConflictParametricControl.restrictedRow) (b,u)).toReal =
    Matrix.vecMul (fun x => (p x).toReal) (greedyClosedLoopMatrix ConflictParametricControl.R) (b,u)
  rw [ConflictParametricControl.restricted_bind_real,original_restricted_greedy_matrix]
  simp only [Matrix.vecMul,dotProduct,ConflictParametricControl.D_eq]
  cases b <;> simp [Fintype.sum_prod_type] <;> ring

/-- ALL original restricted GOAs, in its original simplex type, are exactly
    the two-fiber mixtures. No outside action or invariant class was removed. -/
theorem original_restricted_GOA_all_rows (q : stdSimplex ℝ State) :
    q ∈ GreedyInvariantGOASet ConflictParametricControl.R ↔
      ∃ theta : ℝ, ∃ h0 : 0 ≤ theta, ∃ h1 : theta ≤ 1,
        q = lawSimplex (mu theta h0 h1) := by
  let p : PMF State := FiniteProbabilityRow.ofRealRow q.val (stdSimplex.zero_le q) (stdSimplex.sum_eq_one q)
  have hp (y : State) : (p y).toReal = q.val y := FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _
  have hqp : lawSimplex p = q := by
    apply Subtype.ext
    funext y
    exact hp y
  have hc : q ∈ GreedyInvariantGOASet ConflictParametricControl.R ↔
      p.bind ConflictParametricControl.restrictedRow = p := by
    rw [← hqp]
    change UEOT.V3.FiniteDobrushin.step _ _ (lawSimplex p) = lawSimplex p ↔ _
    rw [← original_restricted_step_pmf]
    constructor
    · intro h
      apply PMF.ext
      intro y
      apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
      exact congrArg (fun q : stdSimplex ℝ State => q.val y) h
    · intro h
      rw [h]
  rw [hc,ConflictParametricControl.invariant_iff_mixture]
  constructor
  · rintro ⟨theta,h0,h1,hp⟩
    exact ⟨theta,h0,h1,hqp.symm.trans (congrArg lawSimplex hp)⟩
  · rintro ⟨theta,h0,h1,hq⟩
    refine ⟨theta,h0,h1,?_⟩
    apply PMF.ext
    intro y
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    exact congrArg (fun q : stdSimplex ℝ State => q.val y) (hqp.trans hq)

theorem restricted_initial_step :
    ConflictParametricStationary.initial.bind ConflictParametricControl.restrictedRow =
      mu 0 (by norm_num) (by norm_num) := by
  change (PMF.pure (true,false)).bind ConflictParametricControl.restrictedRow = _
  rw [PMF.pure_bind, ConflictParametricControl.restrictedRow_original]
  unfold mu closedRow FiniteActionRealizabilityCheck.actionMixture
  rw [ConflictParametricControl.actionLaw_zero, PMF.pure_bind]
  rfl

/-- Actual restricted greedy evolution from the original safe initial point
    is transported to theta0; outside that initial region it is different. -/
theorem restricted_orbit_safe_source (t : ℕ) :
    orbit (greedyClosedLoopMatrix ConflictParametricControl.R)
      (greedyClosedLoopMatrix_rowStochastic ConflictParametricControl.R)
      (lawSimplex ConflictParametricStationary.initial) t =
    orbit (ConflictParametricStationary.P 0)
      (ConflictParametricStationary.matrix_stochastic 0 (by norm_num) (by norm_num))
      (lawSimplex ConflictParametricStationary.initial) t := by
  have hinit := original_restricted_step_pmf ConflictParametricStationary.initial
  rw [restricted_initial_step] at hinit
  have hinv := original_restricted_step_pmf (mu 0 (by norm_num) (by norm_num))
  rw [ConflictParametricControl.all_mixtures_invariant] at hinv
  have hz : ∀ k : ℕ,
      (orbit (greedyClosedLoopMatrix ConflictParametricControl.R)
        (greedyClosedLoopMatrix_rowStochastic ConflictParametricControl.R)
        (lawSimplex ConflictParametricStationary.initial) (k+1) : State → ℝ) =
        (lawSimplex (mu 0 (by norm_num) (by norm_num))).val := by
    intro k
    induction k with
    | zero =>
        rw [orbit_succ,orbit_zero]
        exact (congrArg Subtype.val hinit).symm
    | succ k ih =>
        rw [orbit_succ,ih]
        exact (congrArg Subtype.val hinv).symm
  apply Subtype.ext
  funext y
  cases t with
  | zero =>
      exact (congrFun (orbit_zero _ _ _) y).trans (congrFun (orbit_zero _ _ _) y).symm
  | succ t =>
      exact (congrFun (hz t) y).trans
        (congrFun (ConflictParametricStationary.orbit_after_one 0 (by norm_num) (by norm_num)
          ConflictParametricStationary.initial t) y).symm

theorem restricted_cesaro_safe_source (n : ℕ) :
    cesaroRow (greedyClosedLoopMatrix ConflictParametricControl.R)
      (greedyClosedLoopMatrix_rowStochastic ConflictParametricControl.R)
      (lawSimplex ConflictParametricStationary.initial) n =
    cesaroRow (ConflictParametricStationary.P 0)
      (ConflictParametricStationary.matrix_stochastic 0 (by norm_num) (by norm_num))
      (lawSimplex ConflictParametricStationary.initial) n := by
  apply Subtype.ext
  simp only [cesaroRow]
  simp_rw [restricted_orbit_safe_source]

/-- The original restricted CesaroLimitGOA from the specified safe initial
    law is exactly mu0, although its FULL invariant GOA set is not singleton. -/
theorem original_restricted_cesaro_GOA_iff (q : stdSimplex ℝ State) :
    CesaroLimitGOA (greedyClosedLoopMatrix ConflictParametricControl.R)
      (greedyClosedLoopMatrix_rowStochastic ConflictParametricControl.R)
      (lawSimplex ConflictParametricStationary.initial) q ↔
      q = lawSimplex (mu 0 (by norm_num) (by norm_num)) := by
  have hf : Tendsto (cesaroRow (greedyClosedLoopMatrix ConflictParametricControl.R)
      (greedyClosedLoopMatrix_rowStochastic ConflictParametricControl.R)
      (lawSimplex ConflictParametricStationary.initial)) atTop
      (𝓝 (lawSimplex (mu 0 (by norm_num) (by norm_num)))) :=
    (tendsto_congr' (Eventually.of_forall restricted_cesaro_safe_source)).mpr
      (actual_cesaro_simplex_tendsto 0 (by norm_num) (by norm_num))
  constructor
  · rintro ⟨phi,hphi,hlim⟩
    exact tendsto_nhds_unique hlim (hf.comp hphi.tendsto_atTop)
  · intro h
    subst q
    exact ⟨id,strictMono_id,hf⟩

/-- Every original QSD statement is now on THIS complete path source and
    the original initial point; the safe subtype is not silently Bool. -/
def original_safe_initial : PMF ConflictParametricQSD.K :=
  PMF.pure (ConflictParametricQSD.safeEquiv false)

theorem original_safe_initial_map : original_safe_initial.map Subtype.val = PMF.pure (true,false) := by
  rw [original_safe_initial, PMF.pure_map]
  rfl

theorem same_full_record_qsd_source (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (T : ℕ) :
    law theta h0 h1 T = ConflictParametricQSD.actualLaw theta h0 h1 original_safe_initial T := by
  unfold ConflictParametricQSD.actualLaw
  rw [original_safe_initial_map]
  rfl

theorem same_original_survival_event : ∀ n (h : History n),
    survives n h ↔ ¬ riskEverFailure (fun x => x ∉ ConflictParametricQSD.K) n h := by
  intro n
  induction n with
  | zero => intro h; simp [survives,riskEverFailure,ConflictParametricQSD.K]
  | succ n ih =>
      rintro ⟨h,a,z⟩
      simp [survives,riskEverFailure,ih,ConflictParametricQSD.K]

theorem mixture_safe_iff (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    UEOT.V3.ViabilityKernel.StaysIn (mu theta h0 h1) conflictSurvivalRegion ↔ theta = 0 := by
  constructor
  · intro hs
    by_contra hn
    have ht : 0 < theta := lt_of_le_of_ne h0 (Ne.symm hn)
    have hv : (mu theta h0 h1 (false,false)).toReal > 0 := by rw [mu_real];norm_num;linarith
    have hm : (false,false) ∈ (mu theta h0 h1).support :=
      (PMF.mem_support_iff _ _).mpr (by intro h;rw [h] at hv;norm_num at hv)
    have hh := hs hm
    change false = true at hh
    cases hh
  · intro ht
    subst theta
    intro x hx
    have hh := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hx) (PMF.apply_ne_top _ _)
    rw [mu_real] at hh
    cases hb : x.1 with
    | false => norm_num [hb] at hh
    | true => exact hb

theorem original_safe_restricted_GOA_unique (p : PMF State)
    (hs : UEOT.V3.ViabilityKernel.StaysIn p conflictSurvivalRegion)
    (hg : lawSimplex p ∈ GreedyInvariantGOASet ConflictParametricControl.R) :
    p = mu 0 (by norm_num) (by norm_num) := by
  rcases (original_restricted_GOA_all_rows (lawSimplex p)).mp hg with ⟨theta,h0,h1,hp⟩
  have he : p = mu theta h0 h1 := by
    apply PMF.ext
    intro y
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    exact congrArg (fun q : stdSimplex ℝ State => q.val y) hp
  rw [he] at hs
  have ht := (mixture_safe_iff theta h0 h1).mp hs
  subst theta
  exact he

/-- The actual safe-subtype fair distribution is exactly the theta0 physical
    law; this explicit map is not an identification of the two state types. -/
theorem actual_qsd_fair_is_mu_zero :
    ConflictParametricQSD.fairPMF.map Subtype.val = mu 0 (by norm_num) (by norm_num) := by
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum (by
    intro x _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  simp only [apply_ite,ENNReal.toReal_zero,ConflictParametricQSD.fairPMF_real]
  rw [ConflictParametricQSD.safe_sum]
  rcases z with ⟨b,u⟩
  cases b <;> cases u <;> norm_num [ConflictParametricQSD.safeEquiv,ConflictParametricQSD.fair,mu_real]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricCommonConsumer
