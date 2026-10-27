import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizability
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindow

/-!
# An actual action consumer of finite-window conditional transport

The target is the previously constructed total finite-window process of the
same source. Its initial law is the remaining-survival tilt. A time-dependent
observation policy acts through the ORIGINAL model transition PMFs. Erasing
the sampled action records yields the target path when the common action
mixtures exist on its occupied observation fibers. No path equality or
formation/transport compatibility is assumed.

Only states occupied by the target before the horizon impose a constraint.
Null and unreachable rows are not required to be implementable. This is a
finite-horizon, current-observation feedback consumer; it does not identify
ontic parents, infer independent lineage, or establish general-history no-go.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransportCheck

open MeasureTheory UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl
open UEOT.V3.CoreOperationalAssembly
open SourcePolicyPathBridgeCheck FiniteActionRealizabilityCheck
open SameSourceKilledPathCheck SameSourceConditionedTerminalCheck
open SameSourceFiniteWindowCheck TotalFiniteWindowCheck
open scoped BigOperators Classical

noncomputable section
universe u

/-- A genuine time-dependent current-observation action policy. -/
def timeObservationPolicy {Y A : Type u} (sigma : ℕ → Y → PMF A) :
    ∀ n, CausalHistory Y (A × Y) n → PMF A :=
  fun n h => sigma n (riskLastState n h)

/-- The actual state marginal obtained by mixing original action rows. -/
def timeMixtureKernel {X Y A : Type u} [Fintype X] [Fintype A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : ℕ → Y → PMF A) :
    ∀ n, CausalHistory X X n → PMF X :=
  fun n h => actionMixture (M.transitionPMF (currentState n h))
    (sigma n (q (currentState n h)))

private theorem current_erase {X A : Type u}
    (n : ℕ) (h : CausalHistory X (A × X) n) :
    currentState n (eraseActionHistory n h) = riskLastState n h := by
  cases n <;> rfl

/-- Source identity for the complete time-dependent action experiment.
The state kernel is derived from the action PMF and the original model. -/
theorem time_action_state_path_eq_mixture
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y) (sigma : ℕ → Y → PMF A)
    (p0 : PMF X) (n : ℕ) :
    (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (timeObservationPolicy sigma)) n).map (eraseActionHistory n) =
      causalLaw p0 (timeMixtureKernel M q sigma) n := by
  let K := riskMicroControlKernel q (fun _ => M.transitionPMF)
    (timeObservationPolicy sigma)
  let L := timeMixtureKernel M q sigma
  change (causalLaw p0 K n).map (eraseActionHistory n) = causalLaw p0 L n
  have hrow (t : ℕ) (h : CausalHistory X (A × X) t) :
      (K t h).map Prod.snd = L t (eraseActionHistory t h) := by
    change (riskMicroControlKernel q (fun _ => M.transitionPMF)
      (observationMarkovPolicy (sigma t)) t h).map Prod.snd =
        actionMixture (M.transitionPMF (currentState t (eraseActionHistory t h)))
          (sigma t (q (currentState t (eraseActionHistory t h))))
    rw [current_erase, actual_next_state_eq_stationary_row,
      stationary_row_eq_actionMixture]
  have hprojected : riskProjectedKernel p0 K id Prod.snd L = L := by
    funext t h
    change riskConditionedRow (causalLaw p0 K t) (eraseActionHistory t)
      (fun g => (K t g).map Prod.snd) (L t) h = L t h
    by_cases hp : h ∈ ((causalLaw p0 K t).map (eraseActionHistory t)).support
    · rw [riskConditionedRow, dif_pos hp]
      let posterior := riskFiberPosterior (causalLaw p0 K t) (eraseActionHistory t) h hp
      change posterior.bind (fun g => (K t g).map Prod.snd) = L t h
      have hbind : posterior.bind (fun g => (K t g).map Prod.snd) =
          posterior.bind (fun _ => L t h) := by
        apply PMF.ext
        intro z
        simp only [PMF.bind_apply]
        apply tsum_congr
        intro g
        by_cases hg : posterior g = 0
        · simp [hg]
        · have hmem : g ∈ posterior.support := (PMF.mem_support_iff _ _).mpr hg
          have hfiber : eraseActionHistory t g = h :=
            (riskFiberPosterior_support (causalLaw p0 K t)
              (eraseActionHistory t) h hp ▸ hmem).1
          rw [hrow t g, hfiber]
      simpa only [PMF.bind_const] using hbind
    · rw [riskConditionedRow, dif_neg hp]
  change (causalLaw p0 K n).map (riskHistoryMap id Prod.snd n) = causalLaw p0 L n
  rw [risk_causalLaw_map p0 K id Prod.snd L n, PMF.map_id, hprojected]

/-- A state target built by recursion, independently of the actions. -/
def targetPath {X : Type u} (p0 : PMF X) (R : ℕ → X → PMF X) (n : ℕ) :
    PMF (CausalHistory X X n) :=
  causalLaw p0 (fun k h => R k (currentState k h)) n

/-- Actual positive-occupancy states of the target at this time. -/
def occupiedState {X : Type u} (p0 : PMF X) (R : ℕ → X → PMF X) (n : ℕ) : Set X :=
  {x | ∃ h : CausalHistory X X n, targetPath p0 R n h ≠ 0 ∧ currentState n h = x}

/-- Convex feasibility of the WHOLE occupied observation fiber. There is one
action mixture per time and observation, not one per hidden state. -/
def OccupiedFiberFeasible
    {X Y A : Type u} [Fintype X] [Fintype A]
    (M : Model X (fun _ => A)) (q : X → Y)
    (p0 : PMF X) (R : ℕ → X → PMF X) (T : ℕ) : Prop :=
  ∀ t : Fin T, ∀ y,
    (fun x : {x : occupiedState p0 R t.val // q x.val = y} => realRow (R t.val x.val.val)) ∈
      convexHull ℝ (Set.range (fun a (x : {x : occupiedState p0 R t.val // q x.val = y}) =>
        realRow (M.transitionPMF x.val.val a)))

private theorem causalLaw_eq_on_target_support
    {X : Type u} [Fintype X] (p0 : PMF X)
    (K L : ∀ n, CausalHistory X X n → PMF X) (T : ℕ)
    (hrow : ∀ n, n < T → ∀ h, causalLaw p0 L n h ≠ 0 → K n h = L n h) :
    ∀ n, n ≤ T → causalLaw p0 K n = causalLaw p0 L n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hn' : n ≤ T := by omega
      have hlt : n < T := by omega
      apply PMF.ext
      intro hz
      rcases hz with ⟨h, z⟩
      change pmfExtend (causalLaw p0 K n) (K n) (h, z) =
        pmfExtend (causalLaw p0 L n) (L n) (h, z)
      rw [pmfExtend_apply, pmfExtend_apply, ih hn']
      by_cases hp : causalLaw p0 L n h = 0
      · simp [hp]
      · rw [hrow n hlt h hp]

/-- From actual finite-action convex feasibility to a complete controlled
path. The initial law is shared explicitly. No condition is imposed on rows
that the target never occupies, and no fitted path equality is an input. -/
theorem occupied_fibers_supply_actual_path
    {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
    (M : Model X (fun _ => A)) (q : X → Y)
    (p0 : PMF X) (R : ℕ → X → PMF X) (T : ℕ)
    (hfeasible : OccupiedFiberFeasible M q p0 R T) :
    ∃ sigma : ℕ → Y → PMF A,
      (causalLaw p0 (riskMicroControlKernel q (fun _ => M.transitionPMF)
        (timeObservationPolicy sigma)) T).map (eraseActionHistory T) = targetPath p0 R T := by
  have hex (t : Fin T) : ∃ s : Y → PMF A,
      ∀ x : occupiedState p0 R t.val,
        actionMixture (M.transitionPMF x.val) (s (q x.val)) = R t.val x.val := by
    exact (observation_realizable_iff_fiber_convexHull (fun x => q x.val)
      (fun x : occupiedState p0 R t.val => M.transitionPMF x.val)
      (fun x => R t.val x.val)).mpr (hfeasible t)
  choose s hs using hex
  let sigma : ℕ → Y → PMF A := fun n =>
    if hn : n < T then s ⟨n, hn⟩ else fun _ => PMF.pure (Classical.choice inferInstance)
  refine ⟨sigma, ?_⟩
  rw [time_action_state_path_eq_mixture]
  apply causalLaw_eq_on_target_support p0 (timeMixtureKernel M q sigma)
    (fun n h => R n (currentState n h)) T ?_ T (le_refl T)
  intro n hn h hp
  have he := hs ⟨n, hn⟩ ⟨currentState n h, ⟨h, hp, rfl⟩⟩
  simpa only [timeMixtureKernel, sigma, dif_pos hn] using he

section ConditionedSource

variable {X Y A : Type u} [Fintype X] [Fintype A] [Nonempty A]
variable [MeasurableSpace X] [MeasurableSingletonClass X]
variable [MeasurableSpace A] [MeasurableSingletonClass A]
variable (M : Model X (fun _ => A)) (q : X → Y) (basePolicy : Y → PMF A)
variable (p0 : PMF X) (safe : Set X) (T : ℕ)
variable (hpos : 0 < actualSurvivalMass M q basePolicy p0 safe T)
variable (fallback : ℕ → safe → PMF safe) (outside : ℕ → X → PMF X)

/-- The prepared initial marginal is the independently constructed survival
tilt at time zero. Actions after time zero cannot prepare this law for free. -/
def preparedInitial : PMF X :=
  generatedAmbientPrefix M q basePolicy p0 safe T hpos fallback outside 0

/-- Total finite-window rows on the original ambient state alphabet. -/
def conditionedTargetRow (n : ℕ) : X → PMF X :=
  ambientWindowRow M q basePolicy safe fallback outside (T - (n + 1))

/-- C4 concrete consumer: the convex action certificate supplies an actual
time-dependent control experiment whose full state path is the ORIGINAL
survival-conditioned experiment. All target/source identities are derived.
This certifies operational path transport, not ontic parent equality. -/
theorem occupied_conditioned_fibers_supply_actual_experiment
    (hfeasible : OccupiedFiberFeasible M q
      (preparedInitial M q basePolicy p0 safe T hpos fallback outside)
      (conditionedTargetRow M q basePolicy safe T fallback outside) T) :
    ∃ sigma : ℕ → Y → PMF A,
      (causalLaw (preparedInitial M q basePolicy p0 safe T hpos fallback outside)
        (riskMicroControlKernel q (fun _ => M.transitionPMF) (timeObservationPolicy sigma)) T).map
          (eraseActionHistory T) =
        actualConditionedPrefix M q basePolicy p0 safe T 0 hpos := by
  obtain ⟨sigma, hs⟩ := occupied_fibers_supply_actual_path M q
    (preparedInitial M q basePolicy p0 safe T hpos fallback outside)
    (conditionedTargetRow M q basePolicy safe T fallback outside) T hfeasible
  refine ⟨sigma, hs.trans ?_⟩
  change generatedAmbientPrefix M q basePolicy p0 safe T hpos fallback outside T = _
  exact generated_ambient_eq_actual M q basePolicy p0 safe T 0 hpos fallback outside

end ConditionedSource

/-- An explicit fully actuated source: selecting action a sets the next state
to a. This states the actuation power as a model, not as a universal fact. -/
def stateSelectionModel (X : Type u) [Fintype X] : Model X (fun _ => X) where
  transition := fun _ a y => (PMF.pure a y).toReal
  reward := fun _ _ => 0
  rewardBound := 1
  discount := 1 / 2
  transition_nonneg := fun _ _ _ => ENNReal.toReal_nonneg
  transition_sum_one := fun _ a => coverage_sum_toReal (PMF.pure a)
  reward_abs_le := by intros; norm_num
  discount_pos := by norm_num
  discount_lt_one := by norm_num

private theorem stateSelection_row {X : Type u} [Fintype X] [Nonempty X] (x a : X) :
    (stateSelectionModel X).transitionPMF x a = PMF.pure a := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [Model.transitionPMF_apply_toReal]
  rfl

/-- Nonvacuous constructive family: when all state-selection actions are
actually allowed and the state is observed, every positive finite-window
conditioning of this same source can be implemented after preparing its
initial tilt. The feasibility condition is proved, not assumed. -/
theorem state_selection_realizes_its_conditioned_path
    {X : Type u} [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (basePolicy : X → PMF X) (p0 : PMF X) (safe : Set X) (T : ℕ)
    (hpos : 0 < actualSurvivalMass (stateSelectionModel X) id basePolicy p0 safe T)
    (fallback : ℕ → safe → PMF safe) (outside : ℕ → X → PMF X) :
    ∃ sigma : ℕ → X → PMF X,
      (causalLaw (preparedInitial (stateSelectionModel X) id basePolicy p0 safe T hpos fallback outside)
        (riskMicroControlKernel id (fun _ => (stateSelectionModel X).transitionPMF)
          (timeObservationPolicy sigma)) T).map (eraseActionHistory T) =
        actualConditionedPrefix (stateSelectionModel X) id basePolicy p0 safe T 0 hpos := by
  apply occupied_conditioned_fibers_supply_actual_experiment
    (stateSelectionModel X) id basePolicy p0 safe T hpos fallback outside
  intro t
  apply (observation_realizable_iff_fiber_convexHull
    (fun x : occupiedState
      (preparedInitial (stateSelectionModel X) id basePolicy p0 safe T hpos fallback outside)
      (conditionedTargetRow (stateSelectionModel X) id basePolicy safe T fallback outside) t.val =>
        id x.val)
    (fun x => (stateSelectionModel X).transitionPMF x.val)
    (fun x => conditionedTargetRow (stateSelectionModel X) id basePolicy safe T fallback outside t.val x.val)).mp
  refine ⟨conditionedTargetRow (stateSelectionModel X) id basePolicy safe T fallback outside t.val, ?_⟩
  intro x
  simp only [actionMixture, id_eq]
  rw [show (stateSelectionModel X).transitionPMF x.val = PMF.pure from
    funext (fun a => stateSelection_row x.val a)]
  exact PMF.bind_pure _

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConditionedActionTransportCheck
