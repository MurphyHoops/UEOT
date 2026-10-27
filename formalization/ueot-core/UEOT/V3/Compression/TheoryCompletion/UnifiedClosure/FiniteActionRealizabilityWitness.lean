import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizability
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteConditionalStability
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteWindowDoobWitness

/-!
# Positive implementation and genuine action/information obstructions

The existing three-state source has only one allowed action. Its actual
one-step survival-conditioned row is a fair law on the two safe states,
whereas every original action randomization retains cemetery mass. The exact
irreducible row errors are 1/4 and 3/4. Adding the two deterministic safe
actions permits a fair randomization to implement that SAME conditioned row.

A separate two-state example isolates the observation-fiber obstruction.
Finally the three-state experiment's actual conditional initial tilt gives a
1/4 full-path lower bound for ANY causal kernel with the original initial law.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck

open MeasureTheory
open UEOT.V3.PathError UEOT.V3.TotalVariation
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteActionRealizabilityCheck FiniteConditionalStability
open FiniteWindowDoobWitnessCheck
open scoped BigOperators Classical

noncomputable section

local instance : MeasurableSpace State := ⊤

private theorem cemetery_ne_safe (b : Bool) : (none : State) ≠ some b := by
  intro h
  cases h

/-- This is the original witness model's actual one allowed transition row. -/
def originalRow (i : Bool) : PMF State := model.transitionPMF (some i) ()

private theorem originalRow_atom (i : Bool) (x : State) :
    (originalRow i x).toReal = transition (some i) () x := by
  exact Model.transitionPMF_apply_toReal model (some i) () x

private theorem actual_row_survival (i : Bool) :
    (originalRow i).toMeasure.real safe = if i then 1 / 4 else 3 / 4 := by
  have hs : safe = (({some false, some true} : Finset State) : Set State) := by
    ext x
    fin_cases x <;> simp [safe]
  rw [hs, pmfMeasureReal_eq_sum_finset]
  cases i <;> norm_num [originalRow_atom, transition]

private theorem actual_row_survival_pos (i : Bool) :
    0 < (originalRow i).toMeasure.real safe := by
  rw [actual_row_survival]
  cases i <;> norm_num

/-- Filter the actual original row on survival; no independent target law is
chosen and no identity to a conditional row is assumed. -/
def targetConditionalRow (i : Bool) : PMF State :=
  conditionedPMF (originalRow i) safe (actual_row_survival_pos i)

private theorem targetConditionalRow_atom (i : Bool) (x : State) :
    (targetConditionalRow i x).toReal = match x with
      | none => 0
      | some _ => 1 / 2 := by
  have h := mass_mul_conditioned_atom (originalRow i) safe
    (actual_row_survival_pos i) x
  change (originalRow i).toMeasure.real safe * (targetConditionalRow i x).toReal = _ at h
  rw [actual_row_survival, originalRow_atom] at h
  cases i <;> fin_cases x <;>
    norm_num [safe, transition, Option.some_ne_none, cemetery_ne_safe] at h ⊢ <;> linarith

private theorem singleton_action_mixture (i : Bool) (sigma : PMF Unit) :
    actionMixture (model.transitionPMF (some i)) sigma = originalRow i := by
  have hr : model.transitionPMF (some i) = (fun _ : Unit => originalRow i) := by
    funext a
    cases a
    rfl
  rw [actionMixture, hr, PMF.bind_const]

/-- Exact error of EVERY policy row allowed by the original singleton action
set.  The target is the actual original row conditioned on one-step survival. -/
theorem original_actions_have_irreducible_conditional_error
    (i : Bool) (sigma : PMF Unit) :
    tvDist (actionMixture (model.transitionPMF (some i)) sigma).toMeasure
      (targetConditionalRow i).toMeasure = if i then 3 / 4 else 1 / 4 := by
  rw [singleton_action_mixture, tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, Fintype.sum_option, Fintype.sum_bool,
    originalRow_atom, targetConditionalRow_atom]
  cases i <;> norm_num [transition]

/-- In particular, the actual conditioned row lies OUTSIDE the original
allowed-action convex hull, even though it is a well-defined stochastic row. -/
theorem conditional_row_outside_original_action_hull (i : Bool) :
    realRow (targetConditionalRow i) ∉ convexHull ℝ
      (Set.range (fun a : Unit => realRow (model.transitionPMF (some i) a))) := by
  intro h
  obtain ⟨sigma, hsigma⟩ := (row_realizable_iff_mem_convexHull
    (model.transitionPMF (some i)) (targetConditionalRow i)).mpr h
  have herr := original_actions_have_irreducible_conditional_error i sigma
  rw [hsigma, tvDist_self_eq_zero] at herr
  cases i <;> norm_num at herr

/-- The two added deterministic actions choose either safe state. -/
def safeAction (a : Bool) : PMF State := PMF.pure (some a)

/-- The old action is retained as `none`; `some a` is the added safe action. -/
def extendedAction (i : Bool) : Option Bool → PMF State
  | none => originalRow i
  | some a => safeAction a

/-- Randomize only the two safe actions in the enlarged allowed family. -/
def fairSafePolicy : PMF (Option Bool) := (PMF.uniformOfFintype Bool).map some

private theorem fair_safe_mixture_eq_target (i : Bool) :
    actionMixture safeAction (PMF.uniformOfFintype Bool) = targetConditionalRow i := by
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _)).mp
  have h := congrFun (realRow_actionMixture safeAction (PMF.uniformOfFintype Bool)) x
  change (actionMixture safeAction (PMF.uniformOfFintype Bool) x).toReal = _ at h
  rw [h, targetConditionalRow_atom]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, realRow,
    Fintype.sum_bool]
  fin_cases x <;> norm_num [safeAction, PMF.pure_apply, PMF.uniformOfFintype_apply,
    Option.some_ne_none, cemetery_ne_safe]

/-- The old source row and two new deterministic safe actions form one
explicit allowed family. Fair sampling of its safe actions implements the
SAME survival-conditioned target of the retained original action. -/
theorem added_safe_actions_realize_conditional_row (i : Bool) :
    actionMixture (extendedAction i) fairSafePolicy = targetConditionalRow i := by
  unfold actionMixture fairSafePolicy
  rw [PMF.bind_map]
  change actionMixture safeAction (PMF.uniformOfFintype Bool) = _
  exact fair_safe_mixture_eq_target i

/-- No deterministic member of the enlarged allowed family implements the
target; randomization is essential in the positive example. -/
theorem deterministic_extended_action_does_not_realize (i : Bool) (a : Option Bool) :
    extendedAction i a ≠ targetConditionalRow i := by
  cases a with
  | none =>
      intro h
      have herr := original_actions_have_irreducible_conditional_error i (PMF.pure ())
      rw [singleton_action_mixture] at herr
      change originalRow i = targetConditionalRow i at h
      rw [h, tvDist_self_eq_zero] at herr
      cases i <;> norm_num at herr
  | some a =>
      intro h
      have hatom := congrArg (fun p : PMF State => (p (some a)).toReal) h
      rw [targetConditionalRow_atom] at hatom
      norm_num [extendedAction, safeAction, PMF.pure_apply] at hatom

/-- Each hidden state separately has a feasible deterministic action. -/
theorem separately_feasible_hidden_rows :
    ∀ x : Bool, ∃ sigma : PMF Bool,
      actionMixture (fun a => PMF.pure a) sigma = PMF.pure x := by
  intro x
  exact ⟨PMF.pure x, by simp [actionMixture, PMF.pure_bind]⟩

/-- An aliased current observation cannot choose two different action PMFs.
This is an obstruction to current-observation feedback, not a theorem that
all controllers with informative history or memory are impossible. -/
theorem no_common_policy_for_aliased_rows :
    ¬ ∃ sigma : Unit → PMF Bool, ∀ x : Bool,
      actionMixture (fun a => PMF.pure a) (sigma ()) = PMF.pure x := by
  rintro ⟨sigma, h⟩
  have heq : (PMF.pure false : PMF Bool) = PMF.pure true := (h false).symm.trans (h true)
  have hatom := congrArg (fun p : PMF Bool => p false) heq
  norm_num [PMF.pure_apply] at hatom

private theorem conditioned_initial_atom (x : State) :
    (conditionedPair.map Prod.fst x).toReal = match x with
      | none => 0
      | some false => 3 / 4
      | some true => 1 / 4 := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum (by
    intro h _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  simp only [apply_ite, ENNReal.toReal_zero, Fintype.sum_prod_type,
    Fintype.sum_option, Fintype.sum_bool]
  fin_cases x <;> norm_num [conditioned_cemetery_left,
    conditioned_cemetery_right, conditioned_safe_atom, Option.some_ne_none, cemetery_ne_safe]

private theorem original_initial_atom (x : State) :
    (initial x).toReal = match x with
      | none => 0
      | some _ => 1 / 2 := by
  cases x with
  | none =>
      have hz : initial none = 0 := by
        unfold initial
        rw [PMF.map_apply]
        apply ENNReal.tsum_eq_zero.mpr
        intro i
        apply if_neg
        intro heq
        exact i.property heq.symm
      simp [hz]
  | some b => exact initial_safe_mass b

/-- In the actual original three-state experiment, conditioning through time
one changes the initial PMF by TV = 1/4. -/
theorem actual_conditioning_changes_initial_tv :
    tvDist initial.toMeasure (conditionedPair.map Prod.fst).toMeasure = 1 / 4 := by
  rw [tvDist_eq_one_sub_pmfCommonMass]
  simp only [pmfCommonMass, Fintype.sum_option, Fintype.sum_bool,
    original_initial_atom, conditioned_initial_atom]
  norm_num

/-- Even arbitrarily changed future kernels cannot implement this complete
conditional path from the ORIGINAL initial PMF: the initial tilt alone costs
at least 1/4 TV.  This statement permits all causal history dependence. -/
theorem unchanged_initial_forces_path_error
    (L : ∀ n, CausalHistory State State n → PMF State) :
    1 / 4 ≤ tvDist (causalLaw initial L 1).toMeasure conditionedPair.toMeasure := by
  have h := initial_tv_le_path_tv initial L 1 conditionedPair
  change tvDist initial.toMeasure (conditionedPair.map Prod.fst).toMeasure ≤ _ at h
  rw [actual_conditioning_changes_initial_tv] at h
  exact h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteActionRealizabilityWitnessCheck
