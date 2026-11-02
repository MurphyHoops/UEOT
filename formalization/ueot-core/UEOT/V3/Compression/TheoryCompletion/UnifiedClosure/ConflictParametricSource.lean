import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SafeRewardConflictWitness
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePolicyPath

/-!
Original promise: the four-state conflicting reward example admits a parameterized actual stochastic control experiment.
Existing source: conflictRewardControl.micro, its real transitionPMF, and the nonempty safe viability fixed point.
Reduced premise: derive each randomized closed row and invariant candidate from the same original transition PMF.
Family: every real theta in [0,1], including both endpoints, with a constant action PMF at every complete history.
Consumers: actual full-path conditioning, stationary/Cesaro/QSD, and discounted unrestricted/restricted control.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricSource

open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly UEOT.V3.PathError
open FiniteActionRealizabilityCheck SourcePolicyPathBridgeCheck
open scoped BigOperators

noncomputable section

abbrev State := Bool × Bool
def M := conflictRewardControl.micro

theorem transition_eq (x : State) (a : Bool) (y : State) :
    M.transition x a y = if y.1 = a then (1/2 : ℝ) else 0 := rfl

theorem transition_real (x : State) (a : Bool) (y : State) :
    (M.transitionPMF x a y).toReal = if y.1 = a then (1/2 : ℝ) else 0 := by
  rw [Model.transitionPMF_apply_toReal]
  rfl

theorem reward_eq (x : State) (a : Bool) : M.reward x a = if a then (0 : ℝ) else 1 := rfl
theorem discount_eq : M.discount = (1/2 : ℝ) := rfl

def actionWeight (theta : ℝ) (a : Bool) : ℝ := if a then 1-theta else theta

def actionLaw (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) : PMF Bool :=
  FiniteProbabilityRow.ofRealRow (actionWeight theta)
    (by intro a; cases a <;> simp only [actionWeight, Bool.false_eq_true, if_false, if_true]; assumption; linarith)
    (by simp [actionWeight])

theorem actionLaw_real (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (a : Bool) :
    (actionLaw theta h0 h1 a).toReal = actionWeight theta a :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

/-- The complete history is retained, although this particular action law is constant. -/
def historyPolicy (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    ∀ t, CausalHistory State (Bool × State) t → PMF Bool := fun _ _ => actionLaw theta h0 h1

def causalPolicy (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    CausalPolicy State (fun _ => Bool) where
  Memory t := CausalHistory State (Bool × State) t
  current := fun {t} h => riskLastState t h
  advance := fun h a y => (h,(a,y))
  current_advance := by intros; rfl
  actionProb := fun _ a => (actionLaw theta h0 h1 a).toReal
  actionProb_nonneg := by intros; exact ENNReal.toReal_nonneg
  actionProb_sum_one := by intros; exact coverage_sum_toReal _

theorem causalPolicy_action (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    {t : ℕ} (h : (causalPolicy theta h0 h1).Memory t) (a : Bool) :
    (causalPolicy theta h0 h1).actionProb h a = actionWeight theta a :=
  actionLaw_real theta h0 h1 a

def closedRow (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (x : State) : PMF State :=
  actionMixture (M.transitionPMF x) (actionLaw theta h0 h1)

def closedMatrix (theta : ℝ) (_x y : State) : ℝ := if y.1 then (1-theta)/2 else theta/2

theorem closedRow_real (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (x y : State) :
    (closedRow theta h0 h1 x y).toReal = closedMatrix theta x y := by
  have he := congrFun (realRow_actionMixture (M.transitionPMF x) (actionLaw theta h0 h1)) y
  rcases y with ⟨b,u⟩
  cases b <;> simpa [closedRow, realRow, actionLaw_real, Model.transitionPMF_apply_toReal,
    transition_eq, closedMatrix, actionWeight, div_eq_mul_inv] using he

def mu (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) : PMF State :=
  closedRow theta h0 h1 (false,false)

theorem mu_real (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (y : State) :
    (mu theta h0 h1 y).toReal = if y.1 then (1-theta)/2 else theta/2 :=
  closedRow_real theta h0 h1 (false,false) y

theorem closedRow_eq_mu (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (x : State) :
    closedRow theta h0 h1 x = mu theta h0 h1 := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [closedRow_real, mu_real]
  rfl

def policy (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    StationaryPolicy (fun _ : State => Bool) :=
  liftedStationaryPolicy id (fun _ => actionLaw theta h0 h1)

theorem policyMatrix_eq (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    policyMatrix M (policy theta h0 h1) = closedMatrix theta := by
  funext x y
  have he := congrFun (realRow_actionMixture (M.transitionPMF x) (actionLaw theta h0 h1)) y
  have hr : policyMatrix M (policy theta h0 h1) x y = (closedRow theta h0 h1 x y).toReal := by
    simpa [policyMatrix, Model.policyTransition, policy, liftedStationaryPolicy,
      closedRow, realRow] using he.symm
  exact hr.trans (closedRow_real theta h0 h1 x y)

theorem policyTransitionPMF_eq (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (x : State) :
    policyTransitionPMF M (policy theta h0 h1) x = closedRow theta h0 h1 x := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [policyTransitionPMF_apply_toReal, closedRow_real]
  exact congrFun (congrFun (policyMatrix_eq theta h0 h1) x) y

/-- Killing is restriction to the original safe fiber, indexed by its actual hidden bit. -/
def killed (theta : ℝ) (u v : Bool) : ℝ := closedMatrix theta (true,u) (true,v)

theorem killed_actual (theta : ℝ) (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (u v : Bool) :
    killed theta u v = (closedRow theta h0 h1 (true,u) (true,v)).toReal :=
  (closedRow_real theta h0 h1 _ _).symm

theorem killed_eq (theta : ℝ) (u v : Bool) : killed theta u v = (1-theta)/2 := rfl

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricSource
