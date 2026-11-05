import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionCountPosterior
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserverSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionSupportedPolicy

/-!
# Count posterior on arbitrary permitted real-randomized histories

The source likelihood here expands the actual four-branch primitive. A causal
policy's memory is updated only by its own action and permitted receipt. Its
real action-probability product is common to every theta on a fixed history,
so that factor cancels when conditioning. No positivity of individual priors
or rates is assumed; positivity of the actual history proves its denominator.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionCountHistory

open scoped BigOperators
open RegisterJointDecisionSource RegisterDecisionObserver
open RegisterDecisionObserverSource RegisterDecisionCountPosterior
open FiniteJointDecisionSolver (Model)
open FiniteJointDecisionSupportedPolicy (RawCausalPolicy)

def CompatibleHistory (goal : Bool) : Local → History → Prop
  | _, [] => True
  | q, (a,o) :: h => compatible goal q a o ∧ CompatibleHistory goal (update goal q a o) h

def historyLikelihood (r : ℚ) (goal : Bool) : Local → History → ℚ
  | _, [] => 1
  | q, (a,o) :: h => likelihood r goal q a o * historyLikelihood r goal (update goal q a o) h

theorem historyLikelihood_nonneg (r : ℚ) (hr : 0 ≤ r ∧ r ≤ 1) (goal : Bool) :
    ∀ (h : History) (q : Local), 0 ≤ historyLikelihood r goal q h := by
  intro h
  induction h with
  | nil => intro q; exact zero_le_one
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro q
      exact mul_nonneg (likelihood_nonneg r hr goal q a o) (ih _)

theorem incompatible_likelihood_zero (r : ℚ) (goal : Bool) :
    ∀ (h : History) (q : Local), ¬CompatibleHistory goal q h → historyLikelihood r goal q h = 0 := by
  intro h
  induction h with
  | nil => intro q hc; exact (hc trivial).elim
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro q hc
      by_cases hrow : compatible goal q a o
      · have htail : ¬CompatibleHistory goal (update goal q a o) h := fun hh => hc ⟨hrow, hh⟩
        rw [historyLikelihood, ih _ htail, mul_zero]
      · rw [historyLikelihood, likelihood_counts, if_neg hrow, zero_mul]

variable {Theta : Type} [Fintype Theta]

/-- Multiplicative likelihood along any compatible history is exactly the
increment in the executable observer's informative counts. -/
theorem countWeight_history (r prior : Theta → ℚ) (goal : Bool) :
    ∀ (h : History) (st : Stat), CompatibleHistory goal st.q h → ∀ theta,
      countWeight r prior (summarizeFrom goal st h).s (summarizeFrom goal st h).f theta =
        countWeight r prior st.s st.f theta * historyLikelihood (r theta) goal st.q h := by
  intro h
  induction h with
  | nil => intro st hc theta; simp [historyLikelihood]
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro st hc theta
      rw [summarizeFrom_cons, ih (updateStat goal st a o) hc.2 theta]
      change countWeight r prior (st.s + successIncrement goal st.q a o)
          (st.f + failureIncrement goal st.q a o) theta *
          historyLikelihood (r theta) goal (update goal st.q a o) h = _
      rw [countWeight_update r prior st.s st.f goal st.q a o hc.1 theta]
      simp only [historyLikelihood]
      ring

/-- Literal original packed primitive likelihood. Labels and uninformative
mode outcomes are summed here, rather than treated as extra observed samples. -/
def worldLikelihood (r : Theta → ℚ) (goal : Bool) : World Theta → History → ℚ
  | _, [] => 1
  | w, (a,o) :: h =>
      ∑ z : Noise, primitiveWeight r w z *
        (if observe goal w a z = o then worldLikelihood r goal (step goal w a z) h else 0)

theorem worldLikelihood_eq_local (r : Theta → ℚ) (goal : Bool) :
    ∀ (h : History) (w : World Theta), Rooted w →
      worldLikelihood r goal w h = historyLikelihood (r w.theta) goal (projectLocal goal w) h := by
  intro h
  induction h with
  | nil => intro w hw; rfl
  | cons e h ih =>
      rcases e with ⟨a,o⟩
      intro w hw
      simp only [worldLikelihood, historyLikelihood]
      rw [← primitive_likelihood r goal w a o hw, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases ho : observe goal w a z = o
      · simp only [if_pos ho]
        rw [ih (step goal w a z) (rooted_step goal w a z hw), theta_preserved,
          update_project goal w a z hw, ho]
      · simp [ho]

def initialWorld (goal : Bool) (theta : Theta) : World Theta :=
  ⟨theta, [some (!goal)], false⟩

/-- Exact finite prior atom times the actual fixed-theta history likelihood. -/
theorem initial_likelihood_counts (r prior : Theta → ℚ) (goal : Bool)
    (h : History) (hc : CompatibleHistory goal (init goal) h) (theta : Theta) :
    prior theta * worldLikelihood r goal (initialWorld goal theta) h =
      countWeight r prior (summarize goal h).s (summarize goal h).f theta := by
  rw [worldLikelihood_eq_local r goal h (initialWorld goal theta) (initial_rooted goal theta)]
  change prior theta * historyLikelihood (r theta) goal (init goal) h = _
  have he := countWeight_history r prior goal h (initialStat goal) hc theta
  simpa [summarize, initialStat] using he.symm

variable {I : Type*}

/-- Action randomization depends on permitted memory, which may be the full
visible history. The same initial h and subsequent action/receipt sequence are
used for every theta; no world is passed to the policy. -/
noncomputable def actionFactor {M : Model I Act Obs} (pi : RawCausalPolicy M) :
    pi.Memory → History → ℝ
  | _, [] => 1
  | h, (a,o) :: rest => pi.actionProb h a * actionFactor pi (pi.advance h a o) rest

theorem actionFactor_nonneg {M : Model I Act Obs} (pi : RawCausalPolicy M) :
    ∀ (history : History) (h : pi.Memory), 0 ≤ actionFactor pi h history := by
  intro history
  induction history with
  | nil => intro h; exact zero_le_one
  | cons e rest ih =>
      rcases e with ⟨a,o⟩
      intro h
      exact mul_nonneg (pi.actionProb_nonneg h a) (ih _)

/-- Direct primitive execution of a prescribed visible history by an arbitrary
real randomized causal kernel. It includes every hidden mode/label branch. -/
noncomputable def rawWorldLikelihood (r : Theta → ℚ) (goal : Bool)
    {M : Model I Act Obs} (pi : RawCausalPolicy M) : pi.Memory → World Theta → History → ℝ
  | _, _, [] => 1
  | h, w, (a,o) :: rest =>
      pi.actionProb h a * ∑ z : Noise, (primitiveWeight r w z : ℝ) *
        (if observe goal w a z = o then
          rawWorldLikelihood r goal pi (pi.advance h a o) (step goal w a z) rest else 0)

/-- Causal action factors separate from the true hidden-source likelihood.
This theorem is stronger than restricting to a particular summary policy or
to rational randomization, and does not assume a posterior-correctness field. -/
theorem rawWorldLikelihood_factor (r : Theta → ℚ) (goal : Bool)
    {M : Model I Act Obs} (pi : RawCausalPolicy M) :
    ∀ (history : History) (h : pi.Memory) (w : World Theta),
      rawWorldLikelihood r goal pi h w history =
        actionFactor pi h history * (worldLikelihood r goal w history : ℝ) := by
  intro history
  induction history with
  | nil => intro h w; simp [rawWorldLikelihood, actionFactor, worldLikelihood]
  | cons e rest ih =>
      rcases e with ⟨a,o⟩
      intro h w
      simp only [rawWorldLikelihood, actionFactor, worldLikelihood,
        Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_zero, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases ho : observe goal w a z = o
      · simp only [if_pos ho]
        rw [ih]
        ring
      · simp [ho]

noncomputable def rawPriorMass (r prior : Theta → ℚ) (goal : Bool)
    {M : Model I Act Obs} (pi : RawCausalPolicy M) (h : pi.Memory) (history : History) : ℝ :=
  ∑ theta, (prior theta : ℝ) * rawWorldLikelihood r goal pi h (initialWorld goal theta) history

theorem rawPriorMass_eq (r prior : Theta → ℚ) (goal : Bool)
    {M : Model I Act Obs} (pi : RawCausalPolicy M) (h : pi.Memory) (history : History)
    (hc : CompatibleHistory goal (init goal) history) :
    rawPriorMass r prior goal pi h history =
      actionFactor pi h history * (normalizer r prior (summarize goal history).s
        (summarize goal history).f : ℝ) := by
  simp only [rawPriorMass, normalizer, Rat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro theta htheta
  rw [rawWorldLikelihood_factor]
  have he : (prior theta : ℝ) *
      (worldLikelihood r goal (initialWorld goal theta) history : ℝ) =
        (countWeight r prior (summarize goal history).s (summarize goal history).f theta : ℝ) := by
    exact_mod_cast initial_likelihood_counts r prior goal history hc theta
  rw [← he]
  ring

theorem incompatible_prior_mass_zero (r prior : Theta → ℚ) (goal : Bool)
    {M : Model I Act Obs} (pi : RawCausalPolicy M) (h : pi.Memory) (history : History)
    (hc : ¬CompatibleHistory goal (init goal) history) :
    rawPriorMass r prior goal pi h history = 0 := by
  apply Finset.sum_eq_zero
  intro theta htheta
  rw [rawWorldLikelihood_factor,
    worldLikelihood_eq_local r goal history (initialWorld goal theta) (initial_rooted goal theta)]
  change (prior theta : ℝ) * (actionFactor pi h history *
    (historyLikelihood (r theta) goal (init goal) history : ℝ)) = 0
  rw [incompatible_likelihood_zero (r theta) goal history (init goal) hc]
  simp

/-- Every positive actual history has compatible receipts, a positive common
action factor and a strictly positive count normalizer. This includes zero
prior weights and endpoint rates without additional regularity assumptions. -/
theorem positive_history (r prior : Theta → ℚ) (goal : Bool)
    {M : Model I Act Obs} (pi : RawCausalPolicy M) (h : pi.Memory) (history : History)
    (hp : 0 < rawPriorMass r prior goal pi h history) :
    CompatibleHistory goal (init goal) history ∧ 0 < actionFactor pi h history ∧
      0 < normalizer r prior (summarize goal history).s (summarize goal history).f := by
  have hc : CompatibleHistory goal (init goal) history := by
    by_contra hn
    rw [incompatible_prior_mass_zero r prior goal pi h history hn] at hp
    exact lt_irrefl 0 hp
  rw [rawPriorMass_eq r prior goal pi h history hc] at hp
  rcases mul_pos_iff.mp hp with hpos | hneg
  · exact ⟨hc, hpos.1, by exact_mod_cast hpos.2⟩
  · exact ((not_lt_of_ge (actionFactor_nonneg pi history h)) hneg.1).elim

/-- The actual conditional theta distribution under every real randomized
full-history causal policy is exactly the executable count posterior.
The action randomization factor cancels; it is not confused with a new sample
of theta or with an additional observation. -/
theorem conditional_count_posterior (r prior : Theta → ℚ) (goal : Bool)
    {M : Model I Act Obs} (pi : RawCausalPolicy M) (h : pi.Memory) (history : History)
    (hp : 0 < rawPriorMass r prior goal pi h history) (theta : Theta) :
    ((prior theta : ℝ) * rawWorldLikelihood r goal pi h (initialWorld goal theta) history) /
        rawPriorMass r prior goal pi h history =
      (posteriorWeight r prior (summarize goal history).s (summarize goal history).f theta : ℝ) := by
  obtain ⟨hc, ha, hz⟩ := positive_history r prior goal pi h history hp
  rw [rawWorldLikelihood_factor, rawPriorMass_eq r prior goal pi h history hc]
  have he : (prior theta : ℝ) *
      (worldLikelihood r goal (initialWorld goal theta) history : ℝ) =
        (countWeight r prior (summarize goal history).s (summarize goal history).f theta : ℝ) := by
    exact_mod_cast initial_likelihood_counts r prior goal history hc theta
  have hzR : (normalizer r prior (summarize goal history).s (summarize goal history).f : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hz
  rw [posteriorWeight, if_neg (ne_of_gt hz)]
  push_cast
  rw [← he]
  field_simp [ne_of_gt ha, hzR]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionCountHistory
