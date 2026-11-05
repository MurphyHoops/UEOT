import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionObserverSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionCountPosterior
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionConsumer
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteJointDecisionRefinement

/-!
# The source-derived count representation, with the original action menu

The executable state contains only the receipt observer, informative counts,
elapsed time and the actual payment count. The world-side relation below is
proved from the existing primitive for every action. In particular it does not
give the scheduler a packed Store, the protected program, or a parent identity.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationModel

open scoped BigOperators
open RegisterJointDecisionSource RegisterDecisionObserver RegisterDecisionObserverSource
open RegisterDecisionCountPosterior RegisterJointDecisionConsumer
open FiniteJointDecisionBelief FiniteJointDecisionSolver
open FiniteJointDecisionRefinement

variable {Theta : Type} [Fintype Theta]

def wallet (tariff : ℚ) (initial : Wallet) (st : Stat) : Wallet :=
  ⟨max 0 (initial.val - (st.paidCount : ℚ) * tariff), le_max_left _ _⟩

def model (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) :
    Model Stat Act Obs where
  actions st := menu P.tariff (wallet P.tariff initial st)
  actions_nonempty st := menu_nonempty P.tariff (wallet P.tariff initial st)
  prob st a o := observationMass P.normal prior st.s st.f P.goal st.q a o
  prob_nonneg st a _ o := observationMass_nonneg P.normal prior P.normal_bounds hn
    st.s st.f P.goal st.q a o
  prob_sum_one st a _ := observationMass_total P.normal prior ht st.s st.f P.goal st.q a
  reward _ a o := gain P a o
  next st a o := updateStat P.goal st a o
  discount := P.discount
  discount_nonneg := P.discount_bounds.1

/-- Only this world-side proof relation refers to the full hidden Store. -/
structure BeliefMatches (P : Family Theta) (prior : Theta → ℚ)
    (st : Stat) (b : Belief (World Theta)) : Prop where
  support : ∀ x, b.weight x ≠ 0 → Rooted (b.state x) ∧ projectLocal P.goal (b.state x) = st.q
  theta : ∀ test : Theta → ℚ,
    expect b (fun w => test w.theta) =
      ∑ t, posteriorWeight P.normal prior st.s st.f t * test t

structure Rel (P : Family Theta) (prior : Theta → ℚ) (initial : Wallet)
    (i : Info Theta) (st : Stat) : Prop where
  belief : BeliefMatches P prior st i.1
  balance : i.2 = wallet P.tariff initial st
  denominator : 0 < normalizer P.normal prior st.s st.f

/-- Exact joint theta/receipt law from the old primitive. Zero old atoms are
removed algebraically; all remaining atoms use the proved receipt observer. -/
theorem joint_theta (P : Family Theta) (prior : Theta → ℚ)
    (st : Stat) (b : Belief (World Theta)) (h : BeliefMatches P prior st b)
    (a : Act) (o : Obs) (test : Theta → ℚ) :
    (∑ x : b.Atom × Noise, joint (source P) b a o x *
      test ((source P).next (b.state x.1) a x.2).theta) =
      ∑ t, posteriorWeight P.normal prior st.s st.f t *
        likelihood (P.normal t) P.goal st.q a o * test t := by
  rw [Fintype.sum_prod_type]
  have row (x : b.Atom) :
      (∑ z : Noise, joint (source P) b a o (x,z) *
        test ((source P).next (b.state x) a z).theta) =
        b.weight x * (likelihood (P.normal (b.state x).theta) P.goal st.q a o *
          test (b.state x).theta) := by
    by_cases hx : b.weight x = 0
    · simp [joint, hx]
    · obtain ⟨hr, hq⟩ := h.support x hx
      have term (z : Noise) :
          joint (source P) b a o (x,z) * test ((source P).next (b.state x) a z).theta =
          b.weight x * ((if observe P.goal (b.state x) a z = o then
            primitiveWeight P.normal (b.state x) z else 0) * test (b.state x).theta) := by
        by_cases ho : observe P.goal (b.state x) a z = o <;>
          simp [joint, source, step, ho, mul_assoc]
      simp_rw [term]
      rw [← Finset.mul_sum, ← Finset.sum_mul,
        primitive_likelihood P.normal P.goal (b.state x) a o hr, hq]
  simp_rw [row]
  have ht := h.theta (fun t => likelihood (P.normal t) P.goal st.q a o * test t)
  simpa only [expect, mul_assoc] using ht

theorem mass_eq (P : Family Theta) (prior : Theta → ℚ)
    (st : Stat) (b : Belief (World Theta)) (h : BeliefMatches P prior st b)
    (a : Act) (o : Obs) :
    mass (source P) b a o = observationMass P.normal prior st.s st.f P.goal st.q a o := by
  simpa only [mul_one, mass, observationMass] using joint_theta P prior st b h a o (fun _ => 1)

theorem belief_next (P : Family Theta) (prior : Theta → ℚ)
    (st : Stat) (b : Belief (World Theta)) (h : BeliefMatches P prior st b)
    (hz : 0 < normalizer P.normal prior st.s st.f)
    (a : Act) (o : Obs) (ho : 0 < mass (source P) b a o) :
    BeliefMatches P prior (updateStat P.goal st a o) (posterior (source P) b a o) := by
  have hm : 0 < observationMass P.normal prior st.s st.f P.goal st.q a o := by
    rw [← mass_eq P prior st b h a o]; exact ho
  constructor
  · apply posterior_supported (source P) b a o (ne_of_gt ho)
    intro x z hx _ hxz
    obtain ⟨hr, hq⟩ := h.support x hx
    refine ⟨rooted_step P.goal (b.state x) a z hr, ?_⟩
    change projectLocal P.goal (step P.goal (b.state x) a z) = update P.goal st.q a o
    rw [update_project P.goal (b.state x) a z hr, hq]
    change observe P.goal (b.state x) a z = o at hxz
    rw [hxz]
  · intro test
    apply (mul_left_cancel₀ (ne_of_gt ho))
    rw [posterior_identity, joint_theta P prior st b h a o test,
      mass_eq P prior st b h a o]
    exact (posterior_test_identity P.normal prior st.s st.f P.goal st.q a o hz hm test).symm

theorem clamp_sub (x c : ℚ) (hc : 0 ≤ c) :
    max 0 (max 0 x - c) = max 0 (x-c) := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_left hx', max_eq_left (by linarith : 0-c ≤ 0),
      max_eq_left (by linarith : x-c ≤ 0)]

/-- The total off-path wallet definition commutes too. Supported execution
uses literal subtraction, obtained later from the original prepayment law. -/
theorem wallet_next (P : Family Theta) (initial : Wallet) (st : Stat) (a : Act) (o : Obs) :
    wallet P.tariff initial (updateStat P.goal st a o) =
      advance P.tariff (wallet P.tariff initial st) a o := by
  apply Subtype.ext
  rcases o with ⟨birth, paid⟩
  cases paid
  · simp [wallet, updateStat, advance, charge]
  · simp only [wallet, updateStat, Bool.true_eq, ↓reduceIte, Nat.cast_add,
      Nat.cast_one, advance, charge]
    rw [clamp_sub _ _ P.tariff_pos.le]
    congr 1
    ring

theorem rel_next (P : Family Theta) (prior : Theta → ℚ) (initial : Wallet)
    (i : Info Theta) (st : Stat) (h : Rel P prior initial i st)
    (a : Act) (o : Obs) (ho : 0 < mass (source P) i.1 a o) :
    Rel P prior initial ((RegisterJointDecisionConsumer.model P).next i a o)
      (updateStat P.goal st a o) := by
  refine ⟨belief_next P prior st i.1 h.belief h.denominator a o ho, ?_, ?_⟩
  · change advance P.tariff i.2 a o = wallet P.tariff initial (updateStat P.goal st a o)
    rw [h.balance, wallet_next]
  · exact (positive_update P.normal prior st.s st.f P.goal st.q a o h.denominator
      (by rw [← mass_eq P prior st i.1 h.belief a o]; exact ho)).2

/-- A concrete instance of the old finite-model transfer: every premise here
is derived from actual Register source semantics, including every legal action. -/
def refinement (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) :
    StepRefinement (RegisterJointDecisionConsumer.model P) (model P prior hn ht initial)
      (Rel P prior initial) where
  actions i st h := by change menu P.tariff i.2 = _; rw [h.balance]; rfl
  prob i st h a _ o := mass_eq P prior st i.1 h.belief a o
  reward _ _ _ _ _ := rfl
  discount := rfl
  next i st h a _ o ho := rel_next P prior initial i st h a o ho

theorem initial_relation (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) :
    Rel P prior initial (initialBelief P prior hn ht, initial) (initialStat P.goal) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro t _
    exact ⟨initial_rooted P.goal t, rfl⟩
  · intro test
    simp only [expect, initialBelief, initialStat,
      posterior_zero_zero P.normal prior ht]
  · apply Subtype.ext
    simp [wallet, initialStat, max_eq_right initial.property]
  · simpa only [initialStat, normalizer_zero_zero P.normal prior ht] using (zero_lt_one : (0:ℚ)<1)

/-- Equality of the all-action optimum, inherited from the existing finite
Bellman theorem after proving the concrete representation relation. -/
theorem optimalValue_initial (P : Family Theta) (prior : Theta → ℚ)
    (hn : ∀ t, 0 ≤ prior t) (ht : ∑ t, prior t = 1) (initial : Wallet) (H : ℕ) :
    optimalValue (RegisterJointDecisionConsumer.model P) H
        (initialBelief P prior hn ht, initial) =
      optimalValue (model P prior hn ht initial) H (initialStat P.goal) :=
  optimalValue_transfer (refinement P prior hn ht initial) H _ _
    (initial_relation P prior hn ht initial)

/-- Arbitrary joint tests of the permitted receipt, next observer, birth,
actual fee and balance. No independent marginal-product assumption is used. -/
theorem joint_observable_law (P : Family Theta) (prior : Theta → ℚ)
    (initial : Wallet) (i : Info Theta) (st : Stat) (h : Rel P prior initial i st)
    (a : Act) (test : Obs → Stat → ℚ → ℚ → ℚ → ℚ) :
    expect i.1 (fun w => ∑ z : Noise, primitiveWeight P.normal w z *
      test (observe P.goal w a z) (updateStat P.goal st a (observe P.goal w a z))
        (if (observe P.goal w a z).1 then 1 else 0)
        (charge P.tariff (observe P.goal w a z))
        (advance P.tariff i.2 a (observe P.goal w a z)).val) =
    ∑ o : Obs, observationMass P.normal prior st.s st.f P.goal st.q a o *
      test o (updateStat P.goal st a o) (if o.1 then 1 else 0)
        (charge P.tariff o) (wallet P.tariff initial (updateStat P.goal st a o)).val := by
  change expect i.1 (fun w => ∑ z, (source P).chance w z *
    (fun o (_ : World Theta) => test o (updateStat P.goal st a o) (if o.1 then 1 else 0)
      (charge P.tariff o) (advance P.tariff i.2 a o).val)
        ((source P).observe w a z) ((source P).next w a z)) = _
  rw [FiniteJointDecisionFilteredModel.primitive_expectation]
  apply Finset.sum_congr rfl
  intro o _
  rw [expect_const, mass_eq P prior st i.1 h.belief a o, h.balance, ← wallet_next]

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentationModel
