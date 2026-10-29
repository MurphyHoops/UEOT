import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismPurpose

/-! The already interpreted repair program, not a replacement greedy selector,
optimizes the registered source payoff when priced writes cost at most one
living birth. This is a sufficient evaluation regime, not a universal purpose. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterProgramOptimality
open UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterMechanismPurpose
noncomputable section

def value {n : ℕ} (i : Fin n) (m : Mechanism) (price : NNReal) (d : ℝ) (x : State n) : ℝ :=
  if x i = m.goal then 1 / (1-d) else 1 / (1-d) - (price : ℝ) * m.writeCost

theorem qValue_source {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (v : State n → ℝ)
    (x : State n) (a : Action) :
    (model i noise price d hd m).qValue v x a =
      (if update i x a i = m.goal then 1 else 0) - (price : ℝ) * cost m a +
        d * v (update i x a) := by
  rw [Model.qValue, model_expect_eq_update]
  change stage i noise price m x a + d * v (update i x a) = _
  rw [stage, expectedChildren_eq]

theorem value_action_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (hc : (price : ℝ) * m.writeCost ≤ 1) (x : State n) (a : Action) :
    (model i noise price d hd m).qValue (value i m price d) x a ≤ value i m price d x := by
  have hz : 0 < 1-d := sub_pos.mpr hd.2
  have hv : (1-d) * (1/(1-d)) = 1 := by field_simp
  have hp : 0 ≤ (price : ℝ) * m.writeCost := mul_nonneg price.coe_nonneg m.writeCost.coe_nonneg
  have hv1 : 1 ≤ 1/(1-d) := (le_div_iff₀ hz).mpr (by linarith [hd.1])
  have hnet : 0 ≤ (1-d) * (1/(1-d) - (price : ℝ) * m.writeCost) :=
    mul_nonneg hz.le (by linarith)
  simp only [one_div] at hv hv1 hnet
  rw [qValue_source]
  cases a with
  | none =>
      by_cases hx : x i = m.goal <;> simp [value, update, cost, hx] <;> nlinarith
  | some b =>
      by_cases hb : b = m.goal <;> by_cases hx : x i = m.goal <;>
        simp [value, update, cost, hb, hx] <;> nlinarith

/-- The SAME compiled instruction program attains the source Bellman bound. -/
theorem compiled_attains_value {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (x : State n) :
    (model i noise price d hd m).qValue (value i m price d) x
      ((substrate i).execute m.goal x) = value i m price d x := by
  have hz : 0 < 1-d := sub_pos.mpr hd.2
  have hv : (1-d) * (1/(1-d)) = 1 := by field_simp
  simp only [one_div] at hv
  rw [qValue_source, execute_compiled]
  by_cases hx : x i = m.goal <;> simp [value, update, cost, hx] <;> nlinarith

theorem value_eq_optimal {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (hc : (price : ℝ) * m.writeCost ≤ 1) :
    value i m price d = (model i noise price d hd m).optimalValue := by
  apply Model.fixedPoint_unique
  funext x
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    exact value_action_bound i noise m price d hd hc x a
  · rw [← compiled_attains_value i noise m price d hd x]
    exact Finset.le_sup' (fun a => (model i noise price d hd m).qValue
      (value i m price d) x a) (Finset.mem_univ _)

/-- Original causal-control consumer instantiated by the concrete executable
program. No choice-based replacement policy is returned. -/
theorem compiled_optimal_against_all_causal {n : ℕ} (i : Fin n) (noise : PMF Bool)
    (m : Mechanism) (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (hc : (price : ℝ) * m.writeCost ≤ 1) :
    let M := model i noise price d hd m
    (∀ {t : ℕ} (x : State n),
      (selectorPolicy ((substrate i).execute m.goal)).infiniteValue M (t := t) x = M.optimalValue x) ∧
    (∀ (pi : CausalPolicy (State n) (fun _ => Action)) {t : ℕ} (h : pi.Memory t),
      pi.infiniteValue M h ≤ M.optimalValue (pi.current h)) := by
  apply selector_optimal_against_all_causal
  intro x
  rw [← value_eq_optimal i noise m price d hd hc]
  exact compiled_attains_value i noise m price d hd x

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterProgramOptimality
