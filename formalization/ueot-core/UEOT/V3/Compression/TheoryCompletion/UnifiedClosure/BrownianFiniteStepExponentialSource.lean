import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPastStepExponentialSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianLiteralGridBinding
import Mathlib.Algebra.BigOperators.Fin

/-!
Original commitment: finite allowed action tables need a normalized SAME-table exponential density, not a true-martingale field.
Existing result: actual one-step START conditional normalization and preservation of the entire START law, plus native finite input/output/energy interfaces.
Premise reduced: derive weighted-step L1/conditional identities, actual positive finite prefix density martingale and normalized table measure.
Model/witness: original ElementaryInput T clock/coefficient permissions, sourceLaw/Ft, repeated/empty clocks; no new action, output or bound is chosen.
Consumer: finite-table conditional Gaussian/tail cancellation and eventual original P-KL; arbitrary predictable-control exponential remains separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepExponentialSource
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianContinuousSource BrownianMartingaleSource
open BrownianPastStepExponentialSource BrownianIntegralClosure BrownianPredictableInputs BrownianPredictableDensity
open BrownianSimplePredictableIntegral BrownianIntegralTimeEnergy BrownianLiteralGridBinding
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual weighted one-step L1 identity, derived from the SAME Q's START
law preservation and native withDensity integrability. No bounded prefix or
unproved product-integrability condition is assumed. -/
theorem past_weight_step_condExp (H A : (ℝ≥0 → ℝ) → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hH : StronglyMeasurable[naturalFiltration a] H) (hA : StronglyMeasurable[naturalFiltration a] A)
    (hAi : Integrable A sourceLaw) :
    Integrable (A*stepExponential H a b) sourceLaw ∧
      sourceLaw[A*stepExponential H a b | naturalFiltration a] =ᵐ[sourceLaw] A := by
  have hAg : Measurable A := (hA.mono (naturalFiltration.le a)).measurable
  have hmap : (stepLaw H a b).map A=sourceLaw.map A := by
    ext S hS
    rw [Measure.map_apply hAg hS,Measure.map_apply hAg hS]
    exact stepLaw_agrees_start H a b hab hH _ (hA.measurable hS)
  have hAm : Integrable (id : ℝ → ℝ) (sourceLaw.map A) :=
    (integrable_map_measure (by fun_prop) hAg.aemeasurable).2 hAi
  rw [← hmap] at hAm
  have hAQ : Integrable A (stepLaw H a b) :=
    (integrable_map_measure (by fun_prop) hAg.aemeasurable).1 hAm
  have hD : Measurable (fun ω => ENNReal.ofReal (stepExponential H a b ω)) :=
    ((stepExponential_end_past H a b hab hH).mono (naturalFiltration.le b)).measurable.ennreal_ofReal
  have hDf : ∀ᵐ ω ∂sourceLaw, ENNReal.ofReal (stepExponential H a b ω)<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hn := (integrable_withDensity_iff_integrable_smul' hD hDf).1 hAQ
  have hi : Integrable (A*stepExponential H a b) sourceLaw := by
    apply hn.congr
    exact Eventually.of_forall (fun ω => by
      change (ENNReal.ofReal (stepExponential H a b ω)).toReal*A ω=A ω*stepExponential H a b ω
      rw [ENNReal.toReal_ofReal (stepExponential_pos H a b ω).le]
      ring)
  refine ⟨hi,?_⟩
  apply (condExp_mul_of_stronglyMeasurable_left hA hi (stepExponential_condExp H a b hab hH).1).trans
  filter_upwards [(stepExponential_condExp H a b hab hH).2] with ω hω
  simp only [Pi.mul_apply,hω,mul_one]

def stepFactor {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : (ℝ≥0 → ℝ) → ℝ :=
  stepExponential (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)

/-- Native finite partial product of the actual supplied action rows. -/
def prefixExponential {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) : (ℝ≥0 → ℝ) → ℝ :=
  Fin.partialProd (stepFactor r) k

theorem prefix_zero {T : ℝ≥0} (r : ElementaryInput T) : prefixExponential r 0=1 := Fin.partialProd_zero _

theorem prefix_succ {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    prefixExponential r i.succ=prefixExponential r i.castSucc*stepFactor r i := Fin.partialProd_succ _ i

private theorem cell_mono {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) : r.clock i.castSucc ≤ r.clock i.succ :=
  r.clock_mono (by exact_mod_cast Nat.le_succ (i : ℕ))

theorem prefix_past {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) :
    StronglyMeasurable[naturalFiltration (r.clock k)] (prefixExponential r k) := by
  refine Fin.induction ?_ ?_ k
  · rw [prefix_zero]
    exact stronglyMeasurable_const
  · intro i hi
    rw [prefix_succ]
    exact (hi.mono (naturalFiltration.mono (cell_mono r i))).mul
      (stepExponential_end_past _ _ _ (cell_mono r i) (r.coefficient_past i))

theorem prefix_integrable_mean {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) :
    Integrable (prefixExponential r k) sourceLaw ∧ (∫ ω, prefixExponential r k ω ∂sourceLaw)=1 := by
  refine Fin.induction ?_ ?_ k
  · rw [prefix_zero]
    exact ⟨integrable_const _,by simp⟩
  · intro i hi
    rw [prefix_succ]
    have hw := past_weight_step_condExp (r.coefficient i) (prefixExponential r i.castSucc)
      (r.clock i.castSucc) (r.clock i.succ) (cell_mono r i) (r.coefficient_past i) (prefix_past r i.castSucc) hi.1
    refine ⟨hw.1,?_⟩
    change (∫ ω, (prefixExponential r i.castSucc*stepExponential (r.coefficient i) (r.clock i.castSucc) (r.clock i.succ)) ω ∂sourceLaw)=1
    rw [← integral_condExp (naturalFiltration.le (r.clock i.castSucc)),integral_congr_ae hw.2]
    exact hi.2

theorem prefix_pos {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) (ω : ℝ≥0 → ℝ) :
    0 < prefixExponential r k ω := by
  refine Fin.induction ?_ ?_ k
  · rw [prefix_zero]
    norm_num
  · intro i hi
    rw [prefix_succ]
    exact mul_pos hi (stepExponential_pos _ _ _ ω)

theorem prefix_step_conditional {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    sourceLaw[prefixExponential r i.succ | naturalFiltration (r.clock i.castSucc)] =ᵐ[sourceLaw] prefixExponential r i.castSucc := by
  rw [prefix_succ]
  exact (past_weight_step_condExp (r.coefficient i) (prefixExponential r i.castSucc)
    (r.clock i.castSucc) (r.clock i.succ) (cell_mono r i) (r.coefficient_past i) (prefix_past r i.castSucc)
    (prefix_integrable_mean r i.castSucc).1).2

/-- Arbitrary caller grid prefix consistency under the original past,
proved by the native tower property and actual row conditional identities. -/
theorem prefix_conditional {T : ℝ≥0} (r : ElementaryInput T) (j : Fin (r.n+1)) :
    ∀ i, i ≤ j → sourceLaw[prefixExponential r j | naturalFiltration (r.clock i)] =ᵐ[sourceLaw] prefixExponential r i := by
  refine Fin.induction ?_ ?_ j
  · intro i hi
    have he : i=0 := le_antisymm hi (by exact bot_le)
    subst i
    rw [condExp_of_stronglyMeasurable (naturalFiltration.le _) (prefix_past r _) (prefix_integrable_mean r _).1]
  · intro j hj i hi
    by_cases he : i=j.succ
    · subst i
      rw [condExp_of_stronglyMeasurable (naturalFiltration.le _) (prefix_past r _) (prefix_integrable_mean r _).1]
    · have hlt : i<j.succ := lt_of_le_of_ne hi he
      have hij : i ≤ j.castSucc := by
        change (i : ℕ) ≤ (j : ℕ)
        have hh : (i : ℕ)<(j : ℕ)+1 := hlt
        omega
      have ht := condExp_condExp_of_le (μ := sourceLaw) (f := prefixExponential r j.succ)
        (naturalFiltration.mono (r.clock_mono hij)) (naturalFiltration.le (r.clock j.castSucc))
      exact ht.symm.trans ((condExp_congr_ae (m := naturalFiltration (r.clock i)) (prefix_step_conditional r j)).trans (hj i hij))

def prefixFiltration {T : ℝ≥0} (r : ElementaryInput T) : Filtration (Fin (r.n+1)) (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) where
  seq k := naturalFiltration (r.clock k)
  mono' := fun _ _ h => naturalFiltration.mono (r.clock_mono h)
  le' := fun k => naturalFiltration.le (r.clock k)

theorem prefix_martingale {T : ℝ≥0} (r : ElementaryInput T) :
    Martingale (prefixExponential r) (prefixFiltration r) sourceLaw :=
  ⟨prefix_past r,fun i j hij => prefix_conditional r j i hij⟩

def prefixLaw {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) : Measure (ℝ≥0 → ℝ) :=
  sourceLaw.withDensity (fun ω => ENNReal.ofReal (prefixExponential r k ω))

instance prefixLaw_probability {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) : IsProbabilityMeasure (prefixLaw r k) where
  measure_univ := by
    rw [prefixLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (prefix_integrable_mean r k).1
        (Eventually.of_forall (fun ω => (prefix_pos r k ω).le)),(prefix_integrable_mean r k).2]
    norm_num

/-- Actual finite density changes agree on every actual original prefix
past: this is the future-tail cancellation needed by the next source. -/
theorem prefixLaw_agrees_past {T : ℝ≥0} (r : ElementaryInput T) (i j : Fin (r.n+1)) (hij : i ≤ j)
    (A : Set (ℝ≥0 → ℝ)) (hA : MeasurableSet[naturalFiltration (r.clock i)] A) :
    prefixLaw r j A=prefixLaw r i A := by
  have hg : MeasurableSet A := naturalFiltration.le (r.clock i) A hA
  rw [prefixLaw,prefixLaw,withDensity_apply _ hg,withDensity_apply _ hg,
    ← ofReal_integral_eq_lintegral_ofReal (prefix_integrable_mean r j).1.integrableOn
      (Eventually.of_forall (fun ω => (prefix_pos r j ω).le)),
    ← ofReal_integral_eq_lintegral_ofReal (prefix_integrable_mean r i).1.integrableOn
      (Eventually.of_forall (fun ω => (prefix_pos r i ω).le))]
  exact congrArg ENNReal.ofReal ((prefix_martingale r).setIntegral_eq hij hA).symm

def tableLaw {T : ℝ≥0} (r : ElementaryInput T) : Measure (ℝ≥0 → ℝ) := prefixLaw r (Fin.last r.n)

instance tableLaw_probability {T : ℝ≥0} (r : ElementaryInput T) : IsProbabilityMeasure (tableLaw r) :=
  prefixLaw_probability r (Fin.last r.n)

/-- Every original row contributes its exact original elapsed energy. -/
def tableEnergy {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) : ℝ :=
  ∑ i : Fin r.n, ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*r.coefficient i ω^2

theorem prefix_last {T : ℝ≥0} (r : ElementaryInput T) : prefixExponential r (Fin.last r.n)=∏ i : Fin r.n,stepFactor r i := by
  change ((List.ofFn (stepFactor r)).take r.n).prod=∏ i : Fin r.n,stepFactor r i
  rw [List.take_of_length_le (by simp),List.prod_ofFn]

/-- The computed positive product is the exponential of the SAME literal
integral table and SAME energy table, before any AE representative changes. -/
theorem table_exponential_formula {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    prefixExponential r (Fin.last r.n) ω=Real.exp (simpleIntegral r.clock r.coefficient ω-(1/2 : ℝ)*tableEnergy r ω) := by
  rw [prefix_last]
  simp only [Finset.prod_apply,stepFactor,stepExponential]
  rw [← Real.exp_sum]
  congr 1
  unfold simpleIntegral tableEnergy
  rw [Finset.sum_sub_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [NNReal.coe_sub (cell_mono r i)]
  ring

/-- Exact binding to the original full-predictable integral's actual
returned value and the original SAME-input timeEnergy. No new policy or
abstract exponential-integral certificate is selected. -/
theorem table_exponential_actual_integral {T : ℝ≥0} (r : ElementaryInput T) :
    prefixExponential r (Fin.last r.n) =ᵐ[sourceLaw] fun ω =>
      Real.exp ((predictableIntegral T (literalPredictableInput r) : (ℝ≥0 → ℝ) → ℝ) ω-
        (1/2 : ℝ)*timeEnergy T (literalPredictableInput r) T ω) := by
  have hi : (predictableIntegral T (literalPredictableInput r) : (ℝ≥0 → ℝ) → ℝ) =ᵐ[sourceLaw]
      simpleIntegral r.clock r.coefficient := by
    rw [predictableIntegral_returns_literal]
    exact (simpleIntegral_memLp_two r.clock r.coefficient r.coefficient_bounded).coeFn_toLp
  filter_upwards [hi,timeEnergy_literal_horizon r] with ω hi he
  change timeEnergy T (literalPredictableInput r) T ω=tableEnergy r ω at he
  rw [table_exponential_formula,hi,he]

theorem prefixLaw_zero {T : ℝ≥0} (r : ElementaryInput T) : prefixLaw r 0=sourceLaw := by
  simp [prefixLaw,prefix_zero]

theorem prefixLaw_absolutelyContinuous {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) : prefixLaw r k ≪ sourceLaw :=
  withDensity_absolutelyContinuous sourceLaw _

/-- RN derivative is the SAME actual computed prefix product, whose
normalization and original source/input binding have just been proved. -/
theorem prefixLaw_rnDeriv {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1)) :
    (prefixLaw r k).rnDeriv sourceLaw =ᵐ[sourceLaw] fun ω => ENNReal.ofReal (prefixExponential r k ω) :=
  Measure.rnDeriv_withDensity sourceLaw ((prefix_past r k).mono (naturalFiltration.le (r.clock k))).measurable.ennreal_ofReal

/-- Actual next-prefix measure is the actual prior-prefix measure tilted
by the SAME next action row; no alternative normalization or law is chosen. -/
theorem prefixLaw_step_composition {T : ℝ≥0} (r : ElementaryInput T) (i : Fin r.n) :
    prefixLaw r i.succ=(prefixLaw r i.castSucc).withDensity (fun ω => ENNReal.ofReal (stepFactor r i ω)) := by
  have he : (fun ω => ENNReal.ofReal (prefixExponential r i.succ ω))=
      (fun ω => ENNReal.ofReal (prefixExponential r i.castSucc ω))*(fun ω => ENNReal.ofReal (stepFactor r i ω)) := by
    funext ω
    rw [prefix_succ]
    exact ENNReal.ofReal_mul (prefix_pos r i.castSucc ω).le
  rw [prefixLaw,prefixLaw,he]
  exact withDensity_mul sourceLaw
    ((prefix_past r i.castSucc).mono (naturalFiltration.le (r.clock i.castSucc))).measurable.ennreal_ofReal
    ((stepExponential_end_past _ _ _ (cell_mono r i) (r.coefficient_past i)).mono
      (naturalFiltration.le (r.clock i.succ))).measurable.ennreal_ofReal

/-- Future-tail cancellation for every genuinely original prefix-measurable
readout, including the joint state/coefficient/noise consumers to follow. -/
theorem tableLaw_map_prefix_readout {T : ℝ≥0} (r : ElementaryInput T) (k : Fin (r.n+1))
    {E : Type*} [MeasurableSpace E] (Y : (ℝ≥0 → ℝ) → E)
    (hY : @Measurable (ℝ≥0 → ℝ) E (naturalFiltration (r.clock k)) inferInstance Y) :
    (tableLaw r).map Y=(prefixLaw r k).map Y := by
  have hg : Measurable Y := hY.mono (naturalFiltration.le (r.clock k)) le_rfl
  ext S hS
  rw [Measure.map_apply hg hS,Measure.map_apply hg hS]
  exact prefixLaw_agrees_past r k (Fin.last r.n) (Fin.le_last _) _ (hY hS)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepExponentialSource
