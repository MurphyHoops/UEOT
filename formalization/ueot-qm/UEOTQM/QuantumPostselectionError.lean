import UEOTQM.QuantumTraceDistance

/-!
# Sharp finite postselection stability from actual quantum effects

Two complementary effects INSIDE the accepted branch give the sharp factor
1 / max(p,q).  This proof uses the existing Kraus effect pullback, positivity,
and normalized Born probabilities.  It assumes no Schatten norm triangle axiom
and no conclusion-shaped accepted-state error field.
-/

namespace UEOTQM.QuantumPostselectionError

noncomputable section

/-- If p is the larger accepted mass, testing the accepted effect and its
accepted complement bounds the posterior gap with denominator p. -/
theorem binary_gap_le_div_of_le (a b p q delta : ℝ)
    (hp : 0 < p) (hqp : q ≤ p) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hE : |p * a - q * b| ≤ delta)
    (hEc : |p * (1 - a) - q * (1 - b)| ≤ delta) :
    |a - b| ≤ delta / p := by
  have hup : p * (a - b) ≤ delta := by
    have hpos := mul_nonneg (sub_nonneg.mpr hqp) hb0
    have h := (abs_le.mp hE).2
    nlinarith
  have hlo : -delta ≤ p * (a - b) := by
    have hpos := mul_nonneg (sub_nonneg.mpr hqp) (sub_nonneg.mpr hb1)
    have h := (abs_le.mp hEc).2
    nlinarith
  apply (le_div_iff₀ hp).mpr
  calc
    |a - b| * p = |p * (a - b)| := by rw [abs_mul, abs_of_pos hp]; ring
    _ ≤ delta := abs_le.mpr ⟨hlo, hup⟩

theorem binary_gap_le_div_max (a b p q delta : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hE : |p * a - q * b| ≤ delta)
    (hEc : |p * (1 - a) - q * (1 - b)| ≤ delta) :
    |a - b| ≤ delta / max p q := by
  rcases le_total q p with hqp | hpq
  · rw [max_eq_left hqp]
    exact binary_gap_le_div_of_le a b p q delta hp hqp hb0 hb1 hE hEc
  · rw [max_eq_right hpq]
    have hE' : |q * b - p * a| ≤ delta := by
      simpa only [abs_sub_comm] using hE
    have hEc' : |q * (1 - b) - p * (1 - a)| ≤ delta := by
      simpa only [abs_sub_comm] using hEc
    have h := binary_gap_le_div_of_le b a q p delta hq hpq ha0 ha1 hE' hEc'
    simpa only [abs_sub_comm] using h

variable {ι O κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ]

theorem probability_mul_posterior (I : Instrument ι O κ) (o : O)
    (E : Effect ι) (ρ : Density ι) (hp : 0 < I.probability ρ o) :
    I.probability ρ o * E.probability (I.posterior ρ o hp) =
      (I.branchEffect o E).probability ρ := by
  rw [I.probability_posterior o E ρ hp]
  field_simp [hp.ne']

/-- Sharp posterior bound for one actual branch of one complete instrument.
To compare two different source processes, use their full CQ outputs as the
two inputs and the SAME acceptance extraction instrument as I. -/
theorem posterior_effectDistance_le_div_max
    (I : Instrument ι O κ) (o : O) (ρ σ : Density ι)
    (hp : 0 < I.probability ρ o) (hq : 0 < I.probability σ o) :
    effectDistance (I.posterior ρ o hp) (I.posterior σ o hq) ≤
      effectDistance ρ σ / max (I.probability ρ o) (I.probability σ o) := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  have hE := (I.branchEffect o E).probability_sub_le_effectDistance ρ σ
  rw [← probability_mul_posterior I o E ρ hp,
    ← probability_mul_posterior I o E σ hq] at hE
  have hEc := (I.branchEffect o E.complement).probability_sub_le_effectDistance ρ σ
  rw [← probability_mul_posterior I o E.complement ρ hp,
    ← probability_mul_posterior I o E.complement σ hq] at hEc
  simp only [Effect.probability_complement] at hEc
  exact binary_gap_le_div_max _ _ _ _ _ hp hq
    (E.probability_nonneg _) (E.probability_le_one _)
    (E.probability_nonneg _) (E.probability_le_one _) hE hEc

theorem posterior_effectDistance_le_min
    (I : Instrument ι O κ) (o : O) (ρ σ : Density ι)
    (hp : 0 < I.probability ρ o) (hq : 0 < I.probability σ o)
    {epsilon : ℝ} (herror : effectDistance ρ σ ≤ epsilon) :
    effectDistance (I.posterior ρ o hp) (I.posterior σ o hq) ≤
      min 1 (epsilon / max (I.probability ρ o) (I.probability σ o)) := by
  apply le_min (effectDistance_le_one _ _)
  apply (posterior_effectDistance_le_div_max I o ρ σ hp hq).trans
  exact div_le_div_of_nonneg_right herror (hp.le.trans (le_max_left _ _))

/-- Existing trace-distance identification transfers the proved operational
bound to the actual matrix absolute value; it is not a definition by fiat. -/
theorem posterior_half_traceAbsolute_le_min
    (I : Instrument ι O κ) (o : O) (ρ σ : Density ι)
    (hp : 0 < I.probability ρ o) (hq : 0 < I.probability σ o)
    {epsilon : ℝ} (herror : effectDistance ρ σ ≤ epsilon) :
    QuantumTraceDistance.traceAbsolute
      ((I.posterior ρ o hp).matrix - (I.posterior σ o hq).matrix) / 2 ≤
      min 1 (epsilon / max (I.probability ρ o) (I.probability σ o)) := by
  rw [← QuantumTraceDistance.effectDistance_eq_half_traceAbsolute]
  exact posterior_effectDistance_le_min I o ρ σ hp hq herror

end

end UEOTQM.QuantumPostselectionError
