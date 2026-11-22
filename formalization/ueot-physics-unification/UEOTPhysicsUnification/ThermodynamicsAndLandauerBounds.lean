import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Quantum Thermodynamics, Persistent-Bath Backflow & Omega-Loop No-Go (`P-THERMO-01`, `P-OMEGA-02`)

Formalizes the universal algebraic laws underlying `physics/qm/correlated_bath/sectors/heat.py`
and closes Row 7 of `PREMISES_AND_RESPONSIBILITIES.md` §5:

1. **Energy-Conserving Partial Swap & Fresh-Bath Geometric Contraction (`fresh_bath_iterated_contraction`)**:
   For resonant energy-preserving swap probability `s = sin^2 θ ∈ [0, 1]` between a probe of excitation
   `p` and a Gibbs bath qubit of excitation `q`, total excitation `p' + q' = p + q` is conserved and
   `n` fresh-bath collisions contract initial bias geometrically as `(1 - s)^n (p - q)`.

2. **Persistent-Bath Non-Markovian Memory Excess (`persistent_vs_fresh_second_cycle_excess`)**:
   Retaining the bath state across cycles while re-preparing the probe yields an exact rational/trigonometric
   second-cycle excess `s^2 (p - q)` over a fresh Gibbs bath, specializing at `(s = 1/4, p = 4/5, q = 1/5)`
   to the exact Chapter 71 value `3 / 80 = 0.0375`.

3. **Omega-Loop Self-Sustaining No-Go Without External Reset Work (`bistochastic_purity_strict_decrease`)**:
   Under any nontrivial doubly-stochastic thermal mixing `0 < s < 1` with `p ≠ q`, joint 2-purity strictly
   decreases by `4 s (1 - s) (p - q)^2 > 0`, ruling out autonomous purity regeneration without external
   re-preparation work.

4. **Cauchy-Schwarz Participation Lower Bound for Non-Commuting Limit Exchange (`participation_return_lower_bound`)**:
   For any normalized spectral weight distribution `∑_{i : Fin d} w_i = 1` (`d ≥ 1`), the infinite-time
   Cesaro return probability `∑ w_i^2` is bounded below by `1 / d > 0`, establishing a strict gap against
   continuum decay limits (`lim_{t→∞} lim_{d→∞} = 0 ≠ lim_{T→∞} p_avg(d) ≥ 1/d`).
-/

namespace UEOTPhysicsUnification.ThermodynamicsAndLandauerBounds

open scoped BigOperators

/-! ## 1. Resonant Partial-Swap Conservation & Fresh-Bath Contraction -/

/-- Post-collision probe excitation probability under resonant swap weight `s ∈ [0, 1]`. -/
def swapProbe (s p q : ℝ) : ℝ := (1 - s) * p + s * q

/-- Post-collision bath excitation probability under resonant swap weight `s ∈ [0, 1]`. -/
def swapBath (s p q : ℝ) : ℝ := (1 - s) * q + s * p

/-- Exact resonant energy conservation `p' + q' = p + q` and heat balance `ΔE_bath = -(ΔE_probe) = s(p - q)`. -/
theorem swap_energy_conservation (s p q : ℝ) :
    swapProbe s p q + swapBath s p q = p + q ∧
      swapBath s p q - q = s * (p - q) ∧
      swapProbe s p q - p = -s * (p - q) := by
  unfold swapProbe swapBath
  refine ⟨by ring, by ring, by ring⟩

/-- Iterated fresh-bath collision operator refreshing `q` at every cycle. -/
def freshBathIter (s q : ℝ) : ℕ → ℝ → ℝ
  | 0, p => p
  | n + 1, p => swapProbe s (freshBathIter s q n p) q

/-- Exact geometric contraction `(1 - s)^n (p - q)` under repeated fresh Gibbs collisions. -/
theorem fresh_bath_iterated_contraction (s q p : ℝ) (n : ℕ) :
    freshBathIter s q n p - q = (1 - s) ^ n * (p - q) := by
  induction n with
  | zero =>
    simp [freshBathIter]
  | succ k ih =>
    simp only [freshBathIter, swapProbe]
    calc
      (1 - s) * freshBathIter s q k p + s * q - q
          = (1 - s) * (freshBathIter s q k p - q) := by ring
      _ = (1 - s) * ((1 - s) ^ k * (p - q)) := by rw [ih]
      _ = (1 - s) ^ (k + 1) * (p - q) := by ring

/-! ## 2. Persistent-Bath Non-Markovian Memory Return -/

/-- Exact universal formula for second-cycle persistent-bath vs fresh-bath probe excitation excess:
retaining `q' = swapBath s p q` while re-preparing `S` at `p` shifts the output by `s^2 (p - q)`. -/
theorem persistent_vs_fresh_second_cycle_excess (s p q : ℝ) :
    swapProbe s p (swapBath s p q) - swapProbe s p q = s ^ 2 * (p - q) := by
  unfold swapProbe swapBath
  ring

/-- Exact specialization recovering the Chapter 71 (`sectors/heat.py`) rational benchmark `3 / 80 = 0.0375`
at swap area `π/6` (`s = sin^2(π/6) = 1/4`), `p = 4/5`, `q = 1/5`, together with `p' = 13/20, q' = 7/20`. -/
theorem persistent_excess_ch71_benchmark :
    swapProbe (1 / 4 : ℚ) (4 / 5) (1 / 5) = 13 / 20 ∧
      swapBath (1 / 4 : ℚ) (4 / 5) (1 / 5) = 7 / 20 ∧
      swapProbe (1 / 4 : ℚ) (4 / 5) (swapBath (1 / 4) (4 / 5) (1 / 5)) -
        swapProbe (1 / 4 : ℚ) (4 / 5) (1 / 5) = 3 / 80 := by
  unfold swapProbe swapBath
  norm_num

/-! ## 3. Omega-Loop No-Go Without External Work & Finite-Bath Excess -/

/-- Binary Rényi-2 purity `x^2 + (1 - x)^2` of a two-level diagonal state. -/
def binaryPurity (x : ℝ) : ℝ := x ^ 2 + (1 - x) ^ 2

/-- Exact doubly-stochastic purity dissipation identity:
`(P(p') + P(q')) - (P(p) + P(q)) = -4 s (1 - s) (p - q)^2`. -/
theorem bistochastic_purity_drop_identity (s p q : ℝ) :
    (binaryPurity (swapProbe s p q) + binaryPurity (swapBath s p q)) -
      (binaryPurity p + binaryPurity q) = -4 * s * (1 - s) * (p - q) ^ 2 := by
  unfold binaryPurity swapProbe swapBath
  ring

/-- Strict purity decrease (`Omega-loop no-go`): for `0 < s < 1` and `p ≠ q`, isolated doubly-stochastic
exchange strictly reduces total 2-purity without external reset work. -/
theorem bistochastic_purity_strict_decrease
    {s p q : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hpq : p ≠ q) :
    binaryPurity (swapProbe s p q) + binaryPurity (swapBath s p q) <
      binaryPurity p + binaryPurity q := by
  have h1s : 0 < 1 - s := by linarith
  have hpq_ne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hpq_sq : 0 < (p - q) ^ 2 := sq_pos_of_ne_zero hpq_ne
  have hprod : 0 < 4 * s * (1 - s) * (p - q) ^ 2 := by positivity
  have hid := bistochastic_purity_drop_identity s p q
  linarith

/-- Elementary finite-bath quadratic Pinsker/variance excess: shifting bath excitation from `q` to `q'`
produces a strictly positive squared population displacement `(q' - q)^2 = s^2 (p - q)^2 > 0`. -/
theorem finite_bath_displacement_pos
    {s p q : ℝ} (hs : s ≠ 0) (hpq : p ≠ q) :
    0 < (swapBath s p q - q) ^ 2 := by
  have hdiff : swapBath s p q - q = s * (p - q) := (swap_energy_conservation s p q).2.1
  rw [hdiff]
  have hne : s * (p - q) ≠ 0 := mul_ne_zero hs (sub_ne_zero.mpr hpq)
  exact sq_pos_of_ne_zero hne

/-! ## 4. Non-Commuting Limit-Exchange Participation Bound -/

/-- Exact variance decomposition over `Fin d`:
`∑_i (w_i - 1/d)^2 = ∑_i w_i^2 - 1/d` whenever `∑_i w_i = 1`. -/
theorem participation_variance_identity
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (hsum : ∑ i : Fin d, w i = 1) :
    ∑ i : Fin d, (w i - 1 / (d : ℝ)) ^ 2 = (∑ i : Fin d, (w i) ^ 2) - 1 / (d : ℝ) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have hlin : ∑ i : Fin d, ((w i) ^ 2 - 2 * (1 / (d : ℝ)) * w i + (1 / (d : ℝ)) ^ 2) =
      (∑ i : Fin d, (w i) ^ 2) - 2 * (1 / (d : ℝ)) * (∑ i : Fin d, w i) +
        (d : ℝ) * (1 / (d : ℝ)) ^ 2 := by
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    ∑ i : Fin d, (w i - 1 / (d : ℝ)) ^ 2
        = ∑ i : Fin d, ((w i) ^ 2 - 2 * (1 / (d : ℝ)) * w i + (1 / (d : ℝ)) ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = (∑ i : Fin d, (w i) ^ 2) - 2 * (1 / (d : ℝ)) * (∑ i : Fin d, w i) +
          (d : ℝ) * (1 / (d : ℝ)) ^ 2 := hlin
    _ = (∑ i : Fin d, (w i) ^ 2) - 1 / (d : ℝ) := by
          rw [hsum]
          field_simp [hdR]
          ring

/-- Universal finite-bath Cesaro return lower bound: for any `d > 0` and normalized spectral weights
`∑_{i : Fin d} w_i = 1`, the long-time diagonal return probability satisfies `1 / d ≤ ∑_i w_i^2`,
which is strictly above `0` (the irreversible continuum decay value). -/
theorem participation_return_lower_bound
    {d : ℕ} (hd : 0 < d) (w : Fin d → ℝ) (hsum : ∑ i : Fin d, w i = 1) :
    1 / (d : ℝ) ≤ ∑ i : Fin d, (w i) ^ 2 ∧ 0 < 1 / (d : ℝ) := by
  have hid := participation_variance_identity hd w hsum
  have hsq : 0 ≤ ∑ i : Fin d, (w i - 1 / (d : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  exact ⟨by linarith, by positivity⟩

end UEOTPhysicsUnification.ThermodynamicsAndLandauerBounds
