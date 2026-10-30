import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStepExponentialSource
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
Original commitment: a bounded-predictable limit must not assume normalization or uniform integrability of its actual densities.
Existing result: each supplied finite table computes an exactly normalized actual exponential density.
Premise reduced: derive actual squared-density bounds and native uniform integrability under one uniform SOURCE-AE coefficient bound.
Model/witness: SAME original tables/input/integral/source; the doubled table is only an auxiliary normalization proof, never a replacement selected policy.
Consumer: native Vitali passage to the same bounded full-predictable terminal exponential; actual bounded table approximation and full limit-Q path remain separate.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteDensityL2Source
open MeasureTheory ProbabilityTheory Set Filter
open BrownianProjectiveSource BrownianIntegralClosure BrownianFiniteStepExponentialSource
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Auxiliary scaled table, retaining all original clocks and START permissions. -/
def scaleTable {T : ℝ≥0} (r : ElementaryInput T) (c : ℝ) : ElementaryInput T where
  n := r.n
  clock := r.clock
  coefficient i ω := c*r.coefficient i ω
  clock_mono := r.clock_mono
  clock_zero := r.clock_zero
  clock_end := r.clock_end
  coefficient_past i := stronglyMeasurable_const.mul (r.coefficient_past i)
  coefficient_bounded i := (r.coefficient_bounded i).const_mul c

def terminalDensity {T : ℝ≥0} (r : ElementaryInput T) : (ℝ≥0 → ℝ) → ℝ :=
  prefixExponential r (Fin.last r.n)

private theorem scale_integral {T : ℝ≥0} (r : ElementaryInput T) (c : ℝ) (ω : ℝ≥0 → ℝ) :
    BrownianSimplePredictableIntegral.simpleIntegral (scaleTable r c).clock (scaleTable r c).coefficient ω=
      c*BrownianSimplePredictableIntegral.simpleIntegral r.clock r.coefficient ω := by
  unfold BrownianSimplePredictableIntegral.simpleIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (c*r.coefficient i ω)*BrownianMartingaleSource.increment (r.clock i.castSucc) (r.clock i.succ) ω=
    c*(r.coefficient i ω*BrownianMartingaleSource.increment (r.clock i.castSucc) (r.clock i.succ) ω)
  ring
private theorem scale_energy {T : ℝ≥0} (r : ElementaryInput T) (c : ℝ) (ω : ℝ≥0 → ℝ) :
    tableEnergy (scaleTable r c) ω=c^2*tableEnergy r ω := by
  unfold tableEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*(c*r.coefficient i ω)^2=
    c^2*(((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*r.coefficient i ω^2)
  ring

/-- Exact identity for the actual original density. The auxiliary table is
used solely on the right to invoke its already proved normalization. -/
theorem density_square_factor {T : ℝ≥0} (r : ElementaryInput T) (ω : ℝ≥0 → ℝ) :
    terminalDensity r ω^2=terminalDensity (scaleTable r 2) ω*Real.exp (tableEnergy r ω) := by
  unfold terminalDensity
  rw [table_exponential_formula,table_exponential_formula,scale_integral,scale_energy,
    ← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

/-- An actual upper energy bound gives an actual L2 density bound; neither
L2 nor normalization is supplied as a certificate field. -/
theorem density_square_integrable_bound {T : ℝ≥0} (r : ElementaryInput T) (C : ℝ)
    (hE : ∀ᵐ ω ∂sourceLaw, tableEnergy r ω≤C) :
    Integrable (fun ω => terminalDensity r ω^2) sourceLaw ∧
      (∫ ω, terminalDensity r ω^2 ∂sourceLaw)≤Real.exp C := by
  have hD : Integrable (terminalDensity (scaleTable r 2)) sourceLaw :=
    (prefix_integrable_mean (scaleTable r 2) (Fin.last r.n)).1
  have hdom : ∀ᵐ ω ∂sourceLaw, ‖terminalDensity r ω^2‖≤Real.exp C*terminalDensity (scaleTable r 2) ω := by
    filter_upwards [hE] with ω hω
    rw [Real.norm_eq_abs,abs_sq,density_square_factor,mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hω) (prefix_pos (scaleTable r 2) _ ω).le
  have hi : Integrable (fun ω => terminalDensity r ω^2) sourceLaw :=
    (hD.const_mul (Real.exp C)).mono'
      (((prefix_past r (Fin.last r.n)).mono (BrownianMartingaleSource.naturalFiltration.le _)).pow 2).aestronglyMeasurable hdom
  refine ⟨hi,?_⟩
  have h := integral_mono_ae hi (hD.const_mul (Real.exp C)) (hdom.mono (fun ω hω => by
    simpa only [Real.norm_eq_abs,abs_sq] using hω))
  have hmean : (∫ ω, terminalDensity (scaleTable r 2) ω ∂sourceLaw)=1 :=
    (prefix_integrable_mean (scaleTable r 2) (Fin.last r.n)).2
  rw [integral_const_mul,hmean,mul_one] at h
  exact h

private theorem clock_telescope {T : ℝ≥0} (r : ElementaryInput T) :
    (∑ i : Fin r.n, ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ)))=(T : ℝ) := by
  have h := (Fin.sum_univ_succ (fun k : Fin (r.n+1) => (r.clock k : ℝ))).symm.trans
    (Fin.sum_univ_castSucc (fun k : Fin (r.n+1) => (r.clock k : ℝ)))
  rw [r.clock_zero,r.clock_end] at h
  simp only [NNReal.coe_zero,zero_add] at h
  rw [Finset.sum_sub_distrib]
  linarith

/-- A true SOURCE-AE coefficient bound yields the SAME actual time-energy
bound, including T=0. No raw global bound or modified input is inferred. -/
theorem tableEnergy_le_of_coefficients {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) :
    ∀ᵐ ω ∂sourceLaw, tableEnergy r ω≤K^2*(T : ℝ) := by
  filter_upwards [ae_all_iff.mpr hH] with ω hω
  calc
    tableEnergy r ω ≤ ∑ i : Fin r.n, ((r.clock i.succ : ℝ)-(r.clock i.castSucc : ℝ))*K^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left
      · simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hω i)
      · exact sub_nonneg.mpr (by exact_mod_cast r.clock_mono (show i.castSucc ≤ i.succ by exact_mod_cast Nat.le_succ (i : ℕ)))
    _ = K^2*(T : ℝ) := by rw [← Finset.sum_mul,clock_telescope,mul_comm]

theorem bounded_density_square {T : ℝ≥0} (r : ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ i, ∀ᵐ ω ∂sourceLaw, |r.coefficient i ω|≤K) :
    Integrable (fun ω => terminalDensity r ω^2) sourceLaw ∧
      (∫ ω, terminalDensity r ω^2 ∂sourceLaw)≤Real.exp (K^2*(T : ℝ)) :=
  density_square_integrable_bound r _ (tableEnergy_le_of_coefficients r K hK hH)

/-- Explicit L1 tail estimate for the SAME density, derived from its actual
squared moment, sufficient for native uniform integrability. -/
theorem density_tail_bound {T : ℝ≥0} (r : ElementaryInput T) (C : ℝ)
    (hE : ∀ᵐ ω ∂sourceLaw, tableEnergy r ω≤C) (R : ℝ≥0) (hR : 0<R) :
    eLpNorm ({ω | R≤‖terminalDensity r ω‖₊}.indicator (terminalDensity r)) 1 sourceLaw≤
      ENNReal.ofReal (Real.exp C/(R : ℝ)) := by
  let S := {ω | R≤‖terminalDensity r ω‖₊}
  have hD : Integrable (terminalDensity r) sourceLaw := (prefix_integrable_mean r _).1
  have hS : MeasurableSet S := measurableSet_le measurable_const
    (((prefix_past r (Fin.last r.n)).mono (BrownianMartingaleSource.naturalFiltration.le _)).nnnorm.measurable)
  have ht : Integrable (S.indicator (terminalDensity r)) sourceLaw := hD.indicator hS
  have hd := density_square_integrable_bound r C hE
  rw [eLpNorm_one_eq_lintegral_enorm,← ofReal_integral_norm_eq_lintegral_enorm ht]
  apply ENNReal.ofReal_le_ofReal
  have hdom : ∀ ω, ‖S.indicator (terminalDensity r) ω‖≤terminalDensity r ω^2/(R : ℝ) := by
    intro ω
    by_cases hs : ω∈S
    · rw [Set.indicator_of_mem hs,Real.norm_eq_abs,abs_of_pos (show 0<terminalDensity r ω from prefix_pos r _ ω)]
      have hr : (R : ℝ)≤terminalDensity r ω := by
        have hh : (R : ℝ)≤‖terminalDensity r ω‖ := by exact_mod_cast hs
        simpa only [Real.norm_eq_abs,abs_of_pos (show 0<terminalDensity r ω from prefix_pos r _ ω)] using hh
      apply (le_div_iff₀ (show (0 : ℝ)<R from hR)).mpr
      nlinarith [prefix_pos r (Fin.last r.n) ω]
    · rw [Set.indicator_of_notMem hs,norm_zero]
      positivity
  have hi := integral_mono ht.norm (hd.1.div_const (R : ℝ)) hdom
  rw [integral_div] at hi
  exact hi.trans (div_le_div_of_nonneg_right hd.2 R.coe_nonneg)

/-- Native uniform integrability of the computed densities of ANY family
of actual tables sharing one declared SOURCE-AE K bound. -/
theorem densities_uniformIntegrable {ι : Type*} {T : ℝ≥0} (r : ι → ElementaryInput T) (K : ℝ) (hK : 0≤K)
    (hH : ∀ j i, ∀ᵐ ω ∂sourceLaw, |(r j).coefficient i ω|≤K) :
    UniformIntegrable (fun j => terminalDensity (r j)) 1 sourceLaw := by
  apply uniformIntegrable_of (by norm_num) (by norm_num)
    (fun j => ((prefix_past (r j) _).mono (BrownianMartingaleSource.naturalFiltration.le _)).aestronglyMeasurable)
  intro ε hε
  let C := Real.exp (K^2*(T : ℝ))
  let R : ℝ≥0 := ⟨C/ε,le_of_lt (div_pos (Real.exp_pos _) hε)⟩
  refine ⟨R,fun j => ?_⟩
  have h := density_tail_bound (r j) _ (tableEnergy_le_of_coefficients (r j) K hK (hH j)) R
    (show 0<R from div_pos (Real.exp_pos _) hε)
  have he : Real.exp (K^2*(T : ℝ))/(R : ℝ)=ε := by
    change C/(C/ε)=ε
    have hC : C ≠ 0 := ne_of_gt (Real.exp_pos _)
    field_simp [hC,ne_of_gt hε]
  rwa [he] at h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteDensityL2Source
