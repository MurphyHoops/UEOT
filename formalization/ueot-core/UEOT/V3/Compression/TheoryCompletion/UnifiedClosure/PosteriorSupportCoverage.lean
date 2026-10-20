import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FinitePMFProjection
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DeploymentCoverage

/-!
# Actual posterior support and deployment coverage

A fixed policy is certified on its own actual positive coarse histories.
The terminal posterior is defined on positive fibers of the existing law;
null histories require no posterior value or certification premise.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
namespace PosteriorSupportCoverageCheck

open MeasureTheory UEOT.V3.PathError
open scoped BigOperators Classical

noncomputable section

universe u

/-- Push the existing positive-fiber posterior through the terminal-state map.
There is intentionally no posterior value at a null coarse history. -/
def fiberTerminalPosterior
    {H G X : Type u} (p : PMF H) (f : H → G) (last : H → X)
    (g : G) (hg : g ∈ (p.map f).support) : PMF X :=
  (riskFiberPosterior p f g hg).map last

/-- Conditional support is the image of actual supported histories in this
complete coarse-history fiber, not the image of arbitrary representatives. -/
theorem mem_fiberTerminalPosterior_support_iff
    {H G X : Type u} (p : PMF H) (f : H → G) (last : H → X)
    (g : G) (hg : g ∈ (p.map f).support) (x : X) :
    x ∈ (fiberTerminalPosterior p f last g hg).support ↔
      ∃ h ∈ p.support, f h = g ∧ last h = x := by
  constructor
  · intro hx
    obtain ⟨h, hh, hlast⟩ :=
      (PMF.mem_support_map_iff last (riskFiberPosterior p f g hg) x).mp hx
    rw [riskFiberPosterior_support] at hh
    exact ⟨h, hh.2, hh.1, hlast⟩
  · rintro ⟨h, hh, hf, hlast⟩
    apply (PMF.mem_support_map_iff last (riskFiberPosterior p f g hg) x).mpr
    refine ⟨h, ?_, hlast⟩
    rw [riskFiberPosterior_support]
    exact ⟨hf, hh⟩

/-- The same actual deployment occupancy is bounded by the policy leakage
cap. Certification is needed only at positively weighted microscopic
histories and actions; the policy bound is needed only at supported coarse
histories. The two zero-mass branches are explicitly discarded below. -/
theorem supported_history_actions_bound_actual_coverage
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (n : ℕ)
    (allowed : CausalHistory Y (A × Y) n → A → Prop) (κ : ℝ)
    (hcert :
      ∀ h ∈ (causalLaw p₀ (riskMicroControlKernel q P π) n).support,
        ∀ a ∈ (π n
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h)).support,
          allowed (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a →
            certified n (riskLastState n h) a)
    (hpolicy :
      ∀ hc ∈ ((causalLaw p₀ (riskMicroControlKernel q P π) n).map
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)).support,
        (π n hc).toMeasure.real {a | ¬ allowed hc a} ≤ κ) :
    (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} ≤ κ := by
  rw [← coverage_uncovered_indicator_expectation, coverage_rowLaw_expectation]
  calc
    _ ≤ ∑ h, (causalLaw p₀ (riskMicroControlKernel q P π) n h).toReal * κ := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hh : h ∈ (causalLaw p₀ (riskMicroControlKernel q P π) n).support
      · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        calc
          _ ≤ ∑ a,
              (π n (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a).toReal *
                (if allowed
                    (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a
                  then 0 else 1) := by
            apply Finset.sum_le_sum
            intro a _
            by_cases ha : a ∈ (π n
                (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h)).support
            · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
              by_cases hallowed : allowed
                  (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a
              · have hc := hcert h hh a ha hallowed
                simp only [if_pos hc, if_pos hallowed, le_refl]
              · by_cases hc : certified n (riskLastState n h) a <;> simp [hallowed, hc]
            · have hzero : π n
                  (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a = 0 := by
                by_contra hne
                exact ha ((PMF.mem_support_iff _ _).mpr hne)
              simp [hzero]
          _ = (π n
                (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h)).toMeasure.real
                {a | ¬ allowed
                  (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h) a} :=
            coverage_uncovered_indicator_expectation _ _
          _ ≤ κ := by
            apply hpolicy
            exact (PMF.mem_support_map_iff _ _ _).mpr ⟨h, hh, rfl⟩
      · have hzero : causalLaw p₀ (riskMicroControlKernel q P π) n h = 0 := by
          by_contra hne
          exact hh ((PMF.mem_support_iff _ _).mpr hne)
        simp [hzero]
    _ = κ := by rw [← Finset.sum_mul, coverage_sum_toReal, one_mul]

/-- Minimal actual-law adapter: history-fiber posterior support replaces the
whole current-observation fiber. All posterior weights use this same π's
actual causal prefix, and the conclusion uses the existing row-law object. -/
theorem posterior_supported_actions_bound_actual_coverage
    {X Y A : Type u} [Fintype X] [Fintype A]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p₀ : PMF X) (q : X → Y) (P : ℕ → X → A → PMF X)
    (π : ∀ n, CausalHistory Y (A × Y) n → PMF A)
    (certified : ℕ → X → A → Prop) (n : ℕ)
    (allowed : CausalHistory Y (A × Y) n → A → Prop) (κ : ℝ)
    (hposterior :
      ∀ hc (hy : hc ∈ ((causalLaw p₀ (riskMicroControlKernel q P π) n).map
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)).support) a,
        a ∈ (π n hc).support → allowed hc a →
          ∀ x ∈ (fiberTerminalPosterior
            (causalLaw p₀ (riskMicroControlKernel q P π) n)
            (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)
            (riskLastState n) hc hy).support,
            certified n x a)
    (hpolicy :
      ∀ hc ∈ ((causalLaw p₀ (riskMicroControlKernel q P π) n).map
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)).support,
        (π n hc).toMeasure.real {a | ¬ allowed hc a} ≤ κ) :
    (coverageDeploymentRowLaw p₀ q P π n).toMeasure.real
      {xa | ¬ certified n xa.1 xa.2} ≤ κ := by
  apply supported_history_actions_bound_actual_coverage
    p₀ q P π certified n allowed κ ?_ hpolicy
  intro h hh a ha hallowed
  have hy :
      riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n h ∈
        ((causalLaw p₀ (riskMicroControlKernel q P π) n).map
          (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨h, hh, rfl⟩
  apply hposterior _ hy a ha hallowed (riskLastState n h)
  exact (mem_fiberTerminalPosterior_support_iff
    (causalLaw p₀ (riskMicroControlKernel q P π) n)
    (riskHistoryMap q (fun ax : A × X => (ax.1, q ax.2)) n)
    (riskLastState n) _ hy (riskLastState n h)).mpr ⟨h, hh, rfl, rfl⟩


end
end PosteriorSupportCoverageCheck
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
