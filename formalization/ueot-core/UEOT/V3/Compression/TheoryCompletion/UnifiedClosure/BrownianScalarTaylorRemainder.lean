import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianIntegralWeightedQV
import Mathlib.Analysis.Calculus.Taylor

/-!
Original commitment: actual scalar Ito requires an actual C2 Taylor remainder limit, not an Ito/source field.
Existing result: SAME-source actual first/second weighted increment limits for every original full predictable L2 input.
Premise reduced: derive quadratic Taylor remainder control from original C2 regularity and native Lagrange theorem; consume actual probabilistic domination.
Model/witness: real C2 observable, SAME original continuous integral and deterministic caller clocks; no extra input L4/third derivative.
Consumer: actual C2 Ito identity; bounded first/second derivative permissions remain explicit regularity, not stochastic source assumptions.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarTaylorRemainder
open MeasureTheory ProbabilityTheory Set Filter
open BrownianQuadraticVariation BrownianProjectiveSource BrownianPredictableInputs BrownianIntegralContinuousVersion
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section

/-- Actual second-order Taylor remainder using native original derivatives. -/
def secondRemainder (φ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  φ b-φ a-deriv φ a*(b-a)-(1/2 : ℝ)*iteratedDeriv 2 φ a*(b-a)^2

/-- Native C2 Lagrange theorem bounds actual remainder by the actual local
oscillation of the original second derivative; no third derivative needed. -/
theorem secondRemainder_bound (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ) (a b ε : ℝ)
    (hvar : ∀ z ∈ uIcc a b, ‖iteratedDeriv 2 φ z-iteratedDeriv 2 φ a‖ ≤ ε) :
    ‖secondRemainder φ a b‖ ≤ (ε/2)*(b-a)^2 := by
  by_cases hab : a = b
  · subst b
    simp only [secondRemainder,sub_self,mul_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),norm_zero,le_refl]
  · obtain ⟨z,hz,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hab hφ.contDiffOn
    have hpoly : taylorWithinEval φ 1 (uIcc a b) a b = φ a+(b-a)*deriv φ a := by
      rw [show (1 : ℕ) = 0+1 by rfl,taylorWithinEval_succ,taylor_within_zero_eval]
      have hd : iteratedDerivWithin 1 φ (uIcc a b) a = deriv φ a := by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hab)
          ((hφ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt) (left_mem_uIcc),iteratedDeriv_one]
      norm_num [hd,smul_eq_mul]
    rw [hpoly] at he
    have hrep : secondRemainder φ a b = (1/2 : ℝ)*(iteratedDeriv 2 φ z-iteratedDeriv 2 φ a)*(b-a)^2 := by
      norm_num at he
      unfold secondRemainder
      linarith
    rw [hrep]
    have hv := hvar z ⟨hz.1.le,hz.2.le⟩
    calc
      _ = (1/2 : ℝ)*‖iteratedDeriv 2 φ z-iteratedDeriv 2 φ a‖*(b-a)^2 := by
        norm_num [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
      _ ≤ (1/2 : ℝ)*ε*(b-a)^2 := by gcongr
      _ = _ := by ring

/-- Native subsequence criterion consumes actual pathwise small-error
coefficients times an actual in-measure finite quantity. No moment/L4 bound
is manufactured, and no arbitrary AE intersection in time is taken. -/
theorem tendstoInMeasure_of_ae_zero_domination {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (R q Q : ℕ → Ω → ℝ) (A : Ω → ℝ)
    (hR : ∀ n, AEStronglyMeasurable (R n) μ)
    (hq : ∀ᵐ ω ∂μ, Tendsto (fun n => q n ω) atTop (𝓝 0))
    (hQ : TendstoInMeasure μ Q atTop A)
    (hb : ∀ n ω, ‖R n ω‖ ≤ q n ω*‖Q n ω‖) :
    TendstoInMeasure μ R atTop (fun _ => (0 : ℝ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff hR).mpr
  intro ns hns
  obtain ⟨ms,hms,hQa⟩ := (hQ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hq,hQa] with ω hq hQa
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hsmall := ((hq.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).mul hQa.norm)
  simp only [zero_mul] at hsmall
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hb _ _) hsmall

/-- Actual caller clock cell distance is bounded by its COMPUTED mesh. -/
theorem clockIncrement_dist_le_mesh {n : ℕ} (τ : Fin (n+1) → ℝ≥0) (hmono : Monotone τ) (i : Fin n) :
    dist (τ i.succ) (τ i.castSucc) ≤ (mesh τ : ℝ) := by
  have ho : τ i.castSucc ≤ τ i.succ := hmono (by exact_mod_cast Nat.le_succ (i : ℕ))
  have hm := NNReal.coe_le_coe.mpr (Finset.le_sup
    (f := fun j : Fin n => τ j.succ-τ j.castSucc) (Finset.mem_univ i))
  rw [NNReal.coe_sub ho] at hm
  rw [NNReal.dist_eq,abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast ho))]
  exact hm

/-- Actual continuous source paths have uniformly small caller-grid
increments on the fixed horizon, from Heine-Cantor and computed mesh. -/
theorem continuous_path_grid_increment_small (T : ℝ≥0) (N : ℕ → ℕ)
    (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0) (hmono : ∀ m, Monotone (τ m))
    (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (X : ℝ≥0 → ℝ) (hX : Continuous X) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ i : Fin (N m), dist (X (τ m i.succ)) (X (τ m i.castSucc)) < ε := by
  have huc : UniformContinuousOn X (Icc (0 : ℝ≥0) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hX.continuousOn
  obtain ⟨δ,hδ,hδX⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  have he : ∀ᶠ m in atTop, (mesh (τ m) : ℝ) < δ := (tendsto_order.mp hmesh).2 δ hδ
  filter_upwards [he] with m hm
  intro i
  have hs (j : Fin (N m+1)) : τ m j ∈ Icc (0 : ℝ≥0) T :=
    ⟨bot_le,((hmono m) (Fin.le_last j)).trans (hend m).le⟩
  exact hδX _ (hs _) _ (hs _) ((clockIncrement_dist_le_mesh (τ m) (hmono m) i).trans_lt hm)

/-- ORIGINAL C2 regularity and an ACTUAL continuous path derive uniformly
small quadratic Taylor error on the caller clocks. No third derivative,
externally supplied modulus or uniform stochastic moment is required. -/
theorem secondRemainder_grid_small (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hmono : ∀ m, Monotone (τ m)) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0))
    (X : ℝ≥0 → ℝ) (hX : Continuous X) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ i : Fin (N m),
      ‖secondRemainder φ (X (τ m i.castSucc)) (X (τ m i.succ))‖ ≤
        ε*(X (τ m i.succ)-X (τ m i.castSucc))^2 := by
  have hcomp : IsCompact (X '' Icc (0 : ℝ≥0) T) := isCompact_Icc.image hX
  obtain ⟨L,hL⟩ := hcomp.bddBelow
  obtain ⟨R,hR⟩ := hcomp.bddAbove
  have hXR {u : ℝ≥0} (hu : u ∈ Icc (0 : ℝ≥0) T) : X u ∈ Icc L R :=
    ⟨hL ⟨u,hu,rfl⟩,hR ⟨u,hu,rfl⟩⟩
  have huc : UniformContinuousOn (iteratedDeriv 2 φ) (Icc L R) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hφ.continuous_iteratedDeriv' 2).continuousOn
  obtain ⟨δ,hδ,hδφ⟩ := Metric.uniformContinuousOn_iff.mp huc (2*ε) (by positivity)
  filter_upwards [continuous_path_grid_increment_small T N τ hmono hend hmesh X hX δ hδ] with m hm
  intro i
  have hu (j : Fin (N m+1)) : τ m j ∈ Icc (0 : ℝ≥0) T :=
    ⟨bot_le,((hmono m) (Fin.le_last j)).trans (hend m).le⟩
  have hvar : ∀ z ∈ uIcc (X (τ m i.castSucc)) (X (τ m i.succ)),
      ‖iteratedDeriv 2 φ z-iteratedDeriv 2 φ (X (τ m i.castSucc))‖ ≤ 2*ε := by
    intro z hz
    have hzR : z ∈ Icc L R :=
      ⟨(le_min (hXR (hu _)).1 (hXR (hu _)).1).trans hz.1,
        hz.2.trans (max_le (hXR (hu _)).2 (hXR (hu _)).2)⟩
    have hzdist : dist z (X (τ m i.castSucc)) < δ :=
      (abs_sub_left_of_mem_uIcc hz).trans_lt (by simpa only [Real.dist_eq] using hm i)
    have hv := hδφ z hzR (X (τ m i.castSucc)) (hXR (hu i.castSucc)) hzdist
    exact le_of_lt (by simpa only [Real.dist_eq,Real.norm_eq_abs] using hv)
  calc
    _ ≤ ((2*ε)/2)*(X (τ m i.succ)-X (τ m i.castSucc))^2 :=
      secondRemainder_bound φ hφ (X (τ m i.castSucc)) (X (τ m i.succ)) (2*ε) hvar
    _ = _ := by ring

/-- Actual SAME original continuous-integral source consumes deterministic
C2 grid control on its ONE already proved full-measure path event. There is
no intersection of independently supplied AE equalities over real times. -/
theorem actualIntegral_remainder_grid_small (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (T : ℝ≥0) (N : ℕ → ℕ) (τ : (m : ℕ) → Fin (N m+1) → ℝ≥0)
    (hmono : ∀ m, Monotone (τ m)) (hend : ∀ m, τ m (Fin.last (N m))=T)
    (hmesh : Tendsto (fun m => (mesh (τ m) : ℝ)) atTop (𝓝 0)) (f : fullPredictableL2 T) :
    ∀ᵐ ω ∂sourceLaw, ∀ ε > 0, ∀ᶠ m in atTop, ∀ i : Fin (N m),
      ‖secondRemainder φ (continuousIntegralProcess T f (τ m i.castSucc) ω)
        (continuousIntegralProcess T f (τ m i.succ) ω)‖ ≤ ε*
      (continuousIntegralProcess T f (τ m i.succ) ω-continuousIntegralProcess T f (τ m i.castSucc) ω)^2 :=
  (continuousIntegralProcess_continuous T f).mono (fun ω hω ε hε =>
    secondRemainder_grid_small φ hφ T N τ hmono hend hmesh (fun u => continuousIntegralProcess T f u ω) hω ε hε)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianScalarTaylorRemainder
