import UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency.Contract
import UEOT.V3.FiniteAlphabetPStat01Radius
import UEOT.V3.FiniteCandidatePStat08
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Field

/-!
# P3.1 — one explicit vanishing confidence schedule

We use

`alpha_n = exp (-sqrt (n+1))`.

It tends to zero slowly enough that the logarithmic confidence penalty remains
sublinear in sample size.  The frozen P-STAT-01 and P-STAT-08 radii therefore
also tend to zero.  One shared asymptotic kernel is used for both radii.
-/

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open Filter Topology
open UEOT.V3.FiniteAlphabetPStat01Radius
open UEOT.V3.FiniteCandidatePStat08

/-- Explicit confidence failure schedule for P3. -/
noncomputable def alphaSchedule (n : ℕ) : ℝ :=
  Real.exp (-Real.sqrt ((n + 1 : ℕ) : ℝ))

@[simp] theorem alphaSchedule_pos (n : ℕ) : 0 < alphaSchedule n := by
  unfold alphaSchedule
  exact Real.exp_pos _

@[simp] theorem alphaSchedule_le_one (n : ℕ) : alphaSchedule n ≤ 1 := by
  unfold alphaSchedule
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Real.sqrt_nonneg _)

/-- The explicit failure probability vanishes. -/
theorem alphaSchedule_tendsto_zero :
    Tendsto alphaSchedule atTop (𝓝 0) := by
  unfold alphaSchedule
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_neg_atTop_atBot.comp
  apply Real.tendsto_sqrt_atTop.comp
  exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/-- Shared analytic kernel: a fixed logarithmic constant plus the square-root
confidence penalty is still sublinear in sample size. -/
theorem tendsto_const_add_sqrt_div (C : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (C + Real.sqrt ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hC : Tendsto (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop hN C
  have hsqrtTop :
      Tendsto (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hN
  have hsqrtInv :
      Tendsto (fun n : ℕ => (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  have hsqrtDiv :
      Tendsto
        (fun n : ℕ => Real.sqrt ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 0) := by
    convert hsqrtInv using 1
    funext n
    exact Real.sqrt_div_self
  simpa only [add_div, zero_add] using hC.add hsqrtDiv

/-- The frozen P-STAT-08 finite-candidate validation radius vanishes under the
explicit schedule. -/
theorem pStat08Radius_alphaSchedule_tendsto_zero
    (m : ℕ) (hm : 0 < m) :
    Tendsto
      (fun n : ℕ => pStat08Radius (n + 1) m (alphaSchedule n))
      atTop (𝓝 0) := by
  have hA : (2 * (m : ℝ)) ≠ 0 := by positivity
  have hlog : ∀ n : ℕ,
      Real.log ((2 * (m : ℝ)) / alphaSchedule n) =
        Real.log (2 * (m : ℝ)) + Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    intro n
    have halpha : alphaSchedule n ≠ 0 := ne_of_gt (alphaSchedule_pos n)
    rw [Real.log_div hA halpha]
    simp [alphaSchedule]
  have hbase := tendsto_const_add_sqrt_div (Real.log (2 * (m : ℝ)))
  have hhalf := hbase.div_const (2 : ℝ)
  have hinner : Tendsto
      (fun n : ℕ =>
        (Real.log (2 * (m : ℝ)) + Real.sqrt ((n + 1 : ℕ) : ℝ)) /
          (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    simpa [div_div, mul_comm] using hhalf
  have hactual : Tendsto
      (fun n : ℕ =>
        Real.log ((2 * (m : ℝ)) / alphaSchedule n) /
          (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    convert hinner using 1
    funext n
    rw [hlog n]
  simpa [pStat08Radius] using hactual.sqrt

/-- The frozen P-STAT-01 clipped finite-alphabet TV radius vanishes under the
same explicit schedule. -/
theorem pStat01Radius_alphaSchedule_tendsto_zero
    (K L : ℕ) (hL : 0 < L) :
    Tendsto
      (fun n : ℕ => pStat01Radius (n + 1) K L (alphaSchedule n))
      atTop (𝓝 0) := by
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hlog : ∀ n : ℕ,
      Real.log ((L : ℝ) / alphaSchedule n) =
        Real.log (L : ℝ) + Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    intro n
    have halpha : alphaSchedule n ≠ 0 := ne_of_gt (alphaSchedule_pos n)
    rw [Real.log_div hL0 halpha]
    simp [alphaSchedule]
  let C : ℝ := (((K + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (L : ℝ))
  have hbase := tendsto_const_add_sqrt_div C
  have hhalf := hbase.div_const (2 : ℝ)
  have hinner : Tendsto
      (fun n : ℕ =>
        (C + Real.sqrt ((n + 1 : ℕ) : ℝ)) /
          (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    simpa [div_div, mul_comm] using hhalf
  let core : ℕ → ℝ := fun n =>
    ((((K + 1 : ℕ) : ℝ) * Real.log 2 +
        Real.log ((L : ℝ) / alphaSchedule n)) /
      (2 * ((n + 1 : ℕ) : ℝ)))
  have hactual : Tendsto core atTop (𝓝 0) := by
    convert hinner using 1
    funext n
    simp only [core]
    rw [hlog n]
    simp only [C]
    ring
  have hraw : Tendsto (fun n => Real.sqrt (core n)) atTop (𝓝 0) := by
    simpa using hactual.sqrt
  have hclip : Tendsto (fun n => min 1 (Real.sqrt (core n))) atTop (𝓝 0) := by
    have hcont : Continuous (fun x : ℝ => min 1 x) :=
      continuous_const.min continuous_id
    simpa [Function.comp_def] using hcont.continuousAt.tendsto.comp hraw
  simpa [pStat01Radius, core, Nat.cast_add, Nat.cast_one] using hclip

/-- P-STAT-01 schedule packaged as a changing-sample-space compatible contract. -/
noncomputable def finiteAlphabetTVSchedule (K L : ℕ) (hL : 0 < L) :
    ConfidenceSchedule where
  failure := alphaSchedule
  radius := fun n => pStat01Radius (n + 1) K L (alphaSchedule n)
  failure_pos := alphaSchedule_pos
  failure_le_one := alphaSchedule_le_one
  radius_nonneg := by
    intro n
    unfold pStat01Radius
    exact le_min (by norm_num) (Real.sqrt_nonneg _)
  failure_tendsto_zero := alphaSchedule_tendsto_zero
  radius_tendsto_zero := pStat01Radius_alphaSchedule_tendsto_zero K L hL

/-- P-STAT-08 schedule packaged with the same failure sequence. -/
noncomputable def finiteCandidateSchedule (m : ℕ) (hm : 0 < m) :
    ConfidenceSchedule where
  failure := alphaSchedule
  radius := fun n => pStat08Radius (n + 1) m (alphaSchedule n)
  failure_pos := alphaSchedule_pos
  failure_le_one := alphaSchedule_le_one
  radius_nonneg := fun _ => Real.sqrt_nonneg _
  failure_tendsto_zero := alphaSchedule_tendsto_zero
  radius_tendsto_zero := pStat08Radius_alphaSchedule_tendsto_zero m hm

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
