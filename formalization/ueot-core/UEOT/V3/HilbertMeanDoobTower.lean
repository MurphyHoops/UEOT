import UEOT.V3.HilbertMeanDoobCore

/-!
# P-STAT-06 — tower form of noninitial Doob increments

For the source concentration proof, every noninitial Doob increment should be
viewed as the current Doob value centered by its conditional expectation under
the previous sigma-algebra.  This file packages that generic tower-property
identity once, independently of the RKHS statistic.
-/

namespace UEOT.V3.HilbertMeanDoobTower

open MeasureTheory
open UEOT.V3.HilbertMeanDoobCore

universe uΩ

variable {Ω : Type uΩ} {mΩ : MeasurableSpace Ω}

/-- A noninitial Doob increment is the current Doob value minus its conditional
expectation with respect to the previous filtration level. -/
theorem doobIncrement_succ_ae_eq_condCentered
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) [SigmaFiniteFiltration μ ℱ]
    (F : Ω → ℝ) (n : ℕ) :
    doobIncrement μ ℱ F (n + 1) =ᵐ[μ]
      fun ω =>
        doobValue μ ℱ F (n + 1) ω -
          μ[doobValue μ ℱ F (n + 1) | ℱ n] ω := by
  have htower :
      μ[doobValue μ ℱ F (n + 1) | ℱ n] =ᵐ[μ]
        doobValue μ ℱ F n := by
    change μ[μ[F | ℱ (n + 1)] | ℱ n] =ᵐ[μ] μ[F | ℱ n]
    exact ℱ.condExp_condExp F (Nat.le_succ n)
  filter_upwards [htower] with ω hω
  simp only [doobIncrement]
  rw [hω]

/-- If the current Doob value is represented almost everywhere by an explicit
continuation `C`, the corresponding noninitial increment is `C` centered by
its previous conditional expectation. -/
theorem doobIncrement_succ_ae_eq_explicitCentered
    (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) [SigmaFiniteFiltration μ ℱ]
    (F C : Ω → ℝ) (n : ℕ)
    (hC : doobValue μ ℱ F (n + 1) =ᵐ[μ] C) :
    doobIncrement μ ℱ F (n + 1) =ᵐ[μ]
      fun ω => C ω - μ[C | ℱ n] ω := by
  have hbase := doobIncrement_succ_ae_eq_condCentered μ ℱ F n
  have hcond :
      μ[doobValue μ ℱ F (n + 1) | ℱ n] =ᵐ[μ] μ[C | ℱ n] :=
    condExp_congr_ae hC
  filter_upwards [hbase, hC, hcond] with ω hbaseω hCω hcondω
  rw [hbaseω, hCω, hcondω]

end UEOT.V3.HilbertMeanDoobTower
