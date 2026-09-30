import UEOT.V3.Compression.PositiveEigenstructure
import UEOT.V3.Compression.OccupationLimitInvariance

/-!
# Second-order feasibility: positive eigenstructure -> invariant limit

This module tests a nontrivial M-PE -> M-OI bridge.

For each index `n`, positive left/right eigenstructure gives a Doob transform
`Pₙ` and an exactly stationary paired weight `qₙ` through M-PE. The transform
is allowed to vary with `n`. If both `Pₙ` and `qₙ` converge, the moving exact
stationarity identities imply a vanishing residual for the fixed limiting
kernel. M-OI then closes that residual to exact stationarity of the limiting
weight for the limiting kernel.

This is intentionally not the cosmetic constant-sequence embedding of an
already stationary law into M-OI.
-/

namespace UEOT.V3.Compression.PositiveEigenInvariantLimit

open Filter Topology
open UEOT.V3.Compression.PositiveEigenstructure
open UEOT.V3.Compression.OccupationLimitInvariance

universe uI

variable {I : Type uI} [Fintype I]

/-- Moving M-PE stationary pairs close to an exact stationary pair at the
limit.

Every stage uses M-PE's exact `invariantWeight_stationary`. The Doob kernels
may vary with `n`; convergence of both the paired weights and the kernels makes
the residual against the fixed limiting kernel vanish. M-OI then supplies the
final limit-closure step. -/
theorem stationary_limit_of_convergent_positiveEigenstructure
    (Mseq : ℕ → Matrix I I ℝ)
    (Dseq : ∀ n, BiEigenData (Mseq n))
    (Pstar : Matrix I I ℝ)
    (qstar : I → ℝ)
    (hq : Tendsto (fun n => invariantWeight (Dseq n)) atTop (𝓝 qstar))
    (hP : Tendsto (fun n => hTransform (Dseq n).right) atTop (𝓝 Pstar)) :
    Matrix.vecMul qstar Pstar = qstar := by
  let qseq : ℕ → (I → ℝ) := fun n => invariantWeight (Dseq n)
  let Pseq : ℕ → Matrix I I ℝ := fun n => hTransform (Dseq n).right
  have hq' : Tendsto qseq atTop (𝓝 qstar) := by
    simpa [qseq] using hq
  have hP' : Tendsto Pseq atTop (𝓝 Pstar) := by
    simpa [Pseq] using hP
  have hstationary : ∀ n, Matrix.vecMul (qseq n) (Pseq n) = qseq n := by
    intro n
    funext j
    simpa [qseq, Pseq, rowApply, Matrix.vecMul_apply_eq_sum] using
      invariantWeight_stationary (Dseq n) j
  have hfixed :
      Tendsto (fun n => Matrix.vecMul (qseq n) Pstar)
        atTop (𝓝 (Matrix.vecMul qstar Pstar)) := by
    have hcont : Continuous (fun q : I → ℝ => Matrix.vecMul q Pstar) :=
      Continuous.matrix_vecMul continuous_id continuous_const
    exact (hcont.tendsto qstar).comp hq'
  have hmoving :
      Tendsto (fun n => Matrix.vecMul (qseq n) (Pseq n))
        atTop (𝓝 (Matrix.vecMul qstar Pstar)) := by
    have hpair :
        Tendsto (fun n => (qseq n, Pseq n)) atTop (𝓝 (qstar, Pstar)) :=
      hq'.prodMk_nhds hP'
    have hcont :
        Continuous
          (fun p : (I → ℝ) × Matrix I I ℝ =>
            Matrix.vecMul p.1 p.2) :=
      Continuous.matrix_vecMul continuous_fst continuous_snd
    exact (hcont.tendsto (qstar, Pstar)).comp hpair
  have hresVec :
      Tendsto
        (fun n => Matrix.vecMul (qseq n) Pstar - qseq n)
        atTop (𝓝 0) := by
    have hdiff := hfixed.sub hmoving
    simpa [hstationary] using hdiff
  let observe : I → (I → ℝ) → ℝ := fun j q => q j
  let advance : Unit → (I → ℝ) → (I → ℝ) :=
    fun _ q => Matrix.vecMul q Pstar
  have hObserve : ∀ j, Continuous (observe j) := by
    intro j
    exact continuous_apply j
  have hAdvanceObserve : ∀ t j,
      Continuous (fun q => observe j (advance t q)) := by
    intro _ j
    exact (continuous_apply j).comp
      (Continuous.matrix_vecMul continuous_id continuous_const)
  have hseparates :
      ∀ x y : I → ℝ, (∀ j, observe j x = observe j y) → x = y := by
    intro x y hxy
    funext j
    exact hxy j
  have hres : ∀ t j, Tendsto
      (fun n => observe j (advance t (qseq n)) - observe j (qseq n))
        atTop (𝓝 0) := by
    intro _ j
    have hj := ((continuous_apply j).tendsto (0 : I → ℝ)).comp hresVec
    change Tendsto
      (fun n => (Matrix.vecMul (qseq n) Pstar - qseq n) j)
      atTop (𝓝 0) at hj
    change Tendsto
      (fun n => (Matrix.vecMul (qseq n) Pstar - qseq n) j)
      atTop (𝓝 0)
    exact hj
  have hinv : ∀ t : Unit, advance t qstar = qstar :=
    invariant_of_continuous_observable_residual
      observe advance qseq qstar hq' hObserve hAdvanceObserve hseparates hres
  simpa [advance] using hinv ()

end UEOT.V3.Compression.PositiveEigenInvariantLimit
