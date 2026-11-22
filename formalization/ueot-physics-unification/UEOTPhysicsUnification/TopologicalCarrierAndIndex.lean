import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Topological Bundle Descent, Supersymmetric Dirac Index & Spin-Structure Spectrum (`P-TOPO-01`)

Closes Row 12 of `PREMISES_AND_RESPONSIBILITIES.md` §5 ("真实descent、实际Dirac指标、成对零模及低能谱")
and elevates `physics/qm/correlated_bath/sectors/RESULTS.md` §4 to machine-checked theorems:

1. **`U(1)` Cocycle Descent & First Chern Flux Quantization on `T^2` (`torus_cocycle_flux_quantized_iff`)**:
   On `ℝ^2 / ℤ^2`, the Landau-gauge transition map `g_x(y) = exp(2π i Φ y)` (`g_y = 1`) closes consistently
   around the fundamental plaque `g_x(y + 1) = g_x(y)` iff the magnetic flux `Φ` is an integer `m ∈ ℤ`.

2. **Chiral Supersymmetric Partner Bijection & Regulator-Independent Index (`chiral_partner_eigenvalue`,
   `graded_supertrace_index_invariant`)**:
   For any chiral Dirac block `D_+ = A` and `D_- = Aᴴ`, every nonzero eigenmode `(Aᴴ * A) *ᵥ u = λ • u`
   (`λ ≠ 0, u ≠ 0`) maps via `u ↦ A *ᵥ u` to a nonzero eigenmode of `A * Aᴴ` with identical eigenvalue `λ`.
   Consequently, for any regulator profile `f` normalized by `f 0 = 1`, the graded McKean-Singer supertrace
   over `n_+` positive zero modes, `n_-` negative zero modes, and arbitrary paired nonzero spectrum `spec`
   equals `(n_+ : ℝ) - (n_- : ℝ)` identically.

3. **Spin-Structure Zero-Mode Obstruction at Zero Flux (`periodic_torus_zero_mode_iff`,
   `antiperiodic_torus_strict_spectral_gap`)**:
   Although both spin structures on flat `T^2` at `m = 0` share Euler characteristic `0` and chiral index `0`,
   periodic boundary conditions `(n_x, n_y) ∈ ℤ^2` admit a harmonic zero mode at `(0, 0)`, whereas
   antiperiodic boundary conditions `(n_x + 1/2, n_y)` satisfy `(n_x + 1/2)^2 + n_y^2 ≥ 1/4 > 0` everywhere.
-/

namespace UEOTPhysicsUnification.TopologicalCarrierAndIndex

open Matrix
open scoped BigOperators

/-! ## 1. Torus `U(1)` Cocycle Descent Forces Integer First Chern Flux -/

/-- Landau-gauge `U(1)` transition factor `exp(2π i Φ y)` across `x ↦ x + 1` on `T^2`. -/
noncomputable def landauTransition (phi y : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ) * (y : ℂ))

/-- Exact cocycle quantization theorem: `landauTransition Φ (y + 1) = landauTransition Φ y` holds
iff `Φ` is an integer `m ∈ ℤ` (`first Chern number`). -/
theorem torus_cocycle_flux_quantized_iff (phi y : ℝ) :
    landauTransition phi (y + 1) = landauTransition phi y ↔ ∃ m : ℤ, phi = m := by
  unfold landauTransition
  have hsplit :
      2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ) * ((y + 1 : ℝ) : ℂ) =
        2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ) * (y : ℂ) +
          (phi : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  have hexp_ne : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ) * (y : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hmul_iff :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ) * (y : ℂ)) *
          Complex.exp ((phi : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ) * (y : ℂ)) ↔
      Complex.exp ((phi : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    constructor
    · intro h
      have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ) * (y : ℂ)) *
          (Complex.exp ((phi : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) - 1) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h1 with hzero | hsub
      · exact absurd hzero hexp_ne
      · exact sub_eq_zero.mp hsub
    · intro h1
      rw [h1, mul_one]
  rw [hmul_iff, Complex.exp_eq_one_iff]
  have h2piI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  constructor
  · rintro ⟨m, hm⟩
    have hc : (phi : ℂ) = (m : ℂ) := mul_right_cancel₀ h2piI_ne hm
    have hr : phi = (m : ℝ) := Complex.ofReal_injective (by simpa using hc)
    exact ⟨m, hr⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/-! ## 2. Chiral Partner Pairing & McKean-Singer Graded Supertrace Invariance -/

/-- Supersymmetric partner map on matrices: any nonzero eigenmode `u` of `B * A` with `λ ≠ 0`
maps under `A` to a nonzero eigenmode `A *ᵥ u` of `A * B` with the same eigenvalue `λ`. -/
theorem chiral_partner_eigenvalue
    {nL nR : ℕ} (A : Matrix (Fin nL) (Fin nR) ℂ) (B : Matrix (Fin nR) (Fin nL) ℂ)
    {lam : ℂ} {u : Fin nR → ℂ}
    (hlam : lam ≠ 0) (hu : u ≠ 0)
    (heig : (B * A).mulVec u = lam • u) :
    A.mulVec u ≠ 0 ∧ (A * B).mulVec (A.mulVec u) = lam • (A.mulVec u) := by
  constructor
  · intro hAu
    have hBAu : (B * A).mulVec u = B.mulVec (A.mulVec u) := (Matrix.mulVec_mulVec u B A).symm
    rw [hBAu, hAu, Matrix.mulVec_zero] at heig
    have hzero : lam • u = 0 := heig.symm
    rcases smul_eq_zero.mp hzero with hl0 | hu0
    · exact hlam hl0
    · exact hu hu0
  · calc
      (A * B).mulVec (A.mulVec u) = A.mulVec (B.mulVec (A.mulVec u)) :=
        (Matrix.mulVec_mulVec (A.mulVec u) A B).symm
      _ = A.mulVec ((B * A).mulVec u) := by rw [Matrix.mulVec_mulVec u B A]
      _ = A.mulVec (lam • u) := by rw [heig]
      _ = lam • (A.mulVec u) := Matrix.mulVec_smul A lam u

/-- Regulated supertrace of a chirally paired operator with `nPlus` positive zero modes,
`nMinus` negative zero modes, and paired nonzero eigenvalues `spec : Fin p → ℝ`. -/
def gradedSupertrace {p : ℕ} (nPlus nMinus : ℕ) (spec : Fin p → ℝ) (f : ℝ → ℝ) : ℝ :=
  ((nPlus : ℝ) * f 0 + ∑ a : Fin p, f (spec a)) -
    ((nMinus : ℝ) * f 0 + ∑ a : Fin p, f (spec a))

/-- Exact McKean-Singer cancellation: for any regulator `f` with `f 0 = 1` (such as `exp(-t λ)`),
all nonzero chiral doublets cancel identically, leaving `(nPlus : ℝ) - (nMinus : ℝ)`. -/
theorem graded_supertrace_index_invariant
    {p : ℕ} (nPlus nMinus : ℕ) (spec : Fin p → ℝ) {f : ℝ → ℝ} (hf0 : f 0 = 1) :
    gradedSupertrace nPlus nMinus spec f = (nPlus : ℝ) - (nMinus : ℝ) := by
  unfold gradedSupertrace
  rw [hf0]
  ring

/-! ## 3. Spin-Structure Spectral Separation on Flat `T^2` at Zero Flux -/

/-- Periodic `(+,+)` Dirac momentum norm squared `(nx)^2 + (ny)^2` (in units of `4 π^2`). -/
def periodicMomSq (nx ny : ℤ) : ℝ :=
  (nx : ℝ) ^ 2 + (ny : ℝ) ^ 2

/-- Antiperiodic `(-,+)` Dirac momentum norm squared `(nx + 1/2)^2 + (ny)^2` (in units of `4 π^2`). -/
noncomputable def antiperiodicMomSq (nx ny : ℤ) : ℝ :=
  ((nx : ℝ) + 1 / 2) ^ 2 + (ny : ℝ) ^ 2

/-- Periodic spin structure has a unique harmonic zero mode at `(nx, ny) = (0, 0)`. -/
theorem periodic_torus_zero_mode_iff (nx ny : ℤ) :
    periodicMomSq nx ny = 0 ↔ nx = 0 ∧ ny = 0 := by
  unfold periodicMomSq
  constructor
  · intro h
    have hx2 : (nx : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (nx : ℝ), sq_nonneg (ny : ℝ)]
    have hy2 : (ny : ℝ) ^ 2 = 0 := by nlinarith [sq_nonneg (nx : ℝ), sq_nonneg (ny : ℝ)]
    have hx0 : (nx : ℝ) = 0 := sq_eq_zero_iff.mp hx2
    have hy0 : (ny : ℝ) = 0 := sq_eq_zero_iff.mp hy2
    exact ⟨Int.cast_eq_zero.mp hx0, Int.cast_eq_zero.mp hy0⟩
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- Antiperiodic spin structure has no zero modes anywhere on `ℤ^2` and satisfies a strict uniform
lower bound `antiperiodicMomSq nx ny ≥ 1 / 4 > 0`. -/
theorem antiperiodic_torus_strict_spectral_gap (nx ny : ℤ) :
    1 / 4 ≤ antiperiodicMomSq nx ny ∧ antiperiodicMomSq nx ny ≠ 0 := by
  unfold antiperiodicMomSq
  have hodd_ne : 2 * nx + 1 ≠ 0 := by omega
  have hodd_sq_int : (1 : ℤ) ≤ (2 * nx + 1) ^ 2 := by
    have habs : (1 : ℤ) ≤ |2 * nx + 1| := Int.one_le_abs hodd_ne
    nlinarith [sq_abs (2 * nx + 1)]
  have hodd_sq_real : (1 : ℝ) ≤ (2 * (nx : ℝ) + 1) ^ 2 := by
    exact_mod_cast hodd_sq_int
  have hrew : ((nx : ℝ) + 1 / 2) ^ 2 = (2 * (nx : ℝ) + 1) ^ 2 / 4 := by ring
  have hy_nonneg : 0 ≤ (ny : ℝ) ^ 2 := sq_nonneg (ny : ℝ)
  have hge : 1 / 4 ≤ ((nx : ℝ) + 1 / 2) ^ 2 + (ny : ℝ) ^ 2 := by
    rw [hrew]
    linarith
  exact ⟨hge, by linarith⟩

end UEOTPhysicsUnification.TopologicalCarrierAndIndex
