import UEOT.V3.Compression.QuotientDescent
import UEOT.V3.FisherGauge
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Read-Only `Core v3` Buckingham-Quotient Descent Unit-Gauge Elimination & Planck-to-Electroweak Coupling Bridge (`C-CORE-CONST-01`, `P-GUT-DESERT-02`)

Addresses `NEXT_GATE` Frontier 3 without modifying `Core v3`:

1. **Exact Integer Dimensional Lattice, Parity-Sublattice Unimodular Factorization & `4 × 4` Buckingham Basis**:
   - Formalizes the `(M, L, T)` dimensional exponent matrix `mPlanck` of `(G, ℏ, c)` alongside `vLambda = (0, -2, 0)`.
   - In raw `(M, L, T)` units, `mPlanck.det = 2` with integer adjugate `adjPlanck` satisfying
     `mPlanck * adjPlanck = 2 • 1` because every constant in `{G, ℏ, c, Λ}` has even total exponent sum
     `e_M + e_L + e_T ∈ 2ℤ` (explaining the half-integer square-root exponents of `(m_P, ℓ_P, t_P)`).
   - Relative to the even-parity sublattice basis `bEven` `(M L, L², L T⁻¹)`, `mPlanck = mPlanckUnimodular * bEven`
     where `mPlanckUnimodular` has `det = -1` and explicit integer inverse `mPlanckUnimodularInv ∈ GL₃(ℤ)`!
   - On `ℤ⁴`, the `4 × 4` Buckingham monomial matrix `uBuckingham` mapping `(G, ℏ, c, Λ)` to
     `(G, ℏ, c, I_Λ = G ℏ Λ / c³)` is unimodular (`det = 1`) with explicit integer inverse `uBuckinghamInv`,
     and `ker_ℤ(dimMatrix3x4)` is generated over `ℤ` by the unique primitive vector `(1, 1, -3, 1)`.

2. **Free Transitive `(ℝ_{>0})³` Unit-Rescaling Torsor, `QuotientDescent` & `FisherGauge` (`P-INV-02`)**:
   - Proves `(G, ℏ, c) ∈ (ℝ_{>0})³` is an exact free transitive torsor under `(λ_M, λ_L, λ_T) ∈ (ℝ_{>0})³`
     (`ghc_unit_rescaling_existsUnique_torsor`).
   - Applies `UEOT.V3.Compression.QuotientDescent.existsUnique_descend` directly to prove that EVERY
     unit-rescaling-invariant observable of `(G, Λ, ℏ, c)` factors **uniquely** through the single dimensionless
     cosmological-Planck invariant `I_Λ := G ℏ Λ / c³ = Λ ℓ_P²` (both on `ℝ_{>0} × ℝ × ℝ_{>0} × ℝ_{>0}` and
     on `(ℝ_{>0})⁴`), while proving formally that distinct values `I₁ ≠ I₂` lie in disjoint unit-gauge orbits
     (so `I_Λ` itself remains an irreducible physical parameter not derived from `Core v3`).
   - Connects directly to `UEOT.V3.FisherGauge.p_inv_02`: along any 1-parameter `(M, L, T)` exponential unit-rescaling
     orbit, every unit-invariant log-likelihood is constant and its tangent direction lies identically in the kernel
     of Fisher information (`fisherAction μ score v = 0`), orthogonal to `∇ ln I_Λ = (1, 1, -3, 1)`.

3. **Exact 1-Loop `(3,3,1)` Gauge Unification Triangle, Scale-Free Collinearity Defect `Δ₁₂₃` & PDG-2024 Exclusion**:
   - Proves `SU(5)` hypercharge normalization `3 / 5` from generation trace equality `Tr_gen(T₁) = Tr_gen(T₂) = Tr_gen(T₃) = 2`
     and derives the exact rational 1-loop `(3,3,1)` SM beta coefficients `(b₁, b₂, b₃) = (41/10, -19/6, -7)`.
   - Proves exact RG scale-invariance of `Δ₁₂₃ := (b₂ - b₃) α₁⁻¹ + (b₃ - b₁) α₂⁻¹ + (b₁ - b₂) α₃⁻¹`, proves
     `Δ₁₂₃ = 0` is necessary and sufficient for single-threshold 1-loop desert unification, derives the exact
     Georgi–Quinn–Weinberg `sin²θ_W` identity, proves `Δ₁₂₃ < -38 < 0` across the entire PDG-2024 `3σ` box
     (certifying `Δ₁₂₃ ≠ 0` and excluding naive single-step 1-loop minimal SM unification), and proves the exact
     intermediate-threshold repair identity showing complete `SU(5)` multiplets or extra generations cannot shift `Δ₁₂₃`.
-/

namespace UEOTPhysicsUnification.CoreUnitGaugeAndDimensionlessConstants

open Function Matrix MeasureTheory
open UEOT.V3.Compression.QuotientDescent
open UEOT.V3.FisherGauge

/-! ## 1. Integer Dimensional Matrices, Unimodular Factorizations & `ℤ⁴` Buckingham Nullspace -/

/-- `(M, L, T)` integer dimensional exponent matrix of `(G, ℏ, c)`:
row 0 `G : M⁻¹ L³ T⁻²`, row 1 `ℏ : M¹ L² T⁻¹`, row 2 `c : M⁰ L¹ T⁻¹`. -/
def mPlanck : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 3, -2;
      1, 2, -1;
      0, 1, -1]

/-- `(M, L, T)` integer dimensional exponent vector of the cosmological constant `Λ : L⁻²`. -/
def vLambda : Fin 3 → ℤ := ![0, -2, 0]

/-- Exact integer adjugate matrix of `mPlanck`, encoding twice the `(G, ℏ, c)` exponents of `(m_P⁻¹, ℓ_P⁻¹, t_P⁻¹)`. -/
def adjPlanck : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 1,  1;
      1, 1, -3;
      1, 1, -5]

/-- Even-parity sublattice basis `(M L, L², L T⁻¹)` of `Λ_even = { (e_M, e_L, e_T) ∈ ℤ³ | Even (e_M + e_L + e_T) }`. -/
def bEven : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 1,  0;
     0, 2,  0;
     0, 1, -1]

/-- Unimodular `3 × 3` integer exponent matrix of `(G, ℏ, c)` in the `(M L, L², L T⁻¹)` basis (`det = -1`). -/
def mPlanckUnimodular : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 1, 2;
      1, 0, 1;
      0, 0, 1]

/-- Explicit integer inverse of `mPlanckUnimodular` over `ℤ` (`GL₃(ℤ)`). -/
def mPlanckUnimodularInv : Matrix (Fin 3) (Fin 3) ℤ :=
  !![0, 1, -1;
     1, 1, -3;
     0, 0,  1]

/-- Full `3 × 4` `(M, L, T)` integer dimensional matrix of `(G, ℏ, c, Λ)` (columns = constants, rows = `M, L, T`). -/
def dimMatrix3x4 : Matrix (Fin 3) (Fin 4) ℤ :=
  !![-1,  1,  0,  0;
      3,  2,  1, -2;
     -2, -1, -1,  0]

/-- Unimodular `4 × 4` Buckingham monomial transformation mapping `(G, ℏ, c, Λ)` to `(G, ℏ, c, I_Λ = G ℏ c⁻³ Λ)`. -/
def uBuckingham : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0,  0, 0;
     0, 1,  0, 0;
     0, 0,  1, 0;
     1, 1, -3, 1]

/-- Explicit integer inverse of `uBuckingham` over `ℤ`, reconstructing `Λ = G⁻¹ ℏ⁻¹ c³ I_Λ`. -/
def uBuckinghamInv : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 1,  0, 0, 0;
      0,  1, 0, 0;
      0,  0, 1, 0;
     -1, -1, 3, 1]

theorem mPlanck_det_eq_two : mPlanck.det = 2 := by
  simp [mPlanck, Matrix.det_fin_three]

theorem mPlanck_mul_adjPlanck :
    mPlanck * adjPlanck = (2 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [mPlanck, adjPlanck, Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)

theorem adjPlanck_mul_mPlanck :
    adjPlanck * mPlanck = (2 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [mPlanck, adjPlanck, Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)

/-- Exact unimodular factorization `mPlanck = mPlanckUnimodular * bEven` with `det mPlanckUnimodular = -1`
and explicit two-sided integer inverse `mPlanckUnimodularInv` over `ℤ`. -/
theorem mPlanckUnimodular_properties :
    mPlanckUnimodular * bEven = mPlanck ∧
      mPlanckUnimodular.det = -1 ∧
      mPlanckUnimodular * mPlanckUnimodularInv = 1 ∧
      mPlanckUnimodularInv * mPlanckUnimodular = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [mPlanckUnimodular, bEven, mPlanck, Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)
  · simp [mPlanckUnimodular, Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [mPlanckUnimodular, mPlanckUnimodularInv, Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [mPlanckUnimodular, mPlanckUnimodularInv, Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)

/-- `vLambda = (0, -2, 0)` lies in the integer row-span of `mPlanck` with exact integer weights `(-1, -1, 3)`
because its `L⁻²` exponent cancels the index-2 parity factor of `mPlanck`. -/
theorem vLambda_integer_combination_of_mPlanck :
    mPlanck.vecMul ![-1, -1, 3] = vLambda := by
  ext j
  fin_cases j <;>
    (simp [mPlanck, vLambda, Matrix.vecMul, dotProduct, Fin.sum_univ_three]; try norm_num)

/-- `uBuckingham` is unimodular over `ℤ` (`det = 1`) with explicit two-sided integer inverse `uBuckinghamInv`. -/
theorem uBuckingham_unimodular :
    uBuckingham.det = 1 ∧
      uBuckingham * uBuckinghamInv = 1 ∧
      uBuckinghamInv * uBuckingham = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_succ_row_zero]
    simp [uBuckingham, Fin.sum_univ_four, Matrix.submatrix, Matrix.det_fin_three]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [uBuckingham, uBuckinghamInv, Matrix.mul_apply, Fin.sum_univ_four]; try norm_num)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [uBuckingham, uBuckinghamInv, Matrix.mul_apply, Fin.sum_univ_four]; try norm_num)

/-- **Complete Integer Buckingham Kernel Theorem**:
An integer exponent 4-tuple `e = (e_G, e_ℏ, e_c, e_Λ) ∈ ℤ⁴` yields an `(M, L, T)`-dimensionless
monomial `G^{e_G} ℏ^{e_ℏ} c^{e_c} Λ^{e_Λ}` if and only if `e = e_Λ • (1, 1, -3, 1)`, i.e., an integer
power of the single primitive invariant `I_Λ = G ℏ Λ / c³`. -/
theorem dimMatrix3x4_int_kernel_iff (e : Fin 4 → ℤ) :
    dimMatrix3x4.mulVec e = 0 ↔
      e 0 = e 3 ∧ e 1 = e 3 ∧ e 2 = -3 * e 3 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [dimMatrix3x4, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h2
    refine ⟨by omega, by omega, by omega⟩
  · rintro ⟨h0, h1, h2⟩
    ext i
    fin_cases i <;>
      (simp [dimMatrix3x4, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0, h1, h2]; try omega)

/-! ## 2. Free Transitive `(ℝ_{>0})³` Unit-Rescaling Torsor, `QuotientDescent` & `FisherGauge` -/

/-- Positive `(M, L, T)` base-unit rescaling factors `(λ_M, λ_L, λ_T) ∈ (ℝ_{>0})³`. -/
@[ext]
structure UnitScale where
  lamM : ℝ
  lamL : ℝ
  lamT : ℝ
  hM : 0 < lamM
  hL : 0 < lamL
  hT : 0 < lamT

namespace UnitScale

def one : UnitScale := ⟨1, 1, 1, zero_lt_one, zero_lt_one, zero_lt_one⟩

noncomputable def mul (u v : UnitScale) : UnitScale :=
  ⟨u.lamM * v.lamM, u.lamL * v.lamL, u.lamT * v.lamT,
    mul_pos u.hM v.hM, mul_pos u.hL v.hL, mul_pos u.hT v.hT⟩

noncomputable def inv (u : UnitScale) : UnitScale :=
  ⟨u.lamM⁻¹, u.lamL⁻¹, u.lamT⁻¹,
    inv_pos.mpr u.hM, inv_pos.mpr u.hL, inv_pos.mpr u.hT⟩

/-- Smooth 1-parameter exponential unit-rescaling subgroup `(e^{a_M t}, e^{a_L t}, e^{a_T t})`. -/
noncomputable def expCurve (aM aL aT t : ℝ) : UnitScale :=
  ⟨Real.exp (aM * t), Real.exp (aL * t), Real.exp (aT * t),
    Real.exp_pos _, Real.exp_pos _, Real.exp_pos _⟩

theorem expCurve_zero (aM aL aT : ℝ) : expCurve aM aL aT 0 = one := by
  ext <;> simp [expCurve, one]

end UnitScale

/-- Positive relativistic-gravitational-quantum constants `(G, ℏ, c) ∈ (ℝ_{>0})³`. -/
@[ext]
structure PosGhc where
  G : ℝ
  hbar : ℝ
  c : ℝ
  hG : 0 < G
  hHbar : 0 < hbar
  hC : 0 < c

/-- Exact `(M, L, T)` dimensional action on `(G, ℏ, c)` generated by `mPlanck`:
`G' = (λ_L³ / (λ_M λ_T²)) G`, `ℏ' = (λ_M λ_L² / λ_T) ℏ`, `c' = (λ_L / λ_T) c`. -/
noncomputable def scaleGhc (u : UnitScale) (p : PosGhc) : PosGhc where
  G := (u.lamL ^ 3 / (u.lamM * u.lamT ^ 2)) * p.G
  hbar := (u.lamM * u.lamL ^ 2 / u.lamT) * p.hbar
  c := (u.lamL / u.lamT) * p.c
  hG := by
    have := u.hM; have := u.hL; have := u.hT; have := p.hG
    positivity
  hHbar := by
    have := u.hM; have := u.hL; have := u.hT; have := p.hHbar
    positivity
  hC := by
    have := u.hL; have := u.hT; have := p.hC
    positivity

theorem scaleGhc_one (p : PosGhc) : scaleGhc UnitScale.one p = p := by
  ext <;> simp [scaleGhc, UnitScale.one]

theorem scaleGhc_mul (u v : UnitScale) (p : PosGhc) :
    scaleGhc (UnitScale.mul u v) p = scaleGhc u (scaleGhc v p) := by
  have huM := ne_of_gt u.hM; have huL := ne_of_gt u.hL; have huT := ne_of_gt u.hT
  have hvM := ne_of_gt v.hM; have hvL := ne_of_gt v.hL; have hvT := ne_of_gt v.hT
  ext <;>
    (simp only [scaleGhc, UnitScale.mul]; field_simp)

/-- **Exact Free Transitive Torsor Theorem (`(G, ℏ, c)` under `UnitScale`)**:
For every pair of positive constant triples `p, q ∈ (ℝ_{>0})³` (in particular `q = (1, 1, 1)` Planck units),
there exists a **unique** positive unit rescaling `u = (λ_M, λ_L, λ_T) ∈ (ℝ_{>0})³` mapping `p` to `q`. -/
theorem ghc_unit_rescaling_existsUnique_torsor (p q : PosGhc) :
    ∃! u : UnitScale, scaleGhc u p = q := by
  let rG : ℝ := q.G / p.G
  let rH : ℝ := q.hbar / p.hbar
  let rC : ℝ := q.c / p.c
  have hrG : 0 < rG := div_pos q.hG p.hG
  have hrH : 0 < rH := div_pos q.hHbar p.hHbar
  have hrC : 0 < rC := div_pos q.hC p.hC
  have hpG : p.G ≠ 0 := ne_of_gt p.hG
  have hpH : p.hbar ≠ 0 := ne_of_gt p.hHbar
  have hpC : p.c ≠ 0 := ne_of_gt p.hC
  have hrC_ne : rC ≠ 0 := ne_of_gt hrC
  have hrH_ne : rH ≠ 0 := ne_of_gt hrH
  let rad : ℝ := rG * rH / rC ^ 3
  have hrad_pos : 0 < rad := by positivity
  let s : ℝ := Real.sqrt rad
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hrad_pos
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hs_sq : s ^ 2 = rG * rH / rC ^ 3 := Real.sq_sqrt (le_of_lt hrad_pos)
  let u₀ : UnitScale :=
    { lamM := rH / (s * rC)
      lamL := s
      lamT := s / rC
      hM := by positivity
      hL := hs_pos
      hT := div_pos hs_pos hrC }
  refine ⟨u₀, ?_, ?_⟩
  · ext
    · dsimp only [scaleGhc, u₀]
      have h1 : s ^ 3 / (rH / (s * rC) * (s / rC) ^ 2) = s ^ 2 * rC ^ 3 / rH := by
        field_simp
      have h2 : s ^ 2 * rC ^ 3 / rH = rG := by
        rw [hs_sq]; field_simp
      rw [h1, h2]
      dsimp only [rG]
      field_simp
    · dsimp only [scaleGhc, u₀, rH]
      field_simp
    · dsimp only [scaleGhc, u₀, rC]
      field_simp
  · intro u hu
    have hG_eq : (u.lamL ^ 3 / (u.lamM * u.lamT ^ 2)) * p.G = q.G := congrArg PosGhc.G hu
    have hH_eq : (u.lamM * u.lamL ^ 2 / u.lamT) * p.hbar = q.hbar := congrArg PosGhc.hbar hu
    have hC_eq : (u.lamL / u.lamT) * p.c = q.c := congrArg PosGhc.c hu
    have huM_ne : u.lamM ≠ 0 := ne_of_gt u.hM
    have huL_ne : u.lamL ≠ 0 := ne_of_gt u.hL
    have huT_ne : u.lamT ≠ 0 := ne_of_gt u.hT
    have h_ratioC : u.lamL / u.lamT = rC := by
      dsimp only [rC]; field_simp at hC_eq ⊢; linarith
    have h_ratioH : u.lamM * u.lamL ^ 2 / u.lamT = rH := by
      dsimp only [rH]; field_simp at hH_eq ⊢; linarith
    have h_ratioG : u.lamL ^ 3 / (u.lamM * u.lamT ^ 2) = rG := by
      dsimp only [rG]; field_simp at hG_eq ⊢; linarith
    have h_prod : (u.lamL ^ 3 / (u.lamM * u.lamT ^ 2)) * (u.lamM * u.lamL ^ 2 / u.lamT) =
        u.lamL ^ 2 * (u.lamL / u.lamT) ^ 3 := by
      field_simp
    have h_lamL_sq : u.lamL ^ 2 = s ^ 2 := by
      rw [hs_sq]
      have hmul : u.lamL ^ 2 * rC ^ 3 = rG * rH := by
        calc
          u.lamL ^ 2 * rC ^ 3 = u.lamL ^ 2 * (u.lamL / u.lamT) ^ 3 := by rw [h_ratioC]
          _ = (u.lamL ^ 3 / (u.lamM * u.lamT ^ 2)) * (u.lamM * u.lamL ^ 2 / u.lamT) := h_prod.symm
          _ = rG * rH := by rw [h_ratioG, h_ratioH]
      field_simp; linarith
    have h_lamL : u.lamL = s := by
      have hpos_sum : 0 < u.lamL + s := add_pos u.hL hs_pos
      nlinarith
    have h_lamT : u.lamT = s / rC := by
      rw [h_lamL] at h_ratioC
      field_simp at h_ratioC ⊢
      linarith
    have h_lamM : u.lamM = rH / (s * rC) := by
      have hMH : u.lamM * u.lamL * (u.lamL / u.lamT) = rH := by
        calc
          u.lamM * u.lamL * (u.lamL / u.lamT) = u.lamM * u.lamL ^ 2 / u.lamT := by field_simp
          _ = rH := h_ratioH
      rw [h_ratioC, h_lamL] at hMH
      field_simp
      linarith
    ext
    · exact h_lamM
    · exact h_lamL
    · exact h_lamT

/-- Full 4-parameter gravitational-vacuum constant space `(G, Λ, ℏ, c)` with `G, ℏ, c > 0` and arbitrary `Λ ∈ ℝ`
(covering `Λ > 0` de Sitter/FRW bounce, `Λ = 0` Minkowski, and `Λ < 0` AdS/crunch). -/
@[ext]
structure GravVacuumConstants extends PosGhc where
  Lambda : ℝ

/-- Positive-cone specialization `(G, Λ, ℏ, c) ∈ (ℝ_{>0})⁴` (`Λ > 0`). -/
abbrev PosGravVacuumConstants := { x : GravVacuumConstants // 0 < x.Lambda }

/-- Unit-rescaling action on `(G, Λ, ℏ, c)`: `Λ ↦ λ_L⁻² Λ` alongside `scaleGhc`. -/
noncomputable def scaleGrav (u : UnitScale) (x : GravVacuumConstants) : GravVacuumConstants :=
  { toPosGhc := scaleGhc u x.toPosGhc
    Lambda := (1 / u.lamL ^ 2) * x.Lambda }

theorem scaleGrav_one (x : GravVacuumConstants) : scaleGrav UnitScale.one x = x := by
  ext
  · exact congrArg PosGhc.G (scaleGhc_one x.toPosGhc)
  · exact congrArg PosGhc.hbar (scaleGhc_one x.toPosGhc)
  · exact congrArg PosGhc.c (scaleGhc_one x.toPosGhc)
  · simp [scaleGrav, UnitScale.one]

/-- Positive-cone unit-rescaling action on `(ℝ_{>0})⁴`. -/
noncomputable def scalePosGrav (u : UnitScale) (x : PosGravVacuumConstants) : PosGravVacuumConstants :=
  ⟨scaleGrav u x.1, by
    dsimp only [scaleGrav]
    have := u.hL; have := x.2
    positivity⟩

/-- Squared Planck length `ℓ_P² = G ℏ / c³ > 0`. -/
noncomputable def planckLengthSq (x : GravVacuumConstants) : ℝ :=
  x.G * x.hbar / x.c ^ 3

/-- Planck length `ℓ_P = √(G ℏ / c³) > 0`. -/
noncomputable def planckLength (x : GravVacuumConstants) : ℝ :=
  Real.sqrt (planckLengthSq x)

/-- **Dimensionless Cosmological-Planck Invariant** `I_Λ := G ℏ Λ / c³ = Λ ℓ_P²`. -/
noncomputable def invariantILambda (x : GravVacuumConstants) : ℝ :=
  x.G * x.hbar * x.Lambda / x.c ^ 3

/-- Positive-cone dimensionless invariant `I_Λ : (ℝ_{>0})⁴ → ℝ_{>0}`. -/
noncomputable def posInvariantILambda (x : PosGravVacuumConstants) : { I : ℝ // 0 < I } :=
  ⟨invariantILambda x.1, by
    unfold invariantILambda
    have := x.1.hG; have := x.1.hHbar; have := x.1.hC; have := x.2
    positivity⟩

/-- Canonical Planck-unit gauge section `I ↦ (G=1, Λ=I, ℏ=1, c=1)`. -/
def planckGaugeSection (I : ℝ) : GravVacuumConstants :=
  { G := 1
    hbar := 1
    c := 1
    hG := zero_lt_one
    hHbar := zero_lt_one
    hC := zero_lt_one
    Lambda := I }

theorem invariantILambda_eq_lambda_mul_planckLength_sq (x : GravVacuumConstants) :
    invariantILambda x = x.Lambda * (planckLength x) ^ 2 := by
  unfold invariantILambda planckLength planckLengthSq
  have hpos : 0 ≤ x.G * x.hbar / x.c ^ 3 := by
    have := x.hG; have := x.hHbar; have := x.hC
    positivity
  rw [Real.sq_sqrt hpos]
  ring

theorem invariantILambda_scaleGrav (u : UnitScale) (x : GravVacuumConstants) :
    invariantILambda (scaleGrav u x) = invariantILambda x := by
  unfold invariantILambda scaleGrav scaleGhc
  have := ne_of_gt u.hM; have := ne_of_gt u.hL; have := ne_of_gt u.hT
  have := ne_of_gt x.hC
  field_simp

theorem invariantILambda_section (I : ℝ) :
    invariantILambda (planckGaugeSection I) = I := by
  simp [invariantILambda, planckGaugeSection]

theorem invariantILambda_surjective : Surjective invariantILambda :=
  fun I => ⟨planckGaugeSection I, invariantILambda_section I⟩

theorem posInvariantILambda_surjective : Surjective posInvariantILambda := by
  rintro ⟨I, hI⟩
  refine ⟨⟨planckGaugeSection I, hI⟩, ?_⟩
  ext
  exact invariantILambda_section I

/-- **Complete Unit-Gauge Orbit Theorem**:
Two 4-tuples `(G₁, Λ₁, ℏ₁, c₁)` and `(G₂, Λ₂, ℏ₂, c₂)` lie in the same `(ℝ_{>0})³` unit-rescaling
orbit **if and only if** they share the exact same dimensionless invariant `I_Λ = G ℏ Λ / c³`. -/
theorem same_unit_orbit_iff_eq_invariantILambda (x y : GravVacuumConstants) :
    (∃ u : UnitScale, scaleGrav u x = y) ↔ invariantILambda x = invariantILambda y := by
  constructor
  · rintro ⟨u, rfl⟩
    exact (invariantILambda_scaleGrav u x).symm
  · intro hI
    obtain ⟨u, hu, _⟩ := ghc_unit_rescaling_existsUnique_torsor x.toPosGhc y.toPosGhc
    refine ⟨u, ?_⟩
    have hG_eq : (u.lamL ^ 3 / (u.lamM * u.lamT ^ 2)) * x.G = y.G := congrArg PosGhc.G hu
    have hH_eq : (u.lamM * u.lamL ^ 2 / u.lamT) * x.hbar = y.hbar := congrArg PosGhc.hbar hu
    have hC_eq : (u.lamL / u.lamT) * x.c = y.c := congrArg PosGhc.c hu
    have huM := ne_of_gt u.hM; have huL := ne_of_gt u.hL; have huT := ne_of_gt u.hT
    have hxG := ne_of_gt x.hG; have hxH := ne_of_gt x.hHbar; have hxC := ne_of_gt x.hC
    have hyG := ne_of_gt y.hG; have hyH := ne_of_gt y.hHbar; have hyC := ne_of_gt y.hC
    unfold invariantILambda at hI
    have hLam : (1 / u.lamL ^ 2) * x.Lambda = y.Lambda := by
      have hscale_factor : y.G * y.hbar / y.c ^ 3 =
          u.lamL ^ 2 * (x.G * x.hbar / x.c ^ 3) := by
        rw [← hG_eq, ← hH_eq, ← hC_eq]
        field_simp
      have hy_prod : (y.G * y.hbar / y.c ^ 3) * y.Lambda =
          (x.G * x.hbar / x.c ^ 3) * x.Lambda := by
        calc
          (y.G * y.hbar / y.c ^ 3) * y.Lambda = y.G * y.hbar * y.Lambda / y.c ^ 3 := by ring
          _ = x.G * x.hbar * x.Lambda / x.c ^ 3 := hI.symm
          _ = (x.G * x.hbar / x.c ^ 3) * x.Lambda := by ring
      rw [hscale_factor] at hy_prod
      have hx_pl_ne : x.G * x.hbar / x.c ^ 3 ≠ 0 := by positivity
      have hmul_eq : u.lamL ^ 2 * y.Lambda = x.Lambda := by
        apply mul_right_cancel₀ hx_pl_ne
        linarith
      field_simp
      linarith
    ext
    · exact hG_eq
    · exact hH_eq
    · exact hC_eq
    · exact hLam

/-- **Main Bridge Theorem 1A (`Core v3` `QuotientDescent` on `(G, Λ, ℏ, c)`)**:
By `UEOT.V3.Compression.QuotientDescent.existsUnique_descend`, EVERY unit-rescaling-invariant
physical observable `Obs : GravVacuumConstants → Z` factors **uniquely** through the single
dimensionless cosmological-Planck invariant `invariantILambda : (G, Λ, ℏ, c) ↦ G ℏ Λ / c³`. -/
theorem unit_invariant_observable_existsUnique_descend
    {Z : Type*} (Obs : GravVacuumConstants → Z)
    (hInv : ∀ (u : UnitScale) (x : GravVacuumConstants), Obs (scaleGrav u x) = Obs x) :
    ∃! ObsBar : ℝ → Z, ObsBar ∘ invariantILambda = Obs := by
  apply UEOT.V3.Compression.QuotientDescent.existsUnique_descend
    invariantILambda Obs invariantILambda_surjective
  intro x y hEq
  obtain ⟨u, rfl⟩ := (same_unit_orbit_iff_eq_invariantILambda x y).mpr hEq
  exact (hInv u x).symm

/-- Exact biconditional characterization via `Core v3` `fiberCompatible_iff_existsUnique_descend`. -/
theorem unit_invariant_iff_existsUnique_descend
    {Z : Type*} (Obs : GravVacuumConstants → Z) :
    (∀ (u : UnitScale) (x : GravVacuumConstants), Obs (scaleGrav u x) = Obs x) ↔
      ∃! ObsBar : ℝ → Z, ObsBar ∘ invariantILambda = Obs := by
  constructor
  · exact unit_invariant_observable_existsUnique_descend Obs
  · rintro ⟨ObsBar, hfac, _⟩ u x
    have hfc := UEOT.V3.Compression.QuotientDescent.fiberCompatible_of_comp_eq
      invariantILambda Obs ObsBar hfac
    exact hfc (invariantILambda_scaleGrav u x)

/-- **Main Bridge Theorem 1B (Positive-Cone `(ℝ_{>0})⁴ → ℝ_{>0}` `QuotientDescent`)**:
Every unit-rescaling-invariant observable on `(G, Λ, ℏ, c) ∈ (ℝ_{>0})⁴` descends **uniquely**
to a function of `I_Λ ∈ ℝ_{>0}`. -/
theorem pos_unit_invariant_observable_existsUnique_descend
    {Z : Type*} (Obs : PosGravVacuumConstants → Z)
    (hInv : ∀ (u : UnitScale) (x : PosGravVacuumConstants), Obs (scalePosGrav u x) = Obs x) :
    ∃! ObsBar : { I : ℝ // 0 < I } → Z, ObsBar ∘ posInvariantILambda = Obs := by
  apply UEOT.V3.Compression.QuotientDescent.existsUnique_descend
    posInvariantILambda Obs posInvariantILambda_surjective
  intro x y hEq
  have hI : invariantILambda x.1 = invariantILambda y.1 := congrArg Subtype.val hEq
  obtain ⟨u, hu⟩ := (same_unit_orbit_iff_eq_invariantILambda x.1 y.1).mpr hI
  have hy : scalePosGrav u x = y := Subtype.ext hu
  rw [← hy]
  exact (hInv u x).symm

/-- **Epistemic Honesty / Non-Derivability Theorem (`I_Λ` Remains Free Modulo Unit Gauge)**:
For any `I₁ ≠ I₂` (e.g., `RC05`/`RC12`'s `I_Λ^model ≈ 3.94 × 10⁻⁸²` vs observed `I_Λ^obs ≈ 2.89 × 10⁻¹²²`),
no unit rescaling can connect `planckGaugeSection I₁` to `planckGaugeSection I₂`: `QuotientDescent`
eliminates the 3 unit-gauge degrees `(G, ℏ, c) ~ (1, 1, 1)` while leaving `I_Λ` as an irreducible
physical parameter not determined by `Core v3`. -/
theorem distinct_ILambda_incomparable_unit_orbits {I₁ I₂ : ℝ} (hNe : I₁ ≠ I₂) :
    ¬ ∃ u : UnitScale, scaleGrav u (planckGaugeSection I₁) = planckGaugeSection I₂ := by
  rw [same_unit_orbit_iff_eq_invariantILambda, invariantILambda_section, invariantILambda_section]
  exact hNe

/-- **Direct Bridge to `UEOT.V3.FisherGauge` (`P-INV-02` Fisher Zero Directions)**:
For any sample space `Ω`, measure `μ`, 4-parameter score `score : Ω → Fin 4 → ℝ` on `(G, ℏ, c, Λ)`,
and unit-invariant log-likelihood `logLikRaw x ω = logLikBar (invariantILambda x) ω`, every smooth
1-parameter `(M, L, T)` exponential unit-rescaling curve `UnitScale.expCurve aM aL aT` annihilates the
Fisher information operator `fisherAction μ score v = 0` along its orbit tangent `v`! -/
theorem unit_rescaling_orbit_is_fisher_zero_direction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (score : Ω → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    (logLikBar : ℝ → Ω → ℝ) (x₀ : GravVacuumConstants) (aM aL aT : ℝ)
    (hderiv : ∀ᵐ ω ∂μ,
      HasDerivAt
        (fun t : ℝ => logLikBar (invariantILambda (scaleGrav (UnitScale.expCurve aM aL aT t) x₀)) ω)
        (directionalScore score v ω) 0) :
    fisherAction μ score v = 0 := by
  apply UEOT.V3.FisherGauge.p_inv_02 μ score v
    (fun t ω => logLikBar (invariantILambda (scaleGrav (UnitScale.expCurve aM aL aT t) x₀)) ω)
  · intro ω t
    rw [invariantILambda_scaleGrav, UnitScale.expCurve_zero, scaleGrav_one]
  · exact hderiv

/-! ## 3. Exact 1-Loop `(3,3,1)` SM Beta Coefficients, Collinearity Defect `Δ₁₂₃` & Desert Exclusion -/

/-- Sum of squared weak hypercharges `∑ Y²` across one complete `(3,3,1)` chiral SM generation
`(Q_L, u_R^c, d_R^c, L_L, e_R^c)` with color/weak multiplicities `(6, 3, 3, 2, 1)`. -/
def smGenHyperchargeSqSum : ℚ :=
  3 * 2 * (1 / 6 : ℚ) ^ 2 + 3 * 1 * (-2 / 3 : ℚ) ^ 2 +
    3 * 1 * (1 / 3 : ℚ) ^ 2 + 1 * 2 * (-1 / 2 : ℚ) ^ 2 + 1 * 1 * (1 : ℚ) ^ 2

/-- Unique `SU(5)` hypercharge normalization `k_Y = 3/5` equalizing per-generation Dynkin traces
`k_Y ∑ Y² = Tr_gen(T₂²) = Tr_gen(T₃²) = 2` and yielding tree-level GUT `sin²θ_W⁰ = 3/8`. -/
theorem su5_hypercharge_norm_and_gut_weinberg_angle (kY : ℚ) :
    smGenHyperchargeSqSum = 10 / 3 ∧
      (kY * smGenHyperchargeSqSum = 2 ↔ kY = 3 / 5) ∧
      (3 / 5 : ℚ) / (1 + 3 / 5) = 3 / 8 := by
  have hsum : smGenHyperchargeSqSum = 10 / 3 := by
    unfold smGenHyperchargeSqSum; norm_num
  refine ⟨hsum, ?_, by norm_num⟩
  rw [hsum]
  constructor <;> intro h <;> linarith

/-- Representation-theoretic 1-loop `U(1)_Y` (`SU(5)`-normalized `3/5`), `SU(2)_L`, and `SU(3)_C`
beta coefficients for `nc` colors, `ng` chiral generations, and `nH` complex Higgs doublets. -/
def smBeta1 (ng nH : ℚ) : ℚ :=
  (2 / 3) * ((3 / 5) * (10 / 3) * ng) + (1 / 3) * ((3 / 5) * (1 / 2) * nH)

def smBeta2 (nc ng nH : ℚ) : ℚ :=
  -(11 / 3) * 2 + (2 / 3) * (ng * (nc + 1) * (1 / 2)) + (1 / 3) * (nH * (1 / 2))

def smBeta3 (ng : ℚ) : ℚ :=
  -(11 / 3) * 3 + (2 / 3) * (4 * (1 / 2) * ng)

/-- Exact minimal `(3,3,1)` 1-loop SM beta coefficients `(b₁, b₂, b₃) = (41/10, -19/6, -7)`. -/
theorem sm_one_loop_beta_exact :
    smBeta1 3 1 = 41 / 10 ∧
      smBeta2 3 3 1 = -19 / 6 ∧
      smBeta3 3 = -7 := by
  unfold smBeta1 smBeta2 smBeta3
  norm_num

/-- Complete chiral generations cancel identically from all pairwise 1-loop beta differences `(b_i - b_j)`
for `nc = 3`! -/
theorem sm_beta_differences_generation_independent (ng nH : ℚ) :
    smBeta1 ng nH - smBeta2 3 ng nH = 22 / 3 - nH / 15 ∧
      smBeta2 3 ng nH - smBeta3 ng = 11 / 3 + nH / 6 ∧
      smBeta3 ng - smBeta1 ng nH = -11 - nH / 10 := by
  unfold smBeta1 smBeta2 smBeta3
  refine ⟨by ring, by ring, by ring⟩

/-- 1-loop RGE trajectory `α_i⁻¹(t) = α_i⁻¹(M_Z) - b_i t` where `t = (1 / (2π)) ln(μ / M_Z)`. -/
def oneLoopInvAlpha (a0 b t : ℝ) : ℝ :=
  a0 - b * t

/-- General scale-free 1-loop collinearity defect `Δ₁₂₃ := (b₂ - b₃) α₁⁻¹ + (b₃ - b₁) α₂⁻¹ + (b₁ - b₂) α₃⁻¹`. -/
def collinearityDefect (b1 b2 b3 a1 a2 a3 : ℝ) : ℝ :=
  (b2 - b3) * a1 + (b3 - b1) * a2 + (b1 - b2) * a3

/-- Minimal `(3,3,1)` SM 1-loop collinearity defect `Δ₁₂₃^SM` with `(b₁, b₂, b₃) = (41/10, -19/6, -7)`. -/
noncomputable def delta123SM (a1 a2 a3 : ℝ) : ℝ :=
  collinearityDefect (41 / 10) (-19 / 6) (-7) a1 a2 a3

/-- **Exact 1-Loop RG Scale-Invariance of `Δ₁₂₃`**:
`Δ₁₂₃(α₁⁻¹(t), α₂⁻¹(t), α₃⁻¹(t)) = Δ₁₂₃(α₁⁻¹(0), α₂⁻¹(0), α₃⁻¹(0))` identically for all `t ∈ ℝ`. -/
theorem collinearityDefect_rg_invariant (b1 b2 b3 a1 a2 a3 t : ℝ) :
    collinearityDefect b1 b2 b3
      (oneLoopInvAlpha a1 b1 t) (oneLoopInvAlpha a2 b2 t) (oneLoopInvAlpha a3 b3 t) =
      collinearityDefect b1 b2 b3 a1 a2 a3 := by
  unfold collinearityDefect oneLoopInvAlpha
  ring

/-- **Exact Necessary and Sufficient Condition for Single-Step 1-Loop Desert Unification**:
Whenever `b₁ ≠ b₂`, all three 1-loop inverse couplings meet at a common point `(t_GUT, α_GUT⁻¹)`
**if and only if** the scale-free collinearity defect `collinearityDefect b1 b2 b3 a1 a2 a3` vanishes! -/
theorem single_step_unification_iff_collinearityDefect_zero
    {b1 b2 b3 a1 a2 a3 : ℝ} (hb12 : b1 ≠ b2) :
    (∃ tGUT aGUT : ℝ,
      oneLoopInvAlpha a1 b1 tGUT = aGUT ∧
      oneLoopInvAlpha a2 b2 tGUT = aGUT ∧
      oneLoopInvAlpha a3 b3 tGUT = aGUT) ↔
      collinearityDefect b1 b2 b3 a1 a2 a3 = 0 := by
  have hdiff : b1 - b2 ≠ 0 := sub_ne_zero.mpr hb12
  constructor
  · rintro ⟨tGUT, aGUT, h1, h2, h3⟩
    unfold oneLoopInvAlpha at h1 h2 h3
    have ha1 : a1 = aGUT + b1 * tGUT := by linarith
    have ha2 : a2 = aGUT + b2 * tGUT := by linarith
    have ha3 : a3 = aGUT + b3 * tGUT := by linarith
    rw [ha1, ha2, ha3]
    unfold collinearityDefect
    ring
  · intro hdef
    let t12 : ℝ := (a1 - a2) / (b1 - b2)
    let aGUT : ℝ := a1 - b1 * t12
    refine ⟨t12, aGUT, rfl, ?_, ?_⟩
    · unfold oneLoopInvAlpha
      dsimp only [aGUT, t12]
      field_simp
      ring
    · unfold oneLoopInvAlpha
      dsimp only [aGUT, t12]
      unfold collinearityDefect at hdef
      have h3 : (b1 - b2) * ((a3 - b3 * ((a1 - a2) / (b1 - b2))) -
          (a1 - b1 * ((a1 - a2) / (b1 - b2)))) =
          (b2 - b3) * a1 + (b3 - b1) * a2 + (b1 - b2) * a3 := by
        field_simp
        ring
      rw [hdef] at h3
      have hsub : (a3 - b3 * ((a1 - a2) / (b1 - b2))) -
          (a1 - b1 * ((a1 - a2) / (b1 - b2))) = 0 :=
        (mul_eq_zero.mp h3).resolve_left hdiff
      linarith

/-- Specialization to minimal `(3,3,1)` 1-loop SM (`b₁ - b₂ = 109/15 ≠ 0`). -/
theorem sm_desert_unification_iff_delta123SM_zero (a1 a2 a3 : ℝ) :
    (∃ tGUT aGUT : ℝ,
      oneLoopInvAlpha a1 (41 / 10) tGUT = aGUT ∧
      oneLoopInvAlpha a2 (-19 / 6) tGUT = aGUT ∧
      oneLoopInvAlpha a3 (-7) tGUT = aGUT) ↔
      delta123SM a1 a2 a3 = 0 :=
  single_step_unification_iff_collinearityDefect_zero (by norm_num)

/-- **Exact Georgi–Quinn–Weinberg Decomposition**:
Writing `α₁⁻¹ = (3/5)(1 - s_W²) α_em⁻¹` and `α₂⁻¹ = s_W² α_em⁻¹`, the minimal SM collinearity defect
equals `(23/10 - (67/5) s_W²) α_em⁻¹ + (109/15) α₃⁻¹`, so `Δ₁₂₃^SM = 0` iff
`sin²θ_W(M_Z) = 23/134 + (109/201) (α_em(M_Z) / α_3(M_Z))`. -/
theorem sm_desert_weinberg_angle_iff
    {aEmInv s2W a3 : ℝ} (haEm : aEmInv ≠ 0) :
    let a1 := (3 / 5 : ℝ) * (1 - s2W) * aEmInv
    let a2 := s2W * aEmInv
    delta123SM a1 a2 a3 = (23 / 10 - (67 / 5) * s2W) * aEmInv + (109 / 15) * a3 ∧
      (delta123SM a1 a2 a3 = 0 ↔
        s2W = 23 / 134 + (109 / 201) * (a3 / aEmInv)) := by
  dsimp only
  have hdecomp : delta123SM ((3 / 5 : ℝ) * (1 - s2W) * aEmInv) (s2W * aEmInv) a3 =
      (23 / 10 - (67 / 5) * s2W) * aEmInv + (109 / 15) * a3 := by
    unfold delta123SM collinearityDefect
    ring
  refine ⟨hdecomp, ?_⟩
  rw [hdecomp]
  constructor
  · intro h0
    field_simp
    linarith
  · intro hs2W
    rw [hs2W]
    field_simp
    ring

/-- **Strict Non-Vanishing & PDG-2024 `3σ` Empirical Exclusion of Minimal 1-Loop Desert SM Unification**:
Across EVERY point in the conservative PDG-2024 `3σ` electroweak + QCD box at `M_Z`
(`α_em⁻¹ ∈ [127.924, 127.978]`, `sin²θ_W ∈ [0.23117, 0.23141]`, `α_s ∈ [0.1153, 0.1207]`),
`Δ₁₂₃^SM < -38 < 0`, certifying `Δ₁₂₃^SM ≠ 0` and strictly excluding single-step 1-loop minimal SM
desert gauge unification. -/
theorem pdg2024_3sigma_excludes_sm_desert_unification
    {aEmInv s2W alphaS : ℝ}
    (haEm_lo : 127924 / 1000 ≤ aEmInv) (_haEm_hi : aEmInv ≤ 127978 / 1000)
    (hs2W_lo : 23117 / 100000 ≤ s2W) (_hs2W_hi : s2W ≤ 23141 / 100000)
    (haS_lo : 1153 / 10000 ≤ alphaS) (_haS_hi : alphaS ≤ 1207 / 10000) :
    let a1 := (3 / 5 : ℝ) * (1 - s2W) * aEmInv
    let a2 := s2W * aEmInv
    let a3 := 1 / alphaS
    delta123SM a1 a2 a3 < -38 ∧
      delta123SM a1 a2 a3 ≠ 0 ∧
      ¬ ∃ tGUT aGUT : ℝ,
          oneLoopInvAlpha a1 (41 / 10) tGUT = aGUT ∧
          oneLoopInvAlpha a2 (-19 / 6) tGUT = aGUT ∧
          oneLoopInvAlpha a3 (-7) tGUT = aGUT := by
  dsimp only
  have haEm_pos : 0 < aEmInv := by linarith
  have haS_pos : 0 < alphaS := by linarith
  have hdecomp : delta123SM ((3 / 5 : ℝ) * (1 - s2W) * aEmInv) (s2W * aEmInv) (1 / alphaS) =
      (23 / 10 - (67 / 5) * s2W) * aEmInv + (109 / 15) * (1 / alphaS) := by
    unfold delta123SM collinearityDefect
    ring
  have hcoeff_ub : 23 / 10 - (67 / 5) * s2W ≤ 23 / 10 - (67 / 5) * (23117 / 100000) := by
    linarith
  have hterm1 : (23 / 10 - (67 / 5) * s2W) * aEmInv ≤
      (23 / 10 - (67 / 5) * (23117 / 100000)) * (127924 / 1000) := by
    nlinarith
  have hinv_aS : 1 / alphaS ≤ 10000 / 1153 := by
    rw [div_le_div_iff₀ haS_pos (by norm_num)]
    linarith
  have hlt : delta123SM ((3 / 5 : ℝ) * (1 - s2W) * aEmInv) (s2W * aEmInv) (1 / alphaS) < -38 := by
    rw [hdecomp]
    linarith
  have hne : delta123SM ((3 / 5 : ℝ) * (1 - s2W) * aEmInv) (s2W * aEmInv) (1 / alphaS) ≠ 0 :=
    ne_of_lt (by linarith)
  refine ⟨hlt, hne, ?_⟩
  rw [sm_desert_unification_iff_delta123SM_zero]
  exact hne

/-- **Exact Intermediate-Threshold Matching Identity (`two_step_threshold_collinearity_repair`)**:
If an intermediate threshold at RG scale `t_I` shifts the 1-loop beta coefficients by `(db₁, db₂, db₃)`
and achieves unification `α_i⁻¹(0) - b_i t_GUT - db_i (t_GUT - t_I) = α_GUT⁻¹` at `t_GUT`, then
`Δ₁₂₃` equals `((b₂ - b₃) db₁ + (b₃ - b₁) db₂ + (b₁ - b₂) db₃) (t_GUT - t_I)`; in particular,
complete `SU(5)` multiplets (`db₁ = db₂ = db₃`) leave `Δ₁₂₃ = 0` unchanged and cannot cure desert non-unification. -/
theorem two_step_threshold_collinearity_repair
    (b1 b2 b3 db1 db2 db3 a1 a2 a3 tI tGUT aGUT : ℝ)
    (h1 : a1 - b1 * tGUT - db1 * (tGUT - tI) = aGUT)
    (h2 : a2 - b2 * tGUT - db2 * (tGUT - tI) = aGUT)
    (h3 : a3 - b3 * tGUT - db3 * (tGUT - tI) = aGUT) :
    collinearityDefect b1 b2 b3 a1 a2 a3 =
      collinearityDefect b1 b2 b3 db1 db2 db3 * (tGUT - tI) ∧
      (db1 = db2 ∧ db2 = db3 → collinearityDefect b1 b2 b3 a1 a2 a3 = 0) := by
  have ha1 : a1 = aGUT + b1 * tGUT + db1 * (tGUT - tI) := by linarith
  have ha2 : a2 = aGUT + b2 * tGUT + db2 * (tGUT - tI) := by linarith
  have ha3 : a3 = aGUT + b3 * tGUT + db3 * (tGUT - tI) := by linarith
  rw [ha1, ha2, ha3]
  unfold collinearityDefect
  refine ⟨by ring, ?_⟩
  rintro ⟨h12, h23⟩
  rw [h12, h23]
  ring

end UEOTPhysicsUnification.CoreUnitGaugeAndDimensionlessConstants
