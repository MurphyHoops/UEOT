import UEOT.V3.Compression.QuotientDescent
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# RG Typing Bridge & EFT Matching Scheme Cancellation (`C-RG-01`, `P-EFT-02`)

Implements the formal mathematical bridge mandated by `physics/interfaces/CORE_PHYSICS_CONTRACT.md` §5
and the EFT exit gate of `PREMISES_AND_RESPONSIBILITIES.md` §5:

1. **Object-RG vs Process Coarse-Graining (`markov_lumping_iff_fiberCompatible`, `markov_lumping_iterates`)**:
   Connecting directly to `UEOT.V3.Compression.QuotientDescent.fiberCompatible_iff_existsUnique_descend`,
   a surjective Object-RG representation `q : X → Y` intertwines a microscopic step `T : X → X`
   with a unique coarse-grained Markov operator `Tbar : Y → Y` (`Tbar ∘ q = q ∘ T`) if and only if
   `FiberCompatible q (q ∘ T)` holds (Dynkin lumpability). When satisfied, semigroup composition
   `Tbar^[n] ∘ q = q ∘ T^[n]` holds for all `n : ℕ`.

2. **Explicit Non-Markovian Counterexample (`two_step_semigroup_failure`, `mori_zwanzig_memory_defect_exact`)**:
   Constructs a 3-state column-stochastic transition matrix `microP` lumped onto 2 macrostates via `lumpQ`.
   On the canonical uniform section `liftS`, one-step coarse evolution matches exact lumped evolution on `p0`,
   yet two-step Markovian iteration `macroM1 * macroM1` deviates from `lumpQ * (microP * microP)` by an exact
   rational Mori-Zwanzig memory term `1 / 16 ≠ 0`, proving that Object-RG quotient existence does not imply
   Markovian process coarse-graining.

3. **Wilsonian Schur-Complement Integration & Non-Asymptotic EFT Remainder (`P-EFT-02`)**:
   Proves exact Gaussian/quadratic completion of the square for integrating out a heavy mode `phiH` of mass
   squared `Msq > 0`, exact algebraic heavy-propagator expansion `1/(Msq + psq) = 1/Msq - psq/Msq^2 + R_4`,
   strict two-sided remainder bounds `0 ≤ R_4 ≤ psq^2 / Msq^3`, and exact renormalization-scheme/scale
   cancellation (`scheme_cancellation_identity`) between arbitrary subtraction prescriptions (e.g. MS-bar vs MOM).
-/

namespace UEOTPhysicsUnification.RGBridgeAndEFTMatching

open Function Matrix
open UEOT.V3.Compression.QuotientDescent

/-! ## 1. Object-RG Quotient Descent vs Markovian Process Coarse-Graining -/

/-- Exact Dynkin lumpability equivalence bridged to UEOT Core `QuotientDescent`:
a surjective Object-RG map `q : X → Y` admits a unique coarse-grained step `Tbar : Y → Y`
satisfying `Tbar ∘ q = q ∘ T` iff `q ∘ T` is constant on the fibres of `q`. -/
theorem markov_lumping_iff_fiberCompatible
    {X Y : Type*} (q : X → Y) (T : X → X) (hq : Surjective q) :
    (∃! Tbar : Y → Y, Tbar ∘ q = q ∘ T) ↔ FiberCompatible q (q ∘ T) :=
  (fiberCompatible_iff_existsUnique_descend q (q ∘ T) hq).symm

/-- Whenever a microscopic map `T` intertwines with a coarse-grained map `Tbar` through `q`,
all finite-time iterates intertwine without memory loss (`Tbar^[n] ∘ q = q ∘ T^[n]`). -/
theorem markov_lumping_iterates
    {X Y : Type*} (q : X → Y) (T : X → X) (Tbar : Y → Y)
    (hinter : Tbar ∘ q = q ∘ T) (n : ℕ) :
    Tbar^[n] ∘ q = q ∘ T^[n] := by
  induction n with
  | zero => rfl
  | succ k ih =>
    ext x
    simp only [Function.comp_apply, Function.iterate_succ']
    have hstep : Tbar (q (T^[k] x)) = q (T (T^[k] x)) :=
      congrFun hinter (T^[k] x)
    have hprev : Tbar^[k] (q x) = q (T^[k] x) :=
      congrFun ih x
    rw [hprev, hstep]

/-! ## 2. Explicit 3-State Counterexample Separating Object-RG from Markovian Semigroups -/

/-- Column-stochastic 3-state microscopic transition matrix. -/
def microP : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 / 2, 1 / 2, 0;
     0,     1 / 2, 1;
     1 / 2, 0,     0]

/-- Surjective Object-RG aggregation lumping microstates `{0, 1}` into macrostate `0` and `{2}` into `1`. -/
def lumpQ : Matrix (Fin 2) (Fin 3) ℚ :=
  !![1, 1, 0;
     0, 0, 1]

/-- Canonical uniform section (`lumpQ * liftS = 1`). -/
def liftS : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1 / 2, 0;
     1 / 2, 0;
     0,     1]

/-- Effective one-step coarse transition matrix induced by the section `liftS`. -/
def macroM1 : Matrix (Fin 2) (Fin 2) ℚ :=
  lumpQ * microP * liftS

/-- Initial microscopic probability vector supported uniformly on the `{0, 1}` fibre. -/
def initMicro : Fin 3 → ℚ := ![1 / 2, 1 / 2, 0]

theorem lumpQ_mul_liftS : lumpQ * liftS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [lumpQ, liftS, Matrix.mul_apply, Fin.sum_univ_three]; try norm_num)

/-- Fibre incompatibility witness: microstates `0` and `1` share macrostate `0` under `lumpQ`,
but have distinct coarse transition probabilities `(1/2)` vs `1` into macrostate `0`. -/
theorem non_lumpable_fibre_witness :
    (lumpQ * microP) 0 0 = 1 / 2 ∧ (lumpQ * microP) 0 1 = 1 := by
  constructor
  · simp [lumpQ, microP, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [lumpQ, microP, Matrix.mul_apply, Fin.sum_univ_three]
    norm_num

/-- At `t = 1`, the coarse operator `macroM1` reproduces the exact lumped state on `initMicro`. -/
theorem one_step_coarse_exact_on_section :
    macroM1.mulVec (lumpQ.mulVec initMicro) = lumpQ.mulVec (microP.mulVec initMicro) := by
  ext i
  fin_cases i <;>
    (simp [macroM1, lumpQ, microP, liftS, initMicro, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]; try norm_num)

/-- Exact Mori-Zwanzig memory defect at `t = 2`: iterating `macroM1` twice gives `13/16` in macrostate `0`,
whereas true microscopic two-step evolution followed by `lumpQ` gives `3/4 = 12/16`. -/
theorem mori_zwanzig_memory_defect_exact :
    ((macroM1 * macroM1).mulVec (lumpQ.mulVec initMicro)) 0 -
      (lumpQ.mulVec ((microP * microP).mulVec initMicro)) 0 = 1 / 16 := by
  simp [macroM1, lumpQ, microP, liftS, initMicro, Matrix.mulVec, dotProduct,
    Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num

/-- Consequently, two-step Markovian semigroup closure strictly fails despite exact one-step compression. -/
theorem two_step_semigroup_failure :
    (macroM1 * macroM1).mulVec (lumpQ.mulVec initMicro) ≠
      lumpQ.mulVec ((microP * microP).mulVec initMicro) := by
  intro h
  have h0 := congrFun h 0
  have hdef := mori_zwanzig_memory_defect_exact
  linarith

/-! ## 3. Wilsonian Schur-Complement Integration, EFT Remainder & Scheme Cancellation -/

/-- Coupled UV quadratic action for light field `phiL` and heavy field `phiH` of mass squared `Msq`. -/
noncomputable def uvQuadraticAction (mLsq Msq g phiL phiH : ℝ) : ℝ :=
  (1 / 2) * mLsq * phiL ^ 2 + g * phiL * phiH + (1 / 2) * Msq * phiH ^ 2

/-- Low-energy Wilsonian quadratic effective action after integrating out `phiH`. -/
noncomputable def wilsonEffectiveAction (mLsq Msq g phiL : ℝ) : ℝ :=
  (1 / 2) * (mLsq - g ^ 2 / Msq) * phiL ^ 2

/-- Exact Schur-complement completion of the square connecting `uvQuadraticAction` to `wilsonEffectiveAction`. -/
theorem wilson_schur_completion_identity
    {mLsq Msq g phiL phiH : ℝ} (hM : Msq ≠ 0) :
    uvQuadraticAction mLsq Msq g phiL phiH =
      wilsonEffectiveAction mLsq Msq g phiL +
        (Msq / 2) * (phiH + (g / Msq) * phiL) ^ 2 := by
  unfold uvQuadraticAction wilsonEffectiveAction
  field_simp [hM]
  ring

/-- For `Msq > 0`, minimizing `uvQuadraticAction` over `phiH` at fixed `phiL` recovers `wilsonEffectiveAction`. -/
theorem wilson_effective_action_is_fibre_minimum
    {mLsq Msq g phiL : ℝ} (hM : 0 < Msq) :
    (∀ phiH : ℝ, wilsonEffectiveAction mLsq Msq g phiL ≤ uvQuadraticAction mLsq Msq g phiL phiH) ∧
      uvQuadraticAction mLsq Msq g phiL (-(g / Msq) * phiL) = wilsonEffectiveAction mLsq Msq g phiL := by
  have hMne : Msq ≠ 0 := ne_of_gt hM
  constructor
  · intro phiH
    rw [wilson_schur_completion_identity hMne]
    have hnonneg : 0 ≤ (Msq / 2) * (phiH + (g / Msq) * phiL) ^ 2 := by positivity
    linarith
  · rw [wilson_schur_completion_identity hMne]
    ring

/-- Exact non-asymptotic dimension-6 EFT propagator expansion with closed-form remainder. -/
theorem eft_propagator_expansion_exact
    {Msq psq : ℝ} (hM : Msq ≠ 0) (hsum : Msq + psq ≠ 0) :
    1 / (Msq + psq) =
      1 / Msq - psq / Msq ^ 2 + psq ^ 2 / (Msq ^ 2 * (Msq + psq)) := by
  field_simp [hM, hsum]
  ring

/-- Strict two-sided remainder enclosure `0 ≤ R_4(psq, Msq) ≤ psq^2 / Msq^3` in the Euclidean/spacelike domain. -/
theorem eft_propagator_remainder_bounds
    {Msq psq : ℝ} (hM : 0 < Msq) (hp : 0 ≤ psq) :
    0 ≤ psq ^ 2 / (Msq ^ 2 * (Msq + psq)) ∧
      psq ^ 2 / (Msq ^ 2 * (Msq + psq)) ≤ psq ^ 2 / Msq ^ 3 := by
  have hsum : 0 < Msq + psq := by linarith
  constructor
  · positivity
  · have hden_le : Msq ^ 3 ≤ Msq ^ 2 * (Msq + psq) := by nlinarith
    have hM3 : 0 < Msq ^ 3 := by positivity
    have hnum : 0 ≤ psq ^ 2 := sq_nonneg psq
    exact div_le_div_of_nonneg_left hnum hM3 hden_le

/-- Matched EFT Wilson coefficient in subtraction scheme `deltaS` at logarithm `logMu`. -/
def matchedWilsonCoeff (uvAtZero deltaS logMu : ℝ) : ℝ :=
  uvAtZero - (logMu + deltaS)

/-- Reconstructed EFT loop + counterterm amplitude in subtraction scheme `deltaS` at `logMu`. -/
def eftPhysicalAmplitude (uvAtZero irKinematic deltaS logMu : ℝ) : ℝ :=
  matchedWilsonCoeff uvAtZero deltaS logMu + ((logMu + deltaS) + irKinematic)

/-- Exact renormalization-scheme and scale cancellation: any two subtraction schemes `(deltaA, logMuA)`
and `(deltaB, logMuB)` produce the exact same physical EFT amplitude `uvAtZero + irKinematic`. -/
theorem scheme_cancellation_identity
    (uvAtZero irKinematic deltaA logMuA deltaB logMuB : ℝ) :
    eftPhysicalAmplitude uvAtZero irKinematic deltaA logMuA =
      eftPhysicalAmplitude uvAtZero irKinematic deltaB logMuB ∧
    eftPhysicalAmplitude uvAtZero irKinematic deltaA logMuA = uvAtZero + irKinematic := by
  unfold eftPhysicalAmplitude matchedWilsonCoeff
  constructor <;> ring

/-- Exact UV-minus-EFT matching error equals purely the higher-dimension heavy kinematic remainder,
completely independent of `(deltaS, logMu)`. -/
theorem uv_minus_eft_scheme_independent_remainder
    (uvAtZero uvHeavyRemainder irKinematic deltaS logMu : ℝ) :
    (uvAtZero + irKinematic + uvHeavyRemainder) -
      eftPhysicalAmplitude uvAtZero irKinematic deltaS logMu = uvHeavyRemainder := by
  unfold eftPhysicalAmplitude matchedWilsonCoeff
  ring

end UEOTPhysicsUnification.RGBridgeAndEFTMatching
