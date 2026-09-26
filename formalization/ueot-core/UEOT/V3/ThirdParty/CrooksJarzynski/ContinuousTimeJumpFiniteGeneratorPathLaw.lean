/-
Copyright (c) 2026 kiyo-e. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kiyo-e
Modified for UEOT Core v3 integration in 2026: module import paths only.
-/
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpFiniteGenerator
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpLocalBalance
import UEOT.V3.ThirdParty.CrooksJarzynski.ContinuousTimeJumpRenewalIntegrals

/-!
# Fixed-initial sector laws for a general finite-state jump generator

For a `FiniteJumpGenerator` on a finite state space this module builds the
`n`-jump sector law started from a prescribed state, and evaluates its mass as a
finite sum over state sequences.

The reference measure is the unsymmetrized counting reference
`rawCountingReference`, the general-generator analogue of the two-state
`rawSectorReference`.  A fixed-initial law must not average a path with its
time reversal, so the fixed-initial construction uses the raw reference
directly.  The driven-balance layer later proves that the raw reference is
itself reversal invariant and agrees with the symmetrized `countingReference`,
so nothing downstream depends on the symmetrization step.

The rate factors are segment-indexed and constant along each segment, exactly as
in `ContinuousTimeJump.density`; nothing in this module depends on absolute
calendar time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators unitInterval

namespace CrooksJarzynski
namespace MeasureProtocol
namespace ContinuousTimeJump

-- `residual` is deliberately left qualified: `_root_.residual` is Mathlib's
-- topological residual filter, so opening the name here would be ambiguous.
open Simplex (cubeExpWeight)
open Renewal (ratePrefixProduct)

universe u

/-! ### Prefactor-free renewal slice

These are statements about a bare rate vector, with none of the jump-rate or
escape-rate prefactors the sector integrals carry.  Keeping them prefactor-free
is what lets the general generator use them: its density carries a product of
jump rates, not of escape rates, so the two cannot be matched under a common
prefactor.  The shared rate-vector lemmas live in the neutral `Renewal`
namespace. -/

/-- Survival integral of the free coordinates alone: the mass of paths whose
first `n` holding intervals fit inside the horizon. -/
noncomputable def arrivalOn {n : ℕ} (r : Fin n → NNReal) (T : NNReal) : ℝ≥0∞ :=
  ∫⁻ u in Simplex.freeSimplexSet n, cubeExpWeight r T u

/-- Survival integral including the residual final segment, held at rate `c`. -/
noncomputable def sectorOn {n : ℕ} (r : Fin n → NNReal) (c T : NNReal) : ℝ≥0∞ :=
  ∫⁻ u in Simplex.freeSimplexSet n,
    cubeExpWeight r T u *
      ENNReal.ofReal
        (Real.exp
          (-((c : ℝ) * (T : ℝ) * Simplex.residual u)))

/-- One renewal slice without prefactors: either the path stops in the final
segment, or it jumps once more. -/
theorem sectorOn_add_arrivalOn_succ
    {n : ℕ} (r : Fin (n + 1) → NNReal) (T : NNReal) :
    sectorOn (fun i : Fin n => r i.castSucc) (r (Fin.last n)) T +
        ((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) * arrivalOn r T =
      arrivalOn (fun i : Fin n => r i.castSucc) T := by
  unfold sectorOn arrivalOn
  rw [Renewal.lintegral_cubeExpWeight_succ r T,
    ← lintegral_add_left (by fun_prop)]
  apply setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n)
  intro v hv
  dsimp only
  have hsum : (∑ i, ((v i : ℝ))) ≤ 1 := hv
  have hres0 : 0 ≤ Simplex.residual v := by
    unfold Simplex.residual
    linarith
  have hx : 0 ≤ (r (Fin.last n) : ℝ) * (T : ℝ) *
      Simplex.residual v := by positivity
  have hexp1 :
      Real.exp
          (-((r (Fin.last n) : ℝ) * (T : ℝ) *
            Simplex.residual v)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.mpr hx)
  rw [← mul_add, ← ENNReal.ofReal_add (Real.exp_nonneg _) (by linarith)]
  rw [show Real.exp
        (-((r (Fin.last n) : ℝ) * (T : ℝ) *
          Simplex.residual v)) +
      (1 - Real.exp
        (-((r (Fin.last n) : ℝ) * (T : ℝ) *
          Simplex.residual v))) = 1 from by ring]
  simp

namespace FiniteJumpGenerator

variable {Ω : Type u} [Fintype Ω] [DecidableEq Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-! ### The unsymmetrized counting reference -/

/-- The counting reference before symmetrization.  This is the general-generator
analogue of the two-state `rawSectorReference`. -/
noncomputable def rawCountingReference
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    Measure (JumpPath Ω n) :=
  simplexSectorMass T n •
    Simplex.rawPathProbability T (G.stateSequenceCountingReference n)

/-- The scaled uniform simplex law is the restricted Lebesgue law scaled by the
horizon power. -/
theorem simplexSectorMass_smul_freeSimplexProbability (T : NNReal) (n : ℕ) :
    simplexSectorMass T n • Simplex.freeSimplexProbability n =
      (T : ℝ≥0∞) ^ n •
        (volume : Measure (Fin n → I)).restrict (Simplex.freeSimplexSet n) := by
  unfold simplexSectorMass Simplex.freeSimplexProbability ProbabilityTheory.cond
  rw [smul_smul]
  congr 1
  have hpos := Simplex.volume_freeSimplexSet_pos n
  have hfinite :
      (volume : Measure (Fin n → I)) (Simplex.freeSimplexSet n) ≠ ∞ := by
    rw [Simplex.volume_freeSimplexSet]
    exact ENNReal.ofReal_ne_top
  rw [mul_assoc, ENNReal.mul_inv_cancel hpos.ne' hfinite, mul_one]

omit [DecidableEq Ω] [MeasurableSingletonClass Ω] in
/-- The raw counting reference in explicit product-chart form. -/
theorem rawCountingReference_eq
    (G : FiniteJumpGenerator Ω) (T : NNReal) (n : ℕ) :
    G.rawCountingReference T n =
      ((G.stateSequenceCountingReference n).prod
        ((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n))).map
        (Simplex.assemblePath T) := by
  unfold rawCountingReference Simplex.rawPathProbability
  rw [← Measure.map_smul, ← Measure.prod_smul_right,
    simplexSectorMass_smul_freeSimplexProbability]

/-! ### The fixed-initial sector law -/

/-- Density against the counting reference that fixes the initial state to `x`.
Counting measure gives every state sequence unit mass, so no normalizing factor
is needed. -/
def fixedInitialWeight (x : Ω) : Ω → ℝ≥0∞ :=
  fun s => if s = x then 1 else 0

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
@[simp]
theorem fixedInitialWeight_self (x : Ω) : fixedInitialWeight x x = 1 := by
  simp [fixedInitialWeight]

omit [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem fixedInitialWeight_of_ne {x s : Ω} (h : s ≠ x) :
    fixedInitialWeight x s = 0 := by
  simp [fixedInitialWeight, h]

/-- The `n`-jump sector law of the generator, started from `x`. -/
noncomputable def sectorLawFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    Measure (JumpPath Ω n) :=
  pathMeasure (G.rawCountingReference T n)
    (JumpPath.rateDensity (fixedInitialWeight x)
      G.pathEscapeRate G.pathJumpRate)

omit [DecidableEq Ω] in
theorem measurable_rateDensity
    (G : FiniteJumpGenerator Ω) (w : Ω → ℝ≥0∞) (n : ℕ) :
    Measurable
      (JumpPath.rateDensity w
        (G.pathEscapeRate (n := n)) (G.pathJumpRate (n := n))) := by
  have hw : Measurable w := Measurable.of_discrete
  unfold JumpPath.rateDensity JumpPath.density
    JumpPath.holdingWeightOfEscapeRate JumpPath.jumpWeightOfRate
    pathEscapeRate pathJumpRate
  fun_prop

/-! ### Sector mass as a finite sum over state sequences -/

/-- The escape rates seen by the free holding coordinates along a state
sequence.  Coordinate `i` is spent in state `states i.castSucc`. -/
def stateEscapeRates (G : FiniteJumpGenerator Ω) {n : ℕ}
    (states : Fin (n + 1) → Ω) : Fin n → NNReal :=
  fun i => G.escapeRate (states i.castSucc)

/-- The product of the jump rates realized by a state sequence. -/
noncomputable def jumpProduct (G : FiniteJumpGenerator Ω) {n : ℕ}
    (states : Fin (n + 1) → Ω) : ℝ≥0∞ :=
  ∏ i : Fin n, (G.jumpRate (states i.castSucc) (states i.succ) : ℝ≥0∞)

omit [DecidableEq Ω] [MeasurableSingletonClass Ω] in
/-- The rate density in the product chart factorizes into the initial weight,
the survival factors of the free coordinates, the realized jump rates, and the
survival factor of the residual final segment. -/
theorem rateDensity_assemblePath
    (G : FiniteJumpGenerator Ω) (w : Ω → ℝ≥0∞) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) (u : Fin n → I)
    (hu : u ∈ Simplex.freeSimplexSet n) :
    JumpPath.rateDensity w G.pathEscapeRate G.pathJumpRate
        (Simplex.assemblePath T (states, u)) =
      w (states 0) * cubeExpWeight (G.stateEscapeRates states) T u *
        G.jumpProduct states *
          ENNReal.ofReal
            (Real.exp
              (-((G.escapeRate (states (Fin.last n)) : ℝ) *
                (T : ℝ) * Simplex.residual u))) := by
  have hsum : (∑ i, Simplex.unitNNReal (u i)) ≤ (1 : NNReal) := by
    change (∑ i, (Simplex.unitNNReal (u i) : ℝ)) ≤ 1 at hu
    exact_mod_cast hu
  have hscaled : (∑ i, T * Simplex.unitNNReal (u i)) ≤ T := by
    rw [← Finset.mul_sum]
    simpa using mul_le_mul_right hsum T
  have hlast :
      ((T - ∑ i, T * Simplex.unitNNReal (u i) : NNReal) : ℝ) =
        (T : ℝ) * Simplex.residual u := by
    rw [NNReal.coe_sub hscaled, NNReal.coe_sum]
    simp only [Simplex.residual, NNReal.coe_mul,
      Simplex.coe_unitNNReal]
    rw [← Finset.mul_sum]
    ring
  simp only [JumpPath.rateDensity, JumpPath.density,
    JumpPath.holdingWeightOfEscapeRate, JumpPath.jumpWeightOfRate,
    pathEscapeRate, pathJumpRate, Simplex.assemblePath,
    Simplex.holdingTimesOfFree, Fin.snoc_castSucc, Fin.snoc_last,
    stateEscapeRates, jumpProduct, cubeExpWeight,
    Simplex.coe_unitNNReal, NNReal.coe_mul, hlast, ← mul_assoc]
  rw [Finset.prod_mul_distrib]
  ac_rfl

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem jumpProduct_ne_top
    (G : FiniteJumpGenerator Ω) {n : ℕ} (states : Fin (n + 1) → Ω) :
    G.jumpProduct states ≠ ∞ := by
  unfold jumpProduct
  exact ENNReal.prod_ne_top fun i _ => ENNReal.coe_ne_top

/-- The holding-time integral of one state sequence: the free coordinates carry
the survival factors of the intermediate segments and the residual carries the
final one. -/
noncomputable def holdingIntegral
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) : ℝ≥0∞ :=
  ∫⁻ u in Simplex.freeSimplexSet n,
    cubeExpWeight (G.stateEscapeRates states) T u *
      ENNReal.ofReal
        (Real.exp
          (-((G.escapeRate (states (Fin.last n)) : ℝ) *
            (T : ℝ) * Simplex.residual u)))

/-- The unnormalized mass a single state sequence contributes to its jump-count
sector. -/
noncomputable def sequenceMass
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n * G.jumpProduct states * G.holdingIntegral T states

omit [DecidableEq Ω] [MeasurableSingletonClass Ω] in
/-- The rate density of one state sequence integrates over the scaled simplex
chart to that sequence's mass, weighted by the initial density. -/
theorem lintegral_rateDensity_assemblePath
    (G : FiniteJumpGenerator Ω) (w : Ω → ℝ≥0∞) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) (hw : w (states 0) ≠ ∞) :
    ∫⁻ u, JumpPath.rateDensity w G.pathEscapeRate G.pathJumpRate
          (Simplex.assemblePath T (states, u))
        ∂((T : ℝ≥0∞) ^ n •
          (volume : Measure (Fin n → I)).restrict
            (Simplex.freeSimplexSet n)) =
      w (states 0) * G.sequenceMass T states := by
  rw [lintegral_smul_measure, smul_eq_mul]
  rw [setLIntegral_congr_fun (Simplex.measurableSet_freeSimplexSet n)
    (fun u hu => G.rateDensity_assemblePath w T states u hu)]
  have hreorder : ∀ u : Fin n → I,
      w (states 0) * cubeExpWeight (G.stateEscapeRates states) T u *
          G.jumpProduct states *
            ENNReal.ofReal
              (Real.exp
                (-((G.escapeRate (states (Fin.last n)) : ℝ) *
                  (T : ℝ) * Simplex.residual u))) =
        (w (states 0) * G.jumpProduct states) *
          (cubeExpWeight (G.stateEscapeRates states) T u *
            ENNReal.ofReal
              (Real.exp
                (-((G.escapeRate (states (Fin.last n)) : ℝ) *
                  (T : ℝ) * Simplex.residual u)))) := by
    intro u
    ac_rfl
  simp_rw [hreorder]
  rw [lintegral_const_mul' _ _
    (ENNReal.mul_ne_top hw (G.jumpProduct_ne_top states))]
  unfold sequenceMass holdingIntegral
  ac_rfl

/-! ### Folding the branching sum over the last state

Summing a sector quantity over the appended state is what turns the jump-rate
prefactor of the physical density into the escape-rate prefactor of the
arrival integrals.  It is the general-generator replacement for the two-state
degeneracy `jumpRate x (flip x) = escapeRate x`, and it only becomes available
after summing over state sequences. -/

/-- Splitting a state sequence into its initial segment and its final state. -/
def snocEquiv (Ω : Type u) (n : ℕ) :
    ((Fin (n + 1) → Ω) × Ω) ≃ (Fin (n + 2) → Ω) where
  toFun p := Fin.snoc p.1 p.2
  invFun s := (Fin.init s, s (Fin.last (n + 1)))
  left_inv := by
    intro p
    simp
  right_inv := by
    intro s
    simp

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The free holding coordinates never see the appended final state: coordinate
`i` is spent in state `init i`. -/
@[simp]
theorem stateEscapeRates_snoc
    (G : FiniteJumpGenerator Ω) {n : ℕ} (init : Fin (n + 1) → Ω) (z : Ω) :
    G.stateEscapeRates (Fin.snoc init z) = fun i => G.escapeRate (init i) := by
  funext i
  simp [stateEscapeRates]

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Appending a state multiplies the jump product by the rate of the new final
jump. -/
theorem jumpProduct_snoc
    (G : FiniteJumpGenerator Ω) {n : ℕ} (init : Fin (n + 1) → Ω) (z : Ω) :
    G.jumpProduct (Fin.snoc init z) =
      G.jumpProduct init *
        (G.jumpRate (init (Fin.last n)) z : ℝ≥0∞) := by
  unfold jumpProduct
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · simp

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The branching sum: summing the jump product over the appended state folds
the last jump rate into the escape rate of the state it leaves. -/
theorem sum_jumpProduct_snoc
    (G : FiniteJumpGenerator Ω) {n : ℕ} (init : Fin (n + 1) → Ω) :
    ∑ z : Ω, G.jumpProduct (Fin.snoc init z) =
      G.jumpProduct init * (G.escapeRate (init (Fin.last n)) : ℝ≥0∞) := by
  simp only [jumpProduct_snoc, ← Finset.mul_sum]
  congr 1
  simp [escapeRate]

/-! ### Telescoping the sector masses -/

/-- The mass of paths from `states 0` whose first `n` jumps realize `states` and
all fit inside the horizon.  Unlike `sequenceMass` there is no survival factor
on the final segment: the path is free to jump again. -/
noncomputable def sequenceArrivalMass
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) : ℝ≥0∞ :=
  (T : ℝ≥0∞) ^ n * G.jumpProduct states *
    arrivalOn (G.stateEscapeRates states) T

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem sequenceMass_eq_sectorOn
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (states : Fin (n + 1) → Ω) :
    G.sequenceMass T states =
      (T : ℝ≥0∞) ^ n * G.jumpProduct states *
        sectorOn (G.stateEscapeRates states)
          (G.escapeRate (states (Fin.last n))) T :=
  rfl

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- One renewal step for a fixed initial segment: the sector that stops after
`n` jumps plus the paths that jump once more, summed over where they jump to,
exhaust the paths whose first `n` jumps fit. -/
theorem sequenceMass_add_sum_sequenceArrivalMass_snoc
    (G : FiniteJumpGenerator Ω) (T : NNReal) {n : ℕ}
    (init : Fin (n + 1) → Ω) :
    G.sequenceMass T init +
        ∑ z : Ω, G.sequenceArrivalMass T (Fin.snoc init z) =
      G.sequenceArrivalMass T init := by
  set r : Fin (n + 1) → NNReal := fun i => G.escapeRate (init i) with hr
  have hcast : G.stateEscapeRates init = fun i : Fin n => r i.castSucc := rfl
  have hlast : G.escapeRate (init (Fin.last n)) = r (Fin.last n) := rfl
  have hsnoc : ∀ z : Ω,
      G.sequenceArrivalMass T (Fin.snoc init z) =
        (T : ℝ≥0∞) ^ (n + 1) * G.jumpProduct (Fin.snoc init z) *
          arrivalOn r T := by
    intro z
    unfold sequenceArrivalMass
    rw [G.stateEscapeRates_snoc init z]
  simp only [hsnoc, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [G.sum_jumpProduct_snoc init]
  rw [G.sequenceMass_eq_sectorOn T init, hcast, hlast]
  unfold sequenceArrivalMass
  rw [hcast]
  rw [show ((T : ℝ≥0∞) ^ (n + 1) *
        (G.jumpProduct init * (G.escapeRate (init (Fin.last n)) : ℝ≥0∞))) *
        arrivalOn r T =
      ((T : ℝ≥0∞) ^ n * G.jumpProduct init) *
        (((r (Fin.last n) : ℝ≥0∞) * (T : ℝ≥0∞)) * arrivalOn r T) from by
    rw [pow_succ]
    ring]
  rw [← mul_add, sectorOn_add_arrivalOn_succ r T]

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω] in
@[simp]
theorem snoc_zero {n : ℕ} (init : Fin (n + 1) → Ω) (z : Ω) :
    (Fin.snoc init z : Fin (n + 2) → Ω) 0 = init 0 := by
  rw [← Fin.castSucc_zero, Fin.snoc_castSucc]

/-- The mass the `n`-jump sector receives from a prescribed initial state. -/
noncomputable def sectorMassFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → Ω,
    fixedInitialWeight x (states 0) * G.sequenceMass T states

/-- The mass of paths from `x` whose first `n` jumps fit inside the horizon. -/
noncomputable def arrivalMassFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → Ω,
    fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Consecutive arrival masses differ by exactly one sector mass.  Summing over
state sequences is what makes the branching identity
`∑ z, jumpRate x z = escapeRate x` available, so this is the general-generator
replacement for the two-state telescoping step. -/
theorem sectorMassFrom_add_arrivalMassFrom_succ
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    G.sectorMassFrom T x n + G.arrivalMassFrom T x (n + 1) =
      G.arrivalMassFrom T x n := by
  have hreindex :
      G.arrivalMassFrom T x (n + 1) =
        ∑ init : Fin (n + 1) → Ω,
          fixedInitialWeight x (init 0) *
            ∑ z : Ω, G.sequenceArrivalMass T (Fin.snoc init z) := by
    unfold arrivalMassFrom
    rw [← Fintype.sum_equiv (snocEquiv Ω n)
      (fun p : (Fin (n + 1) → Ω) × Ω =>
        fixedInitialWeight x ((Fin.snoc p.1 p.2 : Fin (n + 2) → Ω) 0) *
          G.sequenceArrivalMass T (Fin.snoc p.1 p.2))
      _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun init _ => by
      simp [Finset.mul_sum]
  rw [hreindex]
  unfold sectorMassFrom
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun init _ => ?_
  rw [← mul_add, G.sequenceMass_add_sum_sequenceArrivalMass_snoc T init]

/-! ### The vanishing tail

The number of state sequences grows like `|Ω| ^ n`, so a per-sequence bound is
useless.  The branching sum has to be folded at every step first, which is
exactly what turns the jump-rate products into powers of a single rate bound. -/

/-- A uniform bound on the escape rates.  The total rate out of all states is
crude but costs nothing on a finite state space. -/
noncomputable def rateBound (G : FiniteJumpGenerator Ω) : NNReal :=
  ∑ x, G.escapeRate x

omit [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem escapeRate_le_rateBound (G : FiniteJumpGenerator Ω) (x : Ω) :
    G.escapeRate x ≤ G.rateBound :=
  Finset.single_le_sum (f := G.escapeRate) (fun _ _ => zero_le) (Finset.mem_univ x)

/-- Total jump-rate weight of the sequences of `n` jumps out of `x`. -/
noncomputable def jumpMassFrom
    (G : FiniteJumpGenerator Ω) (x : Ω) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → Ω,
    fixedInitialWeight x (states 0) * G.jumpProduct states

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
@[simp]
theorem jumpMassFrom_zero (G : FiniteJumpGenerator Ω) (x : Ω) :
    G.jumpMassFrom x 0 = 1 := by
  unfold jumpMassFrom
  rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Ω).symm
    (fun y : Ω => fixedInitialWeight x y * G.jumpProduct (fun _ : Fin 1 => y))
    _ (fun y => rfl)]
  simp [fixedInitialWeight, jumpProduct]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Folding the branching sum turns one more jump into one more factor of the
escape rate, hence at most one more factor of the rate bound. -/
theorem jumpMassFrom_succ_le
    (G : FiniteJumpGenerator Ω) (x : Ω) (n : ℕ) :
    G.jumpMassFrom x (n + 1) ≤ (G.rateBound : ℝ≥0∞) * G.jumpMassFrom x n := by
  have hreindex :
      G.jumpMassFrom x (n + 1) =
        ∑ init : Fin (n + 1) → Ω,
          fixedInitialWeight x (init 0) *
            (G.jumpProduct init *
              (G.escapeRate (init (Fin.last n)) : ℝ≥0∞)) := by
    unfold jumpMassFrom
    rw [← Fintype.sum_equiv (snocEquiv Ω n)
      (fun p : (Fin (n + 1) → Ω) × Ω =>
        fixedInitialWeight x ((Fin.snoc p.1 p.2 : Fin (n + 2) → Ω) 0) *
          G.jumpProduct (Fin.snoc p.1 p.2))
      _ (fun p => rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun init _ => ?_
    simp only [snoc_zero, ← Finset.mul_sum, G.sum_jumpProduct_snoc init]
  rw [hreindex]
  unfold jumpMassFrom
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun init _ => ?_
  rw [show (G.rateBound : ℝ≥0∞) *
      (fixedInitialWeight x (init 0) * G.jumpProduct init) =
    fixedInitialWeight x (init 0) *
      (G.jumpProduct init * (G.rateBound : ℝ≥0∞)) from by ring]
  gcongr
  exact G.escapeRate_le_rateBound _

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem jumpMassFrom_le_pow
    (G : FiniteJumpGenerator Ω) (x : Ω) (n : ℕ) :
    G.jumpMassFrom x n ≤ (G.rateBound : ℝ≥0∞) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        G.jumpMassFrom x (n + 1)
            ≤ (G.rateBound : ℝ≥0∞) * G.jumpMassFrom x n :=
              G.jumpMassFrom_succ_le x n
        _ ≤ (G.rateBound : ℝ≥0∞) * (G.rateBound : ℝ≥0∞) ^ n := by gcongr
        _ = (G.rateBound : ℝ≥0∞) ^ (n + 1) := by ring

theorem cubeExpWeight_le_one
    {n : ℕ} (r : Fin n → NNReal) (T : NNReal) (u : Fin n → I) :
    cubeExpWeight r T u ≤ 1 := by
  unfold cubeExpWeight
  refine Finset.prod_le_one (fun _ _ => zero_le) fun i _ => ?_
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.2 (neg_nonpos.mpr ?_))
  have h0 : (0 : ℝ) ≤ (u i : ℝ) := (u i).2.1
  positivity

theorem arrivalOn_le {n : ℕ} (r : Fin n → NNReal) (T : NNReal) :
    arrivalOn r T ≤ ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  unfold arrivalOn
  calc
    (∫⁻ u in Simplex.freeSimplexSet n, cubeExpWeight r T u)
        ≤ ∫⁻ _ in Simplex.freeSimplexSet n, 1 :=
          lintegral_mono fun u => cubeExpWeight_le_one r T u
    _ = (volume : Measure (Fin n → I)) (Simplex.freeSimplexSet n) := by
          simp
    _ = ENNReal.ofReal (1 / (n.factorial : ℝ)) :=
          Simplex.volume_freeSimplexSet n

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- The arrival masses obey the Poisson-type tail of a chain whose every escape
rate is capped by `rateBound`. -/
theorem arrivalMassFrom_le
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    G.arrivalMassFrom T x n ≤
      ((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
        ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  have hstep : ∀ states : Fin (n + 1) → Ω,
      fixedInitialWeight x (states 0) * G.sequenceArrivalMass T states ≤
        (fixedInitialWeight x (states 0) * G.jumpProduct states) *
          ((T : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / (n.factorial : ℝ))) := by
    intro states
    unfold sequenceArrivalMass
    calc
      fixedInitialWeight x (states 0) *
            ((T : ℝ≥0∞) ^ n * G.jumpProduct states *
              arrivalOn (G.stateEscapeRates states) T)
          ≤ fixedInitialWeight x (states 0) *
              ((T : ℝ≥0∞) ^ n * G.jumpProduct states *
                ENNReal.ofReal (1 / (n.factorial : ℝ))) := by
            gcongr
            exact arrivalOn_le _ _
      _ = (fixedInitialWeight x (states 0) * G.jumpProduct states) *
            ((T : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / (n.factorial : ℝ))) := by
            ring
  calc
    G.arrivalMassFrom T x n
        ≤ ∑ states : Fin (n + 1) → Ω,
            (fixedInitialWeight x (states 0) * G.jumpProduct states) *
              ((T : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / (n.factorial : ℝ))) :=
          Finset.sum_le_sum fun states _ => hstep states
    _ = G.jumpMassFrom x n *
          ((T : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / (n.factorial : ℝ))) := by
          rw [← Finset.sum_mul]
          rfl
    _ ≤ (G.rateBound : ℝ≥0∞) ^ n *
          ((T : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / (n.factorial : ℝ))) := by
          gcongr
          exact G.jumpMassFrom_le_pow x n
    _ = ((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
          ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
          rw [mul_pow]
          ring

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Non-explosion: almost every path jumps only finitely often, so the arrival
masses vanish. -/
theorem tendsto_arrivalMassFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    Filter.Tendsto (fun n => G.arrivalMassFrom T x n) Filter.atTop
      (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ => (0 : ℝ≥0∞))
    (h := fun n : ℕ =>
      ((G.rateBound : ℝ≥0∞) * (T : ℝ≥0∞)) ^ n *
        ENNReal.ofReal (1 / (n.factorial : ℝ)))
    tendsto_const_nhds
    (Renewal.tendsto_pow_mul_factorial_inv T G.rateBound)
    (fun n => bot_le)
    (fun n => G.arrivalMassFrom_le T x n)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
@[simp]
theorem arrivalMassFrom_zero (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    G.arrivalMassFrom T x 0 = 1 := by
  have harrivalOne : ∀ s : Fin 1 → Ω,
      arrivalOn (G.stateEscapeRates s) T = 1 := by
    intro s
    unfold arrivalOn cubeExpWeight
    simp [Simplex.volume_freeSimplexSet]
  unfold arrivalMassFrom sequenceArrivalMass
  rw [← Fintype.sum_equiv (Equiv.funUnique (Fin 1) Ω).symm
    (fun y : Ω =>
      fixedInitialWeight x y *
        ((T : ℝ≥0∞) ^ 0 * G.jumpProduct (fun _ : Fin 1 => y) *
          arrivalOn (G.stateEscapeRates (fun _ : Fin 1 => y)) T))
    _ (fun y => rfl)]
  simp [harrivalOne, jumpProduct, fixedInitialWeight]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Partial sums of the sector masses telescope against the arrival mass. -/
theorem sum_sectorMassFrom_add_arrivalMassFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (N : ℕ) :
    (∑ n ∈ Finset.range N, G.sectorMassFrom T x n) +
        G.arrivalMassFrom T x N = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc,
        G.sectorMassFrom_add_arrivalMassFrom_succ T x N]
      exact ih

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **Normalization for a general finite-state jump generator.**  The sector
masses of the fixed-initial path law sum to one, so the chain does not explode
within the horizon. -/
theorem tsum_sectorMassFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∑' n, G.sectorMassFrom T x n = 1 := by
  have hpartial :
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, G.sectorMassFrom T x n)
        Filter.atTop (nhds (∑' n, G.sectorMassFrom T x n)) :=
    ENNReal.tendsto_nat_tsum _
  have hsum :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, G.sectorMassFrom T x n) +
            G.arrivalMassFrom T x N)
        Filter.atTop (nhds ((∑' n, G.sectorMassFrom T x n) + 0)) :=
    hpartial.add (G.tendsto_arrivalMassFrom T x)
  rw [add_zero] at hsum
  have hone :
      Filter.Tendsto
        (fun N =>
          (∑ n ∈ Finset.range N, G.sectorMassFrom T x n) +
            G.arrivalMassFrom T x N)
        Filter.atTop (nhds 1) := by
    simp only [G.sum_sectorMassFrom_add_arrivalMassFrom T x]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hsum hone

/-! ### The terminal transition mass

Summing the sector masses that also land on a prescribed final state gives the
terminal-state marginal of the fixed-initial path law.  Working with the sector
sum directly avoids building the dependent-sum measure over all jump counts;
the row-sum identity below is exactly the normalization just proved. -/

/-- The mass the `n`-jump sector sends from `x` to `y`. -/
noncomputable def sectorTerminalMassFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) (n : ℕ) : ℝ≥0∞ :=
  ∑ states : Fin (n + 1) → Ω,
    fixedInitialWeight x (states 0) *
      (fixedInitialWeight y (states (Fin.last n)) * G.sequenceMass T states)

/-- The terminal-state transition mass over the horizon `T`. -/
noncomputable def transitionMass
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x y : Ω) : ℝ≥0∞ :=
  ∑' n, G.sectorTerminalMassFrom T x y n

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
@[simp]
theorem sum_fixedInitialWeight (y : Ω) :
    ∑ z : Ω, fixedInitialWeight z y = 1 := by
  simp [fixedInitialWeight]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- Every sector distributes its whole mass over the possible final states. -/
theorem sum_sectorTerminalMassFrom
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) (n : ℕ) :
    ∑ y : Ω, G.sectorTerminalMassFrom T x y n = G.sectorMassFrom T x n := by
  unfold sectorTerminalMassFrom sectorMassFrom
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun states _ => ?_
  rw [← Finset.mul_sum, ← Finset.sum_mul,
    sum_fixedInitialWeight (states (Fin.last n)), one_mul]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- **The terminal transition mass is a stochastic row.**  Its entries sum to
one because the sector masses do. -/
theorem sum_transitionMass
    (G : FiniteJumpGenerator Ω) (T : NNReal) (x : Ω) :
    ∑ y : Ω, G.transitionMass T x y = 1 := by
  unfold transitionMass
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [G.sum_sectorTerminalMassFrom T x]
  exact G.tsum_sectorMassFrom T x

end FiniteJumpGenerator
end ContinuousTimeJump
end MeasureProtocol
end CrooksJarzynski
