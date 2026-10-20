import UEOTQM.Stability
import UEOTQM.Weighted

/-!
# Actual finite mixtures and certified total-variation budgets

Normalized nonnegative weights construct density matrices and complete Kraus
instruments. The all-effect and all-state bounds are proved from these actual
mixtures, not supplied as fields. The sharp factor one half follows by centering
each Born probability at one half and cancelling the difference of total weights.

All channel libraries here have a common finite matrix carrier. These theorems
do not identify the all-effect distance with a trace norm or a diamond norm, and
do not turn a finite sample of input states into a worst-case certificate.
-/

namespace UEOTQM.Mixture

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {β ι O κ : Type*} [Fintype β] [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype κ]

/-- Probability data only: none of the later stability conclusions is a field. -/
structure Weights (β : Type*) [Fintype β] where
  weight : β → ℝ
  nonneg : ∀ b, 0 ≤ weight b
  sum_one : ∑ b, weight b = 1

/-- Total variation of two normalized distributions on the same finite library. -/
def tv (p q : Weights β) : ℝ := (1 / 2 : ℝ) * ∑ b, |p.weight b - q.weight b|

theorem tv_nonneg (p q : Weights β) : 0 ≤ tv p q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

@[simp] theorem tv_self (p : Weights β) : tv p p = 0 := by simp [tv]

theorem tv_comm (p q : Weights β) : tv p q = tv q p := by
  simp only [tv, abs_sub_comm]

theorem tv_le_one (p q : Weights β) : tv p q ≤ 1 := by
  have h : (∑ b, |p.weight b - q.weight b|) ≤ 2 := by
    calc
      (∑ b, |p.weight b - q.weight b|) ≤ ∑ b, (p.weight b + q.weight b) := by
        apply Finset.sum_le_sum
        intro b _
        exact abs_sub_le_iff.mpr ⟨by linarith [q.nonneg b], by linarith [p.nonneg b]⟩
      _ = 2 := by rw [Finset.sum_add_distrib, p.sum_one, q.sum_one]; norm_num
  dsimp [tv]
  linarith

/-- The finite bounded-observable estimate uses normalization on both sides. -/
theorem expectation_sub_le_tv (p q : Weights β) (f : β → ℝ)
    (hf0 : ∀ b, 0 ≤ f b) (hf1 : ∀ b, f b ≤ 1) :
    |(∑ b, p.weight b * f b) - ∑ b, q.weight b * f b| ≤ tv p q := by
  have hcenter : (∑ b, p.weight b * f b) - ∑ b, q.weight b * f b =
      ∑ b, (p.weight b - q.weight b) * (f b - 1 / 2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, sub_mul, ← Finset.sum_mul]
    rw [p.sum_one, q.sum_one]
    ring
  rw [hcenter]
  calc
    |∑ b, (p.weight b - q.weight b) * (f b - 1 / 2)| ≤
        ∑ b, |(p.weight b - q.weight b) * (f b - 1 / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |p.weight b - q.weight b| * (1 / 2) := by
      apply Finset.sum_le_sum
      intro b _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact abs_le.mpr ⟨by linarith [hf0 b], by linarith [hf1 b]⟩
    _ = tv p q := by rw [← Finset.sum_mul]; unfold tv; ring

/-- The mixture is the actual positive, trace-one matrix sum. -/
def density (p : Weights β) (ρ : β → Density ι) : Density ι where
  matrix := ∑ b, p.weight b • (ρ b).matrix
  positive := Matrix.posSemidef_sum Finset.univ
    (fun b _ => (ρ b).positive.smul (p.nonneg b))
  trace_one := by
    simp only [Matrix.trace_sum, Matrix.trace_smul, Density.trace_one]
    rw [← Finset.sum_smul, p.sum_one, one_smul]

omit [DecidableEq ι] in
@[simp] theorem density_matrix (p : Weights β) (ρ : β → Density ι) :
    (density p ρ).matrix = ∑ b, p.weight b • (ρ b).matrix := rfl

theorem probability_density (p : Weights β) (ρ : β → Density ι) (E : Effect ι) :
    E.probability (density p ρ) = ∑ b, p.weight b * E.probability (ρ b) := by
  change pairing E.matrix (∑ b, p.weight b • (ρ b).matrix) = _
  rw [pairing_sum_right]
  simp only [pairing_smul_right, Effect.probability]

/-- Changing only weights in one actual state library costs at most their TV. -/
theorem density_weight_change_le_tv (p q : Weights β) (ρ : β → Density ι) :
    effectDistance (density p ρ) (density q ρ) ≤ tv p q := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  rw [probability_density, probability_density]
  exact expectation_sub_le_tv p q (fun b => E.probability (ρ b))
    (fun b => E.probability_nonneg (ρ b)) (fun b => E.probability_le_one (ρ b))

/-- At fixed weights the true all-effect errors combine by their weighted sum. -/
theorem density_fixed_weights_le_sum (p : Weights β) (ρ σ : β → Density ι) :
    effectDistance (density p ρ) (density p σ) ≤
      ∑ b, p.weight b * effectDistance (ρ b) (σ b) := by
  apply (effectDistance_le_iff _ _ _).mpr
  intro E
  rw [probability_density, probability_density, ← Finset.sum_sub_distrib]
  calc
    |∑ b, (p.weight b * E.probability (ρ b) - p.weight b * E.probability (σ b))| ≤
        ∑ b, |p.weight b * E.probability (ρ b) - p.weight b * E.probability (σ b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, p.weight b * effectDistance (ρ b) (σ b) := by
      apply Finset.sum_le_sum
      intro b _
      rw [← mul_sub, abs_mul, abs_of_nonneg (p.nonneg b)]
      exact mul_le_mul_of_nonneg_left
        (E.probability_sub_le_effectDistance (ρ b) (σ b)) (p.nonneg b)

theorem density_joint_change_le (p q : Weights β) (ρ σ : β → Density ι) :
    effectDistance (density p ρ) (density q σ) ≤
      tv p q + ∑ b, q.weight b * effectDistance (ρ b) (σ b) := by
  exact (effectDistance_triangle (density p ρ) (density q ρ) (density q σ)).trans
    (add_le_add (density_weight_change_le_tv p q ρ) (density_fixed_weights_le_sum q ρ σ))

/-- Mix a finite library by an actual extra Kraus index. Completeness is derived
from each member's completeness and the normalization of the weights. -/
def weightedInstrument (p : Weights β) (I : β → Instrument ι O κ) :
    WeightedInstrument ι O (β × κ) where
  weight _ bk := p.weight bk.1
  kraus o bk := (I bk.1).kraus o bk.2
  weight_nonneg _ bk := p.nonneg bk.1
  complete := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, Instrument.complete]
    rw [← Finset.sum_smul, p.sum_one, one_smul]

/-- Ordinary Kraus matrices include the actual square roots of the weights. -/
def instrument (p : Weights β) (I : β → Instrument ι O κ) :
    Instrument ι O (β × κ) := (weightedInstrument p I).toInstrument

@[simp] theorem instrument_kraus (p : Weights β) (I : β → Instrument ι O κ)
    (o : O) (bk : β × κ) :
    (instrument p I).kraus o bk = Real.sqrt (p.weight bk.1) • (I bk.1).kraus o bk.2 :=
  rfl

theorem instrument_branch (p : Weights β) (I : β → Instrument ι O κ)
    (o : O) (X : Operator ι) :
    (instrument p I).branch o X = ∑ b, p.weight b • (I b).branch o X := by
  rw [instrument, WeightedInstrument.toInstrument_branch]
  change (∑ bk : β × κ,
    p.weight bk.1 • ((I bk.1).kraus o bk.2 * X * ((I bk.1).kraus o bk.2)ᴴ)) = _
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum]
  rfl

theorem instrument_heisenberg (p : Weights β) (I : β → Instrument ι O κ)
    (o : O) (E : Operator ι) :
    heisenberg ((instrument p I).kraus o) E =
      ∑ b, p.weight b • heisenberg ((I b).kraus o) E := by
  rw [instrument, WeightedInstrument.toInstrument_heisenberg]
  change (∑ bk : β × κ,
    p.weight bk.1 • (((I bk.1).kraus o bk.2)ᴴ * E * (I bk.1).kraus o bk.2)) = _
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum]
  rfl

theorem instrument_channel (p : Weights β) (I : β → Instrument ι O κ)
    (X : Operator ι) :
    (instrument p I).channel X = ∑ b, p.weight b • (I b).channel X := by
  unfold Instrument.channel
  simp only [instrument_branch]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum]

theorem instrument_channelState (p : Weights β) (I : β → Instrument ι O κ)
    (ρ : Density ι) :
    (instrument p I).channelState ρ = density p (fun b => (I b).channelState ρ) := by
  apply Density.ext
  exact instrument_channel p I ρ.matrix

/-- This bounds the supremum over every density input, using the same actual
channel library on both sides. No input-state sampling is used. -/
theorem channelDefect_weight_change_le_tv (p q : Weights β)
    (I : β → Instrument ι O κ) :
    channelDefect (instrument p I).channelState (instrument q I).channelState ≤ tv p q := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · exact tv_nonneg p q
  · dsimp only
    rw [instrument_channelState, instrument_channelState]
    exact density_weight_change_le_tv p q (fun b => (I b).channelState ρ)

/-- Each component defect is itself the actual all-state supremum. The two
libraries may use different finite outcome and Kraus index types. -/
theorem channelDefect_fixed_weights_le_sum {O' κ' : Type*} [Fintype O'] [Fintype κ']
    (p : Weights β) (I : β → Instrument ι O κ) (J : β → Instrument ι O' κ') :
    channelDefect (instrument p I).channelState (instrument p J).channelState ≤
      ∑ b, p.weight b * channelDefect (I b).channelState (J b).channelState := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · exact Finset.sum_nonneg (fun b _ => mul_nonneg (p.nonneg b) (channelDefect_nonneg _ _))
  · dsimp only
    rw [instrument_channelState, instrument_channelState]
    apply (density_fixed_weights_le_sum p
      (fun b => (I b).channelState ρ) (fun b => (J b).channelState ρ)).trans
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left (effectDistance_le_channelDefect _ _ ρ) (p.nonneg b)

theorem channelDefect_joint_change_le {O' κ' : Type*} [Fintype O'] [Fintype κ']
    (p q : Weights β) (I : β → Instrument ι O κ) (J : β → Instrument ι O' κ') :
    channelDefect (instrument p I).channelState (instrument q J).channelState ≤
      tv p q + ∑ b, q.weight b * channelDefect (I b).channelState (J b).channelState := by
  apply csSup_le (Set.insert_nonempty 0 _)
  rintro x (rfl | ⟨ρ, rfl⟩)
  · exact add_nonneg (tv_nonneg p q)
      (Finset.sum_nonneg (fun b _ => mul_nonneg (q.nonneg b) (channelDefect_nonneg _ _)))
  · dsimp only
    rw [instrument_channelState, instrument_channelState]
    apply (density_joint_change_le p q
      (fun b => (I b).channelState ρ) (fun b => (J b).channelState ρ)).trans
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro b _
    exact mul_le_mul_of_nonneg_left (effectDistance_le_channelDefect _ _ ρ) (q.nonneg b)

/-- Exact rational probability data. Conversion preserves its proved premises. -/
structure RationalWeights (β : Type*) [Fintype β] where
  weight : β → ℚ
  nonneg : ∀ b, 0 ≤ weight b
  sum_one : ∑ b, weight b = 1

def RationalWeights.toWeights (p : RationalWeights β) : Weights β where
  weight b := p.weight b
  nonneg b := by exact_mod_cast p.nonneg b
  sum_one := by exact_mod_cast p.sum_one

/-- This expression only uses finite rational arithmetic. -/
def rationalTV (p q : RationalWeights β) : ℚ :=
  (1 / 2 : ℚ) * ∑ b, |p.weight b - q.weight b|

theorem tv_toWeights (p q : RationalWeights β) :
    tv p.toWeights q.toWeights = (rationalTV p q : ℝ) := by
  change (1 / 2 : ℝ) * ∑ b, |(p.weight b : ℝ) - (q.weight b : ℝ)| =
    (((1 / 2 : ℚ) * ∑ b, |p.weight b - q.weight b| : ℚ) : ℝ)
  norm_cast
  push_cast
  norm_num

theorem density_weight_change_le_rational_budget (p q : RationalWeights β)
    (ρ : β → Density ι) (budget : ℚ) (hbudget : rationalTV p q ≤ budget) :
    effectDistance (density p.toWeights ρ) (density q.toWeights ρ) ≤ (budget : ℝ) := by
  apply (density_weight_change_le_tv p.toWeights q.toWeights ρ).trans
  rw [tv_toWeights]
  exact_mod_cast hbudget

/-- A finite rational inequality certifies the actual worst-case defect for
every density input to the common channel library. -/
theorem channelDefect_weight_change_le_rational_budget (p q : RationalWeights β)
    (I : β → Instrument ι O κ) (budget : ℚ) (hbudget : rationalTV p q ≤ budget) :
    channelDefect (instrument p.toWeights I).channelState
      (instrument q.toWeights I).channelState ≤ (budget : ℝ) := by
  apply (channelDefect_weight_change_le_tv p.toWeights q.toWeights I).trans
  rw [tv_toWeights]
  exact_mod_cast hbudget

theorem channelDefect_fixed_weights_le_rational_sum {O' κ' : Type*}
    [Fintype O'] [Fintype κ'] (p : RationalWeights β)
    (I : β → Instrument ι O κ) (J : β → Instrument ι O' κ') (error : β → ℚ)
    (herror : ∀ b, channelDefect (I b).channelState (J b).channelState ≤ (error b : ℝ)) :
    channelDefect (instrument p.toWeights I).channelState
      (instrument p.toWeights J).channelState ≤ ((∑ b, p.weight b * error b : ℚ) : ℝ) := by
  apply (channelDefect_fixed_weights_le_sum p.toWeights I J).trans
  calc
    (∑ b, p.toWeights.weight b * channelDefect (I b).channelState (J b).channelState) ≤
        ∑ b, (p.weight b : ℝ) * (error b : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (herror b) (p.toWeights.nonneg b)
    _ = ((∑ b, p.weight b * error b : ℚ) : ℝ) := by norm_cast

/-- Exact weight drift plus exact, separately proved component-error budgets. -/
def rationalJointBudget (p q : RationalWeights β) (error : β → ℚ) : ℚ :=
  rationalTV p q + ∑ b, q.weight b * error b

theorem channelDefect_joint_change_le_rational_budget {O' κ' : Type*}
    [Fintype O'] [Fintype κ'] (p q : RationalWeights β)
    (I : β → Instrument ι O κ) (J : β → Instrument ι O' κ')
    (error : β → ℚ) (budget : ℚ)
    (herror : ∀ b, channelDefect (I b).channelState (J b).channelState ≤ (error b : ℝ))
    (hbudget : rationalJointBudget p q error ≤ budget) :
    channelDefect (instrument p.toWeights I).channelState
      (instrument q.toWeights J).channelState ≤ (budget : ℝ) := by
  apply (channelDefect_joint_change_le p.toWeights q.toWeights I J).trans
  calc
    tv p.toWeights q.toWeights +
        ∑ b, q.toWeights.weight b * channelDefect (I b).channelState (J b).channelState ≤
        (rationalTV p q : ℝ) + ∑ b, (q.weight b : ℝ) * (error b : ℝ) := by
      rw [tv_toWeights]
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (herror b) (q.toWeights.nonneg b)
    _ = (rationalJointBudget p q error : ℝ) := by
      unfold rationalJointBudget
      norm_cast
    _ ≤ (budget : ℝ) := by exact_mod_cast hbudget

end

end UEOTQM.Mixture
