import UEOTQM.Weighted

/-!
# Zero padding of finite weighted instruments

The source Kraus index may depend on the outcome. An injective embedding into
a common finite index extends both weights and matrices by zero. The branch,
Heisenberg pullback and completeness sums are then proved unchanged.

Outcomes can also be embedded into a larger finite type: original branches are
preserved and added branches are zero. Applying these constructions separately
to each action handles differing finite outcome and Kraus table sizes. The
embeddings are explicit mathematical inputs; this file does not claim that a
particular Python padding routine or its index encoding has been verified.
-/

namespace UEOTQM

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

/-- Extend a finite table along an embedding, with zero outside its image. -/
def zeroExtend {α β V : Type*} [Zero V] (e : α ↪ β) (f : α → V) : β → V :=
  Function.extend e f (fun _ => 0)

@[simp] theorem zeroExtend_apply {α β V : Type*} [Zero V]
    (e : α ↪ β) (f : α → V) (a : α) : zeroExtend e f (e a) = f a :=
  e.injective.extend_apply f (fun _ => 0) a

@[simp] theorem zeroExtend_of_not_mem_range {α β V : Type*} [Zero V]
    (e : α ↪ β) (f : α → V) (b : β) (hb : b ∉ Set.range e) :
    zeroExtend e f b = 0 :=
  Function.extend_apply' f (fun _ => 0) b hb

theorem sum_zeroExtend {α β V : Type*} [Fintype α] [Fintype β] [AddCommMonoid V]
    (e : α ↪ β) (f : α → V) : (∑ b, zeroExtend e f b) = ∑ a, f a := by
  symm
  exact Fintype.sum_of_injective e e.injective f (zeroExtend e f)
    (fun b hb => zeroExtend_of_not_mem_range e f b hb)
    (fun a => (zeroExtend_apply e f a).symm)

theorem zeroExtend_nonneg {α β : Type*} (e : α ↪ β) (w : α → ℝ)
    (hw : ∀ a, 0 ≤ w a) (b : β) : 0 ≤ zeroExtend e w b := by
  classical
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hb
    simpa only [zeroExtend_apply] using hw a
  · rw [zeroExtend_of_not_mem_range e w b hb]

section KrausPadding

variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']

theorem weightedKrausMap_zeroExtend (e : κ ↪ κ') (w : κ → ℝ)
    (K : κ → Operator ι) (X : Operator ι) :
    weightedKrausMap (zeroExtend e w) (zeroExtend e K) X = weightedKrausMap w K X := by
  unfold weightedKrausMap
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro k hk
    simp only [zeroExtend_of_not_mem_range e w k hk, zero_smul]
  · intro k
    simp only [zeroExtend_apply]

theorem weightedHeisenberg_zeroExtend (e : κ ↪ κ') (w : κ → ℝ)
    (K : κ → Operator ι) (E : Operator ι) :
    weightedHeisenberg (zeroExtend e w) (zeroExtend e K) E = weightedHeisenberg w K E := by
  unfold weightedHeisenberg
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro k hk
    simp only [zeroExtend_of_not_mem_range e w k hk, zero_smul]
  · intro k
    simp only [zeroExtend_apply]

theorem weightedGram_zeroExtend (e : κ ↪ κ') (w : κ → ℝ) (K : κ → Operator ι) :
    (∑ k, zeroExtend e w k • ((zeroExtend e K k)ᴴ * zeroExtend e K k)) =
      ∑ k, w k • ((K k)ᴴ * K k) := by
  symm
  apply Fintype.sum_of_injective e e.injective
  · intro k hk
    simp only [zeroExtend_of_not_mem_range e w k hk, zero_smul]
  · intro k
    simp only [zeroExtend_apply]

end KrausPadding

/-- A weighted instrument whose finite Kraus index can vary by outcome. -/
structure RaggedInstrument (ι O : Type*) (κ : O → Type*)
    [Fintype ι] [DecidableEq ι] [Fintype O] [∀ o, Fintype (κ o)] where
  weight : ∀ o, κ o → ℝ
  kraus : ∀ o, κ o → Operator ι
  weight_nonneg : ∀ o k, 0 ≤ weight o k
  complete : (∑ o, ∑ k, weight o k • ((kraus o k)ᴴ * kraus o k)) = 1

namespace RaggedInstrument

variable {ι O κ' : Type*} {κ : O → Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [∀ o, Fintype (κ o)] [Fintype κ']

def branch (R : RaggedInstrument ι O κ) (o : O) (X : Operator ι) : Operator ι :=
  weightedKrausMap (R.weight o) (R.kraus o) X

/-- Pad each outcome's Kraus table into a common finite type. -/
def toWeighted (R : RaggedInstrument ι O κ) (e : ∀ o, κ o ↪ κ') :
    WeightedInstrument ι O κ' where
  weight o := zeroExtend (e o) (R.weight o)
  kraus o := zeroExtend (e o) (R.kraus o)
  weight_nonneg o := zeroExtend_nonneg (e o) (R.weight o) (R.weight_nonneg o)
  complete := by
    calc
      (∑ o, ∑ k, zeroExtend (e o) (R.weight o) k •
        ((zeroExtend (e o) (R.kraus o) k)ᴴ * zeroExtend (e o) (R.kraus o) k)) =
          ∑ o, ∑ k, R.weight o k • ((R.kraus o k)ᴴ * R.kraus o k) := by
        apply Finset.sum_congr rfl
        intro o _
        exact weightedGram_zeroExtend (e o) (R.weight o) (R.kraus o)
      _ = 1 := R.complete

@[simp] theorem toWeighted_weight_apply (R : RaggedInstrument ι O κ)
    (e : ∀ o, κ o ↪ κ') (o : O) (k : κ o) :
    (R.toWeighted e).weight o (e o k) = R.weight o k :=
  zeroExtend_apply (e o) (R.weight o) k

@[simp] theorem toWeighted_kraus_apply (R : RaggedInstrument ι O κ)
    (e : ∀ o, κ o ↪ κ') (o : O) (k : κ o) :
    (R.toWeighted e).kraus o (e o k) = R.kraus o k :=
  zeroExtend_apply (e o) (R.kraus o) k

@[simp] theorem toWeighted_branch (R : RaggedInstrument ι O κ)
    (e : ∀ o, κ o ↪ κ') (o : O) (X : Operator ι) :
    (R.toWeighted e).branch o X = R.branch o X :=
  weightedKrausMap_zeroExtend (e o) (R.weight o) (R.kraus o) X

@[simp] theorem toWeighted_toInstrument_branch (R : RaggedInstrument ι O κ)
    (e : ∀ o, κ o ↪ κ') (o : O) (X : Operator ι) :
    (R.toWeighted e).toInstrument.branch o X = R.branch o X := by
  rw [WeightedInstrument.toInstrument_branch, R.toWeighted_branch]

@[simp] theorem toWeighted_heisenberg (R : RaggedInstrument ι O κ)
    (e : ∀ o, κ o ↪ κ') (o : O) (E : Operator ι) :
    heisenberg ((R.toWeighted e).toInstrument.kraus o) E =
      weightedHeisenberg (R.weight o) (R.kraus o) E := by
  rw [WeightedInstrument.toInstrument_heisenberg]
  exact weightedHeisenberg_zeroExtend (e o) (R.weight o) (R.kraus o) E

theorem toWeighted_toInstrument_kraus_of_not_mem_range (R : RaggedInstrument ι O κ)
    (e : ∀ o, κ o ↪ κ') (o : O) (k : κ') (hk : k ∉ Set.range (e o)) :
    (R.toWeighted e).toInstrument.kraus o k = 0 := by
  rw [WeightedInstrument.toInstrument_kraus]
  change Real.sqrt (zeroExtend (e o) (R.weight o) k) •
    zeroExtend (e o) (R.kraus o) k = 0
  rw [zeroExtend_of_not_mem_range (e o) (R.kraus o) k hk, smul_zero]

end RaggedInstrument

namespace WeightedInstrument

variable {ι O O' κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype O] [Fintype O'] [Fintype κ]

/-- Add zero outcomes along a finite outcome embedding. -/
def padOutcomes (W : WeightedInstrument ι O κ) (e : O ↪ O') :
    WeightedInstrument ι O' κ where
  weight o' k := zeroExtend e (fun o => W.weight o k) o'
  kraus o' k := zeroExtend e (fun o => W.kraus o k) o'
  weight_nonneg o' k :=
    zeroExtend_nonneg e (fun o => W.weight o k) (fun o => W.weight_nonneg o k) o'
  complete := by
    calc
      (∑ o', ∑ k, zeroExtend e (fun o => W.weight o k) o' •
        ((zeroExtend e (fun o => W.kraus o k) o')ᴴ *
          zeroExtend e (fun o => W.kraus o k) o')) =
          ∑ o, ∑ k, W.weight o k • ((W.kraus o k)ᴴ * W.kraus o k) := by
        symm
        apply Fintype.sum_of_injective e e.injective
        · intro o' ho'
          simp only [zeroExtend_of_not_mem_range e _ o' ho', zero_smul,
            Finset.sum_const_zero]
        · intro o
          simp only [zeroExtend_apply]
      _ = 1 := W.complete

@[simp] theorem padOutcomes_branch_apply (W : WeightedInstrument ι O κ)
    (e : O ↪ O') (o : O) (X : Operator ι) :
    (W.padOutcomes e).branch (e o) X = W.branch o X := by
  simp only [branch, weightedKrausMap, padOutcomes, zeroExtend_apply]

theorem padOutcomes_branch_of_not_mem_range (W : WeightedInstrument ι O κ)
    (e : O ↪ O') (o' : O') (ho' : o' ∉ Set.range e) (X : Operator ι) :
    (W.padOutcomes e).branch o' X = 0 := by
  simp only [branch, weightedKrausMap, padOutcomes,
    zeroExtend_of_not_mem_range e _ o' ho', zero_smul, Finset.sum_const_zero]

@[simp] theorem padOutcomes_heisenberg_apply (W : WeightedInstrument ι O κ)
    (e : O ↪ O') (o : O) (E : Operator ι) :
    heisenberg ((W.padOutcomes e).toInstrument.kraus (e o)) E =
      heisenberg (W.toInstrument.kraus o) E := by
  simp only [toInstrument_heisenberg, weightedHeisenberg, padOutcomes, zeroExtend_apply]

theorem padOutcomes_heisenberg_of_not_mem_range (W : WeightedInstrument ι O κ)
    (e : O ↪ O') (o' : O') (ho' : o' ∉ Set.range e) (E : Operator ι) :
    heisenberg ((W.padOutcomes e).toInstrument.kraus o') E = 0 := by
  simp only [toInstrument_heisenberg, weightedHeisenberg, padOutcomes,
    zeroExtend_of_not_mem_range e _ o' ho', zero_smul, Finset.sum_const_zero]

@[simp] theorem padOutcomes_probability_apply (W : WeightedInstrument ι O κ)
    (e : O ↪ O') (ρ : Density ι) (o : O) :
    (W.padOutcomes e).toInstrument.probability ρ (e o) =
      W.toInstrument.probability ρ o := by
  simp only [toInstrument_probability, padOutcomes_branch_apply]

theorem padOutcomes_probability_of_not_mem_range (W : WeightedInstrument ι O κ)
    (e : O ↪ O') (ρ : Density ι) (o' : O') (ho' : o' ∉ Set.range e) :
    (W.padOutcomes e).toInstrument.probability ρ o' = 0 := by
  rw [toInstrument_probability, W.padOutcomes_branch_of_not_mem_range e o' ho']
  simp [mass]

end WeightedInstrument

end

end UEOTQM
