import UEOTQM.QuantumActionRealizability

/-!
# Concrete positive and negative visible-instrument certificates

The state channel in these examples is exactly the identity.  Visible outcome
labels still matter, and a shared observation still forbids different hidden
node randomizations.  All examples use actual complete Kraus instruments.
-/

namespace UEOTQM.QuantumActionRealizability

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Report a deterministic visible bit, leaving the quantum state unchanged. -/
def labelInstrument (label : Bool) : Instrument ι Bool Unit where
  kraus o _ := if o = label then 1 else 0
  complete := by
    cases label <;> simp [Fintype.sum_bool]

@[simp] theorem labelInstrument_branch (label o : Bool) (X : Operator ι) :
    (labelInstrument label).branch o X = if o = label then X else 0 := by
  by_cases h : o = label <;> simp [Instrument.branch, krausMap, labelInstrument, h]

theorem labelInstrument_channel (label : Bool) (X : Operator ι) :
    (labelInstrument label).channel X = X := by
  cases label <;> simp [Instrument.channel, Fintype.sum_bool]

/-- A positive weight certificate constructs the fair visible coin instrument. -/
def fairWeights : Mixture.Weights Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

theorem fair_label_mixture_branch (o : Bool) (X : Operator ι) :
    (Mixture.instrument fairWeights (labelInstrument (ι := ι))).branch o X =
      (1 / 2 : ℝ) • X := by
  cases o <;>
    simp [Mixture.instrument_branch, fairWeights, Fintype.sum_bool]

/-- Equality after forgetting labels is insufficient for instrument equality. -/
theorem swapped_labels_same_channel (X : Operator ι) :
    (labelInstrument false).channel X = (labelInstrument true).channel X := by
  rw [labelInstrument_channel, labelInstrument_channel]

theorem swapped_labels_distinct_visible_branch :
    (labelInstrument (ι := Unit) false).branch true 1 ≠
      (labelInstrument (ι := Unit) true).branch true 1 := by
  simp

/-- Even arbitrary randomization of the original one-action library cannot
silently exchange the visible labels. -/
theorem swapped_labels_not_realizable :
    ¬ ∃ sigma : PMF Unit, ∀ o X,
      (Mixture.instrument (weightsOfPMF sigma)
        (fun _ : Unit => labelInstrument (ι := Unit) false)).branch o X =
      (labelInstrument true).branch o X := by
  rintro ⟨sigma, h⟩
  have hx := h true (1 : Operator Unit)
  have he := congrArg (fun X : Operator Unit => X () ()) hx
  simpa [Mixture.instrument_branch] using he

/-- Each hidden node separately has an exact allowed action. -/
theorem hidden_nodes_individually_realizable :
    ∀ n : Bool, ∃ sigma : PMF Bool, ∀ o X,
      (Mixture.instrument (weightsOfPMF sigma)
        (labelInstrument (ι := Unit))).branch o X =
      (labelInstrument n).branch o X := by
  intro n
  apply (full_instrument_realizable_iff (labelInstrument (ι := Unit))
    (labelInstrument n)).mpr
  exact subset_convexHull ℝ _ (Set.mem_range_self n)

/-- The two hidden nodes share one observation.  Their opposite deterministic
targets cannot be met by a common action distribution, although the preceding
theorem proves every node feasible in isolation. -/
theorem shared_observation_not_realizable :
    ¬ ∃ sigma : Unit → PMF Bool, ∀ n : Bool, ∀ o X,
      (Mixture.instrument (weightsOfPMF (sigma ()))
        (labelInstrument (ι := Unit))).branch o X =
      (labelInstrument n).branch o X := by
  rintro ⟨sigma, h⟩
  have hfalse := h false true (1 : Operator Unit)
  have htrue := h true true (1 : Operator Unit)
  exact swapped_labels_distinct_visible_branch (hfalse.symm.trans htrue)

/-- An explicit real linear Choi separator: the mass of the visible-true block. -/
def visibleTrueChoiMass : (Bool → Operator (Unit × Unit)) →ₗ[ℝ] ℝ where
  toFun C := mass (C true)
  map_add' X Y := by simp [mass]
  map_smul' r X := by
    simpa only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul] using
      mass_smul r (X true)

@[simp] theorem visibleTrueChoiMass_label (label : Bool) :
    visibleTrueChoiMass
      (instrumentChoiAfter (labelInstrument (ι := Unit) label) LinearMap.id) =
      if label then 1 else 0 := by
  cases label <;>
    simp [visibleTrueChoiMass, instrumentChoiAfter, choi, LinearMap.comp_apply,
      matrixUnit, mass, Matrix.trace, Fintype.sum_prod_type]

/-- Actual Choi-vector negative certificate, consumed by the generic separator theorem. -/
theorem swapped_labels_choi_separation :
    instrumentChoiAfter (labelInstrument (ι := Unit) true) LinearMap.id ∉
      convexHull ℝ (Set.range (fun _ : Unit =>
        instrumentChoiAfter (labelInstrument (ι := Unit) false) LinearMap.id)) := by
  apply separator_excludes_convexHull _ _ visibleTrueChoiMass 0
  · intro a
    simp
  · simp

/-- A fiber separator can couple hidden nodes; every one-node test misses this. -/
def fiberDifferenceChoiMass :
    (Bool → Bool → Operator (Unit × Unit)) →ₗ[ℝ] ℝ where
  toFun C := visibleTrueChoiMass (C true) - visibleTrueChoiMass (C false)
  map_add' X Y := by simp only [Pi.add_apply, map_add]; ring
  map_smul' r X := by
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem shared_observation_choi_separation :
    (fun n : Bool => instrumentChoiAfter (labelInstrument (ι := Unit) n) LinearMap.id) ∉
      convexHull ℝ (Set.range (fun a : Bool => fun _ : Bool =>
        instrumentChoiAfter (labelInstrument (ι := Unit) a) LinearMap.id)) := by
  apply separator_excludes_convexHull _ _ fiberDifferenceChoiMass 0
  · intro a
    simp [fiberDifferenceChoiMass]
  · simp [fiberDifferenceChoiMass]

end

end UEOTQM.QuantumActionRealizability
