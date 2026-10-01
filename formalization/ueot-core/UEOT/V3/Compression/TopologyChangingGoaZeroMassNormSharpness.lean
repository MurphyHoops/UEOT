import UEOT.V3.Compression.TopologyChangingGoaZeroMassDimension

/-!
# Sharpness of the zero-mass `L1` / `L2` conversion

The Track-S singular-value robustness theorem ends with the finite-dimensional
conversion

`‖v‖₁ ≤ sqrt(card S) * ‖v‖₂`.

This file pressure-tests whether the `sqrt(card S)` factor can be improved using
only the zero-total-mass condition.  On every positive even cardinality, a
balanced sign vector saturates the bound exactly.  Consequently any uniform
constant valid for all zero-mass vectors on that state space must be at least
`sqrt(card S)`.

So the generic dimension-only factor is genuinely sharp on an infinite family
of state spaces; future improvements must use additional kernel/support
geometry rather than zero-mass alone.
-/

namespace UEOT.V3.Compression.TopologyChangingGoaZeroMassNormSharpness

open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation

noncomputable section

/-- Balanced zero-mass sign vector on two copies of `Fin m`. -/
def balancedSign (m : ℕ) : Sum (Fin m) (Fin m) → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- The balanced sign vector has exactly zero total mass. -/
theorem balancedSign_sum_zero (m : ℕ) :
    ∑ s, balancedSign m s = 0 := by
  rw [Fintype.sum_sum_type]
  simp [balancedSign]

/-- Its `L1` norm is the total number of states. -/
theorem balancedSign_signedL1 {m : ℕ} (hm : 0 < m) :
    letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
    signedL1 (balancedSign m) = (2 * m : ℝ) := by
  letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
  unfold signedL1
  rw [Fintype.sum_sum_type]
  simp [balancedSign]
  ring

/-- The squared `L2` norm is also the total number of states. -/
theorem balancedSign_signedL2_sq {m : ℕ} (hm : 0 < m) :
    letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
    signedL2 (balancedSign m) ^ 2 = (2 * m : ℝ) := by
  letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
  unfold signedL2
  rw [Real.sq_sqrt]
  · rw [Fintype.sum_sum_type]
    simp [balancedSign]
    ring
  · positivity

/-- The balanced vector saturates the generic `sqrt(card S)` norm conversion. -/
theorem balancedSign_saturates_l1_l2 {m : ℕ} (hm : 0 < m) :
    letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
    signedL1 (balancedSign m) =
      Real.sqrt (Fintype.card (Sum (Fin m) (Fin m))) *
        signedL2 (balancedSign m) := by
  letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
  have hL1 := balancedSign_signedL1 hm
  have hL2sq := balancedSign_signedL2_sq hm
  have hL2nonneg : 0 ≤ signedL2 (balancedSign m) := by
    unfold signedL2
    positivity
  have hcard : (Fintype.card (Sum (Fin m) (Fin m)) : ℝ) = 2 * m := by
    simp
    ring
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (Fintype.card (Sum (Fin m) (Fin m))) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      (Real.sqrt (Fintype.card (Sum (Fin m) (Fin m)))) ^ 2 =
        (Fintype.card (Sum (Fin m) (Fin m)) : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  have hsqrt_eq :
      Real.sqrt (Fintype.card (Sum (Fin m) (Fin m))) =
        signedL2 (balancedSign m) := by
    nlinarith [hL2sq, hsqrt_sq, hcard]
  rw [hL1, hsqrt_eq]
  nlinarith

/-- **Optimality of the dimension-only zero-mass conversion on even state
spaces.**

Among all constants `C` making

`‖v‖₁ ≤ C ‖v‖₂`

hold for every zero-mass signed vector on `Fin m ⊕ Fin m`, the least one is
exactly `sqrt(card S)`. -/
theorem sqrt_card_isLeast_zeroMass_l1_l2_constant {m : ℕ} (hm : 0 < m) :
    letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
    IsLeast
      {C : ℝ |
        ∀ v : Sum (Fin m) (Fin m) → ℝ,
          (∑ s, v s) = 0 → signedL1 v ≤ C * signedL2 v}
      (Real.sqrt (Fintype.card (Sum (Fin m) (Fin m)))) := by
  letI : Nonempty (Sum (Fin m) (Fin m)) := ⟨Sum.inl ⟨0, hm⟩⟩
  constructor
  · intro v hv
    exact signedL1_le_sqrt_card_mul_l2 v
  · intro C hC
    have hzero := balancedSign_sum_zero m
    have hbound := hC (balancedSign m) hzero
    have hsat := balancedSign_saturates_l1_l2 hm
    have hL2sq := balancedSign_signedL2_sq hm
    have hL2nonneg : 0 ≤ signedL2 (balancedSign m) := by
      unfold signedL2
      positivity
    have hL2pos : 0 < signedL2 (balancedSign m) := by
      have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
      nlinarith
    rw [hsat] at hbound
    nlinarith

end

end UEOT.V3.Compression.TopologyChangingGoaZeroMassNormSharpness
