import UEOT.V3.FiniteStablePartition

/-!
# P-ALG-01 — quotient laws for a controlled-stable finite partition

This module is independent of the terminating construction.  Given any stable
setoid that refines the source output/reward partition, it proves that output,
reward, and every action's one-step block distribution descend canonically to
the quotient.
-/

namespace UEOT.V3.FiniteStablePartition

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}
variable [Fintype X] [Fintype A]

/-- Output descends to any refinement of the initial output/reward partition. -/
def quotientOutput
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) : Quotient S → O :=
  fun q => Quotient.liftOn q M.output (by
    intro x y hxy
    exact (hSinit hxy).1)

@[simp] theorem quotientOutput_mk
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) (x : X) :
    quotientOutput M S hSinit ⟦x⟧ = M.output x := rfl

/-- Reward for each action descends to the same quotient. -/
def quotientReward
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) (a : A) : Quotient S → R :=
  fun q => Quotient.liftOn q (fun x => M.reward x a) (by
    intro x y hxy
    exact (hSinit hxy).2 a)

@[simp] theorem quotientReward_mk
    (M : Model X A R O) (S : Setoid X)
    (hSinit : Refines S (initialSetoid M)) (a : A) (x : X) :
    quotientReward M S hSinit a ⟦x⟧ = M.reward x a := rfl

/-- Exact one-step transition mass descends in both source and target classes
when `S` is controlled-stable. -/
noncomputable def quotientTransition
    (M : Model X A R O) (S : Setoid X) (hStable : Stable M S)
    (a : A) : Quotient S → Quotient S → ℝ :=
  fun q q' => Quotient.liftOn₂ q q'
    (fun x z => blockMass M S a x z)
    (by
      intro x₁ z₁ x₂ z₂ hx hz
      calc
        blockMass M S a x₁ z₁ = blockMass M S a x₂ z₁ := hStable hx a z₁
        _ = blockMass M S a x₂ z₂ := blockMass_target_eq M S hz a x₂)

@[simp] theorem quotientTransition_mk
    (M : Model X A R O) (S : Setoid X) (hStable : Stable M S)
    (a : A) (x z : X) :
    quotientTransition M S hStable a ⟦x⟧ ⟦z⟧ = blockMass M S a x z := rfl

/-- Exact one-step class probabilities are preserved under the quotient map.
`blockMass` is the source finite sum over the represented target block, with its
classical decidability kept internal rather than leaked into this theorem. -/
theorem quotient_one_step_preserved
    (M : Model X A R O) (S : Setoid X) (hStable : Stable M S)
    (a : A) (x z : X) :
    quotientTransition M S hStable a ⟦x⟧ ⟦z⟧ =
      blockMass M S a x z := by
  rw [quotientTransition_mk]

/-- Quotient transition masses are nonnegative. -/
theorem quotientTransition_nonneg
    (M : Model X A R O) (S : Setoid X) (hStable : Stable M S)
    (a : A) (q q' : Quotient S) :
    0 ≤ quotientTransition M S hStable a q q' := by
  refine Quotient.inductionOn q ?_
  intro x
  refine Quotient.inductionOn q' ?_
  intro z
  rw [quotientTransition_mk]
  unfold blockMass
  apply Finset.sum_nonneg
  intro y hy
  split_ifs
  · exact M.transition_nonneg a x y
  · exact le_rfl

end UEOT.V3.FiniteStablePartition
