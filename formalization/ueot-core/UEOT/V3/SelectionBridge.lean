import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# P-BRG-02 — behavioral equivalence and selection indistinguishability

Source contract:

* a controller type θ induces an environmental path law Q_θ^e;
* reproduction is completely determined by one common functional
  R_e(θ) = ℛ_e(Q_θ^e);
* no type-dependent mutation or additional replication channel is included in
  this bridge.

The theorem therefore separates two claims:

1. equal behavioral/path-law responses imply equal reproductive fitness;
2. any selection update that uses only this bridge assigns the same
   multiplicative fitness factor to behaviorally equivalent types.

Different mutation neighborhoods, material costs, or other type-dependent
channels are model changes and are intentionally not represented here.
-/

namespace UEOT.V3.SelectionBridge

universe uΘ uQ

structure ReplicationBridge (Θ : Type uΘ) (Q : Type uQ) where
  response : Θ → Q
  replicate : Q → ℝ

namespace ReplicationBridge

variable {Θ : Type uΘ} {Q : Type uQ}

def fitness (B : ReplicationBridge Θ Q) (θ : Θ) : ℝ :=
  B.replicate (B.response θ)

def BehaviorEquivalent (B : ReplicationBridge Θ Q) (θ θ' : Θ) : Prop :=
  B.response θ = B.response θ'

theorem behavior_equiv_fitness_eq
    (B : ReplicationBridge Θ Q) {θ θ' : Θ}
    (h : B.BehaviorEquivalent θ θ') :
    B.fitness θ = B.fitness θ' := by
  exact congrArg B.replicate h

def selectionWeight
    (B : ReplicationBridge Θ Q) (mass : Θ → ℝ) (θ : Θ) : ℝ :=
  mass θ * B.fitness θ

theorem behavior_equiv_same_multiplier
    (B : ReplicationBridge Θ Q) {θ θ' : Θ}
    (h : B.BehaviorEquivalent θ θ') :
    B.fitness θ = B.fitness θ' :=
  B.behavior_equiv_fitness_eq h

theorem behavior_equiv_selection_cross_eq
    (B : ReplicationBridge Θ Q) (mass : Θ → ℝ) {θ θ' : Θ}
    (h : B.BehaviorEquivalent θ θ') :
    B.selectionWeight mass θ * mass θ' =
      B.selectionWeight mass θ' * mass θ := by
  unfold selectionWeight
  rw [B.behavior_equiv_fitness_eq h]
  ring

theorem behavior_equiv_positive_ratio_preserved
    (B : ReplicationBridge Θ Q) (mass : Θ → ℝ) {θ θ' : Θ}
    (h : B.BehaviorEquivalent θ θ')
    (hfit : 0 < B.fitness θ)
    (hmass : mass θ' ≠ 0) :
    B.selectionWeight mass θ / B.selectionWeight mass θ' =
      mass θ / mass θ' := by
  have hfit' : B.fitness θ' = B.fitness θ :=
    (B.behavior_equiv_fitness_eq h).symm
  simp only [selectionWeight, hfit']
  field_simp [hmass, ne_of_gt hfit]

end ReplicationBridge

end UEOT.V3.SelectionBridge
