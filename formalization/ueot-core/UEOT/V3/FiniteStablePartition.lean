import Mathlib

/-!
# P-ALG-01 — finite controlled stable-partition refinement

This module follows frozen Core 3 §28.5.  A finite controlled model carries a
common finite action set, an exact transition matrix for every action, rewards,
and an output label.  The initial partition keeps exactly the output label and
complete reward vector.  One refinement step splits a current block whenever
transition mass to some current block differs under some action.

No floating tolerance is used here: all equalities are exact.
-/

namespace UEOT.V3.FiniteStablePartition

open Finset

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}

/-- A finite controlled Markov model in the exact source sense of §28.5. -/
structure Model (X : Type uX) (A : Type uA) (R : Type uR) (O : Type uO)
    [Fintype X] where
  transition : A → X → X → ℝ
  reward : X → A → R
  output : X → O
  transition_nonneg : ∀ a x y, 0 ≤ transition a x y
  transition_sum_one : ∀ a x, ∑ y, transition a x y = 1

section Refinement

variable [Fintype X] [Fintype A]

/-- `S` refines `T` when every `S`-block is contained in a `T`-block. -/
def Refines (S T : Setoid X) : Prop :=
  ∀ ⦃x y⦄, S.r x y → T.r x y

@[refl] theorem Refines.refl (S : Setoid X) : Refines S S :=
  fun _ _ h => h

@[trans] theorem Refines.trans {S T U : Setoid X}
    (hST : Refines S T) (hTU : Refines T U) : Refines S U :=
  fun _ _ h => hTU (hST h)

/-- The initial partition groups states with identical output label and the
entire reward vector, exactly as in frozen §28.5. -/
def initialSetoid (M : Model X A R O) : Setoid X where
  r x y := M.output x = M.output y ∧ ∀ a, M.reward x a = M.reward y a
  iseqv := by
    constructor
    · intro x
      exact ⟨rfl, fun _ => rfl⟩
    · intro x y h
      exact ⟨h.1.symm, fun a => (h.2 a).symm⟩
    · intro x y z hxy hyz
      exact ⟨hxy.1.trans hyz.1, fun a => (hxy.2 a).trans (hyz.2 a)⟩

/-- Exact transition mass from `x` into the current `S`-block represented by
`z`, under action `a`. -/
noncomputable def blockMass
    (M : Model X A R O) (S : Setoid X) (a : A) (x z : X) : ℝ := by
  classical
  exact ∑ y : X, if S.r y z then M.transition a x y else 0

/-- One exact signature-refinement round.  The old block relation is retained,
so the operation can only split blocks, never merge them. -/
noncomputable def refineSetoid
    (M : Model X A R O) (S : Setoid X) : Setoid X where
  r x y :=
    S.r x y ∧
      ∀ a z, blockMass M S a x z = blockMass M S a y z
  iseqv := by
    constructor
    · intro x
      exact ⟨S.refl x, fun _ _ => rfl⟩
    · intro x y h
      exact ⟨S.symm h.1, fun a z => (h.2 a z).symm⟩
    · intro x y z hxy hyz
      exact ⟨S.trans hxy.1 hyz.1,
        fun a w => (hxy.2 a w).trans (hyz.2 a w)⟩

/-- A refinement round only splits the current partition. -/
theorem refineSetoid_refines
    (M : Model X A R O) (S : Setoid X) :
    Refines (refineSetoid M S) S := by
  intro x y hxy
  exact hxy.1

/-- Source-level controlled lumpability/stability for a partition. -/
def Stable (M : Model X A R O) (S : Setoid X) : Prop :=
  ∀ ⦃x y⦄, S.r x y →
    ∀ a z, blockMass M S a x z = blockMass M S a y z

/-- A partition is stable exactly when one refinement round leaves it fixed. -/
theorem refineSetoid_eq_iff_stable
    (M : Model X A R O) (S : Setoid X) :
    refineSetoid M S = S ↔ Stable M S := by
  constructor
  · intro h x y hxy a z
    have href : (refineSetoid M S).r x y := by
      rw [h]
      exact hxy
    exact href.2 a z
  · intro h
    apply Setoid.ext
    intro x y
    constructor
    · intro hxy
      exact hxy.1
    · intro hxy
      exact ⟨hxy, h hxy⟩

/-- Block mass does not depend on the chosen representative of the target
block. -/
theorem blockMass_target_eq
    (M : Model X A R O) (S : Setoid X)
    {z z' : X} (hzz : S.r z z') (a : A) (x : X) :
    blockMass M S a x z = blockMass M S a x z' := by
  classical
  unfold blockMass
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hyz : S.r y z
  · have hyz' : S.r y z' := S.trans hyz hzz
    simp [hyz, hyz']
  · have hyz' : ¬ S.r y z' := by
      intro h
      exact hyz (S.trans h (S.symm hzz))
    simp [hyz, hyz']

/-- The finite set of related ordered pairs is a concrete decreasing measure
for the refinement algorithm. -/
noncomputable def relPairs (S : Setoid X) : Finset (X × X) := by
  classical
  exact Finset.univ.filter (fun p => S.r p.1 p.2)

@[simp] theorem mem_relPairs (S : Setoid X) (x y : X) :
    (x, y) ∈ relPairs S ↔ S.r x y := by
  classical
  simp [relPairs]

/-- Relation refinement induces inclusion of the finite related-pair sets. -/
theorem relPairs_mono {S T : Setoid X} (hST : Refines S T) :
    relPairs S ⊆ relPairs T := by
  intro p hp
  rcases p with ⟨x, y⟩
  simpa using hST ((mem_relPairs S x y).1 hp)

/-- The finite pair representation is faithful. -/
theorem setoid_eq_of_relPairs_eq {S T : Setoid X}
    (h : relPairs S = relPairs T) : S = T := by
  apply Setoid.ext
  intro x y
  have hp := congrArg (fun U : Finset (X × X) => (x, y) ∈ U) h
  simpa using hp

end Refinement

end UEOT.V3.FiniteStablePartition
