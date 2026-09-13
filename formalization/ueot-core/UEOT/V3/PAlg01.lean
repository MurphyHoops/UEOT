import UEOT.V3.FiniteStablePartitionCoarsestFixedPoint
import UEOT.V3.FiniteStablePartitionFiniteHorizon

/-!
# P-ALG-01 — exact finite controlled stable quotient

Source-facing assembly of frozen Core 3 §28.5.

For a finite controlled Markov state model, the exact refinement starts from
output label plus the complete reward vector, terminates by a strict finite
relation-pair measure, and returns the coarsest controlled-stable refinement.
The induced quotient preserves output, reward, every-action one-step block
probabilities, stochastic normalization, and every corresponding finite-horizon
output-word law.

This theorem is deliberately scoped to the specified finite Markov state
domain.  It does not identify the quotient with an unconditional full-history
FFIPS object, does not introduce floating tolerances, and does not import the
§28.4 constraint-data construction.
-/

namespace UEOT.V3.PAlg01

open Finset
open UEOT.V3.FiniteStablePartition

universe uX uA uR uO

variable {X : Type uX} {A : Type uA} {R : Type uR} {O : Type uO}

/-- **P-ALG-01.** Exact finite controlled refinement terminates at a coarsest
stable quotient and the quotient preserves the source observable/reward,
one-step controlled stochastic laws, and all finite-horizon output-word laws.

Termination is machine-checked by the well-founded definition of `stabilizeStep`
used to construct `terminalSetoid`; the fixed-point conjunct exposes its
terminal character at the source-facing theorem boundary. -/
theorem p_alg_01
    [Fintype X] [Fintype A]
    (M : Model X A R O) :
    ∃ (S : Setoid X)
      (hinit : Refines S (initialSetoid M))
      (hstable : Stable M S),
      refineSetoid M S = S ∧
      (∀ Q : Setoid X,
        Refines Q (initialSetoid M) → Stable M Q → Refines Q S) ∧
      (∀ x : X,
        quotientOutput M S hinit ⟦x⟧ = M.output x) ∧
      (∀ (a : A) (x : X),
        quotientReward M S hinit a ⟦x⟧ = M.reward x a) ∧
      (∀ (a : A) (x z : X),
        quotientTransition M S hstable a ⟦x⟧ ⟦z⟧ =
          blockMass M S a x z) ∧
      (∀ (a : A) (x : X),
        (∑ t ∈ quotientClassBlocks S,
          ∑ y ∈ t, M.transition a x y) = 1) ∧
      (∀ (actions : List A) (word : List O) (x x' : X),
        S.r x x' →
          finiteHorizonOutputWordMass M actions word x =
            finiteHorizonOutputWordMass M actions word x') := by
  let S : Setoid X := terminalSetoid M
  have hinit : Refines S (initialSetoid M) := by
    dsimp [S]
    exact terminal_refines_initial M
  have hstable : Stable M S := by
    dsimp [S]
    exact terminal_stable M
  refine ⟨S, hinit, hstable, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (refineSetoid_eq_iff_stable M S).2 hstable
  · intro Q hQinit hQstable
    dsimp [S]
    exact terminal_coarsest M Q hQinit hQstable
  · intro x
    exact quotientOutput_mk M S hinit x
  · intro a x
    exact quotientReward_mk M S hinit a x
  · intro a x z
    exact quotient_one_step_preserved M S hstable a x z
  · intro a x
    exact transition_sum_over_quotientClassBlocks M S a x
  · intro actions word x x' hxx
    exact finiteHorizonOutputWordMass_eq_of_rel
      M S hinit hstable actions word hxx

end UEOT.V3.PAlg01
