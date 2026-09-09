import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# P-PRED-02 — target pushforward and protocol refinement

This module formalizes all three source clauses:

1. deterministic measurable target transformations push every predictive kernel;
2. enlarging the protocol family refines the generated sigma-factor;
3. a countable union of protocol families generates exactly the supremum of the
   individual sigma-factors.

The countable-union theorem is slightly stronger than the source statement:
monotonicity of the family is not needed for the sigma-algebra identity.
-/

namespace UEOT.V3.PredictionRefinement

open MeasureTheory ProbabilityTheory

universe uH uI uY₁ uY₂

variable {H : Type uH} {I : Type uI}
variable {Y₁ : Type uY₁} {Y₂ : Type uY₂}

def canonicalState [MeasurableSpace H] [MeasurableSpace Y₂]
    (K : I → Kernel H Y₂) : H → (I → Measure Y₂) :=
  fun h i => K i h

def pushTarget [MeasurableSpace H] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    (K : I → Kernel H Y₂) (T : Y₂ → Y₁) (_hT : Measurable T) :
    I → Kernel H Y₁ :=
  fun i => Kernel.map (K i) T

theorem pushTarget_apply [MeasurableSpace H] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    (K : I → Kernel H Y₂) (T : Y₂ → Y₁) (hT : Measurable T)
    (i : I) (h : H) :
    pushTarget K T hT i h = (K i h).map T := by
  simpa [pushTarget] using Kernel.map_apply (K i) hT h

theorem canonical_target_pushforward
    [MeasurableSpace H] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    (K : I → Kernel H Y₂) (T : Y₂ → Y₁) (hT : Measurable T) (h : H) :
    canonicalState (pushTarget K T hT) h =
      fun i => (K i h).map T := by
  funext i
  exact pushTarget_apply K T hT i h

section Protocols

universe uJ
variable {J : Type uJ} [MeasurableSpace H] [MeasurableSpace Y₂]

def sigmaCanonical (K : J → Kernel H Y₂) (S : Set J) : MeasurableSpace H :=
  MeasurableSpace.comap (fun h (i : S) => K i.1 h) inferInstance

theorem sigmaCanonical_eq_iSup_coordinates
    (K : J → Kernel H Y₂) (S : Set J) :
    sigmaCanonical K S =
      ⨆ i : S, MeasurableSpace.comap (fun h => K i.1 h) inferInstance := by
  exact MeasurableSpace.comap_process_pi (fun i : S => fun h => K i.1 h)

theorem protocol_refinement_sigma_le
    (K : J → Kernel H Y₂) {S T : Set J} (hST : S ⊆ T) :
    sigmaCanonical K S ≤ sigmaCanonical K T := by
  rw [sigmaCanonical_eq_iSup_coordinates, sigmaCanonical_eq_iSup_coordinates]
  refine iSup_le ?_
  intro i
  simpa using
    (le_iSup
      (fun j : T =>
        MeasurableSpace.comap (fun h => K j.1 h) inferInstance)
      ⟨i.1, hST i.2⟩)

theorem sigmaCanonical_iUnion
    (K : J → Kernel H Y₂) (S : ℕ → Set J) :
    sigmaCanonical K (⋃ n, S n) = ⨆ n, sigmaCanonical K (S n) := by
  apply le_antisymm
  · rw [sigmaCanonical_eq_iSup_coordinates]
    refine iSup_le ?_
    intro i
    rcases Set.mem_iUnion.mp i.2 with ⟨n, hin⟩
    calc
      MeasurableSpace.comap (fun h => K i.1 h) inferInstance
          ≤ sigmaCanonical K (S n) := by
              rw [sigmaCanonical_eq_iSup_coordinates]
              simpa using
                (le_iSup
                  (fun j : S n =>
                    MeasurableSpace.comap (fun h => K j.1 h) inferInstance)
                  ⟨i.1, hin⟩)
      _ ≤ ⨆ n, sigmaCanonical K (S n) :=
        le_iSup (fun n => sigmaCanonical K (S n)) n
  · refine iSup_le ?_
    intro n
    exact protocol_refinement_sigma_le (K := K)
      (S := S n) (T := ⋃ k, S k)
      (fun j hj => Set.mem_iUnion.mpr ⟨n, hj⟩)

theorem sigmaCanonical_iUnion_of_monotone
    (K : J → Kernel H Y₂) (S : ℕ → Set J) (_hS : Monotone S) :
    sigmaCanonical K (⋃ n, S n) = ⨆ n, sigmaCanonical K (S n) :=
  sigmaCanonical_iUnion K S

end Protocols

end UEOT.V3.PredictionRefinement
