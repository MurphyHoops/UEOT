import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.StochasticPredictiveNullspace
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BeliefTimingBoundary
import Mathlib.Tactic

/-!
# Finite completeness of predictive separating probes

Every finite family of underlying microscopic states has a finite set of
true future-response coordinates separating every pair of distinct entire
future functions. This is an existential finite-extraction result, not an
algorithmic statistical certificate and NOT a strong-lumpability theorem:
pairwise separation is weaker than linear independence / indicator spanning.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uX uW uA uO

/-- A finite collection of functions admits a finite set of input probes
whose equality tests recover exactly equality of the full functions. -/
theorem finite_family_has_complete_separating_probes
    {X : Type uX} {W : Type uW} [Fintype X]
    (F : X → W → ℝ) :
    ∃ tests : Finset W,
      ∀ x y : X, (∀ w ∈ tests, F x w = F y w) → F x = F y := by
  classical
  have hwitness (x y : X) (hne : F x ≠ F y) :
      ∃ w : W, F x w ≠ F y w := by
    by_contra hnone
    apply hne
    funext w
    by_contra hdiff
    exact hnone ⟨w, hdiff⟩
  have hpair (x y : X) :
      ∃ s : Finset W,
        (∀ w ∈ s, F x w = F y w) → F x = F y := by
    by_cases heq : F x = F y
    · exact ⟨∅, fun _ => heq⟩
    · obtain ⟨w, hw⟩ := hwitness x y heq
      refine ⟨{w}, ?_⟩
      intro hall
      exact False.elim (hw (hall w (by simp)))
  let pairTests : X → X → Finset W := fun x y =>
    Classical.choose (hpair x y)
  refine ⟨Finset.univ.biUnion (fun x : X =>
    Finset.univ.biUnion (fun y : X => pairTests x y)), ?_⟩
  intro x y hall
  apply Classical.choose_spec (hpair x y)
  intro w hw
  apply hall w
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨x, y, hw⟩

/-- In any finite stochastic controlled system, a single finite probe
set distinguishes exactly the same microscopic states as *all* declared
future action-observation words. No lumpability is needed for this fact. -/
theorem exists_finite_complete_stochastic_future_probes
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O) :
    ∃ probes : Finset (List (A × O)),
      ∀ x y : X,
        (∀ w ∈ probes,
          stochasticFuture K read x w = stochasticFuture K read y w) ↔
        stochasticFuture K read x = stochasticFuture K read y := by
  obtain ⟨probes, hcomplete⟩ :=
    finite_family_has_complete_separating_probes (stochasticFuture K read)
  refine ⟨probes, ?_⟩
  intro x y
  constructor
  · exact hcomplete x y
  · intro h w _
    exact congrFun h w

/-- Finite separating observations can exist even where no Markov
transition quotient exists on their (fully predictive) equivalence classes.
This guards against confusing injectivity of tests with lumpability. -/
theorem finite_predictive_separation_does_not_force_markov_quotient :
    (∃ probes : Finset (List Bool),
      ∀ x y : Fin 6,
        (∀ w ∈ probes,
          stochasticOutputTrace x w =
          stochasticOutputTrace y w) ↔
          stochasticOutputTrace x = stochasticOutputTrace y) ∧
    ¬ StrongLumpability traceCounterexampleKernel stochasticOutputTrace := by
  obtain ⟨probes, hcomplete⟩ :=
    finite_family_has_complete_separating_probes stochasticOutputTrace
  refine ⟨⟨probes, ?_⟩, unrestricted_stochastic_trace_lumping_is_false⟩
  intro x y
  constructor
  · exact hcomplete x y
  · intro h w _
    exact congrFun h w

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
