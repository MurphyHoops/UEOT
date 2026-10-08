import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteStochasticQuotient
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# N1: a linear predictive realization survives failed Markov class-lumping

For a finite controlled stochastic system and deterministic emitted outputs,
the family of all future *action/output* response functions spans a vector
space closed under prepending any observation/action experiment. In contrast,
the set of microstate predictive-equivalence classes need not admit any
Markov transition kernel (SISCStochasticTraceNoGo).

This is a finite-state observable-operator / predictive-state representation
principle, not original linear system theory or an ontological identity axiom.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

universe uX uA uO

/-- Probability of an intervention/output *word*. At each symbol `(a,o)`
the system first emits `o=read x` and then applies action `a`. -/
noncomputable def controlledOutputTrace
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) : List (A × O) → ℝ
  | [] => 1
  | (a, o) :: w =>
      if read x = o then
        ∑ y, K.mass x a y * controlledOutputTrace K read y w
      else 0

/-- Prepending an observed action-event is linear on all real-valued trace
functions; no stochastic quotient or class-selection assumption is needed. -/
def prependEventLinear {A : Type uA} {O : Type uO} (a : A) (o : O) :
    (List (A × O) → ℝ) →ₗ[ℝ] (List (A × O) → ℝ) where
  toFun := fun f w => f ((a, o) :: w)
  map_add' := by
    intro f g
    funext w
    rfl
  map_smul' := by
    intro r f
    funext w
    rfl

/-- The exact finite-dimensional (at most |X|-generated) linear predictive
carrier. It is a span of genuine source-state response functions. -/
noncomputable def controlledTraceSpan
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O) :
    Submodule ℝ (List (A × O) → ℝ) :=
  Submodule.span ℝ (Set.range (controlledOutputTrace K read))

/-- An event shift of any *single* microscopic predictive response is still
in the span. The operator sends a generator to a controlled nonnegative
linear combination of generators, or to zero for an impossible observation. -/
theorem shifted_source_trace_in_span
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (x : X) (a : A) (o : O) :
    prependEventLinear a o (controlledOutputTrace K read x) ∈
      controlledTraceSpan K read := by
  classical
  by_cases h : read x = o
  · have hsum : prependEventLinear a o (controlledOutputTrace K read x) =
        ∑ y : X, K.mass x a y • controlledOutputTrace K read y := by
      funext w
      simp [prependEventLinear, controlledOutputTrace, h,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    exact Submodule.sum_mem _ (fun y _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self y)))
  · have hzero : prependEventLinear a o (controlledOutputTrace K read x) = 0 := by
      funext w
      simp [prependEventLinear, controlledOutputTrace, h]
    rw [hzero]
    exact Submodule.zero_mem _

/-- MAIN RESCUE: the **linear space** of all exact future trace predictions
is closed under every registered action/observation shift, regardless of
whether source trace equivalence is strongly Markov lumpable. This avoids
the invalid leap from predictive trace equality to an ordinary Markov chain
on the set of equivalent microscopic tokens. -/
theorem controlled_trace_span_shift_invariant
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O)
    (a : A) (o : O)
    (f : List (A × O) → ℝ)
    (hf : f ∈ controlledTraceSpan K read) :
    prependEventLinear a o f ∈ controlledTraceSpan K read := by
  unfold controlledTraceSpan at hf ⊢
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro g hg
    obtain ⟨x, rfl⟩ := hg
    exact shifted_source_trace_in_span K read x a o
  · simpa only [map_zero] using
      (Submodule.zero_mem (Submodule.span ℝ (Set.range (controlledOutputTrace K read))))
  · intro f g _ _ hf hg
    simpa only [map_add] using
      (Submodule.span ℝ (Set.range (controlledOutputTrace K read))).add_mem hf hg
  · intro r f _ hf
    simpa only [map_smul] using
      (Submodule.span ℝ (Set.range (controlledOutputTrace K read))).smul_mem r hf

/-- The linear predictive realization uses no more independent real
coordinates than the number of physical microscopic states. The trace word
space itself is infinite-dimensional; only the generated response subspace
is proved to have this finite dimension bound. -/
theorem controlled_trace_span_finrank_le_card
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X] [DecidableEq O]
    (K : FiniteControlledStochasticKernel X A) (read : X → O) :
    Module.finrank ℝ (controlledTraceSpan K read) ≤ Fintype.card X := by
  exact finrank_range_le_card (R := ℝ) (controlledOutputTrace K read)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
