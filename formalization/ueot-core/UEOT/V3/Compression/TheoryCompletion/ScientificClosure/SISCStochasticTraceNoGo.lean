import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteStochasticQuotient
import Mathlib.Tactic

/-!
# Stochastic observation trace equivalence ≠ Markov lumpability

A concrete six-state stochastic process shows that even equality of **all**
finite observed output-word distributions need not force a memoryless Markov
transition law on the resulting predictive equivalence classes.

The source of failure is a linear/convex alias: one latent state predicts
exactly the same observed future as a 50/50 mixture of two different latent
states, yet those alternatives have different transition masses into the
individual predictive classes. This is a theorem of finite stochastic
semantics, not a no-go against prediction itself.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.RecursiveSufficientState

private noncomputable def traceMass (i j : Fin 6) : ℝ :=
  match i.val, j.val with
  | 0, 4 => 1
  | 1, 2 => 1 / 2
  | 1, 3 => 1 / 2
  | 2, 2 => 1
  | 3, 5 => 1
  | 4, 2 => 1 / 2
  | 4, 5 => 1 / 2
  | 5, 5 => 1
  | _, _ => 0

private def traceOutput (i : Fin 6) : Bool := i = 5

/-- A finite model with x=0, y=1, latent pure-0=2, delayed-1=3,
intermediate randomizing state=4, and absorbing-1=5. -/
noncomputable def traceCounterexampleKernel : FiniteControlledStochasticKernel (Fin 6) Unit where
  mass := fun i _ j => traceMass i j
  nonneg := by
    intro i a j
    fin_cases i <;> fin_cases j <;> norm_num [traceMass]
  normalized := by
    intro i a
    fin_cases i <;>
      norm_num [traceMass, Fin.sum_univ_succ]

/-- Output-prefix probability starting at microstate i. For each observed
symbol, first emit the current output and then perform one Markov transition.
All observations use the same declared experiment protocol. -/
noncomputable def stochasticOutputTrace (i : Fin 6) : List Bool → ℝ
  | [] => 1
  | b :: bs =>
    if traceOutput i = b then
      ∑ j : Fin 6, traceCounterexampleKernel.mass i () j *
        stochasticOutputTrace j bs
    else 0

private theorem trace_row_zero (b : Bool) (bs : List Bool) :
    stochasticOutputTrace 0 (b :: bs) =
      if b = false then stochasticOutputTrace 4 bs else 0 := by
  cases b <;>
    norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
      traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff]

private theorem trace_row_one (b : Bool) (bs : List Bool) :
    stochasticOutputTrace 1 (b :: bs) =
      if b = false then
        (stochasticOutputTrace 2 bs + stochasticOutputTrace 3 bs) / 2
      else 0 := by
  cases b <;>
    norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
      traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff] <;> ring

private theorem trace_row_two (b : Bool) (bs : List Bool) :
    stochasticOutputTrace 2 (b :: bs) =
      if b = false then stochasticOutputTrace 2 bs else 0 := by
  cases b <;>
    norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
      traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff]

private theorem trace_row_three (b : Bool) (bs : List Bool) :
    stochasticOutputTrace 3 (b :: bs) =
      if b = false then stochasticOutputTrace 5 bs else 0 := by
  cases b <;>
    norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
      traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff]

private theorem trace_row_mid (b : Bool) (bs : List Bool) :
    stochasticOutputTrace 4 (b :: bs) =
      if b = false then
        (stochasticOutputTrace 2 bs + stochasticOutputTrace 5 bs) / 2
      else 0 := by
  cases b <;>
    norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
      traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff] <;> ring

/-- *Every* future output trace law of state 4 agrees with a convex mixture
of two distinct states 2 and 3. This is an exact for-all-words certificate. -/
theorem stochastic_trace_midpoint_alias (bs : List Bool) :
    stochasticOutputTrace 4 bs =
      (stochasticOutputTrace 2 bs + stochasticOutputTrace 3 bs) / 2 := by
  cases bs with
  | nil => norm_num [stochasticOutputTrace]
  | cons b bs =>
      cases b
      · rw [trace_row_mid, trace_row_two, trace_row_three]
        simp
      · rw [trace_row_mid, trace_row_two, trace_row_three]
        simp

/-- State 0 takes one step to the mixture-behavior latent state 4, while
state 1 takes one step to an actual 50/50 mixture of states 2 and 3.
They emit exactly the same output-word probabilities at every horizon. -/
theorem stochastic_all_future_trace_equivalent :
    stochasticOutputTrace 0 = stochasticOutputTrace 1 := by
  funext bs
  cases bs with
  | nil => rfl
  | cons b bs =>
      rw [trace_row_zero, trace_row_one]
      cases b
      · exact stochastic_trace_midpoint_alias bs
      · rfl

private theorem trace_two_false_false :
    stochasticOutputTrace 2 [false, false] = 1 := by
  norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
    traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff]

private theorem trace_three_false_false :
    stochasticOutputTrace 3 [false, false] = 0 := by
  norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
    traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff]

private theorem trace_mid_false_false :
    stochasticOutputTrace 4 [false, false] = (1 / 2 : ℝ) := by
  norm_num [stochasticOutputTrace, traceOutput, traceCounterexampleKernel,
    traceMass, Fin.sum_univ_succ] <;> simp [Fin.ext_iff]

/-- A predictive state with a 50/50 output trace differs from *each* of its
two extreme components; the distinction is measurable at horizon 2. -/
theorem stochastic_trace_mid_not_extreme :
    stochasticOutputTrace 2 ≠ stochasticOutputTrace 4 ∧
      stochasticOutputTrace 3 ≠ stochasticOutputTrace 4 := by
  constructor
  · intro h
    have hh := congrFun h [false, false]
    rw [trace_two_false_false, trace_mid_false_false] at hh
    norm_num at hh
  · intro h
    have hh := congrFun h [false, false]
    rw [trace_three_false_false, trace_mid_false_false] at hh
    norm_num at hh

/-- CENTRAL NO-GO: exact equality of **all finite stochastic observation
trace distributions** need not yield strong Markov lumpability of the
canonical predictive quotient. In this process, states 0 and 1 have exactly
equal trace laws, but transition to the class of state 4 has probability
1 versus 0. No exact Markov transition on that predictive class exists. -/
theorem all_future_trace_equivalence_not_markov_lumpable :
    ¬ StrongLumpability traceCounterexampleKernel stochasticOutputTrace := by
  intro hlump
  let c : ReachableState stochasticOutputTrace :=
    toReachable stochasticOutputTrace 4
  have hmass := hlump 0 1 stochastic_all_future_trace_equivalent () c
  have h0 : massIntoClass traceCounterexampleKernel
      stochasticOutputTrace 0 () c = 1 := by
    classical
    norm_num [massIntoClass, traceCounterexampleKernel, traceMass,
      Fin.sum_univ_succ, c] <;> rfl
  have h1 : massIntoClass traceCounterexampleKernel
      stochasticOutputTrace 1 () c = 0 := by
    classical
    rcases stochastic_trace_mid_not_extreme with ⟨h24, h34⟩
    simp [massIntoClass, traceCounterexampleKernel, traceMass,
      Fin.sum_univ_succ, c]
    change (if stochasticOutputTrace 2 = stochasticOutputTrace 4 then
        (2 : ℝ)⁻¹ else 0) +
      (if stochasticOutputTrace 3 = stochasticOutputTrace 4 then
        (2 : ℝ)⁻¹ else 0) = 0
    simp [h24, h34]
  rw [h0, h1] at hmass
  norm_num at hmass

/-- Therefore even a real-valued exact class-transition factorization is
impossible on the canonical all-output-traces state of this specific model.
A fortiori no normalized quotient Markov kernel can exist. -/
theorem all_future_trace_quotient_kernel_does_not_exist :
    ¬ ∃! Kbar : ReachableState stochasticOutputTrace → Unit →
        ReachableState stochasticOutputTrace → ℝ,
      ∀ x a c, Kbar (toReachable stochasticOutputTrace x) a c =
        massIntoClass traceCounterexampleKernel stochasticOutputTrace x a c := by
  intro h
  exact all_future_trace_equivalence_not_markov_lumpable
    ((strong_lumpability_iff_existsUnique_class_kernel
      traceCounterexampleKernel stochasticOutputTrace).mpr h)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
