import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFutureResponseCore
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteStochasticQuotient
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCKernelLineageExamples
import Mathlib.Tactic

/-!
# UMC-01 — same-process deterministic/stochastic predictive bridge

For any finite deterministic controlled process, derive its normalized
Dirac stochastic kernel from the very same transition step. Prove that
canonical all-future predictive equivalence automatically yields strong
lumpability and hence a unique normalized stochastic quotient, using the
already proven SISC iff theorem. The generic stochastic case still
requires strong lumpability and can fail.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
open UEOT.V3.Compression.RecursiveSufficientState

universe uX uA uO uQ

/-- Normalized finite Dirac stochastic law derived from one deterministic process. -/
noncomputable def diracControlledKernel
    {X : Type uX} {A : Type uA} [Fintype X]
    (step : X → A → X) : FiniteControlledStochasticKernel X A := by
  classical
  refine {
    mass := fun x a y => if y = step x a then 1 else 0
    nonneg := ?_
    normalized := ?_
  }
  · intro x a y
    split_ifs <;> norm_num
  · intro x a
    simp

theorem dirac_kernel_mass_exact
    {X : Type uX} {A : Type uA} [Fintype X] [DecidableEq X]
    (step : X → A → X) (x y : X) (a : A) :
    (diracControlledKernel step).mass x a y =
      if y = step x a then 1 else 0 := by
  classical
  by_cases h : y = step x a <;> simp [diracControlledKernel, h]

/-- Class mass is the indicator of the successor's one quotient class. -/
theorem dirac_massIntoClass_exact
    {X : Type uX} {A : Type uA} {Q : Type uQ}
    [Fintype X] [DecidableEq X] [DecidableEq Q]
    (step : X → A → X) (q : X → Q)
    (x : X) (a : A) (c : ReachableState q) :
    massIntoClass (diracControlledKernel step) q x a c =
      if q (step x a) = c.1 then 1 else 0 := by
  classical
  unfold massIntoClass
  simp_rw [dirac_kernel_mass_exact]
  calc
    (∑ y : X, if q y = c.1 then
       (if y = step x a then (1 : ℝ) else 0) else 0) =
      ∑ y : X, if y = step x a then
        (if q y = c.1 then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hq : q y = c.1 <;> by_cases hy : y = step x a <;>
            simp [hq, hy]
    _ = if q (step x a) = c.1 then 1 else 0 := by simp

/-- Exact deterministic update congruence implies strong lumpability
for the derived stochastic semantics, rather than an external K. -/
theorem dirac_strong_lumpability_of_congruence
    {X : Type uX} {A : Type uA} {Q : Type uQ} [Fintype X]
    (step : X → A → X) (q : X → Q)
    (hcongr : ∀ x y, q x = q y → ∀ a,
       q (step x a) = q (step y a)) :
    StrongLumpability (diracControlledKernel step) q := by
  intro x y hxy a c
  classical
  rw [dirac_massIntoClass_exact, dirac_massIntoClass_exact,
    hcongr x y hxy a]

theorem canonical_future_dirac_strong_lumpability
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X]
    (step : X → A → X) (read : X → O) :
    StrongLumpability (diracControlledKernel step)
      (canonicalFuture step read) := by
  apply dirac_strong_lumpability_of_congruence
  intro x y hxy a
  apply Subtype.ext
  exact futureResponse_inputFiberCompatible step read
    (congrArg Subtype.val hxy) a

/-- New strict bridge: the identical finite deterministic world process
has a canonical predictive state with a uniquely descended normalized,
nonnegative Markov kernel. This discharges the strong-lumpability premise
in this conditional deterministic-Dirac class only. -/
theorem existsUnique_canonical_future_stochastic_quotient
    {X : Type uX} {A : Type uA} {O : Type uO}
    [Fintype X]
    (step : X → A → X) (read : X → O) :
    letI : Fintype (ReachableState (canonicalFuture step read)) :=
      Fintype.ofFinite _
    ∃! Kbar : FiniteControlledStochasticKernel
      (ReachableState (canonicalFuture step read)) A,
      ∀ x a c, Kbar.mass
        (toReachable (canonicalFuture step read) x) a c =
        massIntoClass (diracControlledKernel step)
          (canonicalFuture step read) x a c := by
  exact (strong_lumpability_iff_existsUnique_stochastic_quotient
    (diracControlledKernel step) (canonicalFuture step read)).mp
      (canonical_future_dirac_strong_lumpability step read)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
