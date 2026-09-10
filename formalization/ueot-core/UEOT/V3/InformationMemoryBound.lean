import UEOT.V3.InformationStatistic
import UEOT.V3.InformationDiscreteEntropy
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# P-INFO-01 — discrete predictive-memory lower bound

This module closes the frozen source chain

  I(H;Y) = I(M;Y) + I(H;Y|M),
  I(H;Y|M) ≤ ε  =>  I(M;Y) ≥ I(H;Y) - ε,
  M discrete    =>  H(M) ≥ I(H;Y) - ε.

The last step does not introduce a new UEOT information axiom.  For a
countable-discrete macrostate and standard-Borel future space, Mathlib's
conditional kernel disintegrates an arbitrary `(M,Y)` joint law as
`P_M ⊗ₘ K`.  The already proved copied-pair data-processing theorem then gives
`I(M;Y) ≤ KL(copy(P_M) || P_M ⊗ P_M)`, and the discrete entropy module
identifies that KL divergence with extended Shannon entropy, including the
`H(M)=∞` case.
-/

namespace UEOT.V3.InformationMemoryBound

open MeasureTheory InformationTheory
open scoped ENNReal ProbabilityTheory
open UEOT.V3.InformationEntropyBound
open UEOT.V3.InformationDiscreteEntropy
open UEOT.V3.InformationStatistic

universe uH uM uY

variable {H : Type uH} {M : Type uM} {Y : Type uY}
variable [MeasurableSpace H] [MeasurableSpace M] [MeasurableSpace Y]

/-- For any probability joint law of a countable-discrete `M` and a
standard-Borel `Y`, mutual information is bounded by the extended Shannon
entropy of the `M` marginal. -/
theorem mutualInfo_le_discreteShannonEntropy
    [Countable M] [MeasurableSingletonClass M]
    [StandardBorelSpace Y] [Nonempty Y]
    (ρ : Measure (M × Y)) [IsProbabilityMeasure ρ] :
    mutualInfo ρ ≤ discreteShannonEntropy ρ.fst := by
  have hdis : ρ.fst ⊗ₘ ρ.condKernel = ρ :=
    Measure.disintegrate ρ ρ.condKernel
  have h := mutualInfo_compProd_le_copy_kl ρ.fst ρ.condKernel
  rw [hdis, copy_kl_eq_discreteShannonEntropy ρ.fst] at h
  exact h

/-- Source-facing additive form.  If the conditional predictive information
left after the deterministic statistic `M=f(H)` is at most `ε`, then the total
predictive information cannot exceed the macrostate Shannon entropy plus
`ε`. -/
theorem predictive_info_le_entropy_add
    [StandardBorelSpace H] [Nonempty H]
    [Countable M] [MeasurableSingletonClass M]
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → M) (hf : Measurable f)
    {ε : ENNReal}
    (hε : conditionalMutualInfoStatistic μ f ≤ ε) :
    mutualInfo μ ≤
      discreteShannonEntropy (statisticJoint μ f hf).fst + ε := by
  calc
    mutualInfo μ ≤ mutualInfo (statisticJoint μ f hf) + ε :=
      mutualInfo_statistic_ge_sub_of_conditional_le μ f hf hε
    _ ≤ discreteShannonEntropy (statisticJoint μ f hf).fst + ε :=
      add_le_add_right
        (mutualInfo_le_discreteShannonEntropy (statisticJoint μ f hf)) ε

/-- **P-INFO-01, discrete entropy corollary.**  This is the literal frozen
source inequality, written with the ordered subtraction on `ℝ≥0∞` so that the
statement remains meaningful without collapsing an infinite Shannon entropy
through `toReal`. -/
theorem p_info_01_discrete_entropy
    [StandardBorelSpace H] [Nonempty H]
    [Countable M] [MeasurableSingletonClass M]
    [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure (H × Y)) [IsProbabilityMeasure μ]
    (f : H → M) (hf : Measurable f)
    {ε : ENNReal}
    (hε : conditionalMutualInfoStatistic μ f ≤ ε) :
    mutualInfo μ - ε ≤
      discreteShannonEntropy (statisticJoint μ f hf).fst := by
  rw [tsub_le_iff_right]
  simpa [add_comm] using predictive_info_le_entropy_add μ f hf hε

end UEOT.V3.InformationMemoryBound
