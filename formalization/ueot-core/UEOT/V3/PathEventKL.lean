import UEOT.V3.InformationEventBernoulli

/-!
# P-KL-01 — survival/event information lower bound

The frozen Core 3 source considers a baseline path law `P0`, an absolutely
continuous reachable path law `Q ≪ P0`, and a measurable event `A`. Writing
`q = P0(A)` and `p = Q(A)`, it states

`D_KL(Q || P0) ≥ d_Bern(p || q)`.

Here `dBern` is exactly the KL divergence between the corresponding real
Bernoulli laws.  The underlying indicator-pushforward identification and KL
data-processing theorem already live in `InformationEventBernoulli`; this file
adds only the source-facing name and wrapper.  The explicit source hypothesis
`Q ≪ P0` is retained even though the existing data-processing theorem is
stronger and does not need it.
-/

namespace UEOT.V3.PathEventKL

open MeasureTheory InformationTheory
open UEOT.V3.InformationBernoulliKL
open UEOT.V3.InformationEventBernoulli

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Bernoulli relative entropy in the frozen P-KL-01 notation. -/
noncomputable def dBern (p q : ℝ) : ENNReal :=
  klDiv (bernoulliLaw p) (bernoulliLaw q)

/-- Source-facing P-KL-01.

For any measurable event, KL on the full path/state law dominates the KL of
the induced event indicator.  The source absolute-continuity hypothesis is
kept explicitly, and therefore its `q=0` / `q=1` boundary discussion is also
covered. -/
theorem p_kl_01
    (Q P0 : Measure X)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P0]
    (A : Set X) (hA : MeasurableSet A)
    (_hQP0 : Q ≪ P0) :
    dBern (Q.real A) (P0.real A) ≤ klDiv Q P0 := by
  simpa [dBern] using bernoulliKL_event_le Q P0 A hA

end UEOT.V3.PathEventKL
