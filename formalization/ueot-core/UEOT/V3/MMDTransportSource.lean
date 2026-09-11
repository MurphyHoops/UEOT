import UEOT.V3.MMDTransport

/-!
# P-STAT-07 source wrapper

The frozen theorem speaks simultaneously about the transported kernel and the
RKHS mean-embedding MMD.  This wrapper keeps those two pieces in one statement:
the pulled-back Hilbert feature realizes exactly the transported kernel, and
its mean-embedding distance is unchanged under the bimeasurable bijection.
-/

namespace UEOT.V3.MMDTransportSource

open MeasureTheory
open UEOT.V3.MMDTransport

universe uX uX' uH

variable {X : Type uX} {X' : Type uX'} {H : Type uH}
variable [MeasurableSpace X] [MeasurableSpace X']
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **P-STAT-07, source-facing feature realization.**  For a Hilbert/RKHS
feature realization of `k`, synchronous transport of both the law and feature
map realizes `k_T(Tx,Ty)=k(x,y)` and preserves the corresponding MMD. -/
theorem p_stat_07_source
    (e : X ≃ᵐ X') (phi : X → H) (P Q : Measure X) :
    featureKernel (transportedFeature e phi) =
        transportedKernel e (featureKernel phi) ∧
      featureMMD (transportedFeature e phi) (P.map e) (Q.map e) =
        featureMMD phi P Q := by
  exact ⟨featureKernel_transportedFeature e phi,
    p_stat_07_meanEmbedding e phi P Q⟩

end UEOT.V3.MMDTransportSource
