import UEOT.V3.Compression.CrossTrack.DualIsolationCanonical
import UEOT.V3.DecoderRadius

/-!
# Dual Isolation — P-CAR-04 decoder-radius bridge

P-CAR-04 supplies a genuine quantitative ambiguity certificate: the diameter
of all responses merged by one readout fibre is at most twice the optimal
decoder radius.  This module feeds that domain quantity into Parent Binding
and Track S.
-/

namespace UEOT.V3.Compression.CrossTrack

open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uH uI uZ uA uS

noncomputable section

variable {H : Type uH} {I : Type uI} {Z : Type uZ} {A : Type uA}
variable [Nonempty H] [Nonempty I] [MetricSpace A]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance dualIsolationDecoderDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- P-CAR-04 converts optimal decoder radius into a within-readout-fibre
assembly-diameter certificate. -/
theorem assemblyDist_le_two_decoderRadius
    (R : H → Z) (response : H → I → A)
    {e r : ℝ}
    (he : IsLUB (UEOT.V3.DecoderRadius.FiberDistances R response) e)
    (hr : IsGLB (UEOT.V3.DecoderRadius.DecoderBounds R response) r)
    {h h' : H} (hR : R h = R h') (i : I) :
    dist (response h i) (response h' i) ≤ 2 * r := by
  have hdistMem : dist (response h i) (response h' i) ∈
      UEOT.V3.DecoderRadius.FiberDistances R response :=
    ⟨h, h', i, hR, rfl⟩
  have hdistE : dist (response h i) (response h' i) ≤ e := he.1 hdistMem
  have hhalf :=
    (UEOT.V3.DecoderRadius.decoder_radius_bounds R response he hr).1
  linarith

/-- The P-CAR-04 optimal decoder radius is nonnegative on a nonempty response
domain. -/
theorem decoderRadius_nonneg
    (R : H → Z) (response : H → I → A)
    {e r : ℝ}
    (he : IsLUB (UEOT.V3.DecoderRadius.FiberDistances R response) e)
    (hr : IsGLB (UEOT.V3.DecoderRadius.DecoderBounds R response) r) :
    0 ≤ r := by
  let h0 : H := Classical.choice inferInstance
  let i0 : I := Classical.choice inferInstance
  have hzeroMem : (0 : ℝ) ∈
      UEOT.V3.DecoderRadius.FiberDistances R response := by
    refine ⟨h0, h0, i0, rfl, ?_⟩
    simp
  have he0 : 0 ≤ e := he.1 hzeroMem
  have hhalf :=
    (UEOT.V3.DecoderRadius.decoder_radius_bounds R response he hr).1
  linarith

/-- **P-CAR-04 -> parent-semantic stability.**

For one response coordinate `i0`, an optimal decoder radius `r` bounds the
assembly diameter of every parent completion sharing a readout value by
`2 r`.  Parent realization sensitivity and semantic isolation then give a
long-run semantic radius `2 L r / kappa`. -/
theorem decoderRadius_parentSemanticDiameter
    (R : H → Z) (response : H → I → A)
    {e r : ℝ}
    (he : IsLUB (UEOT.V3.DecoderRadius.FiberDistances R response) e)
    (hr : IsGLB (UEOT.V3.DecoderRadius.DecoderBounds R response) r)
    (i0 : I)
    (K : H → Matrix S S ℝ)
    (hK : ∀ h, K h ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz (fun h => response h i0) K hK)
    (mu : H → stdSimplex ℝ S)
    (hmu : ∀ h, mu h ∈ invariantLawSet (K h) (hK h))
    (z : Z)
    (hfiberNonempty : ∃ h, R h = z)
    (kappaMin : ℝ)
    (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hisolationFloor : ∀ h, R h = z →
      kappaMin ≤ l1ResidualConorm (K h)) :
    fiberSemanticDiameter R mu z ≤
      bind.L * (2 * r) / kappaMin := by
  apply parentSemanticDiameter_of_binding
    R (fun h => response h i0) K hK bind mu hmu z hfiberNonempty
    (2 * r) kappaMin
  · exact mul_nonneg (by norm_num) (decoderRadius_nonneg R response he hr)
  · exact hkappaMin
  · exact hcard
  · intro h h' hh hh'
    exact assemblyDist_le_two_decoderRadius R response he hr
      (hh.trans hh'.symm) i0
  · exact hisolationFloor

end

end UEOT.V3.Compression.CrossTrack
