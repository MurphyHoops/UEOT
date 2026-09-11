import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# P-STAT-07 — kernel transport covariance of MMD

The frozen source defines MMD through a Bochner-integrable RKHS feature mean
`mu_P = E_P phi(Y)` and then transports the kernel synchronously through a
bimeasurable bijection.  This module exposes that mean-embedding semantics
directly.  It also retains the standard three-kernel-expectation representation
as an independent algebraic check.
-/

namespace UEOT.V3.MMDTransport

open MeasureTheory Real

universe uX uX' uH

variable {X : Type uX} {X' : Type uX'}
variable [MeasurableSpace X] [MeasurableSpace X']

/-- Synchronous transport of a kernel through a bimeasurable bijection. -/
def transportedKernel (e : X ≃ᵐ X') (k : X → X → ℝ) : X' → X' → ℝ :=
  fun x' y' => k (e.symm x') (e.symm y')

/-- Pull a Hilbert feature map through the same bimeasurable equivalence. -/
def transportedFeature {H : Type uH}
    (e : X ≃ᵐ X') (phi : X → H) : X' → H :=
  fun x' => phi (e.symm x')

section MeanEmbedding

variable {H : Type uH}
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Bochner mean embedding associated with a Hilbert feature map. -/
noncomputable def meanEmbedding (phi : X → H) (P : Measure X) : H :=
  ∫ x, phi x ∂P

/-- MMD in exactly the source mean-embedding semantics. -/
noncomputable def featureMMD
    (phi : X → H) (P Q : Measure X) : ℝ :=
  ‖meanEmbedding phi P - meanEmbedding phi Q‖

/-- Mean embeddings are exactly covariant under a common bimeasurable change of
variables when the feature map is pulled back synchronously. -/
theorem meanEmbedding_map_equiv
    (e : X ≃ᵐ X') (phi : X → H) (P : Measure X) :
    meanEmbedding (transportedFeature e phi) (P.map e) =
      meanEmbedding phi P := by
  unfold meanEmbedding
  simpa [transportedFeature] using
    (MeasureTheory.integral_map_equiv (μ := P) e
      (fun x' => transportedFeature e phi x'))

/-- **P-STAT-07 in mean-embedding form.** Synchronous transport of the
representation leaves the RKHS mean-embedding distance unchanged. -/
theorem p_stat_07_meanEmbedding
    (e : X ≃ᵐ X') (phi : X → H) (P Q : Measure X) :
    featureMMD (transportedFeature e phi) (P.map e) (Q.map e) =
      featureMMD phi P Q := by
  simp [featureMMD, meanEmbedding_map_equiv]

end MeanEmbedding

section FeatureKernel

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Scalar kernel realized by a Hilbert feature map.  In the source RKHS one
uses the canonical section feature `phi x = k(x, ·)`. -/
def featureKernel (phi : X → H) : X → X → ℝ :=
  fun x y => inner ℝ (phi x) (phi y)

/-- Pulling back the feature map realizes exactly the synchronously transported
kernel `k_T(Tx,Ty)=k(x,y)`. -/
theorem featureKernel_transportedFeature
    (e : X ≃ᵐ X') (phi : X → H) :
    featureKernel (transportedFeature e phi) =
      transportedKernel e (featureKernel phi) := by
  funext x' y'
  rfl

end FeatureKernel

/-- Mixed kernel expectation `E[k(X,Y)]` under laws `P` and `Q`. -/
noncomputable def kernelExpectation
    (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  ∫ x, ∫ y, k x y ∂Q ∂P

/-- One mixed kernel expectation is exactly invariant under synchronous
transport of both laws and the kernel. -/
theorem kernelExpectation_map_equiv
    (e : X ≃ᵐ X') (k : X → X → ℝ) (P Q : Measure X) :
    kernelExpectation (transportedKernel e k) (P.map e) (Q.map e) =
      kernelExpectation k P Q := by
  unfold kernelExpectation
  rw [MeasureTheory.integral_map_equiv (μ := P) e]
  apply integral_congr_ae
  filter_upwards with x
  simpa [transportedKernel] using
    (MeasureTheory.integral_map_equiv (μ := Q) e
      (fun y' => transportedKernel e k (e x) y'))

/-- Standard three-expectation expression for MMD squared. -/
noncomputable def mmdSq
    (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  kernelExpectation k P P + kernelExpectation k Q Q -
    2 * kernelExpectation k P Q

/-- Energy-form MMD.  On the positive-definite integrable source domain this is
the standard square-root representation of the RKHS mean-embedding distance. -/
noncomputable def mmd
    (k : X → X → ℝ) (P Q : Measure X) : ℝ :=
  sqrt (mmdSq k P Q)

/-- The three-expectation MMD square is representation-covariant. -/
theorem mmdSq_map_equiv
    (e : X ≃ᵐ X') (k : X → X → ℝ) (P Q : Measure X) :
    mmdSq (transportedKernel e k) (P.map e) (Q.map e) =
      mmdSq k P Q := by
  simp [mmdSq, kernelExpectation_map_equiv]

/-- Energy-form covariance, matching the source's stated three-expectation
proof. -/
theorem p_stat_07
    (e : X ≃ᵐ X') (k : X → X → ℝ) (P Q : Measure X) :
    mmd (transportedKernel e k) (P.map e) (Q.map e) =
      mmd k P Q := by
  simp [mmd, mmdSq_map_equiv]

end UEOT.V3.MMDTransport
