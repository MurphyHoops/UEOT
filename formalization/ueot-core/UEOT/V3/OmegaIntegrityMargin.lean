import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# P-OMG-02 — causal-integrity margin is 1-Lipschitz

For a fixed nonempty failure set `F`, the frozen Core 3 source defines the
integrity margin as the metric distance from the current mechanism/model point
to `F`.  Mathlib already proves that point-to-set distance is 1-Lipschitz, so
this layer only exposes the source notation and theorem.
-/

namespace UEOT.V3.OmegaIntegrityMargin

universe u
variable {X : Type u} [PseudoMetricSpace X]

/-- UEOT causal-integrity margin: distance to the failure set. -/
noncomputable def integrityMargin (F : Set X) (T : X) : ℝ :=
  Metric.infDist T F

/-- Source-facing P-OMG-02.  The source assumes `F` nonempty; Mathlib's
point-to-set Lipschitz theorem is actually valid without that extra condition,
so `hF` records the source domain while the proof uses the stronger library
result. -/
theorem p_omg_02
    (F : Set X) (_hF : F.Nonempty) (T S : X) :
    |integrityMargin F T - integrityMargin F S| ≤ dist T S := by
  have h := (Metric.lipschitz_infDist_pt F).dist_le_mul T S
  simpa [integrityMargin, Real.dist_eq] using h

end UEOT.V3.OmegaIntegrityMargin
