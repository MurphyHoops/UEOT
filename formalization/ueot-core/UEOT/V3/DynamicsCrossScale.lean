import UEOT.V3.TotalVariation
import UEOT.V3.InformationPacking

/-!
# P-DYN-04 — cross-scale quotients of one microscopic process

Let two readouts `f_s : X → M_s` and `f_r : X → M_r` satisfy
`f_r = c ∘ f_s`.  If both macro kernels approximate pushforwards of the
same microscopic transition law with TV errors `ε_s` and `ε_r`, then on
the reachable image of `f_s` their cross-scale discrepancy is at most
`ε_s + ε_r`.

The proof is exactly the source proof: insert the common microscopic
pushforward, use TV data processing on the fine-scale error, then use the
triangle inequality.  No claim is made outside the reachable image.
-/

namespace UEOT.V3.DynamicsCrossScale

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.InformationPacking

universe uX uMs uMr uA

variable {X : Type uX} {Ms : Type uMs} {Mr : Type uMr} {A : Type uA}
variable [MeasurableSpace X] [MeasurableSpace Ms] [MeasurableSpace Mr]

/-- Source-facing approximate P-DYN-04 bound on the reachable fine-scale
macro image. -/
theorem p_dyn_04_cross_scale_tv
    (P : X → A → Measure X)
    (Ps : Ms → A → Measure Ms)
    (Pr : Mr → A → Measure Mr)
    (fs : X → Ms) (fr : X → Mr) (c : Ms → Mr)
    (hfs : Measurable fs) (hfr : Measurable fr) (hc : Measurable c)
    (hcomp : ∀ x, fr x = c (fs x))
    (hP : ∀ x a, IsProbabilityMeasure (P x a))
    (hPs : ∀ m a, IsProbabilityMeasure (Ps m a))
    (hPr : ∀ m a, IsProbabilityMeasure (Pr m a))
    (εs εr : ℝ)
    (hs : ∀ x a,
      tvDist ((P x a).map fs) (Ps (fs x) a) ≤ εs)
    (hr : ∀ x a,
      tvDist ((P x a).map fr) (Pr (fr x) a) ≤ εr) :
    ∀ m ∈ Set.range fs, ∀ a,
      tvDist ((Ps m a).map c) (Pr (c m) a) ≤ εs + εr := by
  rintro m ⟨x, rfl⟩ a
  letI : IsProbabilityMeasure (P x a) := hP x a
  letI : IsProbabilityMeasure (Ps (fs x) a) := hPs (fs x) a
  letI : IsProbabilityMeasure (Pr (c (fs x)) a) := hPr (c (fs x)) a
  letI : IsProbabilityMeasure ((P x a).map fs) :=
    (Measure.isProbabilityMeasure_map_iff hfs.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure ((P x a).map fr) :=
    (Measure.isProbabilityMeasure_map_iff hfr.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure ((Ps (fs x) a).map c) :=
    (Measure.isProbabilityMeasure_map_iff hc.aemeasurable).2 inferInstance

  have hmapEq :
      ((P x a).map fs).map c = (P x a).map fr := by
    rw [Measure.map_map hc hfs]
    congr 1
    funext y
    exact (hcomp y).symm

  have hfirstRaw :=
    tvDist_map_le (Ps (fs x) a) ((P x a).map fs) c hc
  have hsym :
      tvDist (Ps (fs x) a) ((P x a).map fs) =
        tvDist ((P x a).map fs) (Ps (fs x) a) :=
    tvDist_symm (Ps (fs x) a) ((P x a).map fs)
  rw [hsym, hmapEq] at hfirstRaw
  have hfirst :
      tvDist ((Ps (fs x) a).map c) ((P x a).map fr) ≤ εs :=
    hfirstRaw.trans (hs x a)

  have hsecond :
      tvDist ((P x a).map fr) (Pr (c (fs x)) a) ≤ εr := by
    simpa [hcomp x] using hr x a

  exact
    (tvDist_triangle
      ((Ps (fs x) a).map c)
      ((P x a).map fr)
      (Pr (c (fs x)) a)).trans
      (add_le_add hfirst hsecond)

/-- Exact P-DYN-04 clause: exact quotients of one microscopic transition law
intertwine on the reachable image. -/
theorem p_dyn_04_exact_intertwining
    (P : X → A → Measure X)
    (Ps : Ms → A → Measure Ms)
    (Pr : Mr → A → Measure Mr)
    (fs : X → Ms) (fr : X → Mr) (c : Ms → Mr)
    (hfs : Measurable fs) (hc : Measurable c)
    (hcomp : ∀ x, fr x = c (fs x))
    (hs : ∀ x a, (P x a).map fs = Ps (fs x) a)
    (hr : ∀ x a, (P x a).map fr = Pr (fr x) a) :
    ∀ m ∈ Set.range fs, ∀ a,
      (Ps m a).map c = Pr (c m) a := by
  rintro m ⟨x, rfl⟩ a
  rw [← hs x a, Measure.map_map hc hfs]
  have hcf : c ∘ fs = fr := by
    funext y
    exact (hcomp y).symm
  rw [hcf, hr x a, hcomp x]

end UEOT.V3.DynamicsCrossScale
