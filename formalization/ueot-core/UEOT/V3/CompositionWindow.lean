import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Order.Compact

/-!
# P-COMP-07 — composition window preserving child individuality

On a compact coupling interval, the frozen Core 3 source assumes an integration
quantity `D` that is continuous and nondecreasing and a child-fidelity quantity
`F` that is continuous and nonincreasing.  Nonempty threshold-feasible sets
therefore have attained boundary points `k_D` and `k_F`; monotonicity then makes
the joint feasible set exactly the interval between them when ordered, and
empty otherwise.

We work on the subtype `Set.Icc a b` itself.  This keeps the compact parameter
window in the type and lets Mathlib's compact-order extreme-value theorem
produce the attained threshold boundaries without adding witness assumptions.
-/

namespace UEOT.V3.CompositionWindow

open Set

/-- **P-COMP-07.** Continuous monotone integration and fidelity diagnostics on
a compact coupling interval have a single closed joint feasibility window. -/
theorem p_comp_07
    (a b dStar fStar : ℝ) (D F : ℝ → ℝ)
    (hDcont : ContinuousOn D (Icc a b))
    (hFcont : ContinuousOn F (Icc a b))
    (hDmono : MonotoneOn D (Icc a b))
    (hFanti : AntitoneOn F (Icc a b))
    (hDfeas : ∃ k ∈ Icc a b, dStar ≤ D k)
    (hFfeas : ∃ k ∈ Icc a b, fStar ≤ F k) :
    ∃ kD kF : Icc a b,
      IsLeast {k : Icc a b | dStar ≤ D k} kD ∧
      IsGreatest {k : Icc a b | fStar ≤ F k} kF ∧
      ({k : Icc a b | dStar ≤ D k ∧ fStar ≤ F k} =
        if kD ≤ kF then Icc kD kF else ∅) := by
  let KD : Set (Icc a b) := {k | dStar ≤ D k}
  let KF : Set (Icc a b) := {k | fStar ≤ F k}
  have hDcontinuous : Continuous (fun k : Icc a b => D k) :=
    hDcont.domRestrict
  have hFcontinuous : Continuous (fun k : Icc a b => F k) :=
    hFcont.domRestrict
  have hKDclosed : IsClosed KD := by
    change IsClosed {k : Icc a b | dStar ≤ D k}
    exact isClosed_le continuous_const hDcontinuous
  have hKFclosed : IsClosed KF := by
    change IsClosed {k : Icc a b | fStar ≤ F k}
    exact isClosed_le continuous_const hFcontinuous
  have hKDcompact : IsCompact KD := hKDclosed.isCompact
  have hKFcompact : IsCompact KF := hKFclosed.isCompact
  have hKDnon : KD.Nonempty := by
    rcases hDfeas with ⟨k, hkK, hkD⟩
    exact ⟨⟨k, hkK⟩, hkD⟩
  have hKFnon : KF.Nonempty := by
    rcases hFfeas with ⟨k, hkK, hkF⟩
    exact ⟨⟨k, hkK⟩, hkF⟩
  obtain ⟨kD, hkDleast⟩ := hKDcompact.exists_isLeast hKDnon
  obtain ⟨kF, hkFgreatest⟩ := hKFcompact.exists_isGreatest hKFnon
  refine ⟨kD, kF, ?_, ?_, ?_⟩
  · simpa [KD] using hkDleast
  · simpa [KF] using hkFgreatest
  · by_cases hcross : kD ≤ kF
    · rw [if_pos hcross]
      ext k
      constructor
      · intro hk
        exact ⟨hkDleast.2 hk.1, hkFgreatest.2 hk.2⟩
      · intro hk
        have hDord : D kD ≤ D k :=
          hDmono kD.property k.property hk.1
        have hFord : F kF ≤ F k :=
          hFanti k.property kF.property hk.2
        exact ⟨hkDleast.1.trans hDord, hkFgreatest.1.trans hFord⟩
    · rw [if_neg hcross]
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hk
      exact hcross ((hkDleast.2 hk.1).trans (hkFgreatest.2 hk.2))

end UEOT.V3.CompositionWindow
