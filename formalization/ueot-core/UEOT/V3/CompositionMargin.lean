import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# P-COMP-03 — composition margin

For a finite nonempty cut family `K π`, the frozen Core 3 source defines

`Γ_comp(T) = min_π d(T, K_π T)`

and assumes each cut is `L_π`-Lipschitz.  With
`L = max_π L_π`, the composition margin is `(1+L)`-Lipschitz.

The theorem below keeps the finite minimum and finite maximum explicit through
`Finset.inf'` and `Finset.sup'`; in particular it does not silently replace the
source constant by `2` unless nonexpansiveness has separately been proved.
-/

namespace UEOT.V3.CompositionMargin

universe uX uI

variable {X : Type uX} {I : Type uI}
variable [PseudoMetricSpace X] [Fintype I] [Nonempty I]

/-- Frozen-source finite composition margin. -/
noncomputable def compositionMargin (K : I → X → X) (T : X) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun π => dist T (K π T))

/-- Maximum of the finitely many declared cut Lipschitz constants. -/
noncomputable def maxCutLipschitz (Lπ : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty Lπ

private theorem fixedCut_margin_difference_le
    (K : I → X → X) (Lπ : I → ℝ)
    (hLip : ∀ π T S, dist (K π T) (K π S) ≤ Lπ π * dist T S)
    (π : I) (T S : X) :
    dist T (K π T) - dist S (K π S) ≤
      (1 + maxCutLipschitz Lπ) * dist T S := by
  have hLmax : Lπ π ≤ maxCutLipschitz Lπ := by
    unfold maxCutLipschitz
    exact Finset.le_sup' Lπ (Finset.mem_univ π)
  have hcut : dist (K π T) (K π S) ≤
      maxCutLipschitz Lπ * dist T S := by
    exact le_trans (hLip π T S)
      (mul_le_mul_of_nonneg_right hLmax dist_nonneg)
  have hcut' : dist (K π S) (K π T) ≤
      maxCutLipschitz Lπ * dist T S := by
    simpa [dist_comm] using hcut
  have htri := dist_triangle4 T S (K π S) (K π T)
  linarith

/-- Source-facing P-COMP-03.

If every cut `K π` is `Lπ π`-Lipschitz, then the minimum cut-distance margin
is `(1 + max π, Lπ π)`-Lipschitz. -/
theorem p_comp_03
    (K : I → X → X) (Lπ : I → ℝ)
    (hLip : ∀ π T S, dist (K π T) (K π S) ≤ Lπ π * dist T S)
    (T S : X) :
    |compositionMargin K T - compositionMargin K S| ≤
      (1 + maxCutLipschitz Lπ) * dist T S := by
  obtain ⟨πS, _hπS, hSmin⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
      (fun π => dist S (K π S))
  obtain ⟨πT, _hπT, hTmin⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty
      (fun π => dist T (K π T))
  change compositionMargin K S = dist S (K πS S) at hSmin
  change compositionMargin K T = dist T (K πT T) at hTmin
  have hTle : compositionMargin K T ≤ dist T (K πS T) := by
    unfold compositionMargin
    exact Finset.inf'_le _ (Finset.mem_univ πS)
  have hSle : compositionMargin K S ≤ dist S (K πT S) := by
    unfold compositionMargin
    exact Finset.inf'_le _ (Finset.mem_univ πT)
  have hforward :
      compositionMargin K T - compositionMargin K S ≤
        (1 + maxCutLipschitz Lπ) * dist T S := by
    have hfixed := fixedCut_margin_difference_le K Lπ hLip πS T S
    rw [hSmin]
    linarith
  have hreverse :
      compositionMargin K S - compositionMargin K T ≤
        (1 + maxCutLipschitz Lπ) * dist T S := by
    have hfixed := fixedCut_margin_difference_le K Lπ hLip πT S T
    rw [hTmin]
    rw [dist_comm S T] at hfixed
    linarith
  exact (abs_le).2 ⟨by linarith, hforward⟩

end UEOT.V3.CompositionMargin
