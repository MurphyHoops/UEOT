import UEOT.V3.TransportDefect
import Mathlib.Tactic.Linarith

/-!
# P-STAT-02 — simultaneous response error implies uniform carrier-defect error

The frozen Core 3 statement works on a finite response table.  For each carrier
`S`, its defect is the maximum (equivalently, supremum) total-variation diameter
among history/protocol cells lying in one `S`-readout fiber.  On the single
simultaneous event where every empirical response is within `η` in TV of its
true response, every carrier defect is therefore within `2η` — with no further
union bound over carriers.

This module isolates exactly that deterministic implication.  The probability
of the simultaneous response event belongs to P-STAT-01, not P-STAT-02.
-/

namespace UEOT.V3.StatisticalDefect

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.TransportDefect

universe uV uH uI uR uY

variable {V : Type uV} {H : Type uH} {I : Type uI}
variable {R : Type uR} {Y : Type uY}
variable [MeasurableSpace Y]

/-- Total variation is symmetric for probability measures. -/
theorem tvDist_symm
    (μ ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = tvDist ν μ := by
  unfold tvDist tvEventSet
  congr 1
  ext r
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, by rw [abs_sub_comm]⟩
  · rintro ⟨A, hA, rfl⟩
    exact ⟨A, hA, by rw [abs_sub_comm]⟩

/-- Perturbing both endpoints of a TV distance changes that distance by at most
the sum of the endpoint perturbations. -/
theorem abs_tvDist_sub_tvDist_le
    (μ₁ μ₂ ν₁ ν₂ : Measure Y)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂] :
    |tvDist μ₁ μ₂ - tvDist ν₁ ν₂| ≤
      tvDist μ₁ ν₁ + tvDist μ₂ ν₂ := by
  have hforward₁ := tvDist_triangle μ₁ ν₁ μ₂
  have hforward₂ := tvDist_triangle ν₁ ν₂ μ₂
  have hforward :
      tvDist μ₁ μ₂ ≤
        tvDist μ₁ ν₁ + tvDist ν₁ ν₂ + tvDist ν₂ μ₂ := by
    linarith
  have hbackward₁ := tvDist_triangle ν₁ μ₁ ν₂
  have hbackward₂ := tvDist_triangle μ₁ μ₂ ν₂
  have hbackward :
      tvDist ν₁ ν₂ ≤
        tvDist ν₁ μ₁ + tvDist μ₁ μ₂ + tvDist μ₂ ν₂ := by
    linarith
  have hbackward' := hbackward
  rw [tvDist_symm ν₁ μ₁] at hbackward'
  have hforward' := hforward
  rw [tvDist_symm ν₂ μ₂] at hforward'
  rw [abs_le]
  constructor <;> linarith

/-- Distances entering the carrier defect: two histories must have the same
carrier readout and the protocol index must agree. -/
def responseDiameterSet
    (readout : Finset V → H → R)
    (p : H → I → Measure Y) (S : Finset V) : Set ℝ :=
  {d | ∃ h h' i, readout S h = readout S h' ∧
      d = tvDist (p h i) (p h' i)}

/-- Source carrier defect `e(S)`: the response diameter inside one readout
fiber, maximized over protocols. -/
noncomputable def responseDefect
    (readout : Finset V → H → R)
    (p : H → I → Measure Y) (S : Finset V) : ℝ :=
  sSup (responseDiameterSet readout p S)

private theorem responseDiameterSet_nonempty
    [Nonempty H] [Nonempty I]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y) (S : Finset V) :
    (responseDiameterSet readout p S).Nonempty := by
  classical
  let h : H := Classical.choice (inferInstance : Nonempty H)
  let i : I := Classical.choice (inferInstance : Nonempty I)
  exact ⟨tvDist (p h i) (p h i), h, h, i, rfl, rfl⟩

private theorem responseDiameterSet_bddAbove
    (readout : Finset V → H → R)
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (S : Finset V) :
    BddAbove (responseDiameterSet readout p S) := by
  refine ⟨1, ?_⟩
  intro d hd
  rcases hd with ⟨h, h', i, _hfiber, rfl⟩
  letI : IsProbabilityMeasure (p h i) := hp h i
  letI : IsProbabilityMeasure (p h' i) := hp h' i
  exact tvDist_le_one _ _

private theorem responseDistance_le_defect
    [Nonempty H] [Nonempty I]
    (readout : Finset V → H → R)
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (S : Finset V) {h h' : H} {i : I}
    (hfiber : readout S h = readout S h') :
    tvDist (p h i) (p h' i) ≤ responseDefect readout p S := by
  unfold responseDefect
  exact le_csSup (responseDiameterSet_bddAbove readout p hp S)
    ⟨h, h', i, hfiber, rfl⟩

/-- P-STAT-02, carrierwise form.  A simultaneous response-level TV error `η`
implies defect error at most `2η` for every carrier. -/
theorem responseDefect_error
    [Nonempty H] [Nonempty I]
    (readout : Finset V → H → R)
    (p pHat : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ h i, IsProbabilityMeasure (pHat h i))
    (η : ℝ)
    (hresp : ∀ h i, tvDist (p h i) (pHat h i) ≤ η)
    (S : Finset V) :
    |responseDefect readout pHat S - responseDefect readout p S| ≤ 2 * η := by
  have hHat_le :
      responseDefect readout pHat S ≤ responseDefect readout p S + 2 * η := by
    unfold responseDefect
    refine csSup_le (responseDiameterSet_nonempty readout pHat S) ?_
    intro d hd
    rcases hd with ⟨h, h', i, hfiber, rfl⟩
    letI : IsProbabilityMeasure (p h i) := hp h i
    letI : IsProbabilityMeasure (p h' i) := hp h' i
    letI : IsProbabilityMeasure (pHat h i) := hpHat h i
    letI : IsProbabilityMeasure (pHat h' i) := hpHat h' i
    have hpair := abs_tvDist_sub_tvDist_le
      (pHat h i) (pHat h' i) (p h i) (p h' i)
    have hleft : tvDist (pHat h i) (p h i) ≤ η := by
      simpa [tvDist_symm] using hresp h i
    have hright : tvDist (pHat h' i) (p h' i) ≤ η := by
      simpa [tvDist_symm] using hresp h' i
    have hbase := responseDistance_le_defect (i := i) readout p hp S hfiber
    rw [abs_le] at hpair
    linarith
  have hTrue_le :
      responseDefect readout p S ≤ responseDefect readout pHat S + 2 * η := by
    unfold responseDefect
    refine csSup_le (responseDiameterSet_nonempty readout p S) ?_
    intro d hd
    rcases hd with ⟨h, h', i, hfiber, rfl⟩
    letI : IsProbabilityMeasure (p h i) := hp h i
    letI : IsProbabilityMeasure (p h' i) := hp h' i
    letI : IsProbabilityMeasure (pHat h i) := hpHat h i
    letI : IsProbabilityMeasure (pHat h' i) := hpHat h' i
    have hpair := abs_tvDist_sub_tvDist_le
      (p h i) (p h' i) (pHat h i) (pHat h' i)
    have hleft := hresp h i
    have hright := hresp h' i
    have hbase := responseDistance_le_defect (i := i) readout pHat hpHat S hfiber
    rw [abs_le] at hpair
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Literal simultaneous-all-carriers form of P-STAT-02.  There is no carrier
count in the conclusion: once the response event holds, every carrier is
controlled by the same deterministic `2η` radius. -/
theorem p_stat_02
    [Nonempty H] [Nonempty I]
    (readout : Finset V → H → R)
    (p pHat : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ h i, IsProbabilityMeasure (pHat h i))
    (η : ℝ)
    (hresp : ∀ h i, tvDist (p h i) (pHat h i) ≤ η) :
    ∀ S : Finset V,
      |responseDefect readout pHat S - responseDefect readout p S| ≤ 2 * η := by
  intro S
  exact responseDefect_error readout p pHat hp hpHat η hresp S

end UEOT.V3.StatisticalDefect
