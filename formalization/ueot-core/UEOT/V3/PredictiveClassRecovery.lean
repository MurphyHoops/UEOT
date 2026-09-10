import UEOT.V3.StatisticalDefect
import Mathlib.Tactic.Linarith

/-!
# P-STAT-05 — recovery of canonical predictive classes

For a finite protocol family, define the distance between two histories as the
maximum total-variation separation of their response laws.  Uniform response
estimation error `η` perturbs this distance by at most `2η`.  Hence a true
between-class gap `γ`, together with `2η < γ/2`, makes the empirical threshold
`γ/2` recover exactly the true predictive equivalence relation.
-/

namespace UEOT.V3.PredictiveClassRecovery

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.TransportDefect
open UEOT.V3.StatisticalDefect

universe uH uI uY

variable {H : Type uH} {I : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]

/-- Protocolwise TV distances for a pair of histories. -/
def protocolDistanceSet
    (p : H → I → Measure Y) (h h' : H) : Set ℝ :=
  {d | ∃ i : I, d = tvDist (p h i) (p h' i)}

/-- Source metric `d(h,h') = max_i D_TV(p_{h,i},p_{h',i})`, written as a
supremum so its proof interface matches the rest of the UEOT TV library. -/
noncomputable def protocolDistance
    (p : H → I → Measure Y) (h h' : H) : ℝ :=
  sSup (protocolDistanceSet p h h')

private theorem protocolDistanceSet_nonempty
    [Nonempty I]
    (p : H → I → Measure Y) (h h' : H) :
    (protocolDistanceSet p h h').Nonempty := by
  let i : I := Classical.choice (inferInstance : Nonempty I)
  exact ⟨tvDist (p h i) (p h' i), i, rfl⟩

private theorem protocolDistanceSet_bddAbove
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (h h' : H) :
    BddAbove (protocolDistanceSet p h h') := by
  refine ⟨1, ?_⟩
  intro d hd
  rcases hd with ⟨i, rfl⟩
  letI : IsProbabilityMeasure (p h i) := hp h i
  letI : IsProbabilityMeasure (p h' i) := hp h' i
  exact tvDist_le_one _ _

private theorem protocolDistance_point_le
    [Nonempty I]
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (h h' : H) (i : I) :
    tvDist (p h i) (p h' i) ≤ protocolDistance p h h' := by
  unfold protocolDistance
  exact le_csSup (protocolDistanceSet_bddAbove p hp h h') ⟨i, rfl⟩

/-- Predictive equivalence: all declared protocol-response laws agree. -/
def trueEquivalent (p : H → I → Measure Y) (h h' : H) : Prop :=
  ∀ i, p h i = p h' i

/-- Uniform response-level TV error perturbs the history-pair protocol distance
by at most `2η`. -/
theorem protocolDistance_error
    [Nonempty I]
    (p pHat : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ h i, IsProbabilityMeasure (pHat h i))
    (η : ℝ)
    (hresp : ∀ h i, tvDist (p h i) (pHat h i) ≤ η)
    (h h' : H) :
    |protocolDistance pHat h h' - protocolDistance p h h'| ≤ 2 * η := by
  have hHat_le :
      protocolDistance pHat h h' ≤ protocolDistance p h h' + 2 * η := by
    unfold protocolDistance
    refine csSup_le (protocolDistanceSet_nonempty pHat h h') ?_
    intro d hd
    rcases hd with ⟨i, rfl⟩
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
    have hbase := protocolDistance_point_le p hp h h' i
    have hbase' :
        tvDist (p h i) (p h' i) ≤ sSup (protocolDistanceSet p h h') := by
      simpa [protocolDistance] using hbase
    rw [abs_le] at hpair
    linarith
  have hTrue_le :
      protocolDistance p h h' ≤ protocolDistance pHat h h' + 2 * η := by
    unfold protocolDistance
    refine csSup_le (protocolDistanceSet_nonempty p h h') ?_
    intro d hd
    rcases hd with ⟨i, rfl⟩
    letI : IsProbabilityMeasure (p h i) := hp h i
    letI : IsProbabilityMeasure (p h' i) := hp h' i
    letI : IsProbabilityMeasure (pHat h i) := hpHat h i
    letI : IsProbabilityMeasure (pHat h' i) := hpHat h' i
    have hpair := abs_tvDist_sub_tvDist_le
      (p h i) (p h' i) (pHat h i) (pHat h' i)
    have hleft := hresp h i
    have hright := hresp h' i
    have hbase := protocolDistance_point_le pHat hpHat h h' i
    have hbase' :
        tvDist (pHat h i) (pHat h' i) ≤ sSup (protocolDistanceSet pHat h h') := by
      simpa [protocolDistance] using hbase
    rw [abs_le] at hpair
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Truly equivalent histories have zero source protocol distance. -/
theorem protocolDistance_eq_zero_of_equivalent
    [Nonempty I]
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    {h h' : H}
    (heq : trueEquivalent p h h') :
    protocolDistance p h h' = 0 := by
  apply le_antisymm
  · unfold protocolDistance
    refine csSup_le (protocolDistanceSet_nonempty p h h') ?_
    intro d hd
    rcases hd with ⟨i, rfl⟩
    letI : IsProbabilityMeasure (p h i) := hp h i
    rw [heq i]
    simpa using tvDist_self (p h' i)
  · let i : I := Classical.choice (inferInstance : Nonempty I)
    letI : IsProbabilityMeasure (p h i) := hp h i
    letI : IsProbabilityMeasure (p h' i) := hp h' i
    exact le_trans (tvDist_nonneg (p h i) (p h' i))
      (protocolDistance_point_le p hp h h' i)

/-- **P-STAT-05.**  If distinct true predictive classes are separated by at
least `γ`, and every response law is estimated within TV error `η`, then the
empirical `γ/2` threshold recovers exactly the true predictive equivalence
relation. -/
theorem p_stat_05
    [Fintype H] [Fintype I] [Nonempty I]
    (p pHat : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (hpHat : ∀ h i, IsProbabilityMeasure (pHat h i))
    (η γ : ℝ)
    (hresp : ∀ h i, tvDist (p h i) (pHat h i) ≤ η)
    (hsep : ∀ h h', ¬ trueEquivalent p h h' →
      γ ≤ protocolDistance p h h')
    (hgap : 2 * η < γ / 2) :
    ∀ h h' : H,
      protocolDistance pHat h h' ≤ γ / 2 ↔ trueEquivalent p h h' := by
  intro h h'
  have herr := protocolDistance_error p pHat hp hpHat η hresp h h'
  rw [abs_le] at herr
  constructor
  · intro hemp
    by_contra hne
    have htrue := hsep h h' hne
    linarith
  · intro heq
    have hzero := protocolDistance_eq_zero_of_equivalent p hp heq
    linarith

end UEOT.V3.PredictiveClassRecovery
