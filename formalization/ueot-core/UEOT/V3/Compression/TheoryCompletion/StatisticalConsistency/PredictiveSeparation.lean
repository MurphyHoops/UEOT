import UEOT.V3.PredictiveClassRecovery
import UEOT.V3.InformationZeroTV
import Mathlib.Tactic

namespace UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency

open MeasureTheory
open UEOT.V3.TotalVariation
open UEOT.V3.PredictiveClassRecovery
open UEOT.V3.InformationZeroTV

universe uH uI uY
variable {H : Type uH} {I : Type uI} {Y : Type uY}
variable [MeasurableSpace Y]

private theorem protocolDistance_bddAbove
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (h h' : H) :
    BddAbove (protocolDistanceSet p h h') := by
  refine ⟨1, ?_⟩
  intro d hd
  rcases hd with ⟨i, rfl⟩
  let _ : IsProbabilityMeasure (p h i) := hp h i
  let _ : IsProbabilityMeasure (p h' i) := hp h' i
  exact tvDist_le_one _ _

private theorem tvDist_le_protocolDistance
    [Nonempty I]
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (h h' : H) (i : I) :
    tvDist (p h i) (p h' i) ≤ protocolDistance p h h' := by
  unfold protocolDistance
  exact le_csSup (protocolDistance_bddAbove p hp h h') ⟨i, rfl⟩

theorem protocolDistance_pos_of_not_trueEquivalent
    [Nonempty I]
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    {h h' : H} (hne : ¬ trueEquivalent p h h') :
    0 < protocolDistance p h h' := by
  rw [trueEquivalent] at hne
  simp only [not_forall] at hne
  obtain ⟨i, hi⟩ := hne
  let _ : IsProbabilityMeasure (p h i) := hp h i
  let _ : IsProbabilityMeasure (p h' i) := hp h' i
  have htvne : tvDist (p h i) (p h' i) ≠ 0 := by
    intro hzero
    exact hi (measure_eq_of_tvDist_eq_zero _ _ hzero)
  have htvpos : 0 < tvDist (p h i) (p h' i) :=
    lt_of_le_of_ne (tvDist_nonneg _ _) (Ne.symm htvne)
  exact htvpos.trans_le (tvDist_le_protocolDistance p hp h h' i)

noncomputable def predictivePairGap
    (p : H → I → Measure Y) (q : H × H) : ℝ := by
  classical
  exact if trueEquivalent p q.1 q.2 then 1 else protocolDistance p q.1 q.2

theorem predictivePairGap_pos
    [Nonempty I]
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i))
    (q : H × H) : 0 < predictivePairGap p q := by
  classical
  unfold predictivePairGap
  split_ifs with heq
  · norm_num
  · exact protocolDistance_pos_of_not_trueEquivalent p hp heq

noncomputable def canonicalPredictiveGap
    [Fintype H] [Nonempty H]
    (p : H → I → Measure Y) : ℝ :=
  (Finset.univ : Finset (H × H)).inf'
    Finset.univ_nonempty
    (predictivePairGap p)

theorem canonicalPredictiveGap_pos
    [Fintype H] [Nonempty H] [Nonempty I]
    (p : H → I → Measure Y)
    (hp : ∀ h i, IsProbabilityMeasure (p h i)) :
    0 < canonicalPredictiveGap p := by
  classical
  unfold canonicalPredictiveGap
  obtain ⟨q, _hq, hmin⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty : (Finset.univ : Finset (H × H)).Nonempty)
    (predictivePairGap p)
  rw [hmin]
  exact predictivePairGap_pos p hp q

theorem canonicalPredictiveGap_le
    [Fintype H] [Nonempty H] [Nonempty I]
    (p : H → I → Measure Y)
    {h h' : H} (hne : ¬ trueEquivalent p h h') :
    canonicalPredictiveGap p ≤ protocolDistance p h h' := by
  classical
  have hle : canonicalPredictiveGap p ≤ predictivePairGap p (h, h') := by
    unfold canonicalPredictiveGap
    exact Finset.inf'_le _ (Finset.mem_univ (h, h'))
  simpa [predictivePairGap, hne] using hle

end UEOT.V3.Compression.TheoryCompletion.StatisticalConsistency
