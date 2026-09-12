import UEOT.V3.HilbertMeanPrefixFiltration
import Mathlib.Tactic

/-!
# P-STAT-06 — predecessor prefix equals the strict past

For a genuine active index `i` with positive numeric value, the filtration one
step before `i` reveals exactly the coordinates strictly before `i`.
-/

namespace UEOT.V3.HilbertMeanPrefixPredecessor

open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFiltration

/-- If `i > 0`, the numeric prefix at time `i-1` is exactly `past i`. -/
theorem prefixBlock_pred_eq_past {N : ℕ} (i : Fin N) (hi : 0 < i.1) :
    prefixBlock (N := N) (i.1 - 1) = past i := by
  ext j
  simp only [mem_prefixBlock_iff, mem_past_iff]
  rw [Fin.lt_def]
  omega

end UEOT.V3.HilbertMeanPrefixPredecessor
