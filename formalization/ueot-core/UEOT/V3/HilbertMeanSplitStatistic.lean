import UEOT.V3.HilbertMeanConcentration
import UEOT.V3.HilbertMeanPrefixFutureAssembly

/-!
# P-STAT-06 — source Hilbert statistic in prefix/future coordinates

The actual source statistic is the norm error of the empirical Hilbert mean.
This module rewrites that statistic in the canonical prefix/future coordinates
used by the Doob construction and records exact reconstruction on a full sample.
-/

namespace UEOT.V3.HilbertMeanSplitStatistic

open UEOT.V3.HilbertMeanConcentration
open UEOT.V3.HilbertMeanProductBlockIndependence
open UEOT.V3.HilbertMeanPrefixFiltration
open UEOT.V3.HilbertMeanDoobBlocks
open UEOT.V3.HilbertMeanPrefixFutureAssembly

universe uH

variable {H : Type uH}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Hilbert empirical-mean error written as a function of the revealed prefix
and strict future blocks at a genuine sample index `i`. -/
noncomputable def splitMeanError {N : ℕ} (i : Fin N) (μH : H)
    (xy : (prefixBlock i.1 → H) × (future i → H)) : ℝ :=
  ‖empiricalMean (assemblePrefixFuture i xy.1 xy.2) - μH‖

/-- Exact source reconstruction: projecting a full sample into prefix/future
blocks and evaluating the split statistic gives the original Hilbert mean
error, with no almost-everywhere qualification. -/
@[simp] theorem splitMeanError_blockProjections
    {N : ℕ} (i : Fin N) (μH : H) (ω : Fin N → H) :
    splitMeanError i μH
      (blockProjection (prefixBlock i.1) ω, blockProjection (future i) ω) =
      ‖empiricalMean ω - μH‖ := by
  unfold splitMeanError
  rw [assemblePrefixFuture_blockProjections]

end UEOT.V3.HilbertMeanSplitStatistic
