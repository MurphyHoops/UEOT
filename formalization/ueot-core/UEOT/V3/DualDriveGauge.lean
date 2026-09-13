import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# P-DDH-01 — dual-drive gauge freedom

The frozen Core 3 source records a simple but important non-identifiability:
adding the same gauge field `χ` to `Φ` while adding `λχ` to `Π` leaves the
combined objective `Π - λΦ` unchanged.  This theorem formalizes exactly that
algebraic equivalence; semantic anchoring of the two axes is a separate
experimental/modeling obligation.
-/

namespace UEOT.V3.DualDriveGauge

/-- Source-facing P-DDH-01. -/
theorem p_ddh_01 (piVal phiVal lambdaVal chiVal : ℝ) :
    (piVal + lambdaVal * chiVal) - lambdaVal * (phiVal + chiVal) =
      piVal - lambdaVal * phiVal := by
  ring

/-- Pointwise functional form used when the two drives and gauge vary over a
common state/trajectory parameter. -/
theorem p_ddh_01_pointwise {X : Type*}
    (piVal phiVal chiVal : X → ℝ) (lambdaVal : ℝ) (x : X) :
    (piVal x + lambdaVal * chiVal x) -
        lambdaVal * (phiVal x + chiVal x) =
      piVal x - lambdaVal * phiVal x := by
  exact p_ddh_01 (piVal x) (phiVal x) lambdaVal (chiVal x)

end UEOT.V3.DualDriveGauge
