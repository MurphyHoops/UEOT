import UEOT.V3.Compression.CrossTrack.DualIsolationCanonical
import UEOT.V3.Compression.CrossTrack.ParentBindingDynamic

/-!
# Dual Isolation — dynamic observational exactification

The Parent-Binding dynamic lane already proves semantic convergence when the
M-TC assembly-error envelope tends to zero.  This module supplies the
complementary observational route: if lower-level diagnostic uncertainty tends
to zero and both isolation margins stay positive, parent long-run semantics
also converge.
-/

namespace UEOT.V3.Compression.CrossTrack

open Filter
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm

universe uA uY uS

noncomputable section

variable {A : Type uA} {Y : Type uY}
variable [MetricSpace A] [PseudoMetricSpace Y]
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance dualIsolationDynamicDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- Time-slice dual-isolation bound for two evolving assembly realizations. -/
theorem dualIsolation_timeSliceSemanticBound
    (theta thetaBar : ℕ → A)
    (diagnostic : A → Y)
    (beta : ℝ) (hiso : BindingIsolation diagnostic beta)
    (eta : ℕ → ℝ) (observed : ℕ → Y)
    (hobs : ∀ n,
      dist (diagnostic (thetaBar n)) (observed n) ≤ eta n ∧
      dist (diagnostic (theta n)) (observed n) ≤ eta n)
    (K : A → Matrix S S ℝ)
    (hK : ∀ a, K a ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz (fun a : A => a) K hK)
    (mu : A → stdSimplex ℝ S)
    (hmu : ∀ a, mu a ∈ invariantLawSet (K a) (hK a))
    (kappaMin : ℝ) (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hisolationFloor : ∀ n,
      kappaMin ≤ l1ResidualConorm (K (thetaBar n)))
    (n : ℕ) :
    lawTV (mu (thetaBar n)) (mu (theta n)) ≤
      bind.L * (2 * eta n / beta) / kappaMin := by
  exact dualIsolation_pairwiseSemanticBound
    (P := A) (repr := fun a => a) diagnostic beta (eta n) hiso
    (by
      exact dist_nonneg.trans (hobs n).1)
    (observed n) K hK bind mu hmu kappaMin hkappaMin hcard
    (hobs n).1 (hobs n).2 (hisolationFloor n)

/-- **Dynamic dual-isolation exactification.**

If one observational diagnostic radius tends to zero, and binding isolation,
forward realization regularity, and semantic isolation remain fixed, then the
long-run semantics of the two evolving parent realizations converge in TV. -/
theorem dualIsolation_semanticTracking_tendsto_zero
    (theta thetaBar : ℕ → A)
    (diagnostic : A → Y)
    (beta : ℝ) (hiso : BindingIsolation diagnostic beta)
    (eta : ℕ → ℝ) (observed : ℕ → Y)
    (hobs : ∀ n,
      dist (diagnostic (thetaBar n)) (observed n) ≤ eta n ∧
      dist (diagnostic (theta n)) (observed n) ≤ eta n)
    (heta : Tendsto eta atTop (nhds 0))
    (K : A → Matrix S S ℝ)
    (hK : ∀ a, K a ∈ Matrix.rowStochastic ℝ S)
    (bind : ParentBindingLipschitz (fun a : A => a) K hK)
    (mu : A → stdSimplex ℝ S)
    (hmu : ∀ a, mu a ∈ invariantLawSet (K a) (hK a))
    (kappaMin : ℝ) (hkappaMin : 0 < kappaMin)
    (hcard : 1 < Fintype.card S)
    (hisolationFloor : ∀ n,
      kappaMin ≤ l1ResidualConorm (K (thetaBar n))) :
    Tendsto (fun n => lawTV (mu (thetaBar n)) (mu (theta n)))
      atTop (nhds 0) := by
  have hdelta : Tendsto (fun n => 2 * eta n / beta) atTop (nhds 0) := by
    have htwo : Tendsto (fun n => 2 * eta n) atTop (nhds (2 * 0)) :=
      heta.const_mul 2
    have hdiv := htwo.div_const beta
    simpa using hdiv
  apply parentSemanticTracking_tendsto_zero
    (fun n => mu (thetaBar n)) (fun n => mu (theta n))
    (fun n => 2 * eta n / beta) bind.L kappaMin hdelta
  intro n
  exact dualIsolation_timeSliceSemanticBound
    theta thetaBar diagnostic beta hiso eta observed hobs
    K hK bind mu hmu kappaMin hkappaMin hcard hisolationFloor n

end

end UEOT.V3.Compression.CrossTrack
