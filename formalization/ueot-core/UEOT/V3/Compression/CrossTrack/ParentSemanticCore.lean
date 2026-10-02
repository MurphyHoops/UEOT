import UEOT.V3.Compression.QuotientDescent
import UEOT.V3.Compression.Hierarchy
import UEOT.V3.Compression.TopologyChangingGoaTrackSClosure
import UEOT.V3.Compression.TopologyChangingGoaL1ResetFamily
import UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability

/-!
# Track X — shared parent-semantic interfaces

This module contains only thin cross-track adapters over the already merged
M-QD and Track-S surfaces.  It introduces no new finite-state isolation
certificate and changes no counted compression primitive.
-/

namespace UEOT.V3.Compression.CrossTrack

open Function
open UEOT.V3
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.QuotientDescent
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation
open UEOT.V3.Compression.TopologyChangingGoaResidualInverseStability
open UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm
open UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation

universe uP uC uS

noncomputable section

variable {P : Type uP} {C : Type uC}
variable {S : Type uS} [Fintype S] [Nonempty S]
noncomputable local instance parentSemanticCoreDecidableEq : DecidableEq S :=
  Classical.decEq S

/-- Parent completions compatible with one child-evidence value. -/
def ParentFiber (pi : P → C) (c : C) : Set P :=
  {p | pi p = c}

/-- Pairwise long-run semantic distances realized inside one parent-completion
fibre. -/
def fiberSemanticDistances
    (pi : P → C) (mu : P → stdSimplex ℝ S) (c : C) : Set ℝ :=
  {d | ∃ p q, pi p = c ∧ pi q = c ∧ d = lawTV (mu p) (mu q)}

/-- Supremal long-run semantic separation among parent completions over one
child-evidence value. -/
noncomputable def fiberSemanticDiameter
    (pi : P → C) (mu : P → stdSimplex ℝ S) (c : C) : ℝ :=
  sSup (fiberSemanticDistances pi mu c)

/-- Track-S stationary tracking specialized to an **explicitly supplied**
target invariant law.

The merged Track-S theorem constructs some target invariant law.  Track X
needs the stronger quantifier discipline required by Issue #225: whenever a
particular target completion comes with its own invariant-law witness, that
very law obeys the same canonical `epsilon / kappa_1` bound. -/
theorem suppliedInvariant_tracking
    (K0 : Matrix S S ℝ) (hK0 : K0 ∈ Matrix.rowStochastic ℝ S)
    (K1 : Matrix S S ℝ) (hK1 : K1 ∈ Matrix.rowStochastic ℝ S)
    (mu0 mu1 : stdSimplex ℝ S)
    (hmu0 : mu0 ∈ invariantLawSet K0 hK0)
    (hmu1 : mu1 ∈ invariantLawSet K1 hK1)
    (epsilon : ℝ)
    (hcard : 1 < Fintype.card S)
    (hisolation : 0 < l1ResidualConorm K0)
    (hrow : ∀ x, crossRowTV K0 hK0 K1 hK1 x ≤ epsilon) :
    lawTV mu0 mu1 ≤ epsilon / l1ResidualConorm K0 := by
  have hinj : Function.Injective
      (UEOT.V3.Compression.TopologyChangingGoaRestrictedResidualAdapter.zeroSumResidualLinear K0) :=
    (l1ResidualConorm_pos_iff_restricted_injective K0 hcard).1 hisolation
  have hiso :=
    l1ResidualConorm_isolation K0 hcard hinj
  have hmu0' : step K0 hK0 mu0 = mu0 := by
    simpa [mem_invariantLawSet] using hmu0
  have hmu1' : step K1 hK1 mu1 = mu1 := by
    simpa [mem_invariantLawSet] using hmu1
  have hres :=
    residualInverse_of_l1Isolation
      K0 hK0 mu0 hmu0' (l1ResidualConorm K0) hiso
  have hkernel := tv_step_cross_le K0 hK0 K1 hK1 mu1 epsilon hrow
  rw [hmu1'] at hkernel
  have hbound := hres.bound mu1
  have hscaled :
      lawTV mu0 mu1 ≤ (1 / l1ResidualConorm K0) * epsilon :=
    hbound.trans
      (mul_le_mul_of_nonneg_left hkernel hres.C_nonneg)
  calc
    lawTV mu0 mu1
        ≤ (1 / l1ResidualConorm K0) * epsilon := hscaled
    _ = epsilon / l1ResidualConorm K0 := by
      field_simp

end

end UEOT.V3.Compression.CrossTrack
