import Mathlib.Tactic

/-!
# Theory Completion P6.0 — explicit resource accounting semantics

P6 adds a resource-accounting layer *after* P5 joint homeostasis.  Resource
quantities in this module are abstract accounting units.  They are not identified
with thermodynamic work, free energy, money, ATP, compute, or any other domain
quantity without a separate adapter.

In particular, the RH/P5 Lyapunov `repairDrift` is not a resource stock.  P6
therefore introduces explicit maintenance, repair and reconstruction costs,
explicit replenishment schedules, and a cumulative balance independently of the
homeostasis potential.
-/

namespace UEOT.V3.Compression.Objecthood.ResourceClosure

open Filter Topology
open UEOT.V3.Compression.Objecthood

noncomputable section

/-- Abstract nonnegative accounting costs per unit occurrence.

`maintenance` is a baseline recurring cost.  `repair` and `reconstruction` are
extra costs associated with damaged organization.  A domain-specific model may
interpret the accounting unit only through a later explicit adapter. -/
structure ResourceCostModel where
  maintenance : ℝ
  repair : ℝ
  reconstruction : ℝ
  maintenance_nonneg : 0 ≤ maintenance
  repair_nonneg : 0 ≤ repair
  reconstruction_nonneg : 0 ≤ reconstruction

namespace ResourceCostModel

/-- Combined damaged-state surcharge used by the minimal P6 envelope. -/
def variableCost (C : ResourceCostModel) : ℝ :=
  C.repair + C.reconstruction

theorem variableCost_nonneg (C : ResourceCostModel) :
    0 ≤ C.variableCost :=
  add_nonneg C.repair_nonneg C.reconstruction_nonneg

end ResourceCostModel

/-- Cumulative resource balance after `N` steps.  Replenishment and realized
cost are left as arbitrary real-valued schedules; stronger positivity or domain
interpretations belong to later adapters. -/
def cumulativeResourceBalance
    (initial : ℝ) (replenish cost : ℕ → ℝ) (N : ℕ) : ℝ :=
  initial + (∑ n ∈ Finset.range N, replenish n) -
    ∑ n ∈ Finset.range N, cost n

/-- Deterministic/pathwise accounting viability: cumulative balance never
becomes negative.  This is intentionally stronger than an average or expected
resource statement. -/
def ResourceViable
    (initial : ℝ) (replenish cost : ℕ → ℝ) : Prop :=
  ∀ N, 0 ≤ cumulativeResourceBalance initial replenish cost N

/-- Resource viability is exactly the family of cumulative budget inequalities. -/
theorem resourceViable_iff_cumulative_cost_le
    (initial : ℝ) (replenish cost : ℕ → ℝ) :
    ResourceViable initial replenish cost ↔
      ∀ N,
        (∑ n ∈ Finset.range N, cost n) ≤
          initial + ∑ n ∈ Finset.range N, replenish n := by
  constructor
  · intro h N
    have hN := h N
    unfold cumulativeResourceBalance at hN
    linarith
  · intro h N
    unfold cumulativeResourceBalance
    have hN := h N
    linarith

/-- A nonnegative initial stock and pointwise replenishment covering pointwise
realized cost are sufficient for deterministic/pathwise resource viability. -/
theorem resourceViable_of_pointwise_cost_le_replenish
    (initial : ℝ) (replenish cost : ℕ → ℝ)
    (hinit : 0 ≤ initial)
    (hstep : ∀ n, cost n ≤ replenish n) :
    ResourceViable initial replenish cost := by
  rw [resourceViable_iff_cumulative_cost_le]
  intro N
  have hsum :
      (∑ n ∈ Finset.range N, cost n) ≤
        ∑ n ∈ Finset.range N, replenish n := by
    exact Finset.sum_le_sum fun n hn => hstep n
  linarith

end
end UEOT.V3.Compression.Objecthood.ResourceClosure
