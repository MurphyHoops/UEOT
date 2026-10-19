import UEOT.V3.Compression.TransportCertificate
import Mathlib.Tactic.Ring

/-!
# Conditional scalar error certificates through the existing UEOT Core

`scalarBudget` is the exact recurrence evaluated by the executable QM
certificate code. The main theorem calls the existing Core
`weighted_chain_bound` to cover a supplied nonnegative error trace.

An application must establish the stated recurrence for its chosen error,
states and protocols. A finite collection of record-law TV comparisons does
not establish that recurrence for untested preparations or protocols, and is
not identified here with trace distance or diamond norm.

The Core instantiation below uses the directed scalar difference `actual -
budget`. This is an order certificate, not a claim that this difference is a
metric. The supplied recurrence makes every new residual nonpositive; the
nonnegative transport factors preserve its upper bound.
-/

namespace UEOTQM.Transport

open scoped BigOperators

/-- The scalar certificate at every boundary, including its initial budget. -/
noncomputable def scalarBudget (initial : ℝ) (L ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => L n * scalarBudget initial L ε n + ε n

@[simp] theorem scalarBudget_zero (initial : ℝ) (L ε : ℕ → ℝ) :
    scalarBudget initial L ε 0 = initial := rfl

@[simp] theorem scalarBudget_succ (initial : ℝ) (L ε : ℕ → ℝ) (n : ℕ) :
    scalarBudget initial L ε (n + 1) =
      L n * scalarBudget initial L ε n + ε n := rfl

theorem scalarBudget_nonneg (initial : ℝ) (L ε : ℕ → ℝ)
    (hinitial : 0 ≤ initial) (hL : ∀ n, 0 ≤ L n)
    (hε : ∀ n, 0 ≤ ε n) :
    ∀ n, 0 ≤ scalarBudget initial L ε n := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
    exact add_nonneg (mul_nonneg (hL n) ih) (hε n)

/-- Actual M-TC reuse: a scalar trace satisfying the declared local bounds is
covered by the recursively computed certificate. All error and budget signs
are explicit. The local recurrence remains an application-side obligation. -/
theorem scalar_transport_certificate
    (initial : ℝ) (e L ε : ℕ → ℝ)
    (hinitial : 0 ≤ initial)
    (he : ∀ n, 0 ≤ e n)
    (hL : ∀ n, 0 ≤ L n)
    (hε : ∀ n, 0 ≤ ε n)
    (hbase : e 0 ≤ initial)
    (hstep : ∀ n, e (n + 1) ≤ L n * e n + ε n)
    (n : ℕ) :
    0 ≤ e n ∧ e n ≤ scalarBudget initial L ε n ∧
      0 ≤ scalarBudget initial L ε n := by
  have hweighted :=
    UEOT.V3.Compression.TransportCertificate.weighted_chain_bound
      (A := fun _ => ℝ)
      (defect := fun _ budget actual => actual - budget)
      (ideal := scalarBudget initial L ε)
      (actual := e)
      (step := fun t x => L t * x + ε t)
      (L := L) (ε := fun _ => 0)
      (hcontract := by
        intro t
        simp only [scalarBudget_succ]
        exact le_of_eq (by ring))
      (htriangle := by
        intro t
        exact le_of_eq (by ring))
      (hlocal := by
        intro t
        exact sub_nonpos.mpr (hstep t))
      (hL0 := hL) n
  simp only [scalarBudget_zero, zero_mul, Finset.sum_const_zero,
    add_zero] at hweighted
  have hproduct : 0 ≤ ∏ j ∈ Finset.range n, L j :=
    Finset.prod_nonneg (fun j _ => hL j)
  have hbudget : e n ≤ scalarBudget initial L ε n :=
    sub_nonpos.mp (hweighted.trans
      (mul_nonpos_of_nonneg_of_nonpos hproduct (sub_nonpos.mpr hbase)))
  exact ⟨he n, hbudget, scalarBudget_nonneg initial L ε hinitial hL hε n⟩

end UEOTQM.Transport
