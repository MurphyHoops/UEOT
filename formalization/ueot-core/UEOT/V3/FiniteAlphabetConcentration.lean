import UEOT.V3.TotalVariation
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# P-STAT-01 foundation — finite-alphabet TV union layer

This module isolates the finite combinatorial part of the frozen P-STAT-01
proof.  On a finite response alphabet, total variation is controlled by the
finitely many event-mass errors.  A union bound over those `2^K` events and
then over `L` response cells produces the source combinatorial factor.

The Bernoulli/Hoeffding sampling layer is added separately below this layer;
no probabilistic independence is hidden in the finite union argument.
-/

namespace UEOT.V3.FiniteAlphabetConcentration

open MeasureTheory
open UEOT.V3.TotalVariation
open scoped BigOperators

universe uΩ uJ uY

variable {Ω : Type uΩ} {J : Type uJ} {Y : Type uY}
variable [MeasurableSpace Ω] [MeasurableSpace Y]

/-- On a finite measurable alphabet, bounds for every finite event control the
source total-variation supremum. -/
theorem tvDist_le_of_finset_event_le
    [Fintype Y] [MeasurableSingletonClass Y]
    (p q : Measure Y)
    [IsProbabilityMeasure p] [IsProbabilityMeasure q]
    {η : ℝ}
    (h : ∀ A : Finset Y,
      |p.real (A : Set Y) - q.real (A : Set Y)| ≤ η) :
    tvDist p q ≤ η := by
  classical
  unfold tvDist
  refine csSup_le (tvEventSet_nonempty p q) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  let s : Finset Y := Finset.univ.filter (fun y => y ∈ A)
  have hs : (s : Set Y) = A := by
    ext y
    simp [s]
  simpa [hs] using h s

/-- Bad total-variation event for one response cell. -/
def tvBadEvent
    (p : Measure Y) (pHat : Ω → Measure Y) (η : ℝ) : Set Ω :=
  {ω | η < tvDist p (pHat ω)}

/-- Bad event-mass deviation for one finite response-alphabet subset. -/
def subsetBadEvent
    (p : Measure Y) (pHat : Ω → Measure Y) (η : ℝ)
    (A : Finset Y) : Set Ω :=
  {ω | η < |p.real (A : Set Y) - (pHat ω).real (A : Set Y)|}

/-- If TV exceeds `η`, at least one finite-alphabet event has mass error
exceeding `η`.  This is the finite-space step used by P-STAT-01. -/
theorem tvBadEvent_subset_iUnion_subsetBadEvent
    [Fintype Y] [MeasurableSingletonClass Y]
    (p : Measure Y) [IsProbabilityMeasure p]
    (pHat : Ω → Measure Y)
    (hpHat : ∀ ω, IsProbabilityMeasure (pHat ω))
    (η : ℝ) :
    tvBadEvent p pHat η ⊆ ⋃ A : Finset Y, subsetBadEvent p pHat η A := by
  classical
  intro ω hω
  by_contra hnot
  have hfinite : ∀ A : Finset Y,
      |p.real (A : Set Y) - (pHat ω).real (A : Set Y)| ≤ η := by
    intro A
    by_contra hle
    have hlt : η < |p.real (A : Set Y) - (pHat ω).real (A : Set Y)| :=
      lt_of_not_ge hle
    apply hnot
    simp only [Set.mem_iUnion]
    exact ⟨A, hlt⟩
  letI : IsProbabilityMeasure (pHat ω) := hpHat ω
  have htv := tvDist_le_of_finset_event_le p (pHat ω) hfinite
  exact (not_le_of_gt hω) htv

/-- A uniform per-subset tail bound `B` yields a one-cell TV tail bound with
exactly `2^K` event factors, where `K = card Y`. -/
theorem measure_tvBadEvent_le_of_subset_bound
    [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : Measure Y) [IsProbabilityMeasure p]
    (pHat : Ω → Measure Y)
    (hpHat : ∀ ω, IsProbabilityMeasure (pHat ω))
    (η B : ℝ)
    (hB : ∀ A : Finset Y, μ.real (subsetBadEvent p pHat η A) ≤ B) :
    μ.real (tvBadEvent p pHat η) ≤
      (2 ^ Fintype.card Y : ℝ) * B := by
  calc
    μ.real (tvBadEvent p pHat η)
        ≤ μ.real (⋃ A : Finset Y, subsetBadEvent p pHat η A) :=
      measureReal_mono (tvBadEvent_subset_iUnion_subsetBadEvent p pHat hpHat η)
    _ ≤ ∑ A : Finset Y, μ.real (subsetBadEvent p pHat η A) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _A : Finset Y, B := by
      exact Finset.sum_le_sum fun A _ => hB A
    _ = (2 ^ Fintype.card Y : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_finset]
      norm_cast

/-- A uniform one-cell TV tail bound `B` yields a simultaneous bound over `L`
response cells.  This step uses only a union bound and does not assume the cells
are mutually independent. -/
theorem measure_exists_cell_tvBadEvent_le
    [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : J → Measure Y)
    (pHat : J → Ω → Measure Y)
    (η B : ℝ)
    (hcell : ∀ j, μ.real (tvBadEvent (p j) (pHat j) η) ≤ B) :
    μ.real {ω | ∃ j : J, ω ∈ tvBadEvent (p j) (pHat j) η} ≤
      (Fintype.card J : ℝ) * B := by
  have hset :
      {ω | ∃ j : J, ω ∈ tvBadEvent (p j) (pHat j) η} =
        ⋃ j : J, tvBadEvent (p j) (pHat j) η := by
    ext ω
    simp
  rw [hset]
  calc
    μ.real (⋃ j : J, tvBadEvent (p j) (pHat j) η)
        ≤ ∑ j : J, μ.real (tvBadEvent (p j) (pHat j) η) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : J, B := by
      exact Finset.sum_le_sum fun j _ => hcell j
    _ = (Fintype.card J : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_cast

/-- Combined finite-union layer: if every cell/subset deviation has tail at
most `B`, then the probability that any response-cell TV exceeds `η` is bounded
by `L * 2^K * B`.  Setting `B = 2*exp(-2*N*η^2)` gives the frozen
`L * 2^(K+1)` factor. -/
theorem measure_exists_cell_tvBadEvent_le_of_subset_bound
    [Fintype J] [Fintype Y] [MeasurableSingletonClass Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : J → Measure Y)
    (hp : ∀ j, IsProbabilityMeasure (p j))
    (pHat : J → Ω → Measure Y)
    (hpHat : ∀ j ω, IsProbabilityMeasure (pHat j ω))
    (η B : ℝ)
    (hB : ∀ j A,
      μ.real (subsetBadEvent (p j) (pHat j) η A) ≤ B) :
    μ.real {ω | ∃ j : J, ω ∈ tvBadEvent (p j) (pHat j) η} ≤
      (Fintype.card J : ℝ) * (2 ^ Fintype.card Y : ℝ) * B := by
  have hcell : ∀ j,
      μ.real (tvBadEvent (p j) (pHat j) η) ≤
        (2 ^ Fintype.card Y : ℝ) * B := by
    intro j
    letI : IsProbabilityMeasure (p j) := hp j
    exact measure_tvBadEvent_le_of_subset_bound μ (p j) (pHat j)
      (hpHat j) η B (hB j)
  simpa [mul_assoc] using
    measure_exists_cell_tvBadEvent_le μ p pHat η
      ((2 ^ Fintype.card Y : ℝ) * B) hcell

end UEOT.V3.FiniteAlphabetConcentration
