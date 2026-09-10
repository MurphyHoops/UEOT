import UEOT.V3.TotalVariation
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Ring

/-!
# P-ID-01 — transport-defect accumulation

This module formalizes the finite-time TCIC accumulation estimate from Core 3.
`K t` denotes a frozen endpoint kernel at scale/time `t`; it is not a one-step
physical transition kernel.  The proof uses only measurable pushforward
contraction of total variation, the TV triangle inequality, coherent transport
composition, and induction over the horizon.
-/

namespace UEOT.V3.TransportDefect

open MeasureTheory
open UEOT.V3.TotalVariation
open scoped BigOperators

universe u

/-- Total variation vanishes on identical probability measures. -/
theorem tvDist_self {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    tvDist μ μ = 0 := by
  apply le_antisymm
  · unfold tvDist
    refine csSup_le (tvEventSet_nonempty μ μ) ?_
    intro r hr
    rcases hr with ⟨A, _hA, rfl⟩
    simp
  · exact tvDist_nonneg μ μ

/-- Triangle inequality for the source sup-over-measurable-events definition
of total variation. -/
theorem tvDist_triangle {X : Type u} [MeasurableSpace X]
    (μ ν ρ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  unfold tvDist
  refine csSup_le (tvEventSet_nonempty μ ρ) ?_
  intro r hr
  rcases hr with ⟨A, hA, rfl⟩
  have hsplit :
      μ.real A - ρ.real A =
        (μ.real A - ν.real A) + (ν.real A - ρ.real A) := by
    ring
  rw [hsplit]
  exact (abs_add _ _).trans <|
    add_le_add (tvEvent_le μ ν A hA) (tvEvent_le ν ρ A hA)

/-- Frozen endpoint kernels with coherent measurable transports between their
state spaces. -/
structure FrozenTransportSystem (M : ℕ → Type u)
    [∀ n, MeasurableSpace (M n)] where
  K : ∀ n, M n → Measure (M n)
  isProbability_K : ∀ n m, IsProbabilityMeasure (K n m)
  Γ : ∀ s t, M s → M t
  measurable_Γ : ∀ s t, Measurable (Γ s t)
  Γ_id : ∀ t (x : M t), Γ t t x = x
  Γ_comp : ∀ r s t (x : M r), Γ r t x = Γ s t (Γ r s x)

namespace FrozenTransportSystem

variable {M : ℕ → Type u} [∀ n, MeasurableSpace (M n)]

/-- Pointwise form of the adjacent TCIC defect hypothesis. -/
def AdjacentBound (S : FrozenTransportSystem M) (ε : ℕ → ℝ) : Prop :=
  ∀ n (m : M n),
    tvDist ((S.K n m).map (S.Γ n (n + 1)))
      (S.K (n + 1) (S.Γ n (n + 1) m)) ≤ ε n

/-- P-ID-01: endpoint transport defect is bounded by the sum of adjacent
transport defects.  The source supremum-over-initial-state statement follows
pointwise from this theorem. -/
theorem p_id_01
    (S : FrozenTransportSystem M) (ε : ℕ → ℝ)
    (hadj : S.AdjacentBound ε) :
    ∀ n (m : M 0),
      tvDist ((S.K 0 m).map (S.Γ 0 n))
        (S.K n (S.Γ 0 n m)) ≤ ∑ i ∈ Finset.range n, ε i := by
  intro n
  induction n with
  | zero =>
      intro m
      have hΓ0 : S.Γ 0 0 = id := by
        funext x
        exact S.Γ_id 0 x
      letI : IsProbabilityMeasure (S.K 0 m) := S.isProbability_K 0 m
      simp [hΓ0, tvDist_self]
  | succ n ih =>
      intro m
      let μ0 : Measure (M 0) := S.K 0 m
      let μn : Measure (M n) := S.K n (S.Γ 0 n m)
      let μnext : Measure (M (n + 1)) := S.K (n + 1) (S.Γ 0 (n + 1) m)
      let γ : M n → M (n + 1) := S.Γ n (n + 1)
      letI : IsProbabilityMeasure μ0 := S.isProbability_K 0 m
      letI : IsProbabilityMeasure μn := S.isProbability_K n (S.Γ 0 n m)
      letI : IsProbabilityMeasure μnext :=
        S.isProbability_K (n + 1) (S.Γ 0 (n + 1) m)
      have h0n : Measurable (S.Γ 0 n) := S.measurable_Γ 0 n
      have hγ : Measurable γ := S.measurable_Γ n (n + 1)
      have hcomp_fun : S.Γ 0 (n + 1) = γ ∘ S.Γ 0 n := by
        funext x
        exact S.Γ_comp 0 n (n + 1) x
      have hcomp_pt : S.Γ 0 (n + 1) m = γ (S.Γ 0 n m) :=
        S.Γ_comp 0 n (n + 1) m
      have hmap0 :
          μ0.map (S.Γ 0 (n + 1)) = (μ0.map (S.Γ 0 n)).map γ := by
        rw [hcomp_fun]
        exact (Measure.map_map hγ h0n).symm
      letI : IsProbabilityMeasure (μ0.map (S.Γ 0 n)) :=
        (Measure.isProbabilityMeasure_map_iff h0n.aemeasurable).2 inferInstance
      letI : IsProbabilityMeasure ((μ0.map (S.Γ 0 n)).map γ) :=
        (Measure.isProbabilityMeasure_map_iff hγ.aemeasurable).2 inferInstance
      letI : IsProbabilityMeasure (μn.map γ) :=
        (Measure.isProbabilityMeasure_map_iff hγ.aemeasurable).2 inferInstance
      have htri :
          tvDist (μ0.map (S.Γ 0 (n + 1))) μnext ≤
            tvDist ((μ0.map (S.Γ 0 n)).map γ) (μn.map γ) +
              tvDist (μn.map γ) μnext := by
        rw [hmap0]
        exact tvDist_triangle _ _ _
      have hold :
          tvDist ((μ0.map (S.Γ 0 n)).map γ) (μn.map γ) ≤
            tvDist (μ0.map (S.Γ 0 n)) μn :=
        tvDist_map_le _ _ γ hγ
      have hnew : tvDist (μn.map γ) μnext ≤ ε n := by
        simpa [μn, μnext, γ, hcomp_pt] using hadj n (S.Γ 0 n m)
      have hind :
          tvDist (μ0.map (S.Γ 0 n)) μn ≤
            ∑ i ∈ Finset.range n, ε i := by
        simpa [μ0, μn] using ih m
      calc
        tvDist ((S.K 0 m).map (S.Γ 0 (n + 1)))
            (S.K (n + 1) (S.Γ 0 (n + 1) m)) =
            tvDist (μ0.map (S.Γ 0 (n + 1))) μnext := by rfl
        _ ≤ tvDist ((μ0.map (S.Γ 0 n)).map γ) (μn.map γ) +
              tvDist (μn.map γ) μnext := htri
        _ ≤ tvDist (μ0.map (S.Γ 0 n)) μn + ε n := add_le_add hold hnew
        _ ≤ (∑ i ∈ Finset.range n, ε i) + ε n := add_le_add_right hind _
        _ = ∑ i ∈ Finset.range (n + 1), ε i := by
          rw [Finset.sum_range_succ]

end FrozenTransportSystem

end UEOT.V3.TransportDefect
