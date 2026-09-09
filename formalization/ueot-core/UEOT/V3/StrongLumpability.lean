import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
P-DYN-01, kernel-level strong lumpability.

For a measurable coarse map f : X → M and a candidate macro kernel Pbar,
strong lumpability is exactly the intertwining identity

  map P f = comap Pbar f.

This is the general measurable-kernel form of
P(x, f⁻¹ B) = Pbar(f x, B).
-/

namespace UEOT.V3.StrongLumpability

open MeasureTheory ProbabilityTheory

def StrongLumpable
    {X M : Type*}
    [MeasurableSpace X] [MeasurableSpace M]
    (P : Kernel X X) (f : X → M) (hf : Measurable f)
    (Pbar : Kernel M M) : Prop :=
  Kernel.map P f = Kernel.comap Pbar f hf

theorem strongLumpable_iff_setwise
    {X M : Type*}
    [MeasurableSpace X] [MeasurableSpace M]
    (P : Kernel X X) (f : X → M) (hf : Measurable f)
    (Pbar : Kernel M M) :
    StrongLumpable P f hf Pbar ↔
      ∀ x B, MeasurableSet B →
        P x (f ⁻¹' B) = Pbar (f x) B := by
  unfold StrongLumpable
  rw [Kernel.ext_iff']
  constructor
  · intro h x B hB
    have hx := h x B hB
    simpa [Kernel.map_apply' P hf x hB,
      Kernel.comap_apply' Pbar hf x B] using hx
  · intro h x B hB
    rw [Kernel.map_apply' P hf x hB,
      Kernel.comap_apply' Pbar hf x B]
    exact h x B hB

theorem strongLumpable_pointwise
    {X M : Type*}
    [MeasurableSpace X] [MeasurableSpace M]
    {P : Kernel X X} {f : X → M} {hf : Measurable f}
    {Pbar : Kernel M M}
    (h : StrongLumpable P f hf Pbar) (x : X) :
    Kernel.map P f x = Pbar (f x) := by
  have hx := congrArg (fun K : Kernel X M => K x) h
  simpa [StrongLumpable, Kernel.comap_apply] using hx


theorem comap_comp_measure
    {X M : Type*}
    [MeasurableSpace X] [MeasurableSpace M]
    (μ : Measure X) (f : X → M) (hf : Measurable f)
    (Pbar : Kernel M M) :
    (Kernel.comap Pbar f hf) ∘ₘ μ = Pbar ∘ₘ (μ.map f) := by
  ext B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _),
    Measure.bind_apply hB (Kernel.aemeasurable _)]
  rw [lintegral_map (Pbar.measurable_coe hB) hf]
  rfl

theorem one_step_law_commutes
    {X M : Type*}
    [MeasurableSpace X] [MeasurableSpace M]
    (μ : Measure X)
    (P : Kernel X X) (f : X → M) (hf : Measurable f)
    (Pbar : Kernel M M)
    (h : StrongLumpable P f hf Pbar) :
    (P ∘ₘ μ).map f = Pbar ∘ₘ (μ.map f) := by
  rw [Measure.map_comp μ P hf]
  change (Kernel.map P f) ∘ₘ μ = Pbar ∘ₘ (μ.map f)
  rw [h]
  exact comap_comp_measure μ f hf Pbar


def evolve
    {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) : ℕ → Measure X → Measure X
  | 0, μ => μ
  | n + 1, μ => P ∘ₘ evolve P n μ

@[simp]
theorem evolve_zero
    {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) (μ : Measure X) :
    evolve P 0 μ = μ := rfl

@[simp]
theorem evolve_succ
    {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) (n : ℕ) (μ : Measure X) :
    evolve P (n + 1) μ = P ∘ₘ evolve P n μ := rfl

theorem n_step_law_commutes
    {X M : Type*}
    [MeasurableSpace X] [MeasurableSpace M]
    (μ : Measure X)
    (P : Kernel X X) (f : X → M) (hf : Measurable f)
    (Pbar : Kernel M M)
    (h : StrongLumpable P f hf Pbar) :
    ∀ n, (evolve P n μ).map f = evolve Pbar n (μ.map f) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [evolve_succ, evolve_succ,
        one_step_law_commutes (evolve P n μ) P f hf Pbar h, ih]

end UEOT.V3.StrongLumpability
