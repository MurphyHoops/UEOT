import Mathlib.Probability.Kernel.Composition.MapComap

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

end UEOT.V3.StrongLumpability
