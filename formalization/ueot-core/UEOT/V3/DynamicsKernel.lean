import Mathlib.Probability.Kernel.Composition.CompMap

/-!
# P-DYN-01 — general Markov-kernel lumpability

This module formalizes the exact kernel intertwining condition from clause (2)
of P-DYN-01 and propagates it to every finite-step transition kernel.

It does **not** yet identify this with the full conditional-history/path-law
Markov statement in clause (1).  That final bridge remains an explicit
source-level obligation.
-/

namespace UEOT.V3.DynamicsKernel

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe uX uM
variable {X : Type uX} {M : Type uM}
variable [MeasurableSpace X] [MeasurableSpace M]

def StrongLumpability
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f) : Prop :=
  Kernel.map P f = Kernel.comap Pbar f hf

theorem strongLumpability_iff_apply
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f) :
    StrongLumpability P Pbar f hf ↔
      ∀ x, (P x).map f = Pbar (f x) := by
  constructor
  · intro h x
    have hx := congrArg (fun κ : Kernel X M => κ x) h
    unfold StrongLumpability at h
    rw [Kernel.map_apply _ hf, Kernel.comap_apply] at hx
    exact hx
  · intro h
    unfold StrongLumpability
    ext x B hB
    rw [Kernel.map_apply' _ hf _ hB, Kernel.comap_apply']
    have hx := congrArg (fun μ : Measure M => μ B) (h x)
    simpa [Measure.map_apply hf hB] using hx

theorem strongLumpability_iff_preimage
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f) :
    StrongLumpability P Pbar f hf ↔
      ∀ x B, MeasurableSet B →
        P x (f ⁻¹' B) = Pbar (f x) B := by
  rw [strongLumpability_iff_apply]
  constructor
  · intro h x B hB
    have hx := congrArg (fun μ : Measure M => μ B) (h x)
    simpa [Measure.map_apply hf hB] using hx
  · intro h x
    ext B hB
    rw [Measure.map_apply hf hB]
    exact h x B hB

theorem strongLumpability_fiber_constant
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    {x y : X} (hxy : f x = f y) :
    (P x).map f = (P y).map f := by
  rw [(strongLumpability_iff_apply P Pbar f hf).1 h x,
      (strongLumpability_iff_apply P Pbar f hf).1 h y, hxy]

noncomputable def iterateKernel (P : Kernel X X) : ℕ → Kernel X X
  | 0 => Kernel.id
  | n + 1 => P ∘ₖ iterateKernel P n

@[simp]
theorem iterateKernel_zero (P : Kernel X X) :
    iterateKernel P 0 = Kernel.id := rfl

@[simp]
theorem iterateKernel_succ (P : Kernel X X) (n : ℕ) :
    iterateKernel P (n + 1) = P ∘ₖ iterateKernel P n := rfl

theorem iterateKernel_strongLumpability
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf) :
    ∀ n, StrongLumpability (iterateKernel P n) (iterateKernel Pbar n) f hf := by
  intro n
  induction n with
  | zero =>
      unfold StrongLumpability
      simp [iterateKernel, Kernel.id_map, Kernel.id_comap, hf]
  | succ n ih =>
      unfold StrongLumpability at ih ⊢
      simp only [iterateKernel_succ]
      calc
        Kernel.map (P ∘ₖ iterateKernel P n) f
            = Kernel.map P f ∘ₖ iterateKernel P n :=
          Kernel.map_comp (iterateKernel P n) P f
        _ = Kernel.comap Pbar f hf ∘ₖ iterateKernel P n := by
          rw [h]
        _ = Pbar ∘ₖ Kernel.map (iterateKernel P n) f := by
          symm
          exact Kernel.comp_map (iterateKernel P n) Pbar hf
        _ = Pbar ∘ₖ Kernel.comap (iterateKernel Pbar n) f hf := by
          rw [ih]
        _ = (Pbar ∘ₖ iterateKernel Pbar n) ∘ₖ Kernel.deterministic f hf := by
          rw [← Kernel.comp_deterministic_eq_comap (iterateKernel Pbar n) hf,
              ← Kernel.comp_assoc]
        _ = Kernel.comap (Pbar ∘ₖ iterateKernel Pbar n) f hf :=
          Kernel.comp_deterministic_eq_comap _ hf

theorem iterateKernel_pushforward
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    (n : ℕ) (x : X) :
    (iterateKernel P n x).map f = iterateKernel Pbar n (f x) := by
  exact
    (strongLumpability_iff_apply (iterateKernel P n) (iterateKernel Pbar n) f hf).1
      (iterateKernel_strongLumpability P Pbar f hf h n) x

theorem iterateKernel_preimage
    (P : Kernel X X) (Pbar : Kernel M M)
    (f : X → M) (hf : Measurable f)
    (h : StrongLumpability P Pbar f hf)
    (n : ℕ) (x : X) (B : Set M) (hB : MeasurableSet B) :
    iterateKernel P n x (f ⁻¹' B) =
      iterateKernel Pbar n (f x) B := by
  exact
    (strongLumpability_iff_preimage (iterateKernel P n) (iterateKernel Pbar n) f hf).1
      (iterateKernel_strongLumpability P Pbar f hf h n) x B hB

end UEOT.V3.DynamicsKernel
