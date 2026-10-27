import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveLinearGauge

/-!
# Exact inverse classification of nondegenerate linear drive factorizations

The earlier `latent_GL2_reparameterization_preserves_all_responses` gives
forward gauge invariance. This file proves the converse, including uniqueness,
for two *linear* factorizations through a common latent vector space. Both
encoders are surjective and both decoders are injective. For
`L = TwoDriveLatent` this is the full-rank GL(2) classification.

No finite-dimensional input or output assumption is needed. Surjectivity and
injectivity are explicit nondegeneracy hypotheses, not consequences of a
measured rank upper bound. The result does not classify nonlinear models,
rank-deficient factorizations, or physical interpretations of the two axes.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

noncomputable section

universe uX uL uY

/-- Two nondegenerate linear factorizations of the same observable map differ
by one unique invertible latent coordinate change. The equivalence is built
from actual preimages under the encoders; no gauge relation is assumed. -/
theorem nondegenerate_linear_factorization_unique_gauge
    {X : Type uX} {L : Type uL} {Y : Type uY}
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Y] [Module ℝ Y]
    (H H' : X →ₗ[ℝ] L) (G G' : L →ₗ[ℝ] Y)
    (hH : Function.Surjective H) (hH' : Function.Surjective H')
    (hG : Function.Injective G) (hG' : Function.Injective G')
    (hJ : G.comp H = G'.comp H') :
    ∃! A : L ≃ₗ[ℝ] L,
      H' = A.toLinearMap.comp H ∧ G' = G.comp A.symm.toLinearMap := by
  classical
  let f : L → L := fun z => H' (Classical.choose (hH z))
  let g : L → L := fun z => H (Classical.choose (hH' z))
  have hf : ∀ z, G' (f z) = G z := by
    intro z
    have hc := congrArg (fun (F : X →ₗ[ℝ] Y) => F (Classical.choose (hH z))) hJ
    simp only [LinearMap.comp_apply] at hc
    dsimp [f]
    rw [← hc, Classical.choose_spec (hH z)]
  have hg : ∀ z, G (g z) = G' z := by
    intro z
    have hc := congrArg (fun (F : X →ₗ[ℝ] Y) => F (Classical.choose (hH' z))) hJ
    simp only [LinearMap.comp_apply] at hc
    dsimp [g]
    rw [hc, Classical.choose_spec (hH' z)]
  let A : L ≃ₗ[ℝ] L :=
    { toFun := f
      invFun := g
      left_inv := by
        intro z
        apply hG
        rw [hg, hf]
      right_inv := by
        intro z
        apply hG'
        rw [hf, hg]
      map_add' := by
        intro z w
        apply hG'
        rw [hf, map_add, map_add, hf, hf]
      map_smul' := by
        intro c z
        apply hG'
        rw [hf, map_smul, map_smul, hf] }
  have hAH : H' = A.toLinearMap.comp H := by
    ext x
    apply hG'
    change G' (H' x) = G' (f (H x))
    rw [hf]
    exact (congrArg (fun (F : X →ₗ[ℝ] Y) => F x) hJ).symm
  have hGA : G' = G.comp A.symm.toLinearMap := by
    ext z
    exact (hg z).symm
  refine ⟨A, ⟨hAH, hGA⟩, ?_⟩
  intro B hB
  ext z
  obtain ⟨x, hx⟩ := hH z
  subst z
  have ha := congrArg (fun (F : X →ₗ[ℝ] L) => F x) hAH
  have hb := congrArg (fun (F : X →ₗ[ℝ] L) => F x) hB.1
  exact hb.symm.trans ha

/-- Exact observational equivalence is precisely one GL orbit in the
nondegenerate linear model class. This is an iff, not only invariance. -/
theorem same_linear_response_iff_unique_gauge
    {X : Type uX} {L : Type uL} {Y : Type uY}
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup L] [Module ℝ L]
    [AddCommGroup Y] [Module ℝ Y]
    (H H' : X →ₗ[ℝ] L) (G G' : L →ₗ[ℝ] Y)
    (hH : Function.Surjective H) (hH' : Function.Surjective H')
    (hG : Function.Injective G) (hG' : Function.Injective G') :
    G.comp H = G'.comp H' ↔
      ∃! A : L ≃ₗ[ℝ] L,
        H' = A.toLinearMap.comp H ∧ G' = G.comp A.symm.toLinearMap := by
  constructor
  · exact nondegenerate_linear_factorization_unique_gauge H H' G G' hH hH' hG hG'
  · rintro ⟨A, ⟨hAH, hGA⟩, _⟩
    ext x
    change G (H x) = G' (H' x)
    rw [hAH, hGA]
    simp

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
