import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveOperationalAnchors
import UEOT.V3.CommonBottleneckRank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
Original promise: a finite linear response admits a shared two-drive factor precisely when its response rank is at most two.
Existing result: the common bottleneck gives necessity; GL classification compares two independently supplied nondegenerate factorizations.
Reduced premise: construct an actual linear encoder/decoder from the finite rank bound, including rank zero/one; rank two derives both nondegeneracy facts.
Models: finite-dimensional real linear input response; arbitrary real linear output space, with a finite matrix specialization. Rank three remains impossible.
Consumers: original unique GL orbit and registered unit intervention identification, with anchor premises still independent.

The range embeds into the old TwoDriveLatent by mathlib's existing dimension
criterion, and its existing linear left inverse constructs the decoder. No
physical resource/information interpretation of coordinates, global nonlinear
bottleneck, noisy rank decision, numerical algorithm or empirical support is
inferred. Lower-rank padding has unused coordinates; GL uniqueness is asserted
only for rank two. A single derivative matrix need not identify a global model.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
noncomputable section
universe uX uY
variable {X : Type uX} {Y : Type uY}
  [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
  [AddCommGroup Y] [Module ℝ Y]

/-- Necessary AND sufficient finite linear two-drive factorization. The
sufficient direction constructs H/G from the range; neither is an input. -/
theorem finite_rank_le_two_iff_linear_factorization (J : X →ₗ[ℝ] Y) :
    Module.finrank ℝ (LinearMap.range J)≤2 ↔
      ∃ (H : X →ₗ[ℝ] TwoDriveLatent) (G : TwoDriveLatent →ₗ[ℝ] Y), J=G.comp H := by
  constructor
  · intro hJ
    have hdim : Module.finrank ℝ (LinearMap.range J)≤Module.finrank ℝ TwoDriveLatent := by
      simpa [TwoDriveLatent] using hJ
    obtain ⟨e,he⟩ := finrank_le_iff_exists_linearMap.mp hdim
    refine ⟨e.comp J.rangeRestrict,(LinearMap.range J).subtype.comp e.leftInverse,?_⟩
    ext x
    simp only [LinearMap.comp_apply,LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr he)]
    rfl
  · rintro ⟨H,G,rfl⟩
    calc
      Module.finrank ℝ (LinearMap.range (G.comp H))≤Module.finrank ℝ (LinearMap.range G) :=
        Submodule.finrank_mono (LinearMap.range_comp_le_range H G)
      _ ≤ Module.finrank ℝ TwoDriveLatent:=G.finrank_range_le
      _ = 2 := by simp [TwoDriveLatent]

/-- At rank two, ANY factorization through these two coordinates is already
nondegenerate. Surjectivity/injectivity no longer need independent hypotheses. -/
theorem rank_two_factorization_nondegenerate (J : X →ₗ[ℝ] Y)
    (hJ : Module.finrank ℝ (LinearMap.range J)=2)
    (H : X →ₗ[ℝ] TwoDriveLatent) (G : TwoDriveLatent →ₗ[ℝ] Y)
    (hfactor : J=G.comp H) : Function.Surjective H ∧ Function.Injective G := by
  have hd : Module.finrank ℝ TwoDriveLatent=2:=by simp [TwoDriveLatent]
  have hHlower : 2≤Module.finrank ℝ (LinearMap.range H) := by
    have hle : Module.finrank ℝ (LinearMap.range J)≤Module.finrank ℝ (LinearMap.range H) := by
      rw [hfactor,LinearMap.range_comp]
      exact Submodule.finrank_map_le G (LinearMap.range H)
    simpa only [hJ] using hle
  have hHupper : Module.finrank ℝ (LinearMap.range H)≤2:=by
    simpa only [hd] using (LinearMap.range H).finrank_le
  have hGdim : Module.finrank ℝ (LinearMap.range G)=2 := by
    apply le_antisymm
    · simpa only [hd] using G.finrank_range_le
    · have hle : Module.finrank ℝ (LinearMap.range J)≤Module.finrank ℝ (LinearMap.range G) := by
        rw [hfactor]
        exact Submodule.finrank_mono (LinearMap.range_comp_le_range H G)
      simpa only [hJ] using hle
  constructor
  · apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq ((le_antisymm hHupper hHlower).trans hd.symm)
  · apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have h:=G.finrank_range_add_finrank_ker
    rw [hGdim,hd] at h
    omega

/-- Rank alone supplies at least one nondegenerate two-dimensional factor;
this is a constructed existence theorem, not just uniqueness of given factors. -/
theorem rank_two_exists_nondegenerate_factorization (J : X →ₗ[ℝ] Y)
    (hJ : Module.finrank ℝ (LinearMap.range J)=2) :
    ∃ (H : X →ₗ[ℝ] TwoDriveLatent) (G : TwoDriveLatent →ₗ[ℝ] Y),
      J=G.comp H ∧ Function.Surjective H ∧ Function.Injective G := by
  obtain ⟨H,G,hfactor⟩ := (finite_rank_le_two_iff_linear_factorization J).mp hJ.le
  exact ⟨H,G,hfactor,rank_two_factorization_nondegenerate J hJ H G hfactor⟩

/-- The original GL classifier consumes the rank-derived nondegeneracy of
BOTH given factors, so no full-rank encoder/decoder certificate is supplied. -/
theorem rank_two_factorizations_unique_gauge (J : X →ₗ[ℝ] Y)
    (hJ : Module.finrank ℝ (LinearMap.range J)=2)
    (H H' : X →ₗ[ℝ] TwoDriveLatent) (G G' : TwoDriveLatent →ₗ[ℝ] Y)
    (hfactor : J=G.comp H) (hfactor' : J=G'.comp H') :
    ∃! A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent,
      H'=A.toLinearMap.comp H ∧ G'=G.comp A.symm.toLinearMap := by
  have h:=rank_two_factorization_nondegenerate J hJ H G hfactor
  have h':=rank_two_factorization_nondegenerate J hJ H' G' hfactor'
  exact nondegenerate_linear_factorization_unique_gauge H H' G G' h.1 h'.1 h.2 h'.2
    (hfactor.symm.trans hfactor')

/-- Actual old unit-anchor consumer, now with injectivity discharged by the
observable rank. Independent selective unit interventions remain inputs. -/
theorem rank_two_registered_units_identify (J : X →ₗ[ℝ] Y)
    (hJ : Module.finrank ℝ (LinearMap.range J)=2)
    (H H' : X →ₗ[ℝ] TwoDriveLatent) (G G' : TwoDriveLatent →ₗ[ℝ] Y)
    (hfactor : J=G.comp H) (hfactor' : J=G'.comp H') (d : Fin 2→X)
    (ha : ∀i,H (d i)=driveUnitAxis i ∧ H' (d i)=driveUnitAxis i) : H=H' ∧ G=G' := by
  exact registered_unit_interventions_identify_factorization H H' G G'
    (rank_two_factorization_nondegenerate J hJ H G hfactor).2
    (rank_two_factorization_nondegenerate J hJ H' G' hfactor').2
    (hfactor.symm.trans hfactor') d ha

/-- Matrix-facing criterion in the exact old response coordinates. -/
theorem matrix_rank_le_two_iff_linear_factorization {m n : Type*} [Fintype m] [Fintype n]
    (J : Matrix m n ℝ) : J.rank≤2 ↔
      ∃ (H : (n→ℝ) →ₗ[ℝ] TwoDriveLatent) (G : TwoDriveLatent →ₗ[ℝ] (m→ℝ)), J.mulVecLin=G.comp H := by
  exact finite_rank_le_two_iff_linear_factorization J.mulVecLin

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
