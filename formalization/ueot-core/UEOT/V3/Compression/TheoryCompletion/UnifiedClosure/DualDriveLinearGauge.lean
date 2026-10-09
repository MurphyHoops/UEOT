import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveGaugeCompleteness
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCJoint2DRejection
import Mathlib.Tactic

/-!
# UMC-04.2 — two-dimensional latent GL(2) gauge non-identifiability

The scalar Pi-lambda-Phi gauge classification and the independently proved
C5 necessary rank bound are different mathematical claims. Here we show
that any invertible LINEAR change of 2D latent coordinates can be
absorbed into a decoder, preserving all outputs. A nontrivial invertible
change exists. Thus rank at most two, even with exact observations,
does not identify physically named Pi and Phi axes without anchors.

This is a sufficient GL(2) reparameterization invariance, not a claim
that every nonlinearly equivalent model is related by GL(2).
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

abbrev TwoDriveLatent := Fin 2 → ℝ

universe uX uO

/-- Two dimensional registered latent coordinates have a genuine
change-of-basis freedom when the observation decoder is allowed to
transform contragrediently. -/
theorem latent_GL2_reparameterization_preserves_all_responses
    {X : Type uX} {O : Type uO}
    (z : X → TwoDriveLatent) (read : TwoDriveLatent → O)
    (g : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent) :
    (fun x => read (z x)) =
    (fun x => (read ∘ g.symm) (g (z x))) := by
  funext x
  simp

/-- The 2D gauge group is not trivially the identity. A sign inversion
changes a nonzero latent vector while preserving its response when the
decoder changes by the corresponding inverse. -/
theorem two_drive_GL2_gauge_is_nontrivial :
    ∃ g : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent,
      g (fun _ => (1 : ℝ)) ≠ (fun _ => (1 : ℝ)) := by
  refine ⟨LinearEquiv.neg ℝ, ?_⟩
  intro h
  have hh := congrFun h 0
  norm_num at hh

/-- Independent injective decoding is sufficient to identify a
latent representation ONLY when the decoder itself is fixed. -/
theorem fixed_injective_latent_decoder_identifies_latents
    {X : Type uX} {O : Type uO}
    (z z' : X → TwoDriveLatent)
    (read : TwoDriveLatent → O)
    (hinj : Function.Injective read)
    (h : (fun x => read (z x)) = (fun x => read (z' x))) :
    z = z' := by
  funext x
  exact hinj (congrFun h x)

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
