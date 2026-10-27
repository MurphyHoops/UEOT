import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveLinearGaugeClassification

/-!
# What independently calibrated operational anchors identify

This file separates three different assumptions. Preserving each of two
labelled axis lines leaves two nonzero scale factors. Preserving their
oriented rays leaves two positive scale factors. Fixing both *unit vectors*
removes this remaining gauge freedom.

The encoder/decoder consumer uses two actual input interventions whose
latent responses are independently registered in the same units in both
models. The observed composite alone does not supply these anchor premises.
In particular, two available experimental knobs need not be selective for
the intended resource and information mechanisms.
-/

namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure

noncomputable section

/-- A labelled latent axis with a specified unit and orientation. -/
def driveUnitAxis (i : Fin 2) : TwoDriveLatent :=
  fun j => if j = i then 1 else 0

private theorem driveUnitAxis_ne_zero (i : Fin 2) : driveUnitAxis i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [driveUnitAxis] at hi

private theorem drive_coordinate_decomposition (z : TwoDriveLatent) :
    z = z 0 • driveUnitAxis 0 + z 1 • driveUnitAxis 1 := by
  funext i
  fin_cases i <;> simp [driveUnitAxis]

/-- Independent nonzero changes of the two coordinate units are genuine
invertible gauges. Positivity will additionally preserve orientation. -/
def driveAxisScaling (c : Fin 2 → ℝ) (hc : ∀ i, c i ≠ 0) :
    TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent where
  toFun z i := c i * z i
  invFun z i := (c i)⁻¹ * z i
  left_inv := by
    intro z
    funext i
    simp [mul_assoc, hc i]
  right_inv := by
    intro z
    funext i
    simp [mul_assoc, hc i]
  map_add' := by
    intro z w
    funext i
    exact mul_add (c i) (z i) (w i)
  map_smul' := by
    intro r z
    funext i
    change c i * (r * z i) = r * (c i * z i)
    ring

/-- Exact residual freedom after preserving two labelled axis lines.
The scales are forced to be nonzero by invertibility; they need not be
positive unless the orientations have also been registered. -/
theorem labelled_axis_lines_iff_nonzero_diagonal_gauge
    (A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent) :
    (∀ i : Fin 2, ∃ c : ℝ, A (driveUnitAxis i) = c • driveUnitAxis i) ↔
      ∃ (c : Fin 2 → ℝ) (hc : ∀ i, c i ≠ 0), A = driveAxisScaling c hc := by
  classical
  constructor
  · intro h
    let c : Fin 2 → ℝ := fun i => Classical.choose (h i)
    have haxis : ∀ i, A (driveUnitAxis i) = c i • driveUnitAxis i :=
      fun i => Classical.choose_spec (h i)
    have hc : ∀ i, c i ≠ 0 := by
      intro i hi
      have ha : A (driveUnitAxis i) = A 0 := by
        rw [haxis i, hi, zero_smul, map_zero]
      exact driveUnitAxis_ne_zero i (A.injective ha)
    refine ⟨c, hc, ?_⟩
    apply LinearEquiv.ext
    intro z
    calc
      A z = A (z 0 • driveUnitAxis 0 + z 1 • driveUnitAxis 1) :=
        congrArg A (drive_coordinate_decomposition z)
      _ = z 0 • (c 0 • driveUnitAxis 0) + z 1 • (c 1 • driveUnitAxis 1) := by
        rw [map_add, map_smul, map_smul, haxis 0, haxis 1]
      _ = driveAxisScaling c hc z := by
        funext i
        fin_cases i <;> simp [driveUnitAxis, driveAxisScaling, mul_comm]
  · rintro ⟨c, hc, rfl⟩ i
    refine ⟨c i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simp [driveAxisScaling, driveUnitAxis]
    · simp [driveAxisScaling, driveUnitAxis, hj]

/-- Registering directions as *oriented* removes sign changes, but still
leaves an independent positive change of units on each axis. -/
theorem oriented_axis_rays_iff_positive_diagonal_gauge
    (A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent) :
    (∀ i : Fin 2, ∃ c : ℝ, 0 < c ∧ A (driveUnitAxis i) = c • driveUnitAxis i) ↔
      ∃ (c : Fin 2 → ℝ) (hc : ∀ i, 0 < c i),
        A = driveAxisScaling c (fun i => ne_of_gt (hc i)) := by
  constructor
  · intro h
    obtain ⟨c, hc, hA⟩ :=
      (labelled_axis_lines_iff_nonzero_diagonal_gauge A).mp
        (fun i => let ⟨r, _, hr⟩ := h i; ⟨r, hr⟩)
    have hpos : ∀ i, 0 < c i := by
      intro i
      obtain ⟨r, hr, heq⟩ := h i
      rw [hA] at heq
      have hi := congrFun heq i
      have hci : c i = r := by simpa [driveAxisScaling, driveUnitAxis] using hi
      exact hci.symm ▸ hr
    exact ⟨c, hpos, hA⟩
  · rintro ⟨c, hc, rfl⟩ i
    refine ⟨c i, hc i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst j
      simp [driveAxisScaling, driveUnitAxis]
    · simp [driveAxisScaling, driveUnitAxis, hj]

/-- Two unit-calibrated independent anchors remove the entire GL(2) gauge. -/
theorem two_unit_anchors_identify_gauge
    (A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent)
    (h0 : A (driveUnitAxis 0) = driveUnitAxis 0)
    (h1 : A (driveUnitAxis 1) = driveUnitAxis 1) :
    A = LinearEquiv.refl ℝ TwoDriveLatent := by
  apply LinearEquiv.ext
  intro z
  change A z = z
  calc
    A z = A (z 0 • driveUnitAxis 0 + z 1 • driveUnitAxis 1) :=
      congrArg A (drive_coordinate_decomposition z)
    _ = z 0 • driveUnitAxis 0 + z 1 • driveUnitAxis 1 := by
      rw [map_add, map_smul, map_smul, h0, h1]
    _ = z := (drive_coordinate_decomposition z).symm

private theorem unit_anchored_encoder_surjective
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (H : X →ₗ[ℝ] TwoDriveLatent) (d : Fin 2 → X)
    (h : ∀ i, H (d i) = driveUnitAxis i) : Function.Surjective H := by
  intro z
  refine ⟨z 0 • d 0 + z 1 • d 1, ?_⟩
  rw [map_add, map_smul, map_smul, h 0, h 1]
  exact (drive_coordinate_decomposition z).symm

/-- Consumer of the inverse classification: equality of the observed
response together with the SAME two independently unit-calibrated input
interventions identifies both the encoder and the decoder. The actual
interventions supply surjectivity, so it is derived rather than added.

The calibration equalities are external operational premises. This theorem
does not manufacture selective physical interventions from fitted outputs. -/
theorem registered_unit_interventions_identify_factorization
    {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y]
    (H H' : X →ₗ[ℝ] TwoDriveLatent)
    (G G' : TwoDriveLatent →ₗ[ℝ] Y)
    (hG : Function.Injective G) (hG' : Function.Injective G')
    (hJ : G.comp H = G'.comp H')
    (d : Fin 2 → X)
    (hanchor : ∀ i, H (d i) = driveUnitAxis i ∧ H' (d i) = driveUnitAxis i) :
    H = H' ∧ G = G' := by
  have hH := unit_anchored_encoder_surjective H d (fun i => (hanchor i).1)
  have hH' := unit_anchored_encoder_surjective H' d (fun i => (hanchor i).2)
  obtain ⟨A, ⟨hAH, hGA⟩, _⟩ :=
    nondegenerate_linear_factorization_unique_gauge H H' G G' hH hH' hG hG' hJ
  have hfixed : ∀ i, A (driveUnitAxis i) = driveUnitAxis i := by
    intro i
    calc
      A (driveUnitAxis i) = A (H (d i)) := by rw [(hanchor i).1]
      _ = H' (d i) :=
        (congrArg (fun (F : X →ₗ[ℝ] TwoDriveLatent) => F (d i)) hAH).symm
      _ = driveUnitAxis i := (hanchor i).2
  have hA := two_unit_anchors_identify_gauge A (hfixed 0) (hfixed 1)
  constructor
  · ext x
    have hx := congrArg (fun (F : X →ₗ[ℝ] TwoDriveLatent) => F x) hAH
    simpa [hA] using hx.symm
  · ext z
    have hz := congrArg (fun (F : TwoDriveLatent →ₗ[ℝ] Y) => F z) hGA
    simpa [hA] using hz.symm

/-- A shear fixes the first unit-calibrated axis while altering the second.
It provides an explicit residual gauge after only one anchor. -/
def driveShear (c : ℝ) : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent where
  toFun z i := if i = 0 then z 0 + c * z 1 else z 1
  invFun z i := if i = 0 then z 0 - c * z 1 else z 1
  left_inv := by
    intro z
    funext i
    fin_cases i <;> simp
  right_inv := by
    intro z
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro z w
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro r z
    funext i
    fin_cases i <;> simp <;> ring

/-- One independently fixed unit vector does not identify a two-dimensional
latent representation: the displayed nonidentity shear preserves it. -/
theorem one_unit_anchor_leaves_nontrivial_gauge :
    ∃ A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent,
      A (driveUnitAxis 0) = driveUnitAxis 0 ∧
      A ≠ LinearEquiv.refl ℝ TwoDriveLatent := by
  refine ⟨driveShear 1, ?_, ?_⟩
  · funext i
    fin_cases i <;> simp [driveShear, driveUnitAxis]
  · intro h
    have hi := congrArg (fun A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent =>
      A (driveUnitAxis 1) 0) h
    norm_num [driveShear, driveUnitAxis] at hi

/-- Even two correctly labelled and oriented axes leave genuine ambiguity
when their units are not fixed. A factor-two scaling is a concrete witness. -/
theorem two_oriented_axes_do_not_identify_units :
    ∃ A : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent,
      (∀ i : Fin 2, ∃ c : ℝ, 0 < c ∧ A (driveUnitAxis i) = c • driveUnitAxis i) ∧
      A ≠ LinearEquiv.refl ℝ TwoDriveLatent := by
  let A := driveAxisScaling (fun _ => 2) (by intro i; norm_num)
  refine ⟨A, ?_, ?_⟩
  · intro i
    refine ⟨2, by norm_num, ?_⟩
    funext j
    rfl
  · intro h
    have hi := congrArg (fun B : TwoDriveLatent ≃ₗ[ℝ] TwoDriveLatent =>
      B (driveUnitAxis 0) 0) h
    norm_num [A, driveAxisScaling, driveUnitAxis] at hi

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure
