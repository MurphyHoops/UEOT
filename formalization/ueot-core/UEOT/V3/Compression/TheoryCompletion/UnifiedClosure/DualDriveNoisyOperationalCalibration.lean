import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveOperationalAnchors
import UEOT.V3.Compression.ActionGapGaugeStability
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Original commitment: noisy operational anchors must identify the SAME response factors and preserve justified action rankings.
Existing hypotheses: exact GL classification/unit anchors, but no measured-column reconstruction/error source for ranking.
Premise reduced: derive actual returned coefficient/decoder/evaluation errors from SAME anchor/query measurements and checked inverse.
Models: finite square real response, SUP norm, independently registered latent basis; exact inverse equations are data-side conditions.
Consumers: original Decision.action_gap on SAME allowed actions/evaluation, plus exact regular/noisy and near-singular counterexamples.

This finite R^d SUP-norm model is separate from Euclidean Brownian models.
The true response is G(H x). Registered interventions have H(d_i)=B e_i in
independently fixed units/orientations; arbitrary experimental knobs do not
supply that condition. Each measured column is an actual noisy G(H d_i).
The supplied candidate inverse must satisfy exact equations for the matrix
BUILT FROM those columns. This is an exact checked-data condition, NOT an
implemented invertibility search, floating rank test or statistical certificate.
Singular measurements do not receive an inverse-based conclusion. Query noise
may be nonlinear; the returned encoder is therefore a pointwise reconstruction,
not falsely declared an exact linear factor. The evaluation functional and
bounded domain remain independent registered inputs. No dynamic GOA/control
quotient claim follows without its separate reward/transition interface.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveNoisyOperationalCalibration
open scoped BigOperators
noncomputable section

abbrev Coordinate (d : ℕ) := Fin d → ℝ

def unit {d : ℕ} (i : Fin d) : Coordinate d := fun j => if j=i then 1 else 0

def columns {d : ℕ} (samples : Fin d → Coordinate d) : Coordinate d →L[ℝ] Coordinate d :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (samples i)

@[simp] theorem columns_apply {d : ℕ} (samples : Fin d → Coordinate d) (z : Coordinate d) :
    columns samples z = ∑ i, z i • samples i := by simp [columns]

@[simp] theorem columns_unit {d : ℕ} (samples : Fin d → Coordinate d) (i : Fin d) :
    columns samples (unit i) = samples i := by simp [columns_apply,unit,ite_smul]

private theorem coordinate_decomposition {d : ℕ} (z : Coordinate d) :
    ∑ i, z i • unit i = z := by
  ext j
  simp [unit,Finset.sum_apply,Pi.smul_apply]

@[simp] theorem columns_of_map {d : ℕ} (F : Coordinate d →L[ℝ] Coordinate d) :
    columns (fun i => F (unit i)) = F := by
  ext z
  rw [columns_apply]
  simp_rw [← map_smul]
  rw [← map_sum,coordinate_decomposition]

/-- Operator error is DERIVED from the actual column errors in SUP norm. -/
theorem measured_columns_error {d : ℕ} (F : Coordinate d →L[ℝ] Coordinate d)
    (samples : Fin d → Coordinate d) (delta : ℝ) (hdelta : 0 ≤ delta)
    (herr : ∀ i, ‖samples i-F (unit i)‖ ≤ delta) :
    ‖columns samples-F‖ ≤ (d : ℝ)*delta := by
  have heq : columns samples-F = columns (fun i => samples i-F (unit i)) := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [sub_apply,columns_apply,smul_sub,Finset.sum_sub_distrib]
    have hf : (∑ i, z i • F (unit i)) = F z := by rw [← columns_apply,columns_of_map]
    rw [hf]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg d) hdelta)
  intro z
  rw [heq,columns_apply]
  calc
    _ ≤ ∑ i, ‖z i • (samples i-F (unit i))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin d, ‖z‖*delta := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm z i) (herr i) (norm_nonneg _) (norm_nonneg _)
    _ = ((d : ℝ)*delta)*‖z‖ := by simp; ring

/-- The inverse is an EXACT data-side certificate on the ACTUAL measured
columns, with both equations checked by Lean. No choice/search is claimed. -/
def checkedMeasuredEquiv {d : ℕ} (samples : Fin d → Coordinate d)
    (inverse : Coordinate d →L[ℝ] Coordinate d)
    (left : ∀ z, inverse (columns samples z)=z)
    (right : ∀ y, columns samples (inverse y)=y) : Coordinate d ≃L[ℝ] Coordinate d :=
  { toLinearEquiv :=
      { toLinearMap := (columns samples).toLinearMap
        invFun := inverse
        left_inv := left
        right_inv := right }
    continuous_toFun := (columns samples).continuous
    continuous_invFun := inverse.continuous }

@[simp] theorem checkedMeasuredEquiv_inverse {d : ℕ} (samples : Fin d → Coordinate d)
    (inverse : Coordinate d →L[ℝ] Coordinate d) (left) (right) (y : Coordinate d) :
    (checkedMeasuredEquiv samples inverse left right).symm y = inverse y := rfl

/-- Returned coefficients use the ACTUAL supplied/checked measured inverse,
not the unknown true decoder inverse or another chosen latent representation. -/
def coefficients {d : ℕ} (inverse : Coordinate d →L[ℝ] Coordinate d) (measuredResponse : Coordinate d) : Coordinate d :=
  inverse measuredResponse

def encoderEstimate {d : ℕ} (B : Coordinate d ≃L[ℝ] Coordinate d)
    (inverse : Coordinate d →L[ℝ] Coordinate d) (measuredResponse : Coordinate d) : Coordinate d :=
  B (coefficients inverse measuredResponse)

def decoderEstimate {d : ℕ} (B : Coordinate d ≃L[ℝ] Coordinate d)
    (samples : Fin d → Coordinate d) : Coordinate d →L[ℝ] Coordinate d :=
  (columns samples).comp B.symm.toContinuousLinearMap

/-- Native conditioning bound. The error and inverse refer to the SAME
measured matrix; eta bounds the SAME observed query versus the true response. -/
theorem coefficient_error {d : ℕ} (F : Coordinate d →L[ℝ] Coordinate d)
    (samples : Fin d → Coordinate d) (inverse : Coordinate d →L[ℝ] Coordinate d)
    (left : ∀ z, inverse (columns samples z)=z)
    (delta : ℝ) (hdelta : 0 ≤ delta) (herr : ∀ i, ‖samples i-F (unit i)‖ ≤ delta)
    (alpha measuredResponse : Coordinate d) (eta : ℝ) (hquery : ‖measuredResponse-F alpha‖ ≤ eta) :
    ‖coefficients inverse measuredResponse-alpha‖ ≤ ‖inverse‖*(eta+(d : ℝ)*delta*‖alpha‖) := by
  have hop := measured_columns_error F samples delta hdelta herr
  have hm : ‖F alpha-columns samples alpha‖ ≤ (d : ℝ)*delta*‖alpha‖ := by
    rw [norm_sub_rev]
    exact ((columns samples-F).le_opNorm alpha).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
  have htri : ‖measuredResponse-columns samples alpha‖ ≤ ‖measuredResponse-F alpha‖+‖F alpha-columns samples alpha‖ := by
    simpa only [dist_eq_norm] using (dist_triangle measuredResponse (F alpha) (columns samples alpha))
  have ht := htri.trans (add_le_add hquery hm)
  have heq : coefficients inverse measuredResponse-alpha = inverse (measuredResponse-columns samples alpha) := by
    rw [map_sub,left]
    rfl
  rw [heq]
  exact (inverse.le_opNorm _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))

section Source
variable {d : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable (H : X →L[ℝ] Coordinate d) (G : Coordinate d →L[ℝ] Coordinate d)
variable (B : Coordinate d ≃L[ℝ] Coordinate d) (interventions : Fin d → X)
variable (hcalibrated : ∀ i, H (interventions i)=B (unit i))
variable (samples : Fin d → Coordinate d) (delta : ℝ) (hdelta : 0 ≤ delta)
variable (hanchor : ∀ i, ‖samples i-G (H (interventions i))‖ ≤ delta)
include hcalibrated hdelta hanchor

/-- Actual anchor experiments provide the matrix-error premise. -/
theorem actual_anchor_operator_error :
    ‖columns samples-G.comp B.toContinuousLinearMap‖ ≤ (d : ℝ)*delta :=
  measured_columns_error _ samples delta hdelta (fun i => by simpa [hcalibrated i] using hanchor i)

/-- Noisy decoder reconstruction for the SAME response factorization. -/
theorem actual_decoder_error (z : Coordinate d) :
    ‖decoderEstimate B samples z-G z‖ ≤ (d : ℝ)*delta*‖B.symm.toContinuousLinearMap‖*‖z‖ := by
  have heq : decoderEstimate B samples z-G z =
      (columns samples-G.comp B.toContinuousLinearMap) (B.symm z) := by simp [decoderEstimate]
  rw [heq]
  have h1 := ((columns samples-G.comp B.toContinuousLinearMap).le_opNorm (B.symm z)).trans
    (mul_le_mul_of_nonneg_right (actual_anchor_operator_error H G B interventions hcalibrated samples delta hdelta hanchor) (norm_nonneg _))
  exact h1.trans (by
    have h2 : ‖B.symm z‖ ≤ ‖B.symm.toContinuousLinearMap‖*‖z‖ := by
      simpa using B.symm.toContinuousLinearMap.le_opNorm z
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h2 (mul_nonneg (Nat.cast_nonneg d) hdelta))

/-- Operator-norm decoder reconstruction from the actual same-source anchors. -/
theorem actual_decoder_operator_error :
    ‖decoderEstimate B samples-G‖ ≤ (d : ℝ)*delta*‖B.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  exact actual_decoder_error H G B interventions hcalibrated samples delta hdelta hanchor z

/-- Actual coefficient estimate from the SAME measured query and anchor table. -/
theorem actual_coefficient_error (inverse : Coordinate d →L[ℝ] Coordinate d)
    (left : ∀ z, inverse (columns samples z)=z) (x : X) (measuredResponse : Coordinate d)
    (eta : ℝ) (hquery : ‖measuredResponse-G (H x)‖ ≤ eta) :
    ‖coefficients inverse measuredResponse-B.symm (H x)‖ ≤
      ‖inverse‖*(eta+(d : ℝ)*delta*‖B.symm (H x)‖) := by
  apply coefficient_error (G.comp B.toContinuousLinearMap) samples inverse left delta hdelta
    (fun i => by simpa [hcalibrated i] using hanchor i)
  simpa using hquery

/-- Same returned encoder, with independently registered coordinate units B. -/
theorem actual_encoder_error (inverse : Coordinate d →L[ℝ] Coordinate d)
    (left : ∀ z, inverse (columns samples z)=z) (x : X) (measuredResponse : Coordinate d)
    (eta : ℝ) (hquery : ‖measuredResponse-G (H x)‖ ≤ eta) :
    ‖encoderEstimate B inverse measuredResponse-H x‖ ≤
      ‖B.toContinuousLinearMap‖*‖inverse‖*(eta+(d : ℝ)*delta*‖B.symm (H x)‖) := by
  have heq : encoderEstimate B inverse measuredResponse-H x = B (coefficients inverse measuredResponse-B.symm (H x)) := by
    simp [encoderEstimate]
  rw [heq]
  exact (B.toContinuousLinearMap.le_opNorm _).trans (by
    have h := mul_le_mul_of_nonneg_left
      (actual_coefficient_error H G B interventions hcalibrated samples delta hdelta hanchor inverse left x measuredResponse eta hquery)
      (norm_nonneg B.toContinuousLinearMap)
    simpa only [mul_assoc] using h)

/-- Registered evaluation is applied to the SAME actual returned encoder. -/
theorem actual_evaluation_error (evaluation : Coordinate d →L[ℝ] ℝ)
    (inverse : Coordinate d →L[ℝ] Coordinate d) (left : ∀ z, inverse (columns samples z)=z)
    (x : X) (measuredResponse : Coordinate d) (eta : ℝ) (hquery : ‖measuredResponse-G (H x)‖ ≤ eta) :
    |evaluation (H x)-evaluation (encoderEstimate B inverse measuredResponse)| ≤
      ‖evaluation‖*‖B.toContinuousLinearMap‖*‖inverse‖*(eta+(d : ℝ)*delta*‖B.symm (H x)‖) := by
  have hn : ‖H x-encoderEstimate B inverse measuredResponse‖ ≤
      ‖B.toContinuousLinearMap‖*‖inverse‖*(eta+(d : ℝ)*delta*‖B.symm (H x)‖) := by
    rw [norm_sub_rev]
    exact actual_encoder_error H G B interventions hcalibrated samples delta hdelta hanchor inverse left x measuredResponse eta hquery
  calc
    _ = ‖evaluation (H x-encoderEstimate B inverse measuredResponse)‖ := by rw [map_sub,Real.norm_eq_abs]
    _ ≤ ‖evaluation‖*‖H x-encoderEstimate B inverse measuredResponse‖ := evaluation.le_opNorm _
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hn (norm_nonneg evaluation)

/-- SAME allowed action class and SAME actual data/factors. The original
Decision.action_gap receives a DERIVED evaluation error; only the observable
estimated gap and registered bounded domain remain independent conditions.
This is one-decision ranking, not a dynamic GOA/MDP theorem. -/
theorem actual_action_gap {Act : Type*} (inputs : Act → X) (measuredResponse : Act → Coordinate d)
    (evaluation : Coordinate d →L[ℝ] ℝ) (inverse : Coordinate d →L[ℝ] Coordinate d)
    (left : ∀ z, inverse (columns samples z)=z) (eta R : ℝ)
    (hquery : ∀ a, ‖measuredResponse a-G (H (inputs a))‖ ≤ eta)
    (hdomain : ∀ a, ‖B.symm (H (inputs a))‖ ≤ R) (chosen : Act)
    (hgap : ∀ a, a ≠ chosen →
      2*(‖evaluation‖*‖B.toContinuousLinearMap‖*‖inverse‖*(eta+(d : ℝ)*delta*R)) <
        evaluation (encoderEstimate B inverse (measuredResponse chosen))-
        evaluation (encoderEstimate B inverse (measuredResponse a))) :
    ∀ a, a ≠ chosen → evaluation (H (inputs a)) < evaluation (H (inputs chosen)) := by
  apply UEOT.V3.Decision.action_gap (fun a => evaluation (H (inputs a)))
    (fun a => evaluation (encoderEstimate B inverse (measuredResponse a)))
    (‖evaluation‖*‖B.toContinuousLinearMap‖*‖inverse‖*(eta+(d : ℝ)*delta*R)) chosen _ hgap
  intro a
  apply (actual_evaluation_error H G B interventions hcalibrated samples delta hdelta hanchor evaluation inverse left
    (inputs a) (measuredResponse a) eta (hquery a)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (le_refl eta)
    (mul_le_mul_of_nonneg_left (hdomain a) (mul_nonneg (Nat.cast_nonneg d) hdelta))

end Source


@[simp] theorem norm_unit {d : ℕ} (i : Fin d) : ‖unit i‖ = 1 := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    by_cases h : j=i <;> simp [unit,h]
  · simpa [unit] using norm_le_pi_norm (unit i) i

/-- Native finite diagonal operator used for exact data/inverse fixtures. -/
def diagonal {d : ℕ} (c : Fin d → ℝ) : Coordinate d →L[ℝ] Coordinate d :=
  columns (fun i => c i • unit i)

@[simp] theorem diagonal_apply {d : ℕ} (c : Fin d → ℝ) (z : Coordinate d) (j : Fin d) :
    diagonal c z j = c j*z j := by
  simp [diagonal,columns_apply,unit,Finset.sum_apply,Pi.smul_apply,mul_ite,mul_comm]

@[simp] theorem diagonal_unit {d : ℕ} (c : Fin d → ℝ) (i : Fin d) : diagonal c (unit i)=c i • unit i :=
  columns_unit _ _

theorem diagonal_norm_le {d : ℕ} (c : Fin d → ℝ) (K : ℝ) (hK : 0 ≤ K) (hc : ∀ i, |c i| ≤ K) :
    ‖diagonal c‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro z
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hK (norm_nonneg z))).mpr
  intro i
  rw [diagonal_apply,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul (hc i) (norm_le_pi_norm z i) (abs_nonneg _) hK


theorem unit_two_registered (i : Fin 2) : (unit i : Coordinate 2)=driveUnitAxis i := rfl

def regularBasis : Coordinate 2 ≃L[ℝ] Coordinate 2 := ContinuousLinearEquiv.refl ℝ _
def regularEncoder : Coordinate 2 →L[ℝ] Coordinate 2 := ContinuousLinearMap.id ℝ _
def regularDecoder : Coordinate 2 →L[ℝ] Coordinate 2 := diagonal (fun _ => 2)
def regularMeasured : Coordinate 2 →L[ℝ] Coordinate 2 := diagonal (fun i => if i=0 then 2 else 21/10)
def regularSamples (i : Fin 2) : Coordinate 2 := regularMeasured (unit i)
def regularInverse : Coordinate 2 →L[ℝ] Coordinate 2 := diagonal (fun i => if i=0 then 1/2 else 10/21)
def regularEvaluation : Coordinate 2 →L[ℝ] ℝ := ContinuousLinearMap.proj 1

theorem regular_left (z : Coordinate 2) : regularInverse (columns regularSamples z)=z := by
  change regularInverse (columns (fun i => regularMeasured (unit i)) z)=z
  rw [columns_of_map]
  ext i
  fin_cases i <;> norm_num [regularInverse,regularMeasured,diagonal_apply] <;> ring

theorem regular_right (z : Coordinate 2) : columns regularSamples (regularInverse z)=z := by
  change columns (fun i => regularMeasured (unit i)) (regularInverse z)=z
  rw [columns_of_map]
  ext i
  fin_cases i <;> norm_num [regularInverse,regularMeasured,diagonal_apply] <;> ring

/-- Literal exact two-sided inverse for the nontrivial NOISY measured columns. -/
def regularChecked : Coordinate 2 ≃L[ℝ] Coordinate 2 :=
  checkedMeasuredEquiv regularSamples regularInverse regular_left regular_right

theorem regular_anchor_error (i : Fin 2) :
    ‖regularSamples i-regularDecoder (regularEncoder (unit i))‖ ≤ (1/10 : ℝ) := by
  change ‖regularMeasured (unit i)-regularDecoder (unit i)‖ ≤ (1/10 : ℝ)
  rw [regularMeasured,regularDecoder,diagonal_unit,diagonal_unit,← sub_smul,norm_smul,norm_unit,mul_one,Real.norm_eq_abs]
  fin_cases i <;> norm_num

theorem regular_inverse_norm_le : ‖regularInverse‖ ≤ (1/2 : ℝ) :=
  diagonal_norm_le _ _ (by norm_num) (by intro i; fin_cases i <;> norm_num)

private theorem identity_norm_le (d : ℕ) : ‖(ContinuousLinearMap.id ℝ (Coordinate d))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simp

private theorem projection_norm_le {d : ℕ} (i : Fin d) :
    ‖(ContinuousLinearMap.proj i : Coordinate d →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa using norm_le_pi_norm z i

/-- The true regular source is literally the previously verified nonzero
axis gauge; nondegeneracy is checked, not inferred from a numerical rank. -/
def regularTrueEquiv : Coordinate 2 ≃L[ℝ] Coordinate 2 :=
  (driveAxisScaling (fun _ => 2) (by intro i; norm_num)).toContinuousLinearEquiv

theorem regular_decoder_eq_true_equiv : regularDecoder=regularTrueEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  ext i
  simp [regularDecoder,regularTrueEquiv,diagonal_apply,driveAxisScaling]

theorem regular_true_nondegenerate : Function.Bijective regularDecoder := by
  rw [regular_decoder_eq_true_equiv]
  simpa using regularTrueEquiv.bijective

/-- Same allowed Bool actions: 0 and the second independently registered unit.
Query responses are measured from SAME decoder; only anchor1 is noisy. -/
def regularInputs (a : Bool) : Coordinate 2 := if a then unit 1 else 0
def regularQueries (a : Bool) : Coordinate 2 := regularDecoder (regularEncoder (regularInputs a))

private theorem regular_domain (a : Bool) : ‖regularBasis.symm (regularEncoder (regularInputs a))‖ ≤ 1 := by
  cases a <;> simp [regularBasis,regularEncoder,regularInputs]

private theorem regular_radius_le :
    ‖regularEvaluation‖*‖regularBasis.toContinuousLinearMap‖*‖regularInverse‖*
      (0+(2 : ℝ)*(1/10)*1) ≤ (1/10 : ℝ) := by
  have he : ‖regularEvaluation‖ ≤ 1 := projection_norm_le _
  have hb : ‖regularBasis.toContinuousLinearMap‖ ≤ 1 := identity_norm_le 2
  calc
    _ ≤ 1*1*(1/2)*(0+(2 : ℝ)*(1/10)*1) := by
      gcongr
      exact regular_inverse_norm_le
    _ = _ := by norm_num

/-- Original Decision.action_gap is ACTUALLY consumed: the returned noisy
reconstruction's measured gap certifies the true ranking of SAME actions. -/
theorem regular_noisy_action_ranking :
    ∀ a : Bool, a ≠ true → regularEvaluation (regularEncoder (regularInputs a)) <
      regularEvaluation (regularEncoder (regularInputs true)) := by
  apply actual_action_gap regularEncoder regularDecoder regularBasis (@unit 2)
    (fun _ => rfl) regularSamples (1/10) (by norm_num) regular_anchor_error
    regularInputs regularQueries regularEvaluation regularInverse regular_left 0 1
    (fun _ => by simp [regularQueries]) regular_domain true
  intro a ha
  cases a
  · have hscore : regularEvaluation (encoderEstimate regularBasis regularInverse (regularQueries true))-
        regularEvaluation (encoderEstimate regularBasis regularInverse (regularQueries false)) = 20/21 := by
      norm_num [regularEvaluation,encoderEstimate,coefficients,regularBasis,regularInverse,regularQueries,
        regularDecoder,regularEncoder,regularInputs,diagonal_apply,unit]
    rw [hscore]
    linarith [regular_radius_le]
  · simp at ha

/-- A fully nondegenerate family whose exact anchor operator becomes
arbitrarily ill-conditioned, despite exact independent unit calibration. -/
def nearDecoder (t : ℝ) : Coordinate 2 →L[ℝ] Coordinate 2 := diagonal (fun i => if i=0 then 1 else t)
def nearSamples (t : ℝ) (i : Fin 2) : Coordinate 2 := nearDecoder t (unit i)
def nearInverse (t : ℝ) : Coordinate 2 →L[ℝ] Coordinate 2 := diagonal (fun i => if i=0 then 1 else t⁻¹)

theorem near_left (t : ℝ) (ht : 0 < t) (z : Coordinate 2) : nearInverse t (columns (nearSamples t) z)=z := by
  change nearInverse t (columns (fun i => nearDecoder t (unit i)) z)=z
  rw [columns_of_map]
  ext i
  fin_cases i <;> simp [nearInverse,nearDecoder,diagonal_apply,ne_of_gt ht]

theorem near_right (t : ℝ) (ht : 0 < t) (z : Coordinate 2) : columns (nearSamples t) (nearInverse t z)=z := by
  change columns (fun i => nearDecoder t (unit i)) (nearInverse t z)=z
  rw [columns_of_map]
  ext i
  fin_cases i <;> simp [nearInverse,nearDecoder,diagonal_apply,ne_of_gt ht]

def nearChecked (t : ℝ) (ht : 0 < t) : Coordinate 2 ≃L[ℝ] Coordinate 2 :=
  checkedMeasuredEquiv (nearSamples t) (nearInverse t) (near_left t ht) (near_right t ht)

/-- This counterexample satisfies the SAME anchor measurement contract with
ZERO anchor error; its candidate inverse has BOTH exact data-side equations. -/
theorem near_exact_anchor_contract (t : ℝ) (i : Fin 2) :
    ‖nearSamples t i-nearDecoder t (regularEncoder (unit i))‖ ≤ (0 : ℝ) := by
  simp [nearSamples,regularEncoder]

/-- True query coefficient=0, noisy query=t*unit1, returned coefficient=unit1.
Arbitrarily small measurement noise has FIXED reconstruction error one. -/
theorem near_actual_query_contract (t : ℝ) (ht : 0 < t) :
    ‖nearDecoder t (unit 1)-nearDecoder t (0 : Coordinate 2)‖ = t ∧
    ‖coefficients (nearInverse t) (nearDecoder t (unit 1))-(0 : Coordinate 2)‖ = 1 := by
  have hreturn : coefficients (nearInverse t) (nearDecoder t (unit 1)) = unit 1 := by
    have h := near_left t ht (unit 1)
    change nearInverse t (columns (fun i => nearDecoder t (unit i)) (unit 1))=unit 1 at h
    rw [columns_of_map] at h
    exact h
  rw [hreturn]
  simp [nearDecoder,diagonal_unit,norm_smul,Real.norm_eq_abs,abs_of_pos ht]

/-- The SAME general source error theorem consumes the near-singular data.
Thus its required inverse-conditioning factor really diverges as t shrinks. -/
theorem near_required_conditioning (t : ℝ) (ht : 0 < t) : 1 ≤ ‖nearInverse t‖*t := by
  have hquery : ‖nearDecoder t (unit 1)-nearDecoder t (regularEncoder (0 : Coordinate 2))‖ ≤ t := by
    simpa [regularEncoder] using le_of_eq (near_actual_query_contract t ht).1
  have h := actual_coefficient_error regularEncoder (nearDecoder t) regularBasis (@unit 2)
    (fun _ => rfl) (nearSamples t) 0 (le_refl 0) (near_exact_anchor_contract t)
    (nearInverse t) (near_left t ht) 0 (nearDecoder t (unit 1)) t hquery
  have he : ‖coefficients (nearInverse t) (nearDecoder t (unit 1))-(0 : Coordinate 2)‖=1 :=
    (near_actual_query_contract t ht).2
  have he' : ‖coefficients (nearInverse t) (nearDecoder t (unit 1))‖=1 := by simpa using he
  simpa [regularBasis,regularEncoder,he'] using h

/-- No condition-free uniform Lipschitz claim is possible, even for this
nondegenerate linear family with exact anchors and literal verified inverses. -/
theorem no_uniform_condition_free_reconstruction :
    ¬ ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 < t →
      ‖coefficients (nearInverse t) (nearDecoder t (unit 1))-(0 : Coordinate 2)‖ ≤
        K*‖nearDecoder t (unit 1)-nearDecoder t (0 : Coordinate 2)‖ := by
  rintro ⟨K,hK,h⟩
  have hp : 0 < K+1 := by linarith
  have ht : 0 < (K+1)⁻¹ := inv_pos.mpr hp
  have hb := h (K+1)⁻¹ ht
  rw [(near_actual_query_contract _ ht).1,(near_actual_query_contract _ ht).2] at hb
  have hi : (K+1)*(K+1)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hp)
  nlinarith [inv_pos.mpr hp]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveNoisyOperationalCalibration
