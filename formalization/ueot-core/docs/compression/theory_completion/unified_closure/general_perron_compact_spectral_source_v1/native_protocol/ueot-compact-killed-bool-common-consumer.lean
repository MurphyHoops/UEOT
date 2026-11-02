import UEOT
import «ueot-compact-killed-bool-fixture»
import «ueot-compact-killed-bool-kernel»

open MeasureTheory ProbabilityTheory Filter
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactKilledSpectralBinding
open UEOT.V3.ReversibleKilledSpectralQSD
open scoped ENNReal NNReal
noncomputable section
namespace CompactKilledBoolCommon
local instance : MeasurableSpace Bool := ⊤

lemma same_reference : CompactKilledBoolAuthor.m=CompactKilledBoolKernel.m := rfl
lemma same_evolved_density (t:NNReal) : (fun b => CompactKilledBoolAuthor.S t CompactKilledBoolAuthor.g b)=CompactKilledBoolKernel.density t := by
  funext b
  rw [CompactKilledBoolAuthor.evolved_apply]
  rfl
lemma same_actual_initial : (CompactKilledBoolKernel.semigroup.initial : Measure Bool)=
    CompactKilledBoolAuthor.m.withDensity (fun x=>ENNReal.ofReal (CompactKilledBoolAuthor.g x)) := by
  change CompactKilledBoolKernel.initialMeasure=_
  rw [CompactKilledBoolKernel.initial_eq_density]
  congr 1
  funext x
  rw [CompactKilledBoolAuthor.g_apply]
lemma same_actual_evolved (t:NNReal) : CompactKilledBoolKernel.semigroup.evolved t=
    CompactKilledBoolAuthor.m.withDensity (fun x=>ENNReal.ofReal (CompactKilledBoolAuthor.S t CompactKilledBoolAuthor.g x)) := by
  rw [CompactKilledBoolKernel.evolved_eq_density]
  congr 1
  funext x
  rw [CompactKilledBoolAuthor.evolved_apply]
  rfl

def actualCertificate : SpectralData CompactKilledBoolAuthor.m :=
  ofActualSource CompactKilledBoolKernel.semigroup CompactKilledBoolAuthor.g CompactKilledBoolAuthor.phi CompactKilledBoolAuthor.g_nonneg CompactKilledBoolAuthor.g_mass CompactKilledBoolAuthor.phi_positive CompactKilledBoolAuthor.phi_norm
    CompactKilledBoolAuthor.R CompactKilledBoolAuthor.compactR CompactKilledBoolAuthor.symmetricR CompactKilledBoolAuthor.S CompactKilledBoolAuthor.actual_generator CompactKilledBoolAuthor.actual_contraction
    CompactKilledBoolAuthor.actual_evolved_nonneg same_actual_initial same_actual_evolved 1 2
    (by norm_num) (by norm_num) CompactKilledBoolAuthor.R_principal CompactKilledBoolAuthor.orthogonal_rayleigh CompactKilledBoolAuthor.actual_second_mode

lemma actual_killed_identity : actualCertificate.killed=CompactKilledBoolKernel.semigroup := rfl
lemma computed_principal_coefficient : actualCertificate.a1=1 := CompactKilledBoolAuthor.actual_a1
lemma computed_nonzero_residual : actualCertificate.residualL2=1/2 := CompactKilledBoolAuthor.residual_norm
lemma actual_generated_expansion (t:NNReal) :
    actualCertificate.evolvedDensity t =ᵐ[CompactKilledBoolAuthor.m] fun x =>
      Real.exp (-(t:ℝ))*CompactKilledBoolAuthor.phi x+actualCertificate.remainder t x := by
  have he := actualCertificate.spectral_expansion t
  simpa only [show actualCertificate.lambda1=1 from rfl,neg_one_mul,
    computed_principal_coefficient,mul_one,show actualCertificate.phi1=(CompactKilledBoolAuthor.phi : Bool→ℝ) from rfl] using he
lemma actual_generated_remainder_bound (t:NNReal) :
    (∫ x,actualCertificate.remainder t x^2 ∂CompactKilledBoolAuthor.m)^(1/(2:ℝ)) ≤
      Real.exp (-2*(t:ℝ))*(1/2:ℝ) := by
  simpa only [show actualCertificate.lambda2=2 from rfl,computed_nonzero_residual]
    using actualCertificate.remainder_l2_le t
lemma actual_remainder_bound_attained (t:NNReal) :
    (∫ x,actualCertificate.remainder t x^2 ∂CompactKilledBoolAuthor.m)^(1/(2:ℝ)) =
      Real.exp (-2*(t:ℝ))*(1/2:ℝ) := by
  change (∫ x,CompactKilledBoolAuthor.S t (residual CompactKilledBoolAuthor.g CompactKilledBoolAuthor.phi) x^2 ∂CompactKilledBoolAuthor.m)^(1/(2:ℝ))=_
  rw [←lp_norm_eq_integral_sq,CompactKilledBoolAuthor.actual_remainder_norm]

lemma actual_q_uniform : (actualCertificate.q : Measure Bool)=CompactKilledBoolKernel.m := by
  rw [actualCertificate.q_toMeasure]
  have hi : actualCertificate.phiMass=1 := by
    change (∫ x,CompactKilledBoolAuthor.phi x ∂CompactKilledBoolAuthor.m)=1
    rw [CompactKilledBoolAuthor.integral_formula]
    norm_num [CompactKilledBoolAuthor.phi_apply]
  rw [hi]
  simp only [show actualCertificate.phi1=(CompactKilledBoolAuthor.phi : Bool→ℝ) from rfl,CompactKilledBoolAuthor.phi_apply,div_one,
    ENNReal.ofReal_one]
  simp [same_reference]

/-- Genuine nonzero two-mode actual source consumes the ORIGINAL theorem. -/
theorem original_p_qsd_04_same_source :
    ∃ (Cg cg:ℝ) (t0:NNReal), 0<Cg ∧ 0<cg ∧
      (∀ t:NNReal,t0≤t → UEOT.V3.TotalVariation.tvDist
        (CompactKilledBoolKernel.semigroup.conditioned t : Measure Bool) CompactKilledBoolKernel.m ≤ Cg*Real.exp (-(t:ℝ))) ∧
      (∀ t:NNReal,t0≤t → (CompactKilledBoolKernel.semigroup.survival t).toReal ≥ cg*Real.exp (-(t:ℝ))) := by
  obtain ⟨Cg,cg,t0,hCg,hcg,hq,htv,hsurv⟩ := SpectralData.p_qsd_04 actualCertificate
  refine ⟨Cg,cg,t0,hCg,hcg,?_,?_⟩
  · intro t ht
    have he := htv t ht
    rw [conditioned_eq_actual,actual_q_uniform] at he
    rw [actual_killed_identity] at he
    simpa only [show actualCertificate.lambda1=1 from rfl,
      show actualCertificate.lambda2=2 from rfl,show -(2-(1:ℝ)) = -1 by norm_num,neg_one_mul] using he
  · intro t ht
    simpa only [actual_killed_identity,show actualCertificate.lambda1=1 from rfl,neg_one_mul]
      using hsurv t ht

-- Same real law has strictly nonzero transient error and nonzero second mode.
lemma actual_finite_time_tv_positive (t:NNReal) :
    0<UEOT.V3.TotalVariation.tvDist (CompactKilledBoolKernel.semigroup.conditioned t : Measure Bool) CompactKilledBoolKernel.m :=
  CompactKilledBoolKernel.conditioned_tv_positive t
lemma actual_second_mode_nonzero (t:NNReal) : 0<CompactKilledBoolKernel.density t false-CompactKilledBoolKernel.density t true := by
  rw [CompactKilledBoolKernel.evolved_second_mode_nonzero]
  exact CompactKilledBoolKernel.f_pos t

#print axioms actualCertificate
#print axioms actual_generated_expansion
#print axioms actual_generated_remainder_bound
#print axioms actual_remainder_bound_attained
#print axioms original_p_qsd_04_same_source
#print axioms actual_finite_time_tv_positive
end CompactKilledBoolCommon
