import UEOT.V3.QSDTVLimit
import UEOT.V3.InformationKernelTV
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# P-QSD-04 — reversible killed diffusion spectral QSD bound

Frozen Core v3 §10.4 assumes a killed generator which is self-adjoint with
compact resolvent on finite-measure `L²(m)`, with positive principal mode
`φ₁` and strict gap `0 < λ₁ < λ₂`.  Appendix C explicitly licenses the
self-adjoint compact-resolvent spectral decomposition as standard mathematics.

This module keeps an actual compact symmetric resolvent witness on
`Lp ℝ 2 m`, ties `λ₁, λ₂` to the principal/orthogonal resolvent spectral
bounds, and records the standard semigroup spectral expansion
`P_t^D g = exp(-λ₁ t) a₁ φ₁ + R_t` with its L² remainder estimate.
It does **not** assume the source conclusions.  Cauchy--Schwarz,
large-time survival positivity, normalization, and the TV estimate are proved
below.

The source theorem is `p_qsd_04`.
-/

namespace UEOT.V3.ReversibleKilledSpectralQSD

set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open UEOT.V3.TotalVariation
open UEOT.V3.InformationKernelTV
open scoped ENNReal Topology

universe uX

variable {X : Type uX} [MeasurableSpace X]

/-- Build a probability measure from a nonnegative real density of mass one. -/
noncomputable def probabilityWithDensity
    (m : Measure X) (f : X → ℝ)
    (hf : Integrable f m) (hnn : 0 ≤ᵐ[m] f)
    (hmass : ∫ x, f x ∂m = 1) : ProbabilityMeasure X := by
  let ν : Measure X := m.withDensity (fun x => ENNReal.ofReal (f x))
  have hprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hf hnn, hmass]
    simp
  exact ⟨ν, hprob⟩

@[simp] theorem probabilityWithDensity_toMeasure
    (m : Measure X) (f : X → ℝ)
    (hf : Integrable f m) (hnn : 0 ≤ᵐ[m] f)
    (hmass : ∫ x, f x ∂m = 1) :
    (probabilityWithDensity m f hf hnn hmass : Measure X) =
      m.withDensity (fun x => ENNReal.ofReal (f x)) := rfl

/-- Positive-mass normalization of a real density. -/
noncomputable def normalizedDensity (f : X → ℝ) (mass : ℝ) : X → ℝ :=
  fun x => f x / mass

lemma normalizedDensity_integrable
    {m : Measure X} (f : X → ℝ) (mass : ℝ) (hf : Integrable f m) :
    Integrable (normalizedDensity f mass) m := by
  unfold normalizedDensity
  simpa [div_eq_mul_inv, mul_comm] using hf.const_mul mass⁻¹

lemma normalizedDensity_nonneg
    {m : Measure X} (f : X → ℝ) (mass : ℝ) (hmass : 0 < mass)
    (hf : 0 ≤ᵐ[m] f) :
    0 ≤ᵐ[m] normalizedDensity f mass := by
  filter_upwards [hf] with x hx
  exact div_nonneg hx hmass.le

lemma normalizedDensity_integral_one
    {m : Measure X} (f : X → ℝ) (mass : ℝ)
    (hmass : 0 < mass) (hmass_eq : ∫ x, f x ∂m = mass) :
    ∫ x, normalizedDensity f mass x ∂m = 1 := by
  unfold normalizedDensity
  rw [show (fun x => f x / mass) = fun x => mass⁻¹ * f x by
    funext x
    field_simp]
  rw [integral_const_mul, hmass_eq]
  field_simp

/-- Common-base density TV is bounded by the L¹ distance of the real
probability densities. -/
theorem tvDist_probabilityWithDensity_le_integral_abs
    (m : Measure X) (p q : X → ℝ)
    (hp : Integrable p m) (hq : Integrable q m)
    (hpnn : 0 ≤ᵐ[m] p) (hqnn : 0 ≤ᵐ[m] q)
    (hpmass : ∫ x, p x ∂m = 1) (hqmass : ∫ x, q x ∂m = 1)
    (hpmeas : Measurable p) (hqmeas : Measurable q) :
    tvDist
        (probabilityWithDensity m p hp hpnn hpmass : Measure X)
        (probabilityWithDensity m q hq hqnn hqmass : Measure X)
      ≤ ∫ x, |p x - q x| ∂m := by
  let P := probabilityWithDensity m p hp hpnn hpmass
  let Q := probabilityWithDensity m q hq hqnn hqmass
  change tvDist (P : Measure X) (Q : Measure X) ≤ _
  have hP : (P : Measure X) =
      m.withDensity (fun x => ENNReal.ofReal (p x)) := rfl
  have hQ : (Q : Measure X) =
      m.withDensity (fun x => ENNReal.ofReal (q x)) := rfl
  letI hpProb : IsProbabilityMeasure
      (m.withDensity (fun x => ENNReal.ofReal (p x))) := by
    rw [← hP]
    infer_instance
  letI hqProb : IsProbabilityMeasure
      (m.withDensity (fun x => ENNReal.ofReal (q x))) := by
    rw [← hQ]
    infer_instance
  have htv := tvDist_withDensity_eq_toReal_lintegral_tsub
    m hpmeas.ennreal_ofReal hqmeas.ennreal_ofReal
  rw [hP, hQ, htv]
  have hpoint : ∀ᵐ x ∂m,
      ENNReal.ofReal (p x) - ENNReal.ofReal (q x) ≤
        ENNReal.ofReal |p x - q x| := by
    filter_upwards [hqnn] with x hqx
    rw [← ENNReal.ofReal_sub (p x) hqx]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hlin :
      ∫⁻ x, ENNReal.ofReal (p x) - ENNReal.ofReal (q x) ∂m ≤
        ∫⁻ x, ENNReal.ofReal |p x - q x| ∂m :=
    lintegral_mono_ae hpoint
  have habsint : Integrable (fun x => |p x - q x|) m :=
    (hp.sub hq).abs
  have hlin_top : (∫⁻ x, ENNReal.ofReal |p x - q x| ∂m) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal habsint
      (Filter.Eventually.of_forall fun x => abs_nonneg _)]
    exact ENNReal.ofReal_ne_top
  calc
    (∫⁻ x, ENNReal.ofReal (p x) - ENNReal.ofReal (q x) ∂m).toReal
        ≤ (∫⁻ x, ENNReal.ofReal |p x - q x| ∂m).toReal :=
      ENNReal.toReal_mono hlin_top hlin
    _ = ∫ x, |p x - q x| ∂m := by
      have hEq := ofReal_integral_eq_lintegral_ofReal habsint
        (Filter.Eventually.of_forall fun x => abs_nonneg (p x - q x))
      rw [← hEq, ENNReal.toReal_ofReal]
      exact integral_nonneg fun x => abs_nonneg _

/-- Finite-measure Cauchy--Schwarz, in the exact form needed to turn the
spectral L² remainder into an L¹ remainder. -/
lemma l1_le_l2_rpow
    {m : Measure X} [IsFiniteMeasure m]
    (f : X → ℝ) (hf : AEStronglyMeasurable f m)
    (hfsq : Integrable (fun x => f x ^ 2) m) :
    ∫ x, |f x| ∂m ≤
      (∫ x, f x ^ 2 ∂m) ^ (1 / (2 : ℝ)) *
        (m.real Set.univ) ^ (1 / (2 : ℝ)) := by
  have hfL2 : MemLp f (ENNReal.ofReal 2) m := by
    simpa using (memLp_two_iff_integrable_sq hf).2 hfsq
  have h1L2 : MemLp (fun _ : X => (1 : ℝ))
      (ENNReal.ofReal 2) m := memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq
    (μ := m) Real.HolderConjugate.two_two hfL2 h1L2
  simpa [Real.norm_eq_abs] using h

/-- Normalize a principal term plus a signed remainder.  The normalized L¹
error is controlled by twice the remainder L¹ mass divided by total mass. -/
lemma normalized_l1_le_two_remainder_div
    {m : Measure X}
    (f phi r : X → ℝ) (c S M : ℝ)
    (hf : Integrable f m) (hphi : Integrable phi m) (hr : Integrable r m)
    (hphi_nn : 0 ≤ᵐ[m] phi)
    (hM : 0 < M) (hS : 0 < S)
    (hM_eq : ∫ x, phi x ∂m = M)
    (hS_eq : ∫ x, f x ∂m = S)
    (hexp : f =ᵐ[m] fun x => c * phi x + r x) :
    ∫ x, |f x / S - phi x / M| ∂m ≤
      2 * (∫ x, |r x| ∂m) / S := by
  let R : ℝ := ∫ x, r x ∂m
  have hmass : S = c * M + R := by
    rw [← hS_eq, integral_congr_ae hexp]
    rw [integral_add (hphi.const_mul c) hr, integral_const_mul, hM_eq]
  have hdiff : ∀ᵐ x ∂m,
      f x / S - phi x / M =
        r x / S - phi x * R / (M * S) := by
    filter_upwards [hexp] with x hx
    rw [hx]
    field_simp [ne_of_gt hM, ne_of_gt hS]
    rw [hmass]
    ring
  have hpoint : ∀ᵐ x ∂m,
      |f x / S - phi x / M| ≤
        |r x| / S + phi x * |R| / (M * S) := by
    filter_upwards [hdiff, hphi_nn] with x hdx hpx
    rw [hdx]
    calc
      |r x / S - phi x * R / (M * S)|
          ≤ |r x / S| + |phi x * R / (M * S)| := abs_sub _ _
      _ = |r x| / S + phi x * |R| / (M * S) := by
        rw [abs_div, abs_of_pos hS, abs_div, abs_mul, abs_mul,
          abs_of_nonneg hpx, abs_of_pos hM, abs_of_pos hS]
  have hleft_int : Integrable (fun x => |f x / S - phi x / M|) m := by
    exact ((hf.const_mul S⁻¹).sub (hphi.const_mul M⁻¹)).abs.congr
      (Filter.Eventually.of_forall fun x => by
        simp [div_eq_mul_inv, mul_comm])
  have hright_int : Integrable
      (fun x => |r x| / S + phi x * |R| / (M * S)) m := by
    apply Integrable.add
    · exact hr.abs.const_mul S⁻¹ |>.congr
        (Filter.Eventually.of_forall fun x => by simp [div_eq_mul_inv, mul_comm])
    · exact hphi.const_mul (|R| / (M * S)) |>.congr
        (Filter.Eventually.of_forall fun x => by ring)
  have hint := integral_mono_ae hleft_int hright_int hpoint
  calc
    ∫ x, |f x / S - phi x / M| ∂m
        ≤ ∫ x, (|r x| / S + phi x * |R| / (M * S)) ∂m := hint
    _ = (∫ x, |r x| ∂m) / S + |R| / S := by
      rw [integral_add]
      · rw [show (fun x => |r x| / S) = fun x => S⁻¹ * |r x| by
          funext x
          field_simp]
        rw [integral_const_mul]
        rw [show (fun x => phi x * |R| / (M * S)) =
            fun x => (|R| / (M * S)) * phi x by
          funext x
          ring]
        rw [integral_const_mul, hM_eq]
        field_simp [ne_of_gt hM, ne_of_gt hS]
      · exact hr.abs.const_mul S⁻¹ |>.congr
          (Filter.Eventually.of_forall fun x => by simp [div_eq_mul_inv, mul_comm])
      · exact hphi.const_mul (|R| / (M * S)) |>.congr
          (Filter.Eventually.of_forall fun x => by ring)
    _ ≤ 2 * (∫ x, |r x| ∂m) / S := by
      have hR : |R| ≤ ∫ x, |r x| ∂m := by
        simpa [R, Real.norm_eq_abs] using (norm_integral_le_integral_norm r)
      field_simp [ne_of_gt hS]
      nlinarith

lemma exp_neg_gap_nnreal_eventually_le
    (gap eps : ℝ) (hgap : 0 < gap) (heps : 0 < eps) :
    ∃ t0 : NNReal, ∀ t : NNReal, t0 ≤ t →
      Real.exp (-gap * (t : ℝ)) ≤ eps := by
  have hcoe : Tendsto (fun t : NNReal => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hmul : Tendsto (fun t : NNReal => gap * (t : ℝ)) atTop atTop :=
    hcoe.const_mul_atTop hgap
  have hlim : Tendsto (fun t : NNReal => Real.exp (-(gap * (t : ℝ))))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have hev : ∀ᶠ t : NNReal in atTop,
      Real.exp (-(gap * (t : ℝ))) < eps :=
    (tendsto_order.1 hlim).2 eps heps
  rcases (eventually_atTop.1 hev) with ⟨t0, ht0⟩
  refine ⟨t0, ?_⟩
  intro t htt
  simpa [neg_mul] using (ht0 t htt).le

/-- The source's reversible killed-diffusion spectral package.

The `resolvent` is a concrete bounded resolvent operator on `L²(m)`.  Its
compactness and symmetry encode the self-adjoint compact-resolvent hypothesis.
The principal relation and orthogonal Rayleigh bound tie `λ₁, λ₂` to that
operator.  The semigroup expansion and L² remainder estimate are the standard
spectral-decomposition result explicitly licensed by frozen Appendix C. -/
structure SpectralData (m : Measure X) [IsFiniteMeasure m] where
  resolvent : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m
  resolvent_compact : IsCompactOperator resolvent
  resolvent_symmetric :
    (resolvent : Lp ℝ 2 m →ₗ[ℝ] Lp ℝ 2 m).IsSymmetric

  g : X → ℝ
  phi1 : X → ℝ
  evolvedDensity : NNReal → X → ℝ
  remainder : NNReal → X → ℝ

  lambda1 : ℝ
  lambda2 : ℝ
  a1 : ℝ
  residualL2 : ℝ

  lambda1_pos : 0 < lambda1
  spectral_gap_pos : 0 < lambda2 - lambda1
  a1_pos : 0 < a1
  residualL2_nonneg : 0 ≤ residualL2

  g_measurable : Measurable g
  phi1_measurable : Measurable phi1
  evolved_measurable : ∀ t, Measurable (evolvedDensity t)
  remainder_measurable : ∀ t, Measurable (remainder t)

  remainder_sq_integrable : ∀ t, Integrable (fun x => remainder t x ^ 2) m

  g_memLp2 : MemLp g 2 m
  phi1_memLp2 : MemLp phi1 2 m
  phi1_l2_norm_one : ‖phi1_memLp2.toLp phi1‖ = 1

  g_nonneg : 0 ≤ᵐ[m] g
  phi1_pos : ∀ᵐ x ∂m, 0 < phi1 x
  phi1_nonneg : 0 ≤ᵐ[m] phi1
  evolved_nonneg : ∀ t, 0 ≤ᵐ[m] evolvedDensity t

  g_mass_one : ∫ x, g x ∂m = 1
  phi1_mass_pos : 0 < ∫ x, phi1 x ∂m
  a1_eq_inner : a1 = ∫ x, g x * phi1 x ∂m

  /-- We fix the bounded resolvent to be `(I - L_D)⁻¹`, so a generator
  eigenvalue `-λ₁` becomes the resolvent eigenvalue `(1+λ₁)⁻¹`. -/
  resolvent_principal :
    resolvent (phi1_memLp2.toLp phi1) =
      (1 / (1 + lambda1)) • (phi1_memLp2.toLp phi1)

  /-- The nonprincipal resolvent spectral bound corresponding to generator
  eigenvalues at least `λ₂`. -/
  resolvent_orthogonal_le :
    ∀ v : Lp ℝ 2 m,
      inner ℝ v (phi1_memLp2.toLp phi1) = 0 →
      inner ℝ (resolvent v) v ≤
        (1 / (1 + lambda2)) * ‖v‖ ^ 2

  resolvent_second_mode :
    ∃ v : Lp ℝ 2 m,
      v ≠ 0 ∧
      inner ℝ v (phi1_memLp2.toLp phi1) = 0 ∧
      resolvent v = (1 / (1 + lambda2)) • v

  evolved_zero : evolvedDensity 0 =ᵐ[m] g
  remainder_zero : remainder 0 =ᵐ[m] fun x => g x - a1 * phi1 x

  spectral_expansion : ∀ t : NNReal,
    evolvedDensity t =ᵐ[m] fun x =>
      Real.exp (-lambda1 * (t : ℝ)) * a1 * phi1 x + remainder t x

  remainder_l2_le : ∀ t : NNReal,
    (∫ x, remainder t x ^ 2 ∂m) ^ (1 / (2 : ℝ)) ≤
      Real.exp (-lambda2 * (t : ℝ)) * residualL2

  residualL2_eq :
    residualL2 =
      (∫ x, (g x - a1 * phi1 x) ^ 2 ∂m) ^ (1 / (2 : ℝ))

  survival_pos : ∀ t : NNReal, 0 < ∫ x, evolvedDensity t x ∂m

namespace SpectralData

variable {m : Measure X} [IsFiniteMeasure m]

lemma phi1_integrable (D : SpectralData m) :
    Integrable D.phi1 m :=
  D.phi1_memLp2.integrable (by norm_num)

lemma remainder_memLp2 (D : SpectralData m) (t : NNReal) :
    MemLp (D.remainder t) 2 m := by
  exact (memLp_two_iff_integrable_sq
    (D.remainder_measurable t).aestronglyMeasurable).2
    (D.remainder_sq_integrable t)

lemma remainder_integrable (D : SpectralData m) (t : NNReal) :
    Integrable (D.remainder t) m :=
  (D.remainder_memLp2 t).integrable (by norm_num)

lemma evolved_integrable (D : SpectralData m) (t : NNReal) :
    Integrable (D.evolvedDensity t) m := by
  have hrhs :
      Integrable
        (fun x =>
          Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phi1 x +
            D.remainder t x) m :=
    (D.phi1_integrable.const_mul
      (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1)).add
      (D.remainder_integrable t)
  exact hrhs.congr (D.spectral_expansion t).symm

noncomputable def phiMass (D : SpectralData m) : ℝ :=
  ∫ x, D.phi1 x ∂m

noncomputable def survival (D : SpectralData m) (t : NNReal) : ℝ :=
  ∫ x, D.evolvedDensity t x ∂m

noncomputable def qDensity (D : SpectralData m) : X → ℝ :=
  normalizedDensity D.phi1 D.phiMass

noncomputable def conditionedDensity (D : SpectralData m) (t : NNReal) : X → ℝ :=
  normalizedDensity (D.evolvedDensity t) (D.survival t)

lemma phiMass_pos (D : SpectralData m) : 0 < D.phiMass :=
  D.phi1_mass_pos

lemma survival_pos' (D : SpectralData m) (t : NNReal) : 0 < D.survival t :=
  D.survival_pos t

lemma qDensity_integrable (D : SpectralData m) :
    Integrable D.qDensity m :=
  normalizedDensity_integrable D.phi1 D.phiMass D.phi1_integrable

lemma qDensity_nonneg (D : SpectralData m) :
    0 ≤ᵐ[m] D.qDensity :=
  normalizedDensity_nonneg D.phi1 D.phiMass D.phiMass_pos D.phi1_nonneg

lemma qDensity_integral_one (D : SpectralData m) :
    ∫ x, D.qDensity x ∂m = 1 :=
  normalizedDensity_integral_one D.phi1 D.phiMass D.phiMass_pos rfl

lemma conditionedDensity_integrable (D : SpectralData m) (t : NNReal) :
    Integrable (D.conditionedDensity t) m :=
  normalizedDensity_integrable (D.evolvedDensity t) (D.survival t)
    (D.evolved_integrable t)

lemma conditionedDensity_nonneg (D : SpectralData m) (t : NNReal) :
    0 ≤ᵐ[m] D.conditionedDensity t :=
  normalizedDensity_nonneg (D.evolvedDensity t) (D.survival t)
    (D.survival_pos' t) (D.evolved_nonneg t)

lemma conditionedDensity_integral_one (D : SpectralData m) (t : NNReal) :
    ∫ x, D.conditionedDensity t x ∂m = 1 :=
  normalizedDensity_integral_one (D.evolvedDensity t) (D.survival t)
    (D.survival_pos' t) rfl

noncomputable def q (D : SpectralData m) : ProbabilityMeasure X :=
  probabilityWithDensity m D.qDensity D.qDensity_integrable
    D.qDensity_nonneg D.qDensity_integral_one

noncomputable def conditioned (D : SpectralData m) (t : NNReal) :
    ProbabilityMeasure X :=
  probabilityWithDensity m (D.conditionedDensity t)
    (D.conditionedDensity_integrable t)
    (D.conditionedDensity_nonneg t)
    (D.conditionedDensity_integral_one t)

@[simp] theorem q_toMeasure (D : SpectralData m) :
    (D.q : Measure X) =
      m.withDensity (fun x => ENNReal.ofReal (D.phi1 x / D.phiMass)) := by
  rfl

@[simp] theorem conditioned_toMeasure (D : SpectralData m) (t : NNReal) :
    (D.conditioned t : Measure X) =
      m.withDensity
        (fun x => ENNReal.ofReal (D.evolvedDensity t x / D.survival t)) := by
  rfl

noncomputable def baseHalfPower (m : Measure X) : ℝ :=
  (m.real Set.univ) ^ (1 / (2 : ℝ))

noncomputable def remainderScale (D : SpectralData m) : ℝ :=
  D.residualL2 * baseHalfPower m

lemma baseHalfPower_nonneg (m : Measure X) :
    0 ≤ baseHalfPower m := by
  unfold baseHalfPower
  exact Real.rpow_nonneg measureReal_nonneg _

lemma remainderScale_nonneg (D : SpectralData m) :
    0 ≤ D.remainderScale :=
  mul_nonneg D.residualL2_nonneg (baseHalfPower_nonneg m)

lemma remainder_l1_le (D : SpectralData m) (t : NNReal) :
    ∫ x, |D.remainder t x| ∂m ≤
      Real.exp (-D.lambda2 * (t : ℝ)) * D.remainderScale := by
  have hcs := l1_le_l2_rpow (m := m) (D.remainder t)
    (D.remainder_measurable t).aestronglyMeasurable
    (D.remainder_sq_integrable t)
  have hl2 := D.remainder_l2_le t
  calc
    ∫ x, |D.remainder t x| ∂m
        ≤ (∫ x, D.remainder t x ^ 2 ∂m) ^ (1 / (2 : ℝ)) *
            baseHalfPower m := hcs
    _ ≤ (Real.exp (-D.lambda2 * (t : ℝ)) * D.residualL2) *
            baseHalfPower m :=
      mul_le_mul_of_nonneg_right hl2 (baseHalfPower_nonneg m)
    _ = Real.exp (-D.lambda2 * (t : ℝ)) * D.remainderScale := by
      simp [remainderScale, mul_assoc]

lemma survival_eq_principal_add_remainder (D : SpectralData m) (t : NNReal) :
    D.survival t =
      Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phiMass +
        ∫ x, D.remainder t x ∂m := by
  unfold survival
  rw [integral_congr_ae (D.spectral_expansion t)]
  rw [integral_add
    (D.phi1_integrable.const_mul
      (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1))
    (D.remainder_integrable t)]
  rw [integral_const_mul]
  rfl

lemma remainder_l1_eventually_le_half_principal (D : SpectralData m) :
    ∃ t0 : NNReal, ∀ t : NNReal, t0 ≤ t →
      ∫ x, |D.remainder t x| ∂m ≤
        (1 / 2 : ℝ) *
          (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phiMass) := by
  let A : ℝ := D.a1 * D.phiMass
  have hA : 0 < A := mul_pos D.a1_pos D.phiMass_pos
  have hcoe : Tendsto (fun t : NNReal => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hmul :
      Tendsto (fun t : NNReal => (D.lambda2 - D.lambda1) * (t : ℝ))
        atTop atTop :=
    hcoe.const_mul_atTop D.spectral_gap_pos
  have hgaplim :
      Tendsto
        (fun t : NNReal =>
          Real.exp (-((D.lambda2 - D.lambda1) * (t : ℝ))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul
  have hscaled :
      Tendsto
        (fun t : NNReal =>
          Real.exp (-((D.lambda2 - D.lambda1) * (t : ℝ))) *
            D.remainderScale)
        atTop (𝓝 0) := by
    simpa using hgaplim.mul_const D.remainderScale
  have hev : ∀ᶠ t : NNReal in atTop,
      Real.exp (-((D.lambda2 - D.lambda1) * (t : ℝ))) *
          D.remainderScale < A / 2 :=
    (tendsto_order.1 hscaled).2 (A / 2) (half_pos hA)
  rcases eventually_atTop.1 hev with ⟨t0, ht0⟩
  refine ⟨t0, ?_⟩
  intro t htt
  have hsmall :=
    (ht0 t htt).le
  have hfactor :
      Real.exp (-D.lambda2 * (t : ℝ)) =
        Real.exp (-D.lambda1 * (t : ℝ)) *
          Real.exp (-((D.lambda2 - D.lambda1) * (t : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ∫ x, |D.remainder t x| ∂m
        ≤ Real.exp (-D.lambda2 * (t : ℝ)) * D.remainderScale :=
      D.remainder_l1_le t
    _ = Real.exp (-D.lambda1 * (t : ℝ)) *
          (Real.exp (-((D.lambda2 - D.lambda1) * (t : ℝ))) *
            D.remainderScale) := by
      rw [hfactor]
      ring
    _ ≤ Real.exp (-D.lambda1 * (t : ℝ)) * (A / 2) :=
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ = (1 / 2 : ℝ) *
          (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phiMass) := by
      dsimp [A]
      ring

lemma survival_lower_of_remainder_small
    (D : SpectralData m) (t : NNReal)
    (hsmall :
      ∫ x, |D.remainder t x| ∂m ≤
        (1 / 2 : ℝ) *
          (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phiMass)) :
    (1 / 2 : ℝ) *
        (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phiMass)
      ≤ D.survival t := by
  have habs :
      |∫ x, D.remainder t x ∂m| ≤
        ∫ x, |D.remainder t x| ∂m :=
    abs_integral_le_integral_abs
  have hRlower :
      -((1 / 2 : ℝ) *
          (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phiMass)) ≤
        ∫ x, D.remainder t x ∂m :=
    (abs_le.mp (habs.trans hsmall)).1
  rw [D.survival_eq_principal_add_remainder]
  linarith

lemma tvDist_conditioned_le_two_remainder_div
    (D : SpectralData m) (t : NNReal) :
    tvDist (D.conditioned t : Measure X) (D.q : Measure X) ≤
      2 * (∫ x, |D.remainder t x| ∂m) / D.survival t := by
  have htv := tvDist_probabilityWithDensity_le_integral_abs
    m (D.conditionedDensity t) D.qDensity
    (D.conditionedDensity_integrable t) D.qDensity_integrable
    (D.conditionedDensity_nonneg t) D.qDensity_nonneg
    (D.conditionedDensity_integral_one t) D.qDensity_integral_one
    (by
      unfold conditionedDensity normalizedDensity
      exact (D.evolved_measurable t).div_const _)
    (by
      unfold qDensity normalizedDensity
      exact D.phi1_measurable.div_const _)
  have hnorm := normalized_l1_le_two_remainder_div
    (m := m)
    (D.evolvedDensity t) D.phi1 (D.remainder t)
    (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1)
    (D.survival t) D.phiMass
    (D.evolved_integrable t) D.phi1_integrable
    (D.remainder_integrable t) D.phi1_nonneg
    D.phiMass_pos (D.survival_pos' t)
    rfl rfl (D.spectral_expansion t)
  exact htv.trans hnorm

lemma tvDist_large_time_le_gap
    (D : SpectralData m) (t : NNReal)
    (hsmall :
      ∫ x, |D.remainder t x| ∂m ≤
        (1 / 2 : ℝ) *
          (Real.exp (-D.lambda1 * (t : ℝ)) * D.a1 * D.phiMass)) :
    tvDist (D.conditioned t : Measure X) (D.q : Measure X) ≤
      (4 * D.remainderScale / (D.a1 * D.phiMass)) *
        Real.exp (-(D.lambda2 - D.lambda1) * (t : ℝ)) := by
  let A : ℝ := D.a1 * D.phiMass
  have hA : 0 < A := mul_pos D.a1_pos D.phiMass_pos
  have hS : 0 < D.survival t := D.survival_pos' t
  have hsurv :
      Real.exp (-D.lambda1 * (t : ℝ)) * A / 2 ≤ D.survival t := by
    have h := D.survival_lower_of_remainder_small t hsmall
    dsimp [A]
    linarith
  have htv := D.tvDist_conditioned_le_two_remainder_div t
  have hl1 := D.remainder_l1_le t
  have hnum :
      2 * (∫ x, |D.remainder t x| ∂m) ≤
        2 * (Real.exp (-D.lambda2 * (t : ℝ)) * D.remainderScale) :=
    mul_le_mul_of_nonneg_left hl1 (by norm_num)
  have hratio :
      2 * (∫ x, |D.remainder t x| ∂m) / D.survival t ≤
        2 * (Real.exp (-D.lambda2 * (t : ℝ)) * D.remainderScale) /
          D.survival t :=
    (div_le_div_iff₀ hS hS).2
      (mul_le_mul_of_nonneg_right hnum hS.le)
  have hfactor :
      Real.exp (-D.lambda2 * (t : ℝ)) =
        Real.exp (-D.lambda1 * (t : ℝ)) *
          Real.exp (-(D.lambda2 - D.lambda1) * (t : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  let C : ℝ :=
    (4 * D.remainderScale / A) *
      Real.exp (-(D.lambda2 - D.lambda1) * (t : ℝ))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) D.remainderScale_nonneg) hA.le)
      (Real.exp_pos _).le
  have hupper :
      2 * (Real.exp (-D.lambda2 * (t : ℝ)) * D.remainderScale) /
          D.survival t ≤ C := by
    apply (div_le_iff₀ hS).2
    calc
      2 * (Real.exp (-D.lambda2 * (t : ℝ)) * D.remainderScale)
          = C * (Real.exp (-D.lambda1 * (t : ℝ)) * A / 2) := by
            dsimp [C]
            rw [hfactor]
            field_simp [ne_of_gt hA]
            ring
      _ ≤ C * D.survival t :=
        mul_le_mul_of_nonneg_left hsurv hC
  exact htv.trans (hratio.trans (by
    simpa [C, A] using hupper))

/-- **P-QSD-04.**  A reversible killed spectral datum with compact
self-adjoint resolvent has an exponentially attracting conditional law at the
exact spectral-gap rate and an eventual survival lower bound at the principal
decay rate.  The QSD is the normalized positive principal eigenfunction from
the frozen source. -/
theorem p_qsd_04 (D : SpectralData m) :
    ∃ (Cg cg : ℝ) (t0 : NNReal),
      0 < Cg ∧ 0 < cg ∧
      (D.q : Measure X) =
        m.withDensity
          (fun x => ENNReal.ofReal (D.phi1 x / D.phiMass)) ∧
      (∀ t : NNReal, t0 ≤ t →
        tvDist (D.conditioned t : Measure X) (D.q : Measure X) ≤
          Cg * Real.exp (-(D.lambda2 - D.lambda1) * (t : ℝ))) ∧
      (∀ t : NNReal, t0 ≤ t →
        D.survival t ≥
          cg * Real.exp (-D.lambda1 * (t : ℝ))) := by
  let A : ℝ := D.a1 * D.phiMass
  let K : ℝ := D.remainderScale
  let C0 : ℝ := 4 * K / A
  let Cg : ℝ := 1 + C0
  let cg : ℝ := A / 2
  have hA : 0 < A := mul_pos D.a1_pos D.phiMass_pos
  have hK : 0 ≤ K := D.remainderScale_nonneg
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact div_nonneg (mul_nonneg (by norm_num) hK) hA.le
  have hCg : 0 < Cg := by
    dsimp [Cg]
    linarith
  have hcg : 0 < cg := by
    dsimp [cg]
    exact half_pos hA
  obtain ⟨t0, hsmall⟩ := D.remainder_l1_eventually_le_half_principal
  refine ⟨Cg, cg, t0, hCg, hcg, D.q_toMeasure, ?_, ?_⟩
  · intro t htt
    have htv := D.tvDist_large_time_le_gap t (hsmall t htt)
    have hcoef : C0 ≤ Cg := by
      dsimp [Cg]
      linarith
    have hexp0 :
        0 ≤ Real.exp (-(D.lambda2 - D.lambda1) * (t : ℝ)) :=
      (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right hcoef hexp0
    exact htv.trans (by
      simpa [C0, Cg, K, A] using hmul)
  · intro t htt
    have hs := D.survival_lower_of_remainder_small t (hsmall t htt)
    dsimp [cg, A]
    nlinarith [Real.exp_pos (-D.lambda1 * (t : ℝ))]

lemma qDensity_measurable (D : SpectralData m) :
    Measurable D.qDensity := by
  unfold qDensity normalizedDensity
  exact D.phi1_measurable.div_const _

lemma conditionedDensity_measurable (D : SpectralData m) (t : NNReal) :
    Measurable (D.conditionedDensity t) := by
  unfold conditionedDensity normalizedDensity
  exact (D.evolved_measurable t).div_const _

end SpectralData

end

end UEOT.V3.ReversibleKilledSpectralQSD
