import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactSpectralSemigroupSource
import UEOT.V3.ReversibleKilledSpectralQSD

/-!
P-QSD-04 source adapter. The actual L² evolution and actual killed-law
realization are inputs; the spectral expansion, residual, zero-time identities
and L² bound are outputs. In particular no old `SpectralData` is accepted as
an input, and no unrelated semigroup is substituted for the actual source.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactKilledSpectralBinding

open MeasureTheory Filter
open UEOT.V3.ReversibleKilledSpectralQSD
open CompactSpectralSemigroupSource
open scoped ENNReal
noncomputable section

variable {X : Type*} [MeasurableSpace X] {m : Measure X} [IsFiniteMeasure m]

omit [IsFiniteMeasure m] in
/-- The L² norm of its actual measurable representative is precisely the
integral expression used in the original spectral certificate. -/
theorem lp_norm_eq_integral_sq (v : Lp ℝ 2 m) :
    ‖v‖ = (∫ x, v x ^ 2 ∂m) ^ (1/(2:ℝ)) := by
  have hs : ∫ x, v x ^ 2 ∂m = ‖v‖^2 := by
    have h := real_inner_self_eq_norm_sq v
    change (∫ x, v x*v x ∂m) = ‖v‖^2 at h
    simpa only [pow_two] using h
  rw [hs,← Real.sqrt_eq_rpow,Real.sqrt_sq (norm_nonneg v)]

omit [IsFiniteMeasure m] in
/-- Inner-product coefficient, with its source integral representation. -/
theorem lp_inner_eq_integral (g phi : Lp ℝ 2 m) :
    inner ℝ g phi = ∫ x, g x * phi x ∂m := by
  simp [L2.inner_def,mul_comm]

def residual (g phi : Lp ℝ 2 m) : Lp ℝ 2 m := g - inner ℝ g phi • phi

omit [IsFiniteMeasure m] in
theorem residual_ae (g phi : Lp ℝ 2 m) :
    (residual g phi : X → ℝ) =ᵐ[m] fun x => g x - inner ℝ g phi * phi x := by
  filter_upwards [Lp.coeFn_sub g (inner ℝ g phi • phi),
    Lp.coeFn_smul (inner ℝ g phi) phi] with x hx hs
  simpa [residual,Pi.sub_apply,Pi.smul_apply,smul_eq_mul] using hx.trans
    (congrArg (fun y : ℝ => g x-y) hs)


omit [IsFiniteMeasure m] in
/-- Positivity of the computed principal coefficient follows from the actual
nonnegative probability density and positive principal function. -/
theorem coefficient_pos (g phi : Lp ℝ 2 m)
    (hgnn : 0 ≤ᵐ[m] (g : X → ℝ)) (hgmass : ∫ x, g x ∂m = 1)
    (hphi : ∀ᵐ x ∂m, 0 < phi x) : 0 < inner ℝ g phi := by
  have hi : Integrable (fun x => g x*phi x) m := by
    simpa [mul_comm] using (L2.integrable_inner (𝕜 := ℝ) g phi)
  have hnn : 0 ≤ᵐ[m] fun x => g x*phi x := by
    filter_upwards [hgnn,hphi] with x hg hp
    exact mul_nonneg hg hp.le
  rw [lp_inner_eq_integral]
  by_contra hnot
  have hz : ∫ x, g x*phi x ∂m = 0 :=
    le_antisymm (not_lt.mp hnot) (integral_nonneg_of_ae hnn)
  have hprod := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz
  have hgzero : (g : X → ℝ) =ᵐ[m] 0 := by
    filter_upwards [hprod,hphi] with x hx hp
    exact (mul_eq_zero.mp hx).resolve_right hp.ne'
  have hmasszero : ∫ x, g x ∂m = 0 := by rw [integral_congr_ae hgzero]; simp
  linarith


/-- Positive principal mass is implied by the actual probability input and
strict principal positivity; it is not an additional source premise. -/
theorem principal_mass_pos (g phi : Lp ℝ 2 m)
    (hgnn : 0 ≤ᵐ[m] (g : X → ℝ)) (hgmass : ∫ x, g x ∂m = 1)
    (hphi : ∀ᵐ x ∂m, 0 < phi x) : 0 < ∫ x, phi x ∂m := by
  have ha := coefficient_pos g phi hgnn hgmass hphi
  have hnn : 0 ≤ᵐ[m] (phi : X → ℝ) := hphi.mono (fun _ h => h.le)
  have hi : Integrable (phi : X → ℝ) m := (Lp.memLp phi).integrable (by norm_num)
  by_contra hn
  have hz : ∫ x, phi x ∂m = 0 :=
    le_antisymm (not_lt.mp hn) (integral_nonneg_of_ae hnn)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz
  have hprod : (fun x => g x*phi x) =ᵐ[m] 0 := by
    filter_upwards [hzero] with x hx
    simp [hx]
  rw [lp_inner_eq_integral,integral_congr_ae hprod] at ha
  simp at ha

/-- A real resolvent is injective already by the actual generator identity
at time zero; there is no separate injectivity assumption in the builder. -/
theorem generator_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E →L[ℝ] E) (S : ℝ → E →L[ℝ] E) (h : ResolventOrbit R S) :
    Function.Injective R := by
  intro x y hxy
  have hz : R (x-y) = 0 := by simp [map_sub,hxy]
  have hd := h.derivative (x-y) 0 le_rfl
  have hd' : HasDerivWithinAt (fun _ : ℝ => (0:E)) (-(x-y)) (Set.Ici 0) 0 := by
    simpa [hz,h.at_zero] using hd
  have hv := hd'.derivWithin (uniqueDiffWithinAt_Ici (0:ℝ))
  simp at hv
  exact (sub_eq_zero.mp hv.symm).symm

/-- Build the ORIGINAL certificate from the actual source and the original
spectral hypotheses. Only legitimate source semantics and spectral conditions
are supplied; all four formerly external expansion/remainder fields are proved.
`S` is a real-time extension used only at nonnegative times. -/
def ofActualSource
    (killed : UEOT.V3.QSDTVLimit.KilledSemigroup X)
    (g phi : Lp ℝ 2 m)
    (hgnn : 0 ≤ᵐ[m] (g : X → ℝ)) (hgmass : ∫ x, g x ∂m = 1)
    (hphiPos : ∀ᵐ x ∂m, 0 < phi x)
    (hphiNorm : ‖phi‖ = 1)
    (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hcompact : IsCompactOperator R) (hsymmetric : R.IsSymmetric)
    (S : ℝ → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hgenerator : ResolventOrbit R S)
    (hcontract : ∀ v, ‖S 1 v‖ ≤ ‖v‖)
    (hevolvedNonneg : ∀ t : NNReal, 0 ≤ᵐ[m] (S t g : X → ℝ))
    (hinitial : (killed.initial : Measure X) =
      m.withDensity (fun x => ENNReal.ofReal (g x)))
    (hrealized : ∀ t : NNReal, killed.evolved t =
      m.withDensity (fun x => ENNReal.ofReal (S t g x)))
    (lambda1 lambda2 : ℝ) (hfirst : 0 < lambda1) (hgap : 0 < lambda2-lambda1)
    (hprincipal : R phi = (1/(1+lambda1)) • phi)
    (horthogonal : ∀ v : Lp ℝ 2 m, inner ℝ v phi = 0 →
      inner ℝ (R v) v ≤ (1/(1+lambda2))*‖v‖^2)
    (hsecond : ∃ v : Lp ℝ 2 m, v ≠ 0 ∧ inner ℝ v phi = 0 ∧
      R v = (1/(1+lambda2)) • v) : SpectralData m where
  resolvent := R
  resolvent_compact := hcompact
  resolvent_symmetric := hsymmetric
  g := g
  phi1 := phi
  evolvedDensity t := S t g
  remainder t := S t (residual g phi)
  killed := killed
  lambda1 := lambda1
  lambda2 := lambda2
  a1 := inner ℝ g phi
  residualL2 := ‖residual g phi‖
  lambda1_pos := hfirst
  spectral_gap_pos := hgap
  a1_pos := coefficient_pos g phi hgnn hgmass hphiPos
  phi1_measurable := (Lp.stronglyMeasurable phi).measurable
  evolved_measurable t := (Lp.stronglyMeasurable (S t g)).measurable
  remainder_measurable t := (Lp.stronglyMeasurable (S t (residual g phi))).measurable
  remainder_sq_integrable t :=
    (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable (S t (residual g phi)))).mp
      (Lp.memLp (S t (residual g phi)))
  g_memLp2 := Lp.memLp g
  phi1_memLp2 := Lp.memLp phi
  phi1_l2_norm_one := by simpa using hphiNorm
  g_nonneg := hgnn
  phi1_pos := hphiPos
  evolved_nonneg := hevolvedNonneg
  g_mass_one := hgmass
  phi1_mass_pos := principal_mass_pos g phi hgnn hgmass hphiPos
  a1_eq_inner := lp_inner_eq_integral g phi
  killed_initial_eq := hinitial
  killed_evolved_eq := hrealized
  resolvent_principal := by simpa using hprincipal
  resolvent_orthogonal_le := by simpa using horthogonal
  resolvent_second_mode := by simpa using hsecond
  evolved_zero := by simp only [NNReal.coe_zero,hgenerator.at_zero,ContinuousLinearMap.id_apply]; exact Filter.EventuallyEq.rfl
  remainder_zero := by
    simpa only [NNReal.coe_zero,hgenerator.at_zero,ContinuousLinearMap.id_apply] using residual_ae g phi
  spectral_expansion t := by
    have he := (actual_principal_expansion_and_remainder R hcompact hsymmetric (generator_injective R S hgenerator) S
      hgenerator hcontract phi hphiNorm lambda1 lambda2 hfirst (by linarith) hprincipal
      horthogonal g t t.coe_nonneg).1
    have he' : S t g = (Real.exp (-lambda1*(t:ℝ))*inner ℝ g phi) • phi +
        S t (residual g phi) := by simpa [residual,smul_smul] using he
    rw [he']
    filter_upwards [Lp.coeFn_add ((Real.exp (-lambda1*(t:ℝ))*inner ℝ g phi) • phi)
      (S t (residual g phi)),Lp.coeFn_smul (Real.exp (-lambda1*(t:ℝ))*inner ℝ g phi) phi] with x hx hs
    simpa [Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_assoc] using hx.trans
      (congrArg (fun y : ℝ => y + S t (residual g phi) x) hs)
  remainder_l2_le t := by
    rw [← lp_norm_eq_integral_sq]
    exact (actual_principal_expansion_and_remainder R hcompact hsymmetric (generator_injective R S hgenerator) S
      hgenerator hcontract phi hphiNorm lambda1 lambda2 hfirst (by linarith) hprincipal
      horthogonal g t t.coe_nonneg).2
  residualL2_eq := by
    rw [lp_norm_eq_integral_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [residual_ae g phi] with x hx
    rw [hx]


/-- The certificate's conditional density is the SAME original killed
conditional law, including all finite times with positive source survival. -/
theorem conditioned_eq_actual (D : SpectralData m) (t : NNReal) :
    (D.conditioned t : Measure X) = (D.killed.conditioned t : Measure X) := by
  let : ProbabilityTheory.IsFiniteKernel (D.killed.P t) := D.killed.isFiniteKernel t
  let : IsFiniteMeasure (D.killed.evolved t) := by
    unfold UEOT.V3.QSDTVLimit.KilledSemigroup.evolved
    infer_instance
  have htop : D.killed.survival t ≠ ∞ := (measure_lt_top (D.killed.evolved t) Set.univ).ne
  have hsurv : 0 < D.survival t := by
    rw [D.survival_eq_killed_toReal]
    exact ENNReal.toReal_pos (D.killed.survival_pos t).ne' htop
  rw [D.conditioned_toMeasure_of_pos t hsurv,
    UEOT.V3.QSDTVLimit.KilledSemigroup.conditioned_toMeasure,D.killed_evolved_eq]
  rw [← withDensity_smul _ (D.evolved_measurable t).ennreal_ofReal]
  congr 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hsurv,D.survival_eq_killed_toReal,ENNReal.ofReal_toReal htop]
  simp [div_eq_mul_inv,mul_comm]


/-- Actual original P-QSD-04 consumer: the constructed certificate yields the
TV/survival conclusion for THIS killed semigroup, without external expansion
or remainder hypotheses. -/
theorem actual_p_qsd_04
    (killed : UEOT.V3.QSDTVLimit.KilledSemigroup X)
    (g phi : Lp ℝ 2 m)
    (hgnn : 0 ≤ᵐ[m] (g : X → ℝ)) (hgmass : ∫ x, g x ∂m = 1)
    (hphiPos : ∀ᵐ x ∂m, 0 < phi x)
    (hphiNorm : ‖phi‖ = 1)
    (R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hcompact : IsCompactOperator R) (hsymmetric : R.IsSymmetric)
    (S : ℝ → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hgenerator : ResolventOrbit R S)
    (hcontract : ∀ v, ‖S 1 v‖ ≤ ‖v‖)
    (hevolvedNonneg : ∀ t : NNReal, 0 ≤ᵐ[m] (S t g : X → ℝ))
    (hinitial : (killed.initial : Measure X) =
      m.withDensity (fun x => ENNReal.ofReal (g x)))
    (hrealized : ∀ t : NNReal, killed.evolved t =
      m.withDensity (fun x => ENNReal.ofReal (S t g x)))
    (lambda1 lambda2 : ℝ) (hfirst : 0 < lambda1) (hgap : 0 < lambda2-lambda1)
    (hprincipal : R phi = (1/(1+lambda1)) • phi)
    (horthogonal : ∀ v : Lp ℝ 2 m, inner ℝ v phi = 0 →
      inner ℝ (R v) v ≤ (1/(1+lambda2))*‖v‖^2)
    (hsecond : ∃ v : Lp ℝ 2 m, v ≠ 0 ∧ inner ℝ v phi = 0 ∧
      R v = (1/(1+lambda2)) • v) :
    ∃ (q : MeasureTheory.ProbabilityMeasure X) (Cg cg : ℝ) (t0 : NNReal),
      0 < Cg ∧ 0 < cg ∧
      (q : Measure X) = m.withDensity (fun x => ENNReal.ofReal (phi x / ∫ x, phi x ∂m)) ∧
      (∀ t : NNReal, t0 ≤ t →
        UEOT.V3.TotalVariation.tvDist (killed.conditioned t : Measure X) (q : Measure X) ≤
          Cg*Real.exp (-(lambda2-lambda1)*(t:ℝ))) ∧
      (∀ t : NNReal, t0 ≤ t → (killed.survival t).toReal ≥ cg*Real.exp (-lambda1*(t:ℝ))) := by
  let D := ofActualSource killed g phi hgnn hgmass hphiPos hphiNorm R hcompact hsymmetric S hgenerator hcontract hevolvedNonneg hinitial hrealized lambda1 lambda2 hfirst hgap hprincipal horthogonal hsecond
  obtain ⟨Cg,cg,t0,hCg,hcg,hq,htv,hsurv⟩ := SpectralData.p_qsd_04 D
  refine ⟨D.q,Cg,cg,t0,hCg,hcg,hq,?_,hsurv⟩
  intro t ht
  have he := htv t ht
  rw [conditioned_eq_actual] at he
  exact he

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactKilledSpectralBinding
