import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
Source bridge for the general compact-resolvent class of P-QSD-04.
The orbit derivative below is the classical generator/resolvent identity
`A (R v) = R v - v`, propagated by the SAME actual semigroup. No spectral
expansion or decay bound is an input. Compact self-adjoint spectral totality
is supplied by mathlib, on a general Hilbert space rather than a finite model.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactSpectralSemigroupSource

open Set Filter Module
open scoped Topology ENNReal
noncomputable section Sources

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A classical-orbit realization of `R = (I-A)⁻¹` for the actual family `S`.
The only time-derivative input is on the resolvent range (the generator domain).
It contains neither diagonalization nor any norm/decay conclusion. -/
structure ResolventOrbit (R : E →L[ℝ] E) (S : ℝ → E →L[ℝ] E) : Prop where
  at_zero : S 0 = ContinuousLinearMap.id ℝ E
  derivative : ∀ v t, 0 ≤ t →
    HasDerivWithinAt (fun s : ℝ => S s (R v)) (S t (R v - v)) (Ici 0) t

/-- Compact self-adjoint spectral totality produces the complete Hilbert sum
of the ACTUAL resolvent eigenspaces. It is not a supplied spectral basis. -/
theorem resolvent_isHilbertSum [CompleteSpace E] (R : E →L[ℝ] E)
    (hc : IsCompactOperator R) (hs : R.IsSymmetric) :
    IsHilbertSum ℝ (fun r : ℝ => Module.End.eigenspace (R : Module.End ℝ E) r)
      (fun r => (Module.End.eigenspace (R : Module.End ℝ E) r).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal _ hs.orthogonalFamily_eigenspaces
  have htotal : (⨆ r : ℝ, Module.End.eigenspace (R : Module.End ℝ E) r).topologicalClosure = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [Submodule.orthogonal_closure]
    exact R.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs
  exact htotal.ge

/-- The actual resolvent orbit equation implies the scalar ODE on each
nonzero resolvent mode. The exponent `1-r⁻¹` comes from the generator, not
from a separate semigroup diagonalization field. -/
theorem eigenmode_derivative {R : E →L[ℝ] E} {S : ℝ → E →L[ℝ] E}
    (h : ResolventOrbit R S) {r : ℝ} (hr : r ≠ 0) {v : E}
    (hv : R v = r • v) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => S s v)
      ((1 - r⁻¹) • S t v) (Ici 0) t := by
  have hpre : R (r⁻¹ • v) = v := by simp [hv, hr]
  have hd := h.derivative (r⁻¹ • v) t ht
  rw [hpre] at hd
  simpa only [map_sub, map_smul, sub_smul, one_smul] using hd

/-- A vector-valued scalar ODE has its actual exponential solution on the
closed nonnegative time half-line, including time zero. -/
theorem scalar_orbit_eq_exp (f : ℝ → E) (a : ℝ)
    (hd : ∀ t, 0 ≤ t → HasDerivWithinAt f (a • f t) (Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) : f t = Real.exp (a*t) • f 0 := by
  let F : ℝ → E := fun s => Real.exp (-a*s) • f s
  have hF : ∀ s, 0 ≤ s → HasDerivWithinAt F 0 (Ici 0) s := by
    intro s hs
    have he : HasDerivWithinAt (fun x : ℝ => Real.exp (-a*x))
        (Real.exp (-a*s) * (-a)) (Ici 0) s := by
      simpa using ((hasDerivAt_id s).const_mul (-a)).exp.hasDerivWithinAt
    have hdF := he.smul (hd s hs)
    have hz : Real.exp (-a*s) • a • f s +
        (Real.exp (-a*s) * -a) • f s = 0 := by module
    rw [hz] at hdF
    exact hdF
  have hcont : ContinuousOn F (Icc 0 t) := by
    intro s hs
    exact (hF s hs.1).continuousWithinAt.mono (fun _ hx => hx.1)
  have heq := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hF s hs.1).mono (fun _ hx => le_trans hs.1 hx)) t ⟨ht,le_rfl⟩
  have hscaled := congrArg (fun v : E => Real.exp (a*t) • v) heq
  simpa [F, smul_smul, ← Real.exp_add] using hscaled

/-- Actual time evolution of each nonzero resolvent eigenmode, derived from
its true generator/resolvent orbit relation. -/
theorem actual_eigenmode {R : E →L[ℝ] E} {S : ℝ → E →L[ℝ] E}
    (h : ResolventOrbit R S) {r : ℝ} (hr : r ≠ 0) {v : E}
    (hv : R v = r • v) (t : ℝ) (ht : 0 ≤ t) :
    S t v = Real.exp ((1-r⁻¹)*t) • v := by
  have he := scalar_orbit_eq_exp (fun s => S s v) (1-r⁻¹)
    (fun s hs => eigenmode_derivative h hr hv s hs) t ht
  simpa [h.at_zero] using he


variable [CompleteSpace E]

/-- Spectral coordinates are constructed from the actual compact symmetric
resolvent, using the full family of its eigenspaces. -/
def coordinates (R : E →L[ℝ] E) (hc : IsCompactOperator R) (hs : R.IsSymmetric) :
    E ≃ₗᵢ[ℝ] lp (fun r : ℝ => Module.End.eigenspace (R : Module.End ℝ E) r) 2 :=
  (resolvent_isHilbertSum R hc hs).linearIsometryEquiv

omit [CompleteSpace E] in
/-- The zero resolvent eigenspace is trivial because a genuine resolvent is
injective. Zero is not silently assigned a finite generator eigenvalue. -/
theorem zero_mode_eq_zero (R : E →L[ℝ] E) (hi : Function.Injective R)
    (v : Module.End.eigenspace (R : Module.End ℝ E) 0) : (v : E) = 0 := by
  apply hi
  simpa using (Module.End.mem_eigenspace_iff.mp v.property)

theorem coordinates_mode (R : E →L[ℝ] E) (hc : IsCompactOperator R) (hs : R.IsSymmetric)
    (r : ℝ) (v : Module.End.eigenspace (R : Module.End ℝ E) r) :
    coordinates R hc hs (v : E) = lp.single 2 r v := by
  apply (coordinates R hc hs).symm.injective
  simp [coordinates, IsHilbertSum.linearIsometryEquiv_symm_apply_single]

/-- Complete expansion of the actual evolved vector, derived from compact
spectral totality and the actual generator/resolvent relation. -/
theorem actual_spectral_expansion (R : E →L[ℝ] E) (hc : IsCompactOperator R)
    (hs : R.IsSymmetric) (hi : Function.Injective R)
    (S : ℝ → E →L[ℝ] E) (h : ResolventOrbit R S)
    (g : E) (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun r : ℝ => Real.exp ((1-r⁻¹)*t) •
      ((coordinates R hc hs g r : Module.End.eigenspace (R : Module.End ℝ E) r) : E))
      (S t g) := by
  have hexp := (resolvent_isHilbertSum R hc hs).hasSum_linearIsometryEquiv_symm
    (coordinates R hc hs g)
  have hmap := hexp.mapL (S t)
  simp only [coordinates, LinearIsometryEquiv.symm_apply_apply] at hmap
  convert hmap using 1
  funext r
  by_cases hr : r = 0
  · subst r
    simp [zero_mode_eq_zero R hi]
  · exact (actual_eigenmode h hr
      (Module.End.mem_eigenspace_iff.mp (coordinates R hc hs g r).property) t ht).symm

/-- The actual evolved spectral coordinates, for every initial vector. -/
theorem actual_coordinates (R : E →L[ℝ] E) (hc : IsCompactOperator R)
    (hs : R.IsSymmetric) (hi : Function.Injective R)
    (S : ℝ → E →L[ℝ] E) (h : ResolventOrbit R S)
    (g : E) (t : ℝ) (ht : 0 ≤ t) (r : ℝ) :
    coordinates R hc hs (S t g) r =
      Real.exp ((1-r⁻¹)*t) • coordinates R hc hs g r := by
  classical
  let C := coordinates R hc hs
  let P := (lp.evalCLM ℝ (fun q : ℝ => Module.End.eigenspace (R : Module.End ℝ E) q) 2 r).comp C.toLinearIsometry.toContinuousLinearMap
  have he := (actual_spectral_expansion R hc hs hi S h g t ht).mapL P
  have hterm : (fun q : ℝ => P (Real.exp ((1-q⁻¹)*t) • (C g q : E))) =
      fun q : ℝ => if q = r then Real.exp ((1-r⁻¹)*t) • C g r else 0 := by
    funext q
    rw [map_smul]
    change Real.exp ((1-q⁻¹)*t) • (coordinates R hc hs (C g q : E) r) = _
    rw [coordinates_mode]
    by_cases hqr : q = r
    · subst q; simp
    · simp [lp.single_apply,hqr,Ne.symm hqr]

  rw [hterm] at he
  exact he.unique (hasSum_ite_eq r _ )


/-- Orthogonal spectral coordinates are the actual orthogonal projections:
inner products with any vector in one mode are preserved at that coordinate. -/
theorem coordinates_inner_mode (R : E →L[ℝ] E) (hc : IsCompactOperator R)
    (hs : R.IsSymmetric) (g : E) (r : ℝ)
    (v : Module.End.eigenspace (R : Module.End ℝ E) r) :
    inner ℝ (coordinates R hc hs g r) v = inner ℝ g (v : E) := by
  have he := (coordinates R hc hs).inner_map_map g (v : E)
  rw [coordinates_mode, lp.inner_single_right] at he
  exact he

/-- Orthogonality to the principal eigenfunction transfers to every actual
resolvent coordinate. This includes its own eigenspace, without assuming a
separate spectral basis aligned to the principal vector. -/
theorem coordinate_orthogonal_principal (R : E →L[ℝ] E) (hc : IsCompactOperator R)
    (hs : R.IsSymmetric) (phi : E) (r1 : ℝ) (hphi : R phi = r1 • phi)
    (g : E) (hg : inner ℝ g phi = 0) (r : ℝ) :
    inner ℝ (coordinates R hc hs g r : E) phi = 0 := by
  classical
  let phiMode : Module.End.eigenspace (R : Module.End ℝ E) r1 :=
    ⟨phi,Module.End.mem_eigenspace_iff.mpr hphi⟩
  by_cases hr : r = r1
  · subst r
    exact (coordinates_inner_mode R hc hs g r1 phiMode).trans hg
  · exact hs.orthogonalFamily_eigenspaces hr (coordinates R hc hs g r) phiMode

omit [CompleteSpace E] in
/-- The actual contraction semigroup forces every nonzero resolvent mode to
have positive eigenvalue. A negative mode would grow exponentially at time
one. Positivity is DERIVED here, not an extra compact-resolvent assumption. -/
theorem resolvent_mode_pos {R : E →L[ℝ] E} (hi : Function.Injective R)
    {S : ℝ → E →L[ℝ] E} (h : ResolventOrbit R S)
    (hcontract : ∀ v : E, ‖S 1 v‖ ≤ ‖v‖)
    (v : E) (hv : v ≠ 0) (r : ℝ) (he : R v = r • v) : 0 < r := by
  have hrne : r ≠ 0 := by
    intro hr
    have hzero : R v = R 0 := by simpa [hr] using he
    exact hv (hi hzero)
  have hevol := actual_eigenmode h hrne he 1 zero_le_one
  have hn := hcontract v
  rw [hevol,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le] at hn
  have hexp : Real.exp (1-r⁻¹) ≤ 1 := by
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
    simp only [mul_one] at hn
    nlinarith
  have hrate : 1-r⁻¹ ≤ 0 := Real.exp_le_one_iff.mp hexp
  by_contra hr
  have hneg : r < 0 := lt_of_le_of_ne (not_lt.mp hr) hrne
  have hnegInv : r⁻¹ < 0 := inv_lt_zero.mpr hneg
  linarith

omit [CompleteSpace E] in
/-- The genuine orthogonal resolvent Rayleigh bound forces its actual
generator exponent below `-lambda`, once mode positivity is derived from
contraction. No decay estimate is an input. -/
theorem exponent_le_of_rayleigh (R : E →L[ℝ] E)
    (lambda : ℝ) (hl : 0 ≤ lambda) (v : E) (hv : v ≠ 0)
    (r : ℝ) (hr : 0 < r) (he : R v = r • v)
    (hb : inner ℝ (R v) v ≤ (1/(1+lambda))*‖v‖^2) :
    1-r⁻¹ ≤ -lambda := by
  have hn : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have hin : inner ℝ (R v) v = r*‖v‖^2 := by
    rw [he,real_inner_smul_left,real_inner_self_eq_norm_sq]
  have hrb : r ≤ 1/(1+lambda) := by rw [hin] at hb; nlinarith
  have hden : 0 < 1+lambda := by linarith
  have hmul : r*(1+lambda) ≤ 1 := (le_div_iff₀ hden).mp hrb
  have hinv : r*r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  nlinarith

/-- Spectral coordinate comparison bounds the norm of the SAME evolved
vector. This is an internal Parseval step, not a semigroup norm assumption. -/
theorem actual_norm_le_of_mode_bound (R : E →L[ℝ] E) (hc : IsCompactOperator R)
    (hs : R.IsSymmetric) (hi : Function.Injective R)
    (S : ℝ → E →L[ℝ] E) (h : ResolventOrbit R S)
    (g : E) (t : ℝ) (ht : 0 ≤ t) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ r : ℝ, coordinates R hc hs g r ≠ 0 →
      Real.exp ((1-r⁻¹)*t) ≤ b) :
    ‖S t g‖ ≤ b*‖g‖ := by
  let C := coordinates R hc hs
  calc
    ‖S t g‖ = ‖C (S t g)‖ := (C.norm_map _).symm
    _ ≤ ‖b • C g‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro r
      rw [show C (S t g) r = Real.exp ((1-r⁻¹)*t) • C g r from
        actual_coordinates R hc hs hi S h g t ht r]
      by_cases hz : C g r = 0
      · simp [hz]
      · simp only [lp.coeFn_smul,Pi.smul_apply,norm_smul,
          Real.norm_eq_abs,abs_of_nonneg hb,abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hbound r hz) (norm_nonneg _)
    _ = b*‖g‖ := by rw [norm_smul,Real.norm_of_nonneg hb,C.norm_map]

/-- The P-QSD-04 L² orthogonal decay estimate is derived from the compact
resolvent's spectral theorem and its actual generator/orbit realization. -/
theorem actual_orthogonal_decay (R : E →L[ℝ] E) (hc : IsCompactOperator R)
    (hs : R.IsSymmetric) (hi : Function.Injective R)
    (S : ℝ → E →L[ℝ] E) (h : ResolventOrbit R S)
    (hcontract : ∀ v : E, ‖S 1 v‖ ≤ ‖v‖)
    (phi : E) (r1 : ℝ) (hphi : R phi = r1 • phi)
    (lambda : ℝ) (hl : 0 ≤ lambda)
    (hgap : ∀ v : E, inner ℝ v phi = 0 →
      inner ℝ (R v) v ≤ (1/(1+lambda))*‖v‖^2)
    (g : E) (hg : inner ℝ g phi = 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖S t g‖ ≤ Real.exp (-lambda*t)*‖g‖ := by
  apply actual_norm_le_of_mode_bound R hc hs hi S h g t ht _ (Real.exp_pos _).le
  intro r hr
  let v : E := (coordinates R hc hs g r : E)
  have hv : v ≠ 0 := by
    intro hz
    apply hr
    exact Subtype.ext hz
  have he : R v = r • v :=
    Module.End.mem_eigenspace_iff.mp (coordinates R hc hs g r).property
  have horth : inner ℝ v phi = 0 :=
    coordinate_orthogonal_principal R hc hs phi r1 hphi g hg r
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (exponent_le_of_rayleigh R lambda hl v hv r
      (resolvent_mode_pos hi h hcontract v hv r he) he (hgap v horth)) ht)


/-- Same-source principal expansion and strict-gap remainder, with the
coefficient computed as the actual Hilbert inner product. The remainder is
the actual semigroup applied to the actual orthogonal residual. -/
theorem actual_principal_expansion_and_remainder
    (R : E →L[ℝ] E) (hc : IsCompactOperator R) (hs : R.IsSymmetric)
    (hi : Function.Injective R)
    (S : ℝ → E →L[ℝ] E) (h : ResolventOrbit R S)
    (hcontract : ∀ v : E, ‖S 1 v‖ ≤ ‖v‖)
    (phi : E) (hnorm : ‖phi‖ = 1) (lambda1 lambda2 : ℝ)
    (hl1 : 0 < lambda1) (hl2 : 0 ≤ lambda2)
    (hphi : R phi = (1/(1+lambda1)) • phi)
    (hgap : ∀ v : E, inner ℝ v phi = 0 →
      inner ℝ (R v) v ≤ (1/(1+lambda2))*‖v‖^2)
    (g : E) (t : ℝ) (ht : 0 ≤ t) :
    S t g = Real.exp (-lambda1*t) • (inner ℝ g phi • phi) +
        S t (g - inner ℝ g phi • phi) ∧
      ‖S t (g - inner ℝ g phi • phi)‖ ≤
        Real.exp (-lambda2*t)*‖g - inner ℝ g phi • phi‖ := by
  have hd : 1+lambda1 ≠ 0 := by linarith
  have hm := actual_eigenmode h (one_div_ne_zero hd) hphi t ht
  have hexponent : 1-(1/(1+lambda1))⁻¹ = -lambda1 := by
    simp only [one_div,inv_inv]; ring
  rw [hexponent] at hm
  have horth : inner ℝ (g - inner ℝ g phi • phi) phi = 0 := by
    simp [inner_sub_left,real_inner_smul_left,hnorm]
  constructor
  · calc
      S t g = S t (inner ℝ g phi • phi + (g - inner ℝ g phi • phi)) := by
        congr 1; module
      _ = _ := by rw [map_add,map_smul,hm]; module
  · exact actual_orthogonal_decay R hc hs hi S h hcontract phi _ hphi
      lambda2 hl2 hgap _ horth t ht

end Sources
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactSpectralSemigroupSource
