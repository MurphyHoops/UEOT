import UEOT
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactSpectralSemigroupSource
open UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactKilledSpectralBinding
open scoped ENNReal NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CompactKilledBoolAuthor
local instance : MeasurableSpace Bool := ⊤
def m : Measure Bool := (1/2:ℝ≥0) • Measure.count
instance : IsFiniteMeasure m := by dsimp [m]; infer_instance
local instance : Zero (Lp ℝ 2 m) := (inferInstance : NormedAddCommGroup (Lp ℝ 2 m)).toZero
lemma ae_iff {p : Bool → Prop} : (∀ᵐ b ∂m,p b) ↔ ∀ b,p b := by
  simp [m,ae_count_iff]
def mk (f : Bool → ℝ) : Lp ℝ 2 m := (MemLp.of_discrete (f:=f)).toLp f
lemma mk_apply (f : Bool → ℝ) (b : Bool) : mk f b = f b :=
  ae_iff.mp (MemLp.coeFn_toLp (MemLp.of_discrete (f:=f))) b
lemma integral_formula (f : Bool → ℝ) : ∫ b,f b ∂m = (f false+f true)/2 := by
  rw [integral_fintype (by exact memLp_one_iff_integrable.mp MemLp.of_discrete)]
  simp [m,Measure.real,Measure.smul_apply]
  ring
lemma inner_formula (v w : Lp ℝ 2 m) :
    inner ℝ v w = (v false*w false+v true*w true)/2 := by
  rw [lp_inner_eq_integral,integral_formula]
def phi : Lp ℝ 2 m := mk (fun _ => 1)
def psi : Lp ℝ 2 m := mk (fun b => if b then -1 else 1)
def g : Lp ℝ 2 m := mk (fun b => if b then 1/2 else 3/2)
lemma phi_apply (b:Bool) : phi b=1 := mk_apply _ b
lemma psi_apply (b:Bool) : psi b=if b then -1 else 1 := mk_apply _ b
lemma g_apply (b:Bool) : g b=if b then 1/2 else 3/2 := mk_apply _ b
lemma phi_norm : ‖phi‖=1 := by
  have he : ‖phi‖^2=1 := by
    rw [←real_inner_self_eq_norm_sq,inner_formula]
    norm_num [phi_apply]
  nlinarith [norm_nonneg phi]
lemma psi_norm : ‖psi‖=1 := by
  have he : ‖psi‖^2=1 := by
    rw [←real_inner_self_eq_norm_sq,inner_formula]
    norm_num [psi_apply]
  nlinarith [norm_nonneg psi]
lemma phi_psi : inner ℝ phi psi=0 := by norm_num [inner_formula,phi_apply,psi_apply]
lemma actual_a1 : inner ℝ g phi=1 := by norm_num [inner_formula,g_apply,phi_apply]
lemma residual_norm : ‖residual g phi‖=1/2 := by
  rw [lp_norm_eq_integral_sq]
  have he : (∫ x,residual g phi x^2 ∂m) = 1/4 := by
    rw [integral_formula]
    have hres := ae_iff.mp (residual_ae g phi)
    norm_num [hres,actual_a1,g_apply,phi_apply]
  rw [he,←Real.sqrt_eq_rpow]
  norm_num
lemma inner_phi_phi : inner ℝ phi phi=1 := by rw [inner_formula]; norm_num [phi_apply]
lemma inner_psi_psi : inner ℝ psi psi=1 := by rw [inner_formula]; norm_num [psi_apply]
lemma psi_phi : inner ℝ psi phi=0 := by rw [real_inner_comm]; exact phi_psi
lemma norm_combo_sq (a b : ℝ) : ‖a • phi+b • psi‖^2 = a^2+b^2 := by
  rw [←real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,inner_smul_right,
    inner_phi_phi,inner_psi_psi,phi_psi,psi_phi]
  ring
lemma basis_actual (v : Lp ℝ 2 m) : v=inner ℝ phi v • phi+inner ℝ psi v • psi := by
  apply Lp.ext
  apply ae_iff.mpr
  intro b
  have ha := ae_iff.mp (Lp.coeFn_add (inner ℝ phi v • phi) (inner ℝ psi v • psi)) b
  have hphi := ae_iff.mp (Lp.coeFn_smul (inner ℝ phi v) phi) b
  have hpsi := ae_iff.mp (Lp.coeFn_smul (inner ℝ psi v) psi) b
  rw [ha]
  simp only [Pi.add_apply,hphi,hpsi,Pi.smul_apply,smul_eq_mul]
  cases b <;> simp [inner_formula,phi_apply,psi_apply] <;> ring

def P : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m := InnerProductSpace.rankOne ℝ phi phi
def Q : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m := InnerProductSpace.rankOne ℝ psi psi
def R : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m := (1/2:ℝ) • P+(1/3:ℝ) • Q
def S (t:ℝ) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m := Real.exp (-t) • P+Real.exp (-2*t) • Q
lemma P_apply (v : Lp ℝ 2 m) : P v=inner ℝ phi v • phi := rfl
lemma Q_apply (v : Lp ℝ 2 m) : Q v=inner ℝ psi v • psi := rfl
lemma R_apply (v : Lp ℝ 2 m) : R v=(1/2:ℝ) • (inner ℝ phi v • phi)+(1/3:ℝ) • (inner ℝ psi v • psi) := rfl
lemma S_apply (t:ℝ) (v : Lp ℝ 2 m) : S t v=Real.exp (-t) • (inner ℝ phi v • phi)+Real.exp (-2*t) • (inner ℝ psi v • psi) := rfl
lemma P_phi : P phi=phi := by simp [P_apply,phi_norm]
lemma Q_phi : Q phi=0 := by simp [Q_apply,psi_phi]
lemma P_psi : P psi=0 := by simp [P_apply,phi_psi]
lemma Q_psi : Q psi=psi := by simp [Q_apply,psi_norm]
lemma R_principal : R phi=(1/(1+(1:ℝ))) • phi := by norm_num [R_apply,phi_norm,psi_phi]
lemma R_second : R psi=(1/(1+(2:ℝ))) • psi := by norm_num [R_apply,psi_norm,phi_psi]
lemma compactP : IsCompactOperator P := by
  have h := isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ phi)
  rcases h.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ phi) with ⟨K,hK,hN⟩
  refine ⟨K,hK,?_⟩
  convert hN using 1
  rfl
lemma compactQ : IsCompactOperator Q := by
  have h := isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ psi)
  rcases h.clm_comp (ContinuousLinearMap.toSpanSingleton ℝ psi) with ⟨K,hK,hN⟩
  refine ⟨K,hK,?_⟩
  convert hN using 1
  rfl
lemma compactR : IsCompactOperator R := (compactP.smul (1/2:ℝ)).add (compactQ.smul (1/3:ℝ))
lemma symmetricR : R.IsSymmetric := by
  intro v w
  simp [R_apply,inner_add_left,inner_add_right,inner_smul_right,
    real_inner_comm]
  ring
lemma actual_generator : ResolventOrbit R S := by
  constructor
  · apply ContinuousLinearMap.ext
    intro v
    simpa [S_apply] using (basis_actual v).symm
  · intro v t _
    have h1 := (((hasDerivAt_id t).neg).exp).smul_const (inner ℝ phi (R v) • phi)
    have h2 := (((hasDerivAt_id t).const_mul (-2)).exp).smul_const (inner ℝ psi (R v) • psi)
    have hd := (h1.add h2).hasDerivWithinAt (s:=Ici 0)
    convert hd using 1
    · funext s; rfl
    · simp [S_apply,R_apply,inner_add_right,inner_sub_right,inner_smul_right,
        phi_norm,psi_norm,phi_psi,psi_phi,smul_smul]
      module
lemma actual_contraction : ∀ v, ‖S 1 v‖≤‖v‖ := by
  intro v
  have e1 : Real.exp (-1)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have e2 : Real.exp (-2)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have e1sq : Real.exp (-1)^2≤1 := by nlinarith [Real.exp_pos (-1)]
  have e2sq : Real.exp (-2)^2≤1 := by nlinarith [Real.exp_pos (-2)]
  have hn : ‖S 1 v‖^2≤‖v‖^2 := by
    rw [S_apply]
    simp only [mul_one,smul_smul,norm_combo_sq]
    conv_rhs => rw [basis_actual v,norm_combo_sq]
    nlinarith [sq_nonneg (inner ℝ phi v),sq_nonneg (inner ℝ psi v),
      mul_nonneg (sub_nonneg.mpr e1sq) (sq_nonneg (inner ℝ phi v)),
      mul_nonneg (sub_nonneg.mpr e2sq) (sq_nonneg (inner ℝ psi v))]
  nlinarith [norm_nonneg (S 1 v),norm_nonneg v]
lemma orthogonal_rayleigh : ∀ v : Lp ℝ 2 m, inner ℝ v phi=0 →
    inner ℝ (R v) v≤(1/(1+(2:ℝ)))*‖v‖^2 := by
  intro v hv
  have hc : inner ℝ phi v=0 := by rw [real_inner_comm]; exact hv
  have he : v=inner ℝ psi v • psi := by simpa [hc] using basis_actual v
  rw [he,R_apply]
  simp [inner_smul_left,inner_smul_right,phi_psi,norm_smul,psi_norm,
    Real.norm_eq_abs,sq_abs]
  ring_nf
  exact le_rfl

lemma g_nonneg : 0 ≤ᵐ[m] (g : Bool → ℝ) := by
  apply ae_iff.mpr
  intro b
  cases b <;> norm_num [g_apply]
lemma g_mass : ∫ b,g b ∂m=1 := by rw [integral_formula]; norm_num [g_apply]
lemma phi_positive : ∀ᵐ b ∂m,0<phi b := by
  exact ae_iff.mpr (fun b => by norm_num [phi_apply])
lemma actual_second_mode : ∃ v : Lp ℝ 2 m, v≠0 ∧ inner ℝ v phi=0 ∧
    R v=(1/(1+(2:ℝ))) • v := by
  refine ⟨psi,?_,psi_phi,R_second⟩
  intro hz
  have he := psi_norm
  rw [hz,norm_zero] at he
  norm_num at he
lemma actual_b1 : inner ℝ psi g=1/2 := by
  rw [inner_formula]
  norm_num [psi_apply,g_apply]
lemma evolved_apply (t:ℝ) (b:Bool) :
    S t g b = Real.exp (-t)+(1/2:ℝ)*Real.exp (-2*t)*(if b then -1 else 1) := by
  rw [S_apply]
  have ha := ae_iff.mp (Lp.coeFn_add (Real.exp (-t) • (inner ℝ phi g • phi))
    (Real.exp (-2*t) • (inner ℝ psi g • psi))) b
  have hphi := ae_iff.mp (Lp.coeFn_smul (Real.exp (-t)) (inner ℝ phi g • phi)) b
  have hpsi := ae_iff.mp (Lp.coeFn_smul (Real.exp (-2*t)) (inner ℝ psi g • psi)) b
  have hp := ae_iff.mp (Lp.coeFn_smul (inner ℝ phi g) phi) b
  have hq := ae_iff.mp (Lp.coeFn_smul (inner ℝ psi g) psi) b
  rw [ha]
  simp only [Pi.add_apply,hphi,hpsi,Pi.smul_apply,hp,hq,smul_eq_mul]
  have hpg : inner ℝ phi g=1 := by rw [real_inner_comm]; exact actual_a1
  rw [hpg,actual_b1,phi_apply,psi_apply]
  ring
lemma actual_evolved_nonneg (t:NNReal) : 0 ≤ᵐ[m] (S t g : Bool → ℝ) := by
  apply ae_iff.mpr
  intro b
  rw [evolved_apply]
  have hexp : Real.exp (-2*(t:ℝ))≤Real.exp (-(t:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [t.coe_nonneg])
  cases b with
  | false => simp only [Bool.false_eq_true,ite_false,mul_one]; positivity
  | true =>
    simp only [ite_true,mul_neg_one,Pi.zero_apply]
    nlinarith [Real.exp_pos (-(t:ℝ)),Real.exp_pos (-2*(t:ℝ))]

lemma residual_eq_second : residual g phi=(1/2:ℝ) • psi := by
  unfold UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactKilledSpectralBinding.residual
  rw [actual_a1]
  have hpg : inner ℝ phi g=1 := by rw [real_inner_comm]; exact actual_a1
  have hg : g=phi+(1/2:ℝ) • psi := by simpa [hpg,actual_b1] using basis_actual g
  rw [hg]
  module
lemma S_second (t:ℝ) : S t psi=Real.exp (-2*t) • psi := by
  simp [S_apply,phi_psi,psi_norm]
lemma actual_remainder_norm (t:ℝ) :
    ‖S t (residual g phi)‖=Real.exp (-2*t)*(1/2:ℝ) := by
  rw [residual_eq_second,map_smul,S_second,norm_smul,norm_smul,psi_norm]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  norm_num
  ring

#print axioms actual_generator
#print axioms actual_contraction
#print axioms orthogonal_rayleigh
#print axioms residual_norm
#print axioms actual_second_mode
#print axioms evolved_apply

end CompactKilledBoolAuthor
