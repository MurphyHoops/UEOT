import UEOT

/-!
Actual source: Bool killed transition table with rates 1 and 2.
Initial law: false 3/4, true 1/4; reference measure: (1/2:NNReal) • count.
No survival, spectral expansion, or conditional-TV conclusion is assumed.
This helper is a common-consumer source author contribution, not independent review.
-/
namespace CompactKilledBoolKernel
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
local instance : MeasurableSpace Bool:=⊤

def e (t : ℝ≥0) : ℝ:=Real.exp (-(t : ℝ))
def f (t : ℝ≥0) : ℝ:=Real.exp (-2*(t : ℝ))
def k (t : ℝ≥0) (x y : Bool) : ℝ:=if x=y then (e t+f t)/2 else (e t-f t)/2
lemma e_pos (t : ℝ≥0) : 0<e t:=Real.exp_pos _
lemma f_pos (t : ℝ≥0) : 0<f t:=Real.exp_pos _
lemma f_le_e (t : ℝ≥0) : f t≤e t:=Real.exp_le_exp.mpr (by nlinarith [t.2])
lemma k_nonneg (t : ℝ≥0) (x y : Bool) : 0≤k t x y :=by
  unfold k
  split_ifs <;> linarith [e_pos t,f_pos t,f_le_e t]
lemma row_sum (t : ℝ≥0) (x : Bool) : k t x false+k t x true=e t:=by
  cases x <;> simp [k] <;> ring
lemma e_add (s t : ℝ≥0) : e (s+t)=e s*e t:=by simp [e,Real.exp_add,mul_comm]
lemma f_add (s t : ℝ≥0) : f (s+t)=f s*f t:=by
  unfold f
  rw [NNReal.coe_add,show -2*((s : ℝ)+t)=(-2*(s : ℝ))+(-2*(t : ℝ)) by ring,Real.exp_add]
lemma k_chapman (s t : ℝ≥0) (x y : Bool) :
    k (s+t) x y=k s x false*k t false y+k s x true*k t true y:=by
  cases x <;> cases y <;> simp [k,e_add,f_add] <;> ring

def row (t : ℝ≥0) (x : Bool) : Measure Bool:=
  ENNReal.ofReal (k t x false) • Measure.dirac false+
  ENNReal.ofReal (k t x true) • Measure.dirac true

def kernel (t : ℝ≥0) : Kernel Bool Bool:=Kernel.ofFunOfCountable (row t)
@[simp] lemma kernel_apply (t : ℝ≥0) (x : Bool) : kernel t x=row t x:=rfl
@[simp] lemma kernel_singleton (t : ℝ≥0) (x y : Bool) :
    kernel t x {y}=ENNReal.ofReal (k t x y):=by
  rw [kernel_apply]
  cases y <;> simp [row,Measure.add_apply,Measure.smul_apply]
lemma kernel_mass (t : ℝ≥0) (x : Bool) : kernel t x Set.univ=ENNReal.ofReal (e t):=by
  simp only [kernel_apply,row,Measure.add_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add (k_nonneg t x false) (k_nonneg t x true),row_sum]
lemma kernel_subprob (t : ℝ≥0) (x : Bool) : kernel t x Set.univ≤1:=by
  rw [kernel_mass]
  exact (ENNReal.ofReal_le_one).mpr (Real.exp_le_one_iff.mpr (by linarith [t.2]))
lemma kernel_zero : kernel 0=Kernel.id:=by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [kernel_singleton,Kernel.id_apply]
  cases x <;> cases y <;> simp [k,e,f]
lemma kernel_chapman (s t : ℝ≥0) : kernel (s+t)=kernel t ∘ₖ kernel s:=by
  apply Kernel.ext
  intro x
  apply Measure.ext_of_singleton
  intro y
  rw [kernel_singleton,Kernel.comp_apply' _ _ _ (measurableSet_singleton y),kernel_apply]
  simp only [row,lintegral_add_measure,lintegral_smul_measure]
  rw [lintegral_dirac' false (measurable_of_countable _),
    lintegral_dirac' true (measurable_of_countable _)]
  simp only [kernel_singleton,smul_eq_mul]
  rw [←ENNReal.ofReal_mul (k_nonneg s x false),←ENNReal.ofReal_mul (k_nonneg s x true),
    ←ENNReal.ofReal_add (mul_nonneg (k_nonneg s x false) (k_nonneg t false y))
      (mul_nonneg (k_nonneg s x true) (k_nonneg t true y)),k_chapman]

def m : Measure Bool:=(1/2 : ℝ≥0) • Measure.count
@[simp] lemma m_singleton (x : Bool) : m {x}=(1/2 : ℝ≥0∞):=by
  simp [m,Measure.smul_apply]
instance m_probability : IsProbabilityMeasure m:=by
  constructor
  change ((1/2 : ℝ≥0) : ℝ≥0∞)*Measure.count Set.univ=1
  rw [Measure.count_univ]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

def initialMeasure : Measure Bool:=
  ENNReal.ofReal (3/4 : ℝ) • Measure.dirac false+
  ENNReal.ofReal (1/4 : ℝ) • Measure.dirac true
instance initial_probability : IsProbabilityMeasure initialMeasure:=by
  constructor
  simp only [initialMeasure,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),smul_eq_mul,mul_one]
  rw [←ENNReal.ofReal_add (by norm_num : (0 : ℝ)≤3/4) (by norm_num : (0 : ℝ)≤1/4)]
  norm_num
def initial : ProbabilityMeasure Bool:=⟨initialMeasure,inferInstance⟩
lemma initial_integral (g : Bool→ℝ≥0∞) : ∫⁻x,g x ∂initialMeasure=
    ENNReal.ofReal (3/4 : ℝ)*g false+ENNReal.ofReal (1/4 : ℝ)*g true:=by
  simp only [initialMeasure,lintegral_add_measure,lintegral_smul_measure,
    lintegral_dirac' _ (measurable_of_countable _),smul_eq_mul]
lemma evolved_mass (t : ℝ≥0) : (kernel t ∘ₘ initialMeasure) Set.univ=ENNReal.ofReal (e t):=by
  rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _),initial_integral]
  simp only [kernel_mass]
  rw [←add_mul,←ENNReal.ofReal_add (by norm_num : (0 : ℝ)≤3/4) (by norm_num : (0 : ℝ)≤1/4)]
  norm_num

def semigroup : UEOT.V3.QSDTVLimit.KilledSemigroup Bool where
  P:=kernel
  subprob:=kernel_subprob
  zero:=kernel_zero
  semigroup:=kernel_chapman
  initial:=initial
  initialSurvivalPos:=by
    intro t
    change 0<(kernel t ∘ₘ initialMeasure) Set.univ
    rw [evolved_mass]
    exact ENNReal.ofReal_pos.mpr (e_pos t)
lemma survival_eq (t : ℝ≥0) : semigroup.survival t=ENNReal.ofReal (e t):=evolved_mass t

def psi (x : Bool) : ℝ:=if x then -1 else 1
def density (t : ℝ≥0) (x : Bool) : ℝ:=e t+(1/2 : ℝ)*f t*psi x
lemma density_pos (t : ℝ≥0) (x : Bool) : 0<density t x :=by
  cases x <;> simp only [density,psi,Bool.false_eq_true,↓reduceIte] <;>
    nlinarith [e_pos t,f_pos t,f_le_e t]
lemma weighted_row_density (t : ℝ≥0) (y : Bool) :
    (3/4 : ℝ)*k t false y+(1/4 : ℝ)*k t true y=density t y/2:=by
  cases y <;> simp [k,density,psi] <;> ring
lemma evolved_singleton (t : ℝ≥0) (y : Bool) :
    semigroup.evolved t {y}=ENNReal.ofReal (density t y/2):=by
  change (kernel t ∘ₘ initialMeasure) {y}=_
  rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _),initial_integral]
  simp only [kernel_singleton]
  rw [←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤3/4),
    ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤1/4),
    ←ENNReal.ofReal_add (mul_nonneg (by norm_num) (k_nonneg t false y))
      (mul_nonneg (by norm_num) (k_nonneg t true y)),weighted_row_density]
lemma evolved_eq_density (t : ℝ≥0) :
    semigroup.evolved t=m.withDensity (fun x=>ENNReal.ofReal (density t x)):=by
  apply Measure.ext_of_singleton
  intro y
  rw [evolved_singleton,withDensity_apply _ (measurableSet_singleton y),lintegral_singleton,m_singleton]
  rw [div_eq_mul_inv,ENNReal.ofReal_mul (density_pos t y).le]
  rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ)<2)]
  norm_num
lemma initial_eq_density : initialMeasure=m.withDensity (fun x=>ENNReal.ofReal (if x then (1/2 : ℝ) else 3/2)):=by
  have hh:=evolved_eq_density 0
  have hz : semigroup.evolved 0=initialMeasure:=by
    change kernel 0 ∘ₘ initialMeasure=initialMeasure
    rw [kernel_zero,Measure.id_comp]
  rw [hz] at hh
  convert hh using 1
  congr 1
  funext x
  cases x <;> norm_num [density,e,f,psi]


lemma f_eq_e_sq (t : ℝ≥0) : f t=(e t)^2:=by
  unfold f e
  rw [pow_two,←Real.exp_add]
  congr 1
  ring

def conditionalAtom (t : ℝ≥0) (x : Bool) : ℝ:=1/2+(1/4 : ℝ)*e t*psi x
lemma conditioned_singleton_real (t : ℝ≥0) (x : Bool) :
    ((semigroup.conditioned t : Measure Bool) {x}).toReal=conditionalAtom t x:=by
  rw [UEOT.V3.QSDTVLimit.KilledSemigroup.conditioned_toMeasure,Measure.smul_apply,
    survival_eq,evolved_singleton]
  simp only [smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (e_pos t).le,
    ENNReal.toReal_ofReal (div_nonneg (density_pos t x).le (by norm_num : (0 : ℝ)≤2))]
  unfold density conditionalAtom
  rw [f_eq_e_sq]
  field_simp [(e_pos t).ne']
  ring
lemma conditional_deviation (t : ℝ≥0) (x : Bool) :
    |conditionalAtom t x-(1/2 : ℝ)|=(1/4 : ℝ)*e t:=by
  have hp : 0≤(1/4 : ℝ)*e t:=mul_nonneg (by norm_num) (e_pos t).le
  cases x
  · have heq : conditionalAtom t false-1/2=(1/4 : ℝ)*e t:=by simp [conditionalAtom,psi]
    rw [heq,abs_of_nonneg hp]
  · have heq : conditionalAtom t true-1/2=-((1/4 : ℝ)*e t):=by simp [conditionalAtom,psi]
    rw [heq,abs_neg,abs_of_nonneg hp]
lemma conditioned_tv_exact (t : ℝ≥0) :
    UEOT.V3.TotalVariation.tvDist (semigroup.conditioned t : Measure Bool) m=
      (1/4 : ℝ)*Real.exp (-(t : ℝ)):=by
  have hh:=UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs
    (semigroup.conditioned t : Measure Bool).toPMF m.toPMF
  rw [Measure.toPMF_toMeasure,Measure.toPMF_toMeasure] at hh
  rw [hh]
  simp only [Measure.toPMF_apply,conditioned_singleton_real,m_singleton]
  have hm : ((1/2 : ℝ≥0∞)).toReal=(1/2 : ℝ):=by simp
  simp_rw [hm,conditional_deviation]
  rw [Fintype.sum_bool]
  unfold e
  ring


lemma actual_initial (x : Bool) : ((semigroup.initial : Measure Bool) {x}).toReal=
    if x then (1/4 : ℝ) else 3/4:=by
  cases x <;> norm_num [semigroup,initial,initialMeasure,Measure.add_apply,Measure.smul_apply]
lemma initial_tv_nonzero : UEOT.V3.TotalVariation.tvDist
    (semigroup.conditioned 0 : Measure Bool) m=(1/4 : ℝ):=by
  rw [conditioned_tv_exact]
  norm_num
lemma conditioned_tv_positive (t : ℝ≥0) : 0<UEOT.V3.TotalVariation.tvDist
    (semigroup.conditioned t : Measure Bool) m:=by
  rw [conditioned_tv_exact]
  exact mul_pos (by norm_num) (Real.exp_pos _)
lemma evolved_second_mode_nonzero (t : ℝ≥0) : density t false-density t true=f t:=by
  simp [density,psi]
  ring

end
end CompactKilledBoolKernel
