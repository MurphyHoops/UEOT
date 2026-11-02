import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricSource
import UEOT.V3.Compression.PositiveEigenstructure
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceQSDBinding

/-!
M21.3–4: construct Perron/QSD/Doob data on the ORIGINAL safe restriction.
The arbitrary safe initial PMF is not replaced by the QSD. Positive times,
time0, theta0 and theta1 have explicitly different conditioning boundaries.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricQSD
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly UEOT.V3.PathError
open UEOT.V3.QSDPerron
open UEOT.V3.Compression.TheoryCompletion
open ConflictParametricSource SourcePolicyPathBridgeCheck SameSourceKilledPathCheck
open SameSourceConditionedTerminalCheck
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace State :=⊤

def K : Set State:={x | x.1=true}
instance : DecidablePred K :=fun x=>inferInstanceAs (Decidable (x.1=true))

def safeEquiv : Bool≃K where
  toFun:=fun u=>⟨(true,u),rfl⟩
  invFun:=fun x=>x.val.2
  left_inv:=fun _=>rfl
  right_inv:=fun x=>Subtype.ext (Prod.ext x.property.symm rfl)

instance : Fintype K :=Fintype.ofEquiv Bool safeEquiv
local instance : DecidableEq K :=Classical.decEq K

theorem safe_sum (f : K→ℝ) : ∑x : K,f x=f (safeEquiv false)+f (safeEquiv true) :=by
  rw [←Equiv.sum_comp safeEquiv f]
  simp only [Fintype.sum_bool]
  ring

def Q (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) : Matrix K K ℝ :=
  killedMatrix M (policy theta h0 h1) K

def rho (theta : ℝ) : ℝ:=1-theta
def fair (_x : K) : ℝ:=1/2

theorem Q_entry (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (x y : K) :
    Q theta h0 h1 x y=rho theta/2 :=by
  unfold Q killedMatrix
  rw [policyMatrix_eq]
  have hy : y.val.1=true:=y.property
  simp only [closedMatrix,hy,ite_true,rho]

theorem killed_embed (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (u v : Bool) :
    Q theta h0 h1 (safeEquiv u) (safeEquiv v)=killed theta u v :=by
  rw [Q_entry,killed_eq]
  rfl

theorem fair_sum : ∑x : K,fair x=1 :=by rw [safe_sum];norm_num [fair]

theorem fair_left (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (y : K) :
    rowApply fair (Q theta h0 h1) y=rho theta*fair y :=by
  unfold rowApply
  rw [safe_sum]
  simp only [Q_entry,fair]
  ring

/-- Perron data are CONSTRUCTED, not an independent premise to the example. -/
def biData (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1) :
    UEOT.V3.Compression.PositiveEigenstructure.BiEigenData (Q theta h0 h1.le) where
  right:={
    scale:=rho theta
    vector:=fun _=>1
    scale_pos:=by unfold rho;linarith
    vector_pos:=fun _=>by norm_num
    eigen:=by
      intro x
      unfold UEOT.V3.Compression.PositiveEigenstructure.colApply
      rw [safe_sum]
      simp only [Q_entry,mul_one]
      ring }
  left:=fair
  matrix_nonneg:=by intro x y;rw [Q_entry];unfold rho;linarith
  left_nonneg:=fun _=>by norm_num [fair]
  left_sum_one:=fair_sum
  pairing_sum_one:=by simp only [mul_one];exact fair_sum
  left_eigen:=fair_left theta h0 h1.le

theorem actual_qsd_goa (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1) :
    KilledQSDGOA (Q theta h0 h1.le) fair (rho theta) :=by
  refine ⟨?_,?_,fun _=>by norm_num [fair],fair_sum,?_,fair_left theta h0 h1.le⟩
  · intro x y
    rw [Q_entry]
    unfold rho
    linarith
  · intro x
    rw [safe_sum]
    simp only [Q_entry]
    unfold rho
    linarith
  · unfold rho
    linarith

theorem actual_doob_fair (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1) (x y : K) :
    UEOT.V3.Compression.PositiveEigenstructure.hTransform (biData theta h0 h1).right x y=1/2 :=by
  change Q theta h0 h1.le x y*1/(rho theta*1)=1/2
  rw [Q_entry,mul_one,mul_one]
  have hr : rho theta≠0:=by unfold rho;linarith
  field_simp [hr]

theorem paired_weight_fair (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1) (x : K) :
    UEOT.V3.Compression.PositiveEigenstructure.invariantWeight (biData theta h0 h1) x=fair x :=by
  change fair x*1=fair x
  ring

/-- Every normalized initial safe law, NOT just fair, is mixed in one step. -/
theorem arbitrary_one_step (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1)
    (eta : K→ℝ) (hsum : ∑x,eta x=1) (y : K) :
    rowApply eta (Q theta h0 h1) y=rho theta*fair y :=by
  unfold rowApply
  simp only [Q_entry]
  rw [←Finset.sum_mul,hsum]
  simp only [one_mul,fair]
  ring

/-- rho may be zero: actual killed mass is derived even at theta1. -/
theorem arbitrary_positive_power (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1)
    (eta : K→ℝ) (hsum : ∑x,eta x=1) (n : ℕ) (y : K) :
    rowApply eta ((Q theta h0 h1)^(n+1)) y=rho theta^(n+1)*fair y :=by
  rw [pow_succ',rowApply_mul]
  have he : (fun x=>rowApply eta (Q theta h0 h1) x)=fun x=>rho theta*fair x:=
    funext (arbitrary_one_step theta h0 h1 eta hsum)
  rw [he]
  unfold rowApply
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum]
  change rho theta*rowApply fair ((Q theta h0 h1)^n) y=rho theta^(n+1)*fair y
  rw [leftPerron_pow _ _ _ (fair_left theta h0 h1) n y,pow_succ]
  ring

theorem arbitrary_survival_power (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1)
    (eta : K→ℝ) (hsum : ∑x,eta x=1) (n : ℕ) :
    ∑y : K,rowApply eta ((Q theta h0 h1)^(n+1)) y=rho theta^(n+1) :=by
  simp_rw [arbitrary_positive_power theta h0 h1 eta hsum n]
  rw [←Finset.mul_sum,fair_sum,mul_one]

theorem arbitrary_conditioned_power (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1)
    (eta : K→ℝ) (hsum : ∑x,eta x=1) (n : ℕ) (y : K) :
    rowApply eta ((Q theta h0 h1.le)^(n+1)) y/rho theta^(n+1)=fair y :=by
  rw [arbitrary_positive_power theta h0 h1.le eta hsum n y]
  have hr : rho theta≠0:=by unfold rho;linarith
  field_simp [hr]

def fairPMF : PMF K :=FiniteProbabilityRow.ofRealRow fair
  (fun _=>by norm_num [fair]) fair_sum

theorem fairPMF_real (x : K) : (fairPMF x).toReal=fair x :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

/-- Actual original state/action-history source, with ANY chosen safe initial
PMF. The action law is the same frozen constant-at-every-history policy. -/
def actualLaw (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (eta : PMF K) (T : ℕ) :=
  causalLaw (eta.map Subtype.val)
    (riskMicroControlKernel id (fun _=>M.transitionPMF)
      (observationMarkovPolicy (fun _ : State=>actionLaw theta h0 h1))) T

theorem actual_policy_history (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) :
    observationMarkovPolicy (fun _ : State=>actionLaw theta h0 h1)=historyPolicy theta h0 h1 :=rfl

theorem actual_terminal_mass (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1)
    (eta : PMF K) (n : ℕ) (v : K) :
    (actualLaw theta h0 h1 eta (n+1)).toMeasure.real {h |
      ¬riskEverFailure (fun x=>x∉K) (n+1) h ∧riskLastState (n+1) h=v.val}=
      rho theta^(n+1)*fair v :=by
  unfold actualLaw
  rw [actual_survival_terminal_mass_eq_killed_pow,
    SameSourceQSDBindingCheck.safeInitialRow_map_subtype]
  convert arbitrary_positive_power theta h0 h1 (fun v=>(eta v).toReal) (coverage_sum_toReal eta) n v using 1
  congr!

theorem actual_survival_mass (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1)
    (eta : PMF K) (n : ℕ) :
    (actualLaw theta h0 h1 eta (n+1)).toMeasure.real {h |
      ¬riskEverFailure (fun x=>x∉K) (n+1) h}=rho theta^(n+1) :=by
  unfold actualLaw
  rw [actual_survival_mass_eq_killed_pow_sum,
    SameSourceQSDBindingCheck.safeInitialRow_map_subtype]
  convert arbitrary_survival_power theta h0 h1 (fun v=>(eta v).toReal) (coverage_sum_toReal eta) n using 1
  congr!

theorem actual_survival_pos (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1)
    (eta : PMF K) (n : ℕ) :
    0<(actualLaw theta h0 h1.le eta (n+1)).toMeasure.real {h |
      ¬riskEverFailure (fun x=>x∉K) (n+1) h} :=by
  rw [actual_survival_mass]
  exact pow_pos (by unfold rho;linarith) _

/-- Mathlib's REAL filter/map conditional terminal, not a supplied normalized
row, becomes fair after every positive horizon for ANY safe initial law. -/
theorem actual_conditioned_terminal (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1)
    (eta : PMF K) (n : ℕ) :
    actualConditionedTerminal M id (fun _ : State=>actionLaw theta h0 h1.le)
      (eta.map Subtype.val) K (n+1) (actual_survival_pos theta h0 h1 eta n)=
      fairPMF.map Subtype.val :=by
  have hn : normalizedKilledTerminal M id (fun _ : State=>actionLaw theta h0 h1.le)
      (eta.map Subtype.val) K (n+1) (actual_survival_pos theta h0 h1 eta n)=fairPMF :=by
    apply PMF.ext
    intro v
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [normalizedKilledTerminal_apply_toReal,←actual_survival_terminal_mass_eq_killed_pow]
    have hterm:=actual_terminal_mass theta h0 h1.le eta n v
    have hmass:=actual_survival_mass theta h0 h1.le eta n
    unfold actualLaw at hterm hmass
    rw [hterm,hmass,fairPMF_real]
    have hr : rho theta≠0:=by unfold rho;linarith
    field_simp [hr]
  rw [actual_conditioned_terminal_eq_normalized_killed_map,hn]

/-- Time0 preserves the arbitrary initial law; it is not a fairizing step. -/
theorem time_zero_row (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (eta : K→ℝ) :
    rowApply eta ((Q theta h0 h1)^0)=eta :=by
  funext v
  simp [rowApply,Matrix.one_apply]

theorem actual_time_zero_mass (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (eta : PMF K) :
    (actualLaw theta h0 h1 eta 0).toMeasure.real {h |
      ¬riskEverFailure (fun x=>x∉K) 0 h}=1 :=by
  unfold actualLaw
  rw [actual_survival_mass_eq_killed_pow_sum,SameSourceQSDBindingCheck.safeInitialRow_map_subtype]
  have hh : ∑v : K,rowApply (fun v=>(eta v).toReal) ((Q theta h0 h1)^0) v=1:=by
    rw [time_zero_row]
    exact coverage_sum_toReal eta
  convert hh using 1
  congr!

theorem theta_one_survival_zero (eta : PMF K) (n : ℕ) :
    (actualLaw 1 (by norm_num) le_rfl eta (n+1)).toMeasure.real {h |
      ¬riskEverFailure (fun x=>x∉K) (n+1) h}=0 :=by
  rw [actual_survival_mass]
  simp [rho]

theorem theta_zero_survival_one (eta : PMF K) (n : ℕ) :
    (actualLaw 0 le_rfl (by norm_num) eta (n+1)).toMeasure.real {h |
      ¬riskEverFailure (fun x=>x∉K) (n+1) h}=1 :=by
  rw [actual_survival_mass]
  simp [rho]

theorem theta_one_no_qsd (q : K→ℝ) (r : ℝ) :
    ¬KilledQSDGOA (Q 1 (by norm_num) le_rfl) q r :=by
  intro h
  have hs:=qsd_survival_mass _ q r h.2.2.2.1 h.2.2.2.2.2
  have hz : ∑v : K,rowApply q (Q 1 (by norm_num) le_rfl) v=0 :=by
    simp [rowApply,Q_entry,rho]
  rw [hz] at hs
  have hr:=h.2.2.2.2.1
  linarith

/-- Actually consume the original positive-eigenstructure stationary law. -/
theorem actual_doob_invariant (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1) :
    ∀v,UEOT.V3.Compression.PositiveEigenstructure.rowApply
      (UEOT.V3.Compression.PositiveEigenstructure.invariantWeight (biData theta h0 h1))
      (UEOT.V3.Compression.PositiveEigenstructure.hTransform (biData theta h0 h1).right) v=
      UEOT.V3.Compression.PositiveEigenstructure.invariantWeight (biData theta h0 h1) v :=
  UEOT.V3.Compression.PositiveEigenstructure.invariantWeight_stationary (biData theta h0 h1)

/-- The same actual conditioning operation at time0 returns eta, including
at theta1 where no positive future survival is available. -/
theorem actual_conditioned_time_zero (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) (eta : PMF K) :
    actualConditionedTerminal M id (fun _ : State=>actionLaw theta h0 h1)
      (eta.map Subtype.val) K 0 (by rw [show
        (causalLaw (eta.map Subtype.val) (riskMicroControlKernel id (fun _=>M.transitionPMF)
          (observationMarkovPolicy (fun _ : State=>actionLaw theta h0 h1))) 0).toMeasure.real
            {h | ¬riskEverFailure (fun x=>x∉K) 0 h}=1 from actual_time_zero_mass theta h0 h1 eta];norm_num)=
      eta.map Subtype.val :=by
  rw [actual_conditioned_terminal_eq_normalized_killed_map]
  congr 1
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [normalizedKilledTerminal_apply_toReal,SameSourceQSDBindingCheck.safeInitialRow_map_subtype]
  have hm:=actual_time_zero_mass theta h0 h1 eta
  unfold actualLaw at hm
  rw [hm,div_one]
  convert congrFun (time_zero_row theta h0 h1 (fun v=>(eta v).toReal)) v using 1
  congr!

theorem time_zero_delta_not_fair (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1) :
    rowApply (fun v=>(PMF.pure (safeEquiv false) v).toReal)
      ((Q theta h0 h1)^0) (safeEquiv false)≠fair (safeEquiv false) :=by
  rw [time_zero_row]
  norm_num [fair]

theorem theta_one_no_positive_conditioning (eta : PMF K) (n : ℕ) :
    ¬0<(actualLaw 1 (by norm_num) le_rfl eta (n+1)).toMeasure.real {h |
      ¬riskEverFailure (fun x=>x∉K) (n+1) h} :=by
  rw [theta_one_survival_zero]
  exact lt_irrefl _

/-- Consumes the ORIGINAL GOA all-step QSD endpoint with constructed data. -/
theorem original_goa_all_steps (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1) :
    ∀T v,rowApply fair ((Q theta h0 h1.le)^T) v/rho theta^T=fair v :=by
  exact killedQSDGOA_all_steps (Q theta h0 h1.le) fair (rho theta)
    (actual_qsd_goa theta h0 h1)

/-- Actual Doob equals the safe restriction of the SAME model at theta0. -/
theorem doob_eq_actual_safe (theta : ℝ) (h0 : 0≤theta) (h1 : theta<1) :
    UEOT.V3.Compression.PositiveEigenstructure.hTransform (biData theta h0 h1).right=
      Q 0 le_rfl (by norm_num) :=by
  funext x y
  rw [actual_doob_fair,Q_entry]
  norm_num [rho]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricQSD
