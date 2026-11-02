import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricSource
import UEOT.V3.FiniteCesaroInvariant
import UEOT.V3.FiniteDobrushin
import UEOT.V3.FiniteRecurrentDecompositionStability

/-!
M21.1–2: derive the stationary/finite-average claims from the ORIGINAL action
mixture and transition PMF. The source row and initial law are not new table
inputs. Both theta endpoints remain included; initial time is not silently
replaced by the stationary law.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricStationary
open MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.CoreOperationalAssembly UEOT.V3.FiniteDiscountedControl UEOT.V3.PathError
open UEOT.V3.FiniteCesaroInvariant
open ConflictParametricSource
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace State := ⊤
local instance : DecidableEq State :=Classical.decEq State

def P (theta : ℝ) : Matrix State State ℝ :=closedMatrix theta

variable (theta : ℝ) (h0 : 0≤theta) (h1 : theta≤1)

/-- Every actual input probability law reaches mu in ONE original step. -/
theorem actual_one_step (p : PMF State) : p.bind (closedRow theta h0 h1)=mu theta h0 h1 :=by
  have he : closedRow theta h0 h1=fun _=>mu theta h0 h1:=funext (closedRow_eq_mu theta h0 h1)
  rw [he]
  exact PMF.bind_const _ _

theorem actual_invariant : (mu theta h0 h1).bind (closedRow theta h0 h1)=mu theta h0 h1 :=
  actual_one_step theta h0 h1 _

theorem actual_invariant_unique (p : PMF State)
    (hp : p.bind (closedRow theta h0 h1)=p) : p=mu theta h0 h1 :=
  hp.symm.trans (actual_one_step theta h0 h1 p)

def ofPMF (p : PMF State) : stdSimplex ℝ State :=
  ⟨fun x=>(p x).toReal,fun _=>ENNReal.toReal_nonneg,coverage_sum_toReal p⟩

def initial : PMF State :=PMF.pure (true,false)

include h0 h1 in
theorem matrix_stochastic : P theta∈Matrix.rowStochastic ℝ State :=by
  apply (Matrix.mem_rowStochastic_iff_sum (M:=(closedMatrix theta : Matrix State State ℝ))).mpr
  constructor
  · intro x y
    change 0≤closedMatrix theta x y
    rw [←closedRow_real theta h0 h1]
    exact ENNReal.toReal_nonneg
  · intro x
    change ∑y,closedMatrix theta x y=1
    simp_rw [←closedRow_real theta h0 h1 x]
    exact coverage_sum_toReal _

/-- Real row action of the SAME original PMF kernel, for every normalized
row (including rows with zero coordinates). -/
theorem normalized_row_step (eta : State→ℝ) (hsum : ∑x,eta x=1) :
    Matrix.vecMul eta (P theta)=fun y=>(mu theta h0 h1 y).toReal :=by
  funext y
  rw [mu_real]
  simp only [Matrix.vecMul,dotProduct,P,closedMatrix]
  rw [←Finset.sum_mul,hsum,one_mul]

theorem orbit_after_one (p : PMF State) (t : ℕ) :
    (orbit (P theta) (matrix_stochastic theta h0 h1) (ofPMF p) (t+1) : State→ℝ)=
      fun y=>(mu theta h0 h1 y).toReal :=by
  rw [orbit_succ]
  exact normalized_row_step theta h0 h1 _ (stdSimplex.sum_eq_one _)

/-- This law keeps the actual original stationary state histories. -/
def actualMarginal (p : PMF State) (t : ℕ) : PMF State :=
  (causalLaw p (policyPathKernel M (policy theta h0 h1)) t).map (currentState t)

private theorem extend_map_snd {A X : Type*} (p : PMF A) (K : A→PMF X) :
    (pmfExtend p K).map Prod.snd=p.bind K :=by
  unfold pmfExtend
  rw [PMF.map_bind]
  congr 1
  funext a
  rw [PMF.map_comp]
  exact PMF.map_id _

theorem actual_marginal_after_one (p : PMF State) (t : ℕ) :
    actualMarginal theta h0 h1 p (t+1)=mu theta h0 h1 :=by
  change (pmfExtend _ _).map Prod.snd=_
  rw [extend_map_snd]
  have he : (policyPathKernel M (policy theta h0 h1) t)=
      fun _=>mu theta h0 h1 :=by
    funext h
    exact (policyTransitionPMF_eq theta h0 h1 _).trans (closedRow_eq_mu theta h0 h1 _)
  rw [he]
  exact PMF.bind_const _ _

theorem actual_marginal_orbit (p : PMF State) (t : ℕ) :
    (fun y=>(actualMarginal theta h0 h1 p t y).toReal)=
      (orbit (P theta) (matrix_stochastic theta h0 h1) (ofPMF p) t : State→ℝ) :=by
  cases t with
  | zero=>
      rw [orbit_zero]
      change (fun y=>((p.map id) y).toReal)=fun y=>(p y).toReal
      rw [PMF.map_id]
  | succ t=>rw [actual_marginal_after_one,orbit_after_one]

/-- Literal Dobrushin coefficient of the actual closed matrix, not merely
an upper estimate. The two parameter endpoints have the same zero margin. -/
theorem rowPMF_eq_mu (x : State) :
    UEOT.V3.FiniteDobrushin.rowPMF (P theta) (matrix_stochastic theta h0 h1) x=mu theta h0 h1 :=by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [UEOT.V3.FiniteDobrushin.rowPMF_toReal,mu_real]
  rfl

theorem row_tv_zero (x y : State) :
    UEOT.V3.FiniteDobrushin.rowTV (P theta) (matrix_stochastic theta h0 h1) x y=0 :=by
  simp only [UEOT.V3.FiniteDobrushin.rowTV,FiniteProbabilityRow.tvDist]
  exact UEOT.V3.TotalVariation.tvDist_self_eq_zero _

theorem dobrushin_zero :
    UEOT.V3.FiniteDobrushin.dobrushinAlpha (P theta) (matrix_stochastic theta h0 h1)=0 :=by
  unfold UEOT.V3.FiniteDobrushin.dobrushinAlpha
  have he : (fun z : State×State=>UEOT.V3.FiniteDobrushin.rowTV (P theta)
      (matrix_stochastic theta h0 h1) z.1 z.2)=fun _=>0:=funext (fun z=>row_tv_zero theta h0 h1 z.1 z.2)
  rw [he]
  simp

/-- Uses the original Cesaro operator with N=n+1 and the actual initial
point mass; all summands are the actual state marginals by the bridge above. -/
def actualCesaro (n : ℕ) : PMF State :=
  let c:=cesaroRow (P theta) (matrix_stochastic theta h0 h1) (ofPMF initial) n
  FiniteProbabilityRow.ofRealRow c.1 (fun y=>stdSimplex.zero_le c y) (stdSimplex.sum_eq_one c)

theorem cesaro_exact (n : ℕ) (y : State) :
    (actualCesaro theta h0 h1 n y).toReal=
      ((initial y).toReal+(n : ℝ)*(mu theta h0 h1 y).toReal)/((n+1 : ℕ) : ℝ) :=by
  rw [actualCesaro,FiniteProbabilityRow.ofRealRow_apply_toReal]
  simp only [cesaroRow,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  rw [Finset.sum_range_succ']
  have ha (t : ℕ) : (orbit (P theta) (matrix_stochastic theta h0 h1) (ofPMF initial) (t+1)) y=
      (mu theta h0 h1 y).toReal:=congrFun (orbit_after_one theta h0 h1 initial t) y
  simp_rw [ha]
  rw [show (orbit (P theta) (matrix_stochastic theta h0 h1) (ofPMF initial) 0) y=(initial y).toReal from
    congrFun (orbit_zero (P theta) (matrix_stochastic theta h0 h1) (ofPMF initial)) y]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

theorem cesaro_difference (n : ℕ) (y : State) :
    (actualCesaro theta h0 h1 n y).toReal-(mu theta h0 h1 y).toReal=
      ((initial y).toReal-(mu theta h0 h1 y).toReal)/((n+1 : ℕ) : ℝ) :=by
  rw [cesaro_exact]
  have hn : ((n+1 : ℕ) : ℝ)≠0:=by positivity
  push_cast
  field_simp
  ring

theorem initial_mu_l1 : ∑y : State,|(initial y).toReal-(mu theta h0 h1 y).toReal|=1+theta :=by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,mu_real,initial,PMF.pure_apply]
  norm_num
  have ha : 0≤theta/2:=by linarith
  have hb : 0≤(1-theta)/2:=by linarith
  have hc : 0≤1-(1-theta)/2:=by linarith
  rw [abs_of_nonneg hb,abs_of_nonneg hc,abs_of_nonneg ha]
  ring

/-- Exact canonical event-supremum TV, with its original 1/2 normalization. -/
theorem cesaro_tv_exact (n : ℕ) :
    UEOT.V3.TotalVariation.tvDist (actualCesaro theta h0 h1 n).toMeasure (mu theta h0 h1).toMeasure=
      (1+theta)/(2*((n+1 : ℕ) : ℝ)) :=by
  rw [UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs]
  simp_rw [cesaro_difference,abs_div]
  have hn : 0≤((n+1 : ℕ) : ℝ):=by positivity
  simp_rw [abs_of_nonneg hn]
  rw [←Finset.sum_div,initial_mu_l1]
  ring

/-- Exact original Cesaro boundary identity on these actual rows. -/
theorem cesaro_residual (n : ℕ) :
    Matrix.vecMul (fun y=>(actualCesaro theta h0 h1 n y).toReal) (P theta)-
      (fun y=>(actualCesaro theta h0 h1 n y).toReal)=
      fun y=>((mu theta h0 h1 y).toReal-(initial y).toReal)/((n+1 : ℕ) : ℝ) :=by
  rw [normalized_row_step theta h0 h1 _ (coverage_sum_toReal _)]
  ext y
  simp only [Pi.sub_apply]
  have hd:=cesaro_difference theta h0 h1 n y
  calc
    _=-((actualCesaro theta h0 h1 n y).toReal-(mu theta h0 h1 y).toReal):=by ring
    _=_:=by rw [hd];ring

/-- Complete original action records have exactly the same state marginal;
this consumes the existing action-erasure bridge rather than assuming it. -/
theorem original_action_marginal_after_one (p : PMF State) (t : ℕ) :
    (causalLaw p (riskMicroControlKernel id (fun _=>M.transitionPMF)
      (historyPolicy theta h0 h1)) (t+1)).map (riskLastState (t+1))=mu theta h0 h1 :=by
  have hh:=SourcePolicyPathBridgeCheck.actual_state_path_eq_stationary_path M id
    (fun _ : State=>actionLaw theta h0 h1) p (t+1)
  have he:=congrArg (fun law : PMF (CausalHistory State State (t+1))=>law.map (currentState (t+1))) hh
  rw [PMF.map_comp] at he
  change (causalLaw p (riskMicroControlKernel id (fun _=>M.transitionPMF)
      (historyPolicy theta h0 h1)) (t+1)).map (riskLastState (t+1))=
    actualMarginal theta h0 h1 p (t+1) at he
  exact he.trans (actual_marginal_after_one theta h0 h1 p t)

theorem actual_tv_strong_convergence (p : PMF State) :
    Tendsto (fun t : ℕ=>UEOT.V3.TotalVariation.tvDist
      (actualMarginal theta h0 h1 p t).toMeasure (mu theta h0 h1).toMeasure) atTop (𝓝 0) :=by
  have he : ∀ᶠ t : ℕ in atTop,UEOT.V3.TotalVariation.tvDist
      (actualMarginal theta h0 h1 p t).toMeasure (mu theta h0 h1).toMeasure=0 :=by
    filter_upwards [Ici_mem_atTop (1 : ℕ)] with t ht
    cases t with
    | zero=>norm_num at ht
    | succ t=>rw [actual_marginal_after_one];exact UEOT.V3.TotalVariation.tvDist_self_eq_zero _
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem actual_cesaro_tv_convergence :
    Tendsto (fun n : ℕ=>UEOT.V3.TotalVariation.tvDist
      (actualCesaro theta h0 h1 n).toMeasure (mu theta h0 h1).toMeasure) atTop (𝓝 0) :=by
  have hi : Tendsto (fun n : ℕ=>(((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have he : (fun n : ℕ=>UEOT.V3.TotalVariation.tvDist
      (actualCesaro theta h0 h1 n).toMeasure (mu theta h0 h1).toMeasure)=
      fun n : ℕ=>(1+theta)/2*(((n+1 : ℕ) : ℝ))⁻¹ :=by
    funext n
    rw [cesaro_tv_exact]
    ring
  rw [he]
  simpa only [mul_zero] using (tendsto_const_nhds.mul hi :
    Tendsto (fun n : ℕ=>(1+theta)/2*(((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 ((1+theta)/2*0)))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ConflictParametricStationary
