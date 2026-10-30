import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBodyCanonicalPath

/-!
Original promise: original P10 must bound the actual first registered body recovery time, with its source/canonical-kernel/initial-clock semantics fixed.
Existing source: actual physicalPath equals native homTrajMeasure for the literal macro sweep; independent original rounds give exact no-return tails.
Premise reduced: derive actual stopping/measurable hitting readout, exact geometric expectation and original p_rec04 Lyapunov inputs from this source.
Model/boundary: tau observes round ENDS (k actual transactions/round), includes initial time0, and does not execute a new stop/reset; it is NOT the earliest within-round micro hit.
Consumer: SAME actual source and original p_rec_04_hitting_time_bound; initial-good0, initial-bad inverse success mass, zero-size/total-fault boundaries explicit; no resource/discount-unit change.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBodyHittingSource
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.DynamicsKernel UEOT.V3.RecoveryHittingNonnegative UEOT.V3.RecoveryHittingFirstStep UEOT.V3.RecoveryHittingBound
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterRotatingBodySource RegisterRotatingBodyReturns RegisterBodyCanonicalPath
open scoped ENNReal Topology Classical
noncomputable section

/-- The ORIGINAL declared whole-k-body target, tested at registered boundaries. -/
def target {k : ℕ} (b : Bool) : Set (State k):={x | BodyGoal b x}
theorem target_measurable (k : ℕ) (b : Bool) : MeasurableSet (target (k:=k) b):=(Set.toFinite _).measurableSet

/-- First actual registered macro hit, with infinity for never. The protocol
continues executing; this is an observed mathematical stopping time. -/
def tau {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) : RoundStream k→WithTop ℕ:=
  hittingAfter (fun r w=>physicalPath b fee o w r) (target b) 0

theorem tau_stopping {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) :
    IsStoppingTime (RegisterRotatingBodyP10.fullPast k) (tau b fee o) :=
  (physical_adapted b fee o).isStoppingTime_hittingAfter (target_measurable k b)
@[fun_prop] theorem measurable_tau {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) : Measurable (tau b fee o) :=
  (tau_stopping b fee o).measurable'

def survives {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (r : ℕ) : Set (RoundStream k):=
  physicalPath b fee o ⁻¹' survivalSet (target b) r

theorem survives_measurable {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (r : ℕ) : MeasurableSet (survives b fee o r) :=
  (measurableSet_survivalSet (target_measurable k b) r).preimage (measurable_physicalPath b fee o)

theorem tau_le_iff {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (w : RoundStream k) (r : ℕ) :
    tau b fee o w ≤ WithTop.some r ↔ ∃j≤r,physicalPath b fee o w j∈target b :=by
  unfold tau
  rw [MeasureTheory.hittingAfter_le_iff]
  simp only [Set.mem_Icc,Nat.zero_le,true_and]

theorem survives_iff_tau {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (w : RoundStream k) (r : ℕ) :
    w∈survives b fee o r ↔ WithTop.some r<tau b fee o w :=by
  change physicalPath b fee o w∈survivalSet (target b) r ↔ _
  rw [mem_survivalSet_iff,←not_le,tau_le_iff]
  simp only [not_exists,not_and]

/-- Literal original nonnegative hitting functional; the tail identity below
binds it to THIS first stopping time, not a chosen independent time variable. -/
def tauValue {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (w : RoundStream k) : ℝ≥0∞:=
  hittingValue (target b) (physicalPath b fee o w)
@[fun_prop] theorem measurable_tauValue {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) : Measurable (tauValue b fee o) :=
  (measurable_hittingValue (target_measurable k b)).comp (measurable_physicalPath b fee o)

theorem actual_tau_tail_sum {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (w : RoundStream k) :
    tauValue b fee o w=∑'r,(survives b fee o r).indicator (fun _=>(1 : ℝ≥0∞)) w :=by
  change (⨆N : ℕ,∑r∈Finset.range N,(survives b fee o r).indicator (fun _=>(1 : ℝ≥0∞)) w)=_
  exact ENNReal.tsum_eq_iSup_nat.symm

def meanTau {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism k) : ℝ≥0∞:=
  ∫⁻w,tauValue b fee o w ∂infiniteLaw k noise epsilon he

/-- SAME actual-source expectation is the original canonical P-REC quantity. -/
theorem mean_eq_original {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism k) :
    meanTau b fee noise epsilon he o=expectedHittingTime (bodyKernel k b noise epsilon he) o.physical (target b) :=by
  rw [expectedHittingTime,←actual_canonical_path_law b fee noise epsilon he o,
    lintegral_map (measurable_hittingValue (target_measurable k b)) (measurable_physicalPath b fee o)]
  rfl

/-- Outside the actual initial target, surviving through macro r means missing
exactly r already executed rounds; macro0 is not an extra noise draw. -/
theorem actual_survival_mass {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1)
    (o : Organism k) (ho : ¬BodyGoal b o.physical) (r : ℕ) :
    infiniteLaw k noise epsilon he (survives b fee o r)=(1-successMass k epsilon)^r :=by
  have hE : survives b fee o r={w | ∀j∈Finset.range r,¬BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee o w (j+1)).physical} :=by
    ext w
    rw [Set.mem_ofPred_eq]
    change physicalPath b fee o w∈survivalSet (target b) r ↔ _
    rw [mem_survivalSet_iff]
    constructor
    · intro h j hj
      exact h (j+1) (by simpa only [Finset.mem_range] using Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    · intro h j hj
      cases j with
      | zero=>exact ho
      | succ j=>exact h j (Finset.mem_range.mpr (Nat.lt_of_succ_le hj))
  rw [hE]
  simpa only [zero_add] using actual_no_return_tail b fee noise epsilon he o 0 r

theorem bodyState_goal_iff {k : ℕ} (b : Bool) (z : RoundRaw k) : BodyGoal b (bodyState b z) ↔ Good z :=by
  constructor
  · intro h j
    have hh:=h j
    cases b <;> cases hm:(z j).1 <;> simp [bodyState,hm] at hh ⊢
  · intro h j
    simp [bodyState,h j]

theorem bodyLaw_target (k : ℕ) (b : Bool) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) :
    bodyLaw k b noise epsilon he (target b)=successMass k epsilon :=by
  rw [bodyLaw,Measure.map_apply (measurable_of_finite _) (target_measurable k b)]
  have hE : bodyState b ⁻¹' target b={z : RoundRaw k | Good z} :=by ext z;exact bodyState_goal_iff b z
  rw [hE,good_mass]

theorem success_le_one (k : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) : successMass k epsilon≤1 :=by
  rw [←bodyLaw_target k true noise epsilon he]
  exact prob_le_one

/-- Genuine expected first registered hit. It is zero if already in target,
and inverse success mass otherwise; p0 gives infinity without division tricks. -/
theorem actual_mean_exact {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism k) :
    meanTau b fee noise epsilon he o=if BodyGoal b o.physical then 0 else (successMass k epsilon)⁻¹ :=by
  classical
  by_cases ho : BodyGoal b o.physical
  · have hz (w : RoundStream k) : tauValue b fee o w=0 :=by
      unfold tauValue hittingValue truncatedHittingValue
      have hs (r : ℕ) : physicalPath b fee o w∉survivalSet (target b) r :=by
        intro hh
        exact (mem_survivalSet_iff _ _ _).mp hh 0 (Nat.zero_le r) ho
      simp [hs]
    simp [meanTau,hz,ho]
  · rw [if_neg ho]
    unfold meanTau
    simp_rw [actual_tau_tail_sum]
    rw [lintegral_tsum (fun r=>(measurable_const.indicator (survives_measurable b fee o r)).aemeasurable)]
    simp_rw [lintegral_indicator_const (survives_measurable b fee o _),one_mul,
      actual_survival_mass b fee noise epsilon he o ho]
    rw [ENNReal.tsum_geometric,ENNReal.sub_sub_cancel (by simp) (success_le_one k noise epsilon he)]

/-- Nonnegative source Lyapunov potential; NO desired drift field is input. -/
def potential {k : ℕ} (b : Bool) (x : State k) : ℝ≥0∞:=if x∈target b then 0 else 1

/-- Original uniform P-REC-04 drift, derived from the real success event. -/
theorem actual_source_drift {k : ℕ} (b : Bool) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1)
    (x : State k) (hx : x∉target b) :
    (∫⁻y,potential b y ∂bodyKernel k b noise epsilon he x)+successMass k epsilon≤potential b x :=by
  classical
  have hp : potential (k:=k) b=(target b)ᶜ.indicator (fun _=>(1 : ℝ≥0∞)) :=by
    funext z
    by_cases hz : z∈target b <;> simp [potential,hz]
  rw [bodyKernel,Kernel.const_apply,hp,lintegral_indicator_const (target_measurable k b).compl 1,one_mul,
    measure_compl (target_measurable k b) (measure_ne_top _ _),measure_univ,bodyLaw_target]
  rw [Set.indicator_of_mem (show x∈(target b)ᶜ from hx)]
  rw [tsub_add_cancel_of_le (success_le_one k noise epsilon he)]

/-- ORIGINAL p_rec04 is actually called with the derived kernel and drift;
its expectation is exactly the actual retained-parent round-end hitting time. -/
theorem original_p_rec_04_actual {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon<1) (o : Organism k) :
    meanTau b fee noise epsilon he.le o≤potential b o.physical/successMass k epsilon :=by
  rw [mean_eq_original]
  exact p_rec_04_hitting_time_bound (bodyKernel k b noise epsilon he.le) o.physical (target b) (potential b) (successMass k epsilon)
    (target_measurable k b) (measurable_of_finite _) (successMass_pos k epsilon he).ne'
    (ne_top_of_le_ne_top (by simp) (success_le_one k noise epsilon he.le))
    (actual_source_drift b noise epsilon he.le)

/-- Counting the true survival tails is exactly the first registered hit. -/
theorem tauValue_of_finite {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k)
    (w : RoundStream k) (n : ℕ) (hn : tau b fee o w=WithTop.some n) :
    tauValue b fee o w=(n : ℝ≥0∞) :=by
  classical
  rw [actual_tau_tail_sum]
  calc
    (∑'r,(survives b fee o r).indicator (fun _=>(1 : ℝ≥0∞)) w)=
        ∑r∈Finset.range n,(survives b fee o r).indicator (fun _=>(1 : ℝ≥0∞)) w :=by
      apply tsum_eq_sum
      intro r hr
      have hnr : n≤r:=by simpa only [Finset.mem_range,not_lt] using hr
      have hx : w∉survives b fee o r :=by
        rw [survives_iff_tau,hn]
        exact not_lt.mpr (WithTop.coe_le_coe.mpr hnr)
      simp [hx]
    _ = ∑_r∈Finset.range n,(1 : ℝ≥0∞) :=by
      apply Finset.sum_congr rfl
      intro r hr
      have hx : w∈survives b fee o r :=by
        rw [survives_iff_tau,hn]
        exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hr)
      simp [hx]
    _ = (n : ℝ≥0∞) :=by simp

theorem tauValue_of_infinite {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k)
    (w : RoundStream k) (hn : tau b fee o w=⊤) : tauValue b fee o w=∞ :=by
  rw [actual_tau_tail_sum]
  have hx (r : ℕ) : w∈survives b fee o r :=by
    rw [survives_iff_tau,hn]
    exact WithTop.coe_lt_top r
  simp only [Set.indicator_of_mem (hx _)]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem tau_initial_goal {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k)
    (ho : BodyGoal b o.physical) (w : RoundStream k) : tau b fee o w=0 :=by
  apply le_antisymm _ bot_le
  apply (tau_le_iff b fee o w 0).mpr
  exact ⟨0,le_rfl,ho⟩

theorem mean_initial_goal {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon≤1) (o : Organism k) (ho : BodyGoal b o.physical) :
    meanTau b fee noise epsilon he o=0 :=by rw [actual_mean_exact,if_pos ho]

theorem mean_zero_body (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon≤1) (o : Organism 0) :
    meanTau b fee noise epsilon he o=0 :=by
  apply mean_initial_goal
  intro j
  exact Fin.elim0 j

/-- Total-fault impossibility concerns the actual law, not impossible raw words. -/
theorem tau_total_fault {k : ℕ} (hk : 0<k) (b : Bool) (fee : NNReal)
    (noise : PMF Bool) (o : Organism k) (ho : ¬BodyGoal b o.physical) :
    ∀ᵐ w ∂infiniteLaw k noise 1 (by norm_num),tau b fee o w=⊤ :=by
  filter_upwards [total_fault_no_body_round hk b fee noise o] with w hw
  unfold tau
  rw [hittingAfter_eq_top_iff]
  intro j _
  cases j with
  | zero=>exact ho
  | succ j=>exact hw j

theorem mean_total_fault {k : ℕ} (hk : 0<k) (b : Bool) (fee : NNReal)
    (noise : PMF Bool) (o : Organism k) (ho : ¬BodyGoal b o.physical) :
    meanTau b fee noise 1 (by norm_num) o=∞ :=by
  rw [actual_mean_exact,if_neg ho]
  simp [successMass,Nat.ne_of_gt hk]

/-- Nonzero success gives a genuinely finite expectation of THIS stopping time. -/
theorem mean_finite {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon<1) (o : Organism k) :
    meanTau b fee noise epsilon he.le o<∞ :=by
  rw [actual_mean_exact]
  split_ifs
  · exact ENNReal.zero_lt_top
  · exact ENNReal.inv_lt_top.mpr (successMass_pos k epsilon he)

/-- Actual positive success implies the stopping time itself is finite AE. -/
theorem tau_finite_ae {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon<1) (o : Organism k) :
    ∀ᵐ w ∂infiniteLaw k noise epsilon he.le,tau b fee o w<⊤ :=by
  filter_upwards [actual_returns_forever b fee noise epsilon he o] with w hw
  obtain ⟨j,_hj,hbody⟩:=hw 0
  exact lt_of_le_of_lt ((tau_le_iff b fee o w (j+1)).mpr ⟨j+1,le_rfl,hbody⟩)
    (WithTop.coe_lt_top (j+1))

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBodyHittingSource
