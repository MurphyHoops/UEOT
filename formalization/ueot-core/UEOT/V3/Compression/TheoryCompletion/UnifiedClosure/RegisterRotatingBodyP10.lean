import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyReturns
import UEOT.V3.RecoveryProbability
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

/-!
Original promise: original P10 recovery must consume actual time-dependent body execution, not a supplied conditional drift certificate.
Existing result: SAME ongoing complete raw/record source and exact round return tail are constructed from original allowed actions and the registered Fin n sweep.
Reduced premise: derive actual future body-defect conditional mean under the ENTIRE previous raw history, then directly call original p_rec_01 mean/tail consumers.
Model/boundary: macro k means exactly n*k executed transactions, original initial parent retained; new BodyGoal=allports b, fresh original modes/labels and known deterministic phase, no reset/action/observation/supply added.
Consumer: original RecoveryProbability.p_rec_01 on the SAME raw probability law/actual parent defect with kappa0 and derived body noise floor, plus prior genuine return tails; not all-body P5, permanent safety, strategy optimality or a general time-varying World.

The full-raw-past filtration is an ANALYSIS sigma algebra containing past
mode/label outcomes; those outcomes are not passed to the controller. It is
stronger than the original actual physical/action observation history and
future independent modes still give the proved conditional drift. Actual
initial defect is computed from the registered original body at macro0, not
from a success-selected/prepared restart after the first round.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyP10
open MeasureTheory ProbabilityTheory Set Filter
open RegisterRepairSource RegisterRepairHistory RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterRotatingBodyReturns
open UEOT.V3.RecoveryProbability
open scoped ENNReal Topology
noncomputable section

/-- ALL completed primitive outcomes before round k; this is not a controller
input or an added observation channel. -/
def fullPast (n : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (RoundStream n)) where
  seq k:=⨆j : ℕ,⨆(_ : j<k),MeasurableSpace.comap (fun w : RoundStream n=>w j) inferInstance
  mono' := by
    intro a c hac
    exact iSup₂_le fun j hj=>le_iSup_of_le j (le_iSup_of_le (lt_of_lt_of_le hj hac) le_rfl)
  le' k:=iSup₂_le fun j _=>(measurable_pi_apply j).comap_le

theorem previous_raw_measurable {n : ℕ} {j k : ℕ} (h : j<k) :
    Measurable[fullPast n k] (fun w : RoundStream n=>w j) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le j (le_iSup_of_le h le_rfl)


local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

/-- Every actually observed earlier fee/fault/child record is measurable in
this analysis past. Finite raw factors avoid arbitrary list-to-discrete claims. -/
theorem previous_record_measurable {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n)
    {r k : ℕ} (hr : r<k) (j : Fin n) : Measurable[fullPast n k] (recordAt b cost o r j) := by
  cases r with
  | zero=>
    let F : RoundRaw n→ModeRecord n:=fun raw=>(roundTrace b cost raw o).get
      ⟨j,by simpa only [roundTrace,trace_length,List.length_finRange] using j.isLt⟩
    exact (measurable_of_finite F).comp (previous_raw_measurable hr)
  | succ r=>
    let F : RoundRaw n×RoundRaw n→ModeRecord n:=fun raw=>(roundTrace b cost raw.2 (closedParent b raw.1 o)).get
      ⟨j,by simpa only [roundTrace,trace_length,List.length_finRange] using j.isLt⟩
    have he : recordAt b cost o (r+1) j=fun w=>F (w r,w (r+1)) := by
      funext w
      let G : Organism n→ModeRecord n:=fun parent=>(roundTrace b cost (w (r+1)) parent).get
        ⟨j,by simpa only [roundTrace,trace_length,List.length_finRange] using j.isLt⟩
      exact congrArg G (actual_parent_closed b cost o w r)
    rw [he]
    exact (measurable_of_finite F).comp
      ((previous_raw_measurable (show r<k by omega)).prodMk (previous_raw_measurable hr))

/-- Original actual initial body severity, and SAME actual parent after each
executed round. No finite-probability failure is deleted or reinitialized. -/
def defect {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (k : ℕ) (w : RoundStream n) : ℝ≥0∞ := by
  classical
  exact if BodyGoal b (parentAt b cost o w k).physical then 0 else 1

def badScore {n : ℕ} (raw : RoundRaw n) : ℝ := by
  classical
  exact if Good raw then 0 else 1

theorem defect_succ {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (k : ℕ) (w : RoundStream n) :
    defect b cost o (k+1) w=ENNReal.ofReal (badScore (w k)) := by
  classical
  simp only [defect,actual_macro_goal_iff,badScore]
  by_cases h : Good (w k) <;> simp [h]

theorem defect_measurable {n : ℕ} (b : Bool) (cost : NNReal) (o : Organism n) (k : ℕ) : Measurable (defect b cost o k) := by
  cases k with
  | zero=>
    classical
    change Measurable (fun _ : RoundStream n=>if BodyGoal b o.physical then (0 : ℝ≥0∞) else 1)
    exact measurable_const
  | succ k=>
    have he : defect b cost o (k+1)=fun w=>ENNReal.ofReal (badScore (w k)):=funext (defect_succ b cost o k)
    rw [he]
    exact ENNReal.measurable_ofReal.comp ((measurable_of_finite (badScore (n:=n))).comp (measurable_pi_apply k))

def failureRate (n : ℕ) (epsilon : NNReal) : NNReal:=1-(1-epsilon)^n

@[simp] theorem failureRate_coe (n : ℕ) (epsilon : NNReal) :
    (failureRate n epsilon : ℝ≥0∞)=1-successMass n epsilon := by
  simp [failureRate,successMass,ENNReal.coe_sub,ENNReal.coe_pow]

/-- Independence is from the ENTIRE prior raw history (all previous labels,
faults/repairs), stronger than only the current physical state. -/
theorem current_indep_fullPast (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (k : ℕ) :
    Indep (MeasurableSpace.comap (fun w : RoundStream n=>w k) inferInstance)
      (fullPast n k) (infiniteLaw n noise epsilon he) := by
  have hd : Disjoint ({k} : Set ℕ) {j | j<k} := by simp
  have hi:=indep_iSup_of_disjoint (fun j : ℕ=>(measurable_pi_apply j).comap_le)
    (actual_round_independent n noise epsilon he).iIndep hd
  simpa only [iSup_singleton,fullPast,Set.mem_ofPred_eq] using hi

private theorem badScore_bound {n : ℕ} (raw : RoundRaw n) : ‖badScore raw‖≤1 := by
  classical
  unfold badScore
  split_ifs <;> norm_num

private theorem badScore_integral (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (k : ℕ) :
    (∫w,badScore (w k) ∂infiniteLaw n noise epsilon he)=(failureRate n epsilon : ℝ) := by
  have hs:=good_measurable n
  have hm : roundLaw n noise epsilon he {raw | Good raw}ᶜ=1-successMass n epsilon := by
    rw [measure_compl hs (measure_ne_top _ _),good_mass]
    simp
  have hf : badScore (n:=n)=({raw : RoundRaw n | Good raw}ᶜ).indicator (fun _=>1) := by
    funext raw
    classical
    by_cases h : Good raw <;> simp [badScore,h]
  have hI : (∫w,badScore (w k) ∂infiniteLaw n noise epsilon he)=
      ∫raw,badScore raw ∂roundLaw n noise epsilon he := by
    rw [←actual_round_law n noise epsilon he k,
      integral_map (measurable_pi_apply k).aemeasurable (measurable_of_finite (badScore (n:=n))).aestronglyMeasurable]
  rw [hI,hf,integral_indicator_const _ hs.compl]
  change (roundLaw n noise epsilon he {raw | Good raw}ᶜ).toReal*1=_
  rw [hm,mul_one]
  simpa only [ENNReal.coe_toReal] using (congrArg ENNReal.toReal (failureRate_coe n epsilon)).symm

/-- Native real conditional expectation follows from the actual product
independence and actual score mean, with no conditional-mean field supplied. -/
theorem actual_score_condExp (n : ℕ) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (k : ℕ) :
    (infiniteLaw n noise epsilon he)[fun w=>badScore (w k)|fullPast n k]=ᵐ[infiniteLaw n noise epsilon he]
      fun _=>(failureRate n epsilon : ℝ) := by
  have hs : StronglyMeasurable[MeasurableSpace.comap (fun w : RoundStream n=>w k) inferInstance]
      (fun w=>badScore (w k)) :=
    ((measurable_of_finite (badScore (n:=n))).comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  simpa only [badScore_integral] using
    condExp_indep_eq (measurable_pi_apply k).comap_le (fullPast n |>.le k) hs
      (current_indep_fullPast n noise epsilon he k)

/-- Actual source DISCHARGES original P10's conditional-Lebesgue drift input.
No assumptions about iid records/overlapping micro goal indicators are used. -/
theorem actual_p10_conditional_drift {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (o : Organism n) (k : ℕ) :
    (infiniteLaw n noise epsilon he)⁻[defect b cost o (k+1)|fullPast n k] ≤ᵐ[infiniteLaw n noise epsilon he]
      fun w=>(0 : NNReal)*defect b cost o k w+(failureRate n epsilon : ℝ≥0∞) := by
  let mu:=infiniteLaw n noise epsilon he
  have hm : Measurable (fun w : RoundStream n=>badScore (w k)) :=
    (measurable_of_finite (badScore (n:=n))).comp (measurable_pi_apply k)
  have hi : Integrable (fun w : RoundStream n=>badScore (w k)) mu :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun w=>badScore_bound (w k)))
  have hn : 0≤ᵐ[mu] (fun w : RoundStream n=>badScore (w k)) := by
    apply Eventually.of_forall
    intro w
    classical
    change (0 : ℝ)≤badScore (w k)
    unfold badScore
    split_ifs <;> norm_num
  have hc:=condLExp_ofReal (fullPast n k) hi hn
  have hCE:=actual_score_condExp n noise epsilon he k
  have heq : defect b cost o (k+1)=fun w=>ENNReal.ofReal (badScore (w k)):=funext (defect_succ b cost o k)
  rw [heq]
  filter_upwards [hc,hCE] with w hw hCE
  rw [hw,hCE]
  simp

private theorem initial_defect_finite {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (o : Organism n) :
    ennMean (infiniteLaw n noise epsilon he) (defect b cost o) 0<∞ := by
  classical
  unfold ennMean defect
  change (∫⁻w,if BodyGoal b o.physical then (0 : ℝ≥0∞) else 1 ∂infiniteLaw n noise epsilon he)<∞
  split_ifs <;> simp

/-- ORIGINAL p_rec_01 mean consumer, with the actual initial body and SAME
complete ongoing source. The noise floor is derived, not supplied. -/
theorem original_p10_body_mean {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (o : Organism n) (k : ℕ) :
    realMean (infiniteLaw n noise epsilon he) (defect b cost o) (k+1)≤(failureRate n epsilon : ℝ) := by
  have h:=p_rec_01_mean_bound (infiniteLaw n noise epsilon he) (fullPast n) (defect b cost o)
    0 (failureRate n epsilon) (by norm_num) (defect_measurable b cost o)
    (actual_p10_conditional_drift b cost noise epsilon he o) (initial_defect_finite b cost noise epsilon he o) (k+1)
  simpa using h

/-- ORIGINAL p_rec_01 tail consumer on the SAME actual initial body/source.
The event is the new whole-body failure, never old single-port legitimacy. -/
theorem original_p10_body_tail {n : ℕ} (b : Bool) (cost : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (o : Organism n) (k : ℕ) :
    (infiniteLaw n noise epsilon he).real {w | ¬BodyGoal b (parentAt b cost o w (k+1)).physical}≤(failureRate n epsilon : ℝ) := by
  have h:=p_rec_01_tail_bound (infiniteLaw n noise epsilon he) (fullPast n) (defect b cost o)
    0 (failureRate n epsilon) 1 (by norm_num) (by norm_num) (defect_measurable b cost o)
    (actual_p10_conditional_drift b cost noise epsilon he o) (initial_defect_finite b cost noise epsilon he o) (k+1)
  have hs : {w : RoundStream n | ((1 : NNReal) : ℝ≥0∞)≤defect b cost o (k+1) w}=
      {w | ¬BodyGoal b (parentAt b cost o w (k+1)).physical} := by
    classical
    ext w
    unfold defect
    by_cases hh : BodyGoal b (parentAt b cost o w (k+1)).physical <;> simp [hh]
  simpa only [hs,NNReal.coe_zero,NNReal.coe_one,zero_pow (Nat.succ_ne_zero k),zero_mul,
    sub_zero,div_one,mul_one,zero_add] using h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterRotatingBodyP10
