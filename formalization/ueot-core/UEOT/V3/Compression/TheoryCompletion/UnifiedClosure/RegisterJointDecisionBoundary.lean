import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationHistorySource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionSource

/-!
Parameter consequences of the NEW joint-decision protocol, from original Store
transactions. Goal=true is public, the tariff is public, theta selects a normal
execution probability once. This file never reads protected programs or parent
identities to choose a request. The fourth request below uses the second birth
receipt only. The original labels, failed ticks and None slots remain in Store.

These source-value and boundary theorems complement the general solver and its
source bridge. Pairwise inequalities are not silently promoted to global
optimality; finite consumers separately bind the actual returned table.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionBoundary
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultJointRecord RegisterJointRecord
open RegisterPopulationHistorySource
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open scoped BigOperators
noncomputable section

def mechanism (c : NNReal) : Mechanism := ⟨true,c⟩
def initial : Store 1 := founders [⟨[],fun _ => false,true⟩]
def request (parent : ℕ) (a : Action) (mode label : Bool) : Request :=
  ⟨parent,a,mode,label⟩

/-- The original complete transaction, including literal fee and actual child. -/
def nativeReward (price : NNReal) : Option (ClockedRecord 1) → ℝ
  | none => 0
  | some r => RegisterJointRecord.payoff price
      (RegisterTimestampedBirthSource.eraseRecord r).transaction

def nativeTotal (c price : NNReal) (d : ℝ) :
    Store 1 → List Request → ℝ
  | _, [] => 0
  | s, q :: qs => nativeReward price (transaction 0 (mechanism c) s q) +
      d * nativeTotal c price d (next 0 (mechanism c) s q) qs

def twoRequests (b₀ b₁ l₀ l₁ : Bool) : List Request :=
  [request 0 (some true) b₀ l₀,request 0 none b₁ l₁]

def threeRequests (b₀ b₁ b₂ l₀ l₁ l₂ : Bool) : List Request :=
  [request 0 (some true) b₀ l₀,request 0 none b₁ l₁,request 1 none b₂ l₂]

def rootThreeRequests (b₀ b₁ b₂ l₀ l₁ l₂ : Bool) : List Request :=
  [request 0 (some true) b₀ l₀,request 0 none b₁ l₁,request 0 none b₂ l₂]

def fixedFourRequests (b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃ : Bool) : List Request :=
  [request 0 (some true) b₀ l₀,request 0 none b₁ l₁,
   request 1 none b₂ l₂,request 0 none b₃ l₃]

/-- The only branch reads the already delivered second birth receipt. It does
not inspect a Store, mode, physical bit, protected program or identity at run
time; this constructor computes that receipt from the original source for the
purpose of the complete-record expectation proof. -/
def feedbackFourRequests (c : NNReal)
    (b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃ : Bool) : List Request :=
  let q₀ := request 0 (some true) b₀ l₀
  let q₁ := request 0 none b₁ l₁
  let s₁ := next 0 (mechanism c) initial q₀
  let secondBirth := (child 0 (mechanism c) s₁ q₁).isSome
  [q₀,q₁,request 1 none b₂ l₂,
   request (if secondBirth then 0 else 1) none b₃ l₃]

theorem two_path_value (c price : NNReal) (d : ℝ)
    (b₀ b₁ l₀ l₁ : Bool) :
    nativeTotal c price d initial (twoRequests b₀ b₁ l₀ l₁) =
      if b₀ then 1 - (price : ℝ)*c + d*(if b₁ then 1 else 0) else 0 := by
  cases b₀ <;> cases b₁ <;>
    simp [nativeTotal,nativeReward,twoRequests,initial,request,mechanism,
      founders,next,transaction,lookup,child,RegisterTimestampedBirthSource.step,
      RegisterTimestampedBirthSource.eraseRecord,modeRecordStep,recordStep,
      payoff,childCount,cost,birthEvent,repairEvent,execute_compiled,update]

theorem three_path_value (c price : NNReal) (d : ℝ)
    (b₀ b₁ b₂ l₀ l₁ l₂ : Bool) :
    nativeTotal c price d initial (threeRequests b₀ b₁ b₂ l₀ l₁ l₂) =
      if b₀ then 1 - (price : ℝ)*c +
        d*(if b₁ then 1 else 0) + d^2*(if b₂ then 1 else 0) else 0 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;>
    simp [nativeTotal,nativeReward,threeRequests,initial,request,mechanism,
      founders,next,transaction,lookup,child,RegisterTimestampedBirthSource.step,
      RegisterTimestampedBirthSource.eraseRecord,modeRecordStep,recordStep,
      payoff,childCount,cost,birthEvent,repairEvent,execute_compiled,update] <;> ring

theorem root_three_path_value (c price : NNReal) (d : ℝ)
    (b₀ b₁ b₂ l₀ l₁ l₂ : Bool) :
    nativeTotal c price d initial (rootThreeRequests b₀ b₁ b₂ l₀ l₁ l₂) =
      if b₀ then 1 - (price : ℝ)*c +
        d*(if b₁ then 1 else 0) + d^2*(if b₁ && b₂ then 1 else 0) else 0 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;>
    simp [nativeTotal,nativeReward,rootThreeRequests,initial,request,mechanism,
      founders,next,transaction,lookup,child,RegisterTimestampedBirthSource.step,
      RegisterTimestampedBirthSource.eraseRecord,modeRecordStep,recordStep,
      payoff,childCount,cost,birthEvent,repairEvent,execute_compiled,update] <;> ring

theorem fixed_four_path_value (c price : NNReal) (d : ℝ)
    (b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃ : Bool) :
    nativeTotal c price d initial (fixedFourRequests b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃) =
      if b₀ then 1 - (price : ℝ)*c + d*(if b₁ then 1 else 0) +
        d^2*(if b₂ then 1 else 0) + d^3*(if b₁ && b₃ then 1 else 0) else 0 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;>
    simp [nativeTotal,nativeReward,fixedFourRequests,initial,request,mechanism,
      founders,next,transaction,lookup,child,RegisterTimestampedBirthSource.step,
      RegisterTimestampedBirthSource.eraseRecord,modeRecordStep,recordStep,
      payoff,childCount,cost,birthEvent,repairEvent,execute_compiled,update] <;> ring

theorem feedback_four_path_value (c price : NNReal) (d : ℝ)
    (b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃ : Bool) :
    nativeTotal c price d initial (feedbackFourRequests c b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃) =
      if b₀ then 1 - (price : ℝ)*c + d*(if b₁ then 1 else 0) +
        d^2*(if b₂ then 1 else 0) +
        d^3*(if (b₁ || b₂) && b₃ then 1 else 0) else 0 := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;>
    simp [nativeTotal,nativeReward,feedbackFourRequests,initial,request,mechanism,
      founders,next,transaction,lookup,child,RegisterTimestampedBirthSource.step,
      RegisterTimestampedBirthSource.eraseRecord,modeRecordStep,recordStep,
      payoff,childCount,cost,birthEvent,repairEvent,execute_compiled,update] <;> ring

/-- Real Bernoulli row. For 0<=r<=1 this is the old source's modeProbability
with epsilon=1-r, not a re-draw of the unknown mechanism. -/
def chance (r : ℝ) (b : Bool) : ℝ := if b then r else 1-r

theorem chance_sum (r : ℝ) : ∑ b : Bool, chance r b = 1 := by
  simp [chance]
theorem chance_nonneg (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (b : Bool) :
    0 ≤ chance r b := by
  cases b <;> simp [chance] <;> linarith
theorem chance_eq_original (epsilon : NNReal) (b : Bool) :
    chance (1-(epsilon : ℝ)) b =
      RegisterFaultControlModel.modeProbability epsilon b := by
  cases b <;> simp [chance,RegisterFaultControlModel.modeProbability,
    RegisterFaultControlModel.repairChance]

def expectedTwo (r : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  ∑ b₀ : Bool, ∑ b₁ : Bool, chance r b₀ * chance r b₁ *
    nativeTotal c price d initial (twoRequests b₀ b₁ false false)
def expectedThree (r : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool,
    chance r b₀ * chance r b₁ * chance r b₂ *
      nativeTotal c price d initial (threeRequests b₀ b₁ b₂ false false false)
def expectedRootThree (r : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool,
    chance r b₀ * chance r b₁ * chance r b₂ *
      nativeTotal c price d initial (rootThreeRequests b₀ b₁ b₂ false false false)
def expectedFixedFour (r : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
    chance r b₀ * chance r b₁ * chance r b₂ * chance r b₃ *
      nativeTotal c price d initial (fixedFourRequests b₀ b₁ b₂ b₃ false false false false)
def expectedFeedbackFour (r : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
    chance r b₀ * chance r b₁ * chance r b₂ * chance r b₃ *
      nativeTotal c price d initial (feedbackFourRequests c b₀ b₁ b₂ b₃ false false false false)

theorem expected_two_eq (r : ℝ) (c price : NNReal) (d : ℝ) :
    expectedTwo r c price d = r*(1-(price : ℝ)*c) + d*r^2 := by
  simp only [expectedTwo,two_path_value]
  simp [chance]
  ring
theorem expected_three_eq (r : ℝ) (c price : NNReal) (d : ℝ) :
    expectedThree r c price d = r*(1-(price : ℝ)*c) + (d+d^2)*r^2 := by
  simp only [expectedThree,three_path_value]
  simp [chance]
  ring
theorem expected_root_three_eq (r : ℝ) (c price : NNReal) (d : ℝ) :
    expectedRootThree r c price d = r*(1-(price : ℝ)*c) + d*r^2 + d^2*r^3 := by
  simp only [expectedRootThree,root_three_path_value]
  simp [chance]
  ring
theorem expected_fixed_four_eq (r : ℝ) (c price : NNReal) (d : ℝ) :
    expectedFixedFour r c price d =
      r*(1-(price : ℝ)*c) + (d+d^2)*r^2 + d^3*r^3 := by
  simp only [expectedFixedFour,fixed_four_path_value]
  simp [chance]
  ring
theorem expected_feedback_four_eq (r : ℝ) (c price : NNReal) (d : ℝ) :
    expectedFeedbackFour r c price d =
      r*(1-(price : ℝ)*c) + (d+d^2)*r^2 + d^3*(2*r^3-r^4) := by
  simp only [expectedFeedbackFour,feedback_four_path_value]
  simp [chance]
  ring

/-- Arbitrary labels (including all failed-tick labels) give the same reward;
the parameter formulas below are not evaluations at a favorable sampled label. -/
theorem four_labels_irrelevant (c price : NNReal) (d : ℝ)
    (b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃ : Bool) :
    nativeTotal c price d initial (feedbackFourRequests c b₀ b₁ b₂ b₃ l₀ l₁ l₂ l₃) =
      nativeTotal c price d initial
        (feedbackFourRequests c b₀ b₁ b₂ b₃ false false false false) := by
  rw [feedback_four_path_value,feedback_four_path_value]

private theorem pmf_real_sum {L : Type*} [Fintype L] (q : PMF L) :
    ∑ l, (q l).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe q)
  rw [tsum_fintype,ENNReal.toReal_sum (fun l _ => PMF.apply_ne_top _ l)] at h
  simpa using h

/-- Average over ANY independently supplied label-word law. The original fair
i.i.d. labels are a special case; no record or failure is conditioned away. -/
def fullLabelFeedbackFour (r : ℝ) (labels : PMF (Fin 4 → Bool))
    (c price : NNReal) (d : ℝ) : ℝ :=
  ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
    chance r b₀ * chance r b₁ * chance r b₂ * chance r b₃ *
      ∑ l, (labels l).toReal * nativeTotal c price d initial
        (feedbackFourRequests c b₀ b₁ b₂ b₃ (l 0) (l 1) (l 2) (l 3))

theorem full_label_feedback_eq (r : ℝ) (labels : PMF (Fin 4 → Bool))
    (c price : NNReal) (d : ℝ) :
    fullLabelFeedbackFour r labels c price d = expectedFeedbackFour r c price d := by
  unfold fullLabelFeedbackFour expectedFeedbackFour
  simp_rw [four_labels_irrelevant c price d]
  simp only [← Finset.sum_mul,pmf_real_sum,one_mul]

/-- The SAME theta is outside the complete mode-word expectation. -/
def binaryMoment (w r₀ r₁ : ℝ) (k : ℕ) : ℝ :=
  w*r₀^k + (1-w)*r₁^k
def binaryTwo (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  w*expectedTwo r₀ c price d + (1-w)*expectedTwo r₁ c price d
def binaryThree (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  w*expectedThree r₀ c price d + (1-w)*expectedThree r₁ c price d
def binaryRootThree (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  w*expectedRootThree r₀ c price d + (1-w)*expectedRootThree r₁ c price d
def binaryFixedFour (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  w*expectedFixedFour r₀ c price d + (1-w)*expectedFixedFour r₁ c price d
def binaryFeedbackFour (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  w*expectedFeedbackFour r₀ c price d + (1-w)*expectedFeedbackFour r₁ c price d

theorem binary_two_eq (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) :
    binaryTwo w r₀ r₁ c price d =
      binaryMoment w r₀ r₁ 1*(1-(price : ℝ)*c) + d*binaryMoment w r₀ r₁ 2 := by
  simp [binaryTwo,expected_two_eq,binaryMoment]
  ring

theorem binary_three_eq (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) :
    binaryThree w r₀ r₁ c price d =
      binaryMoment w r₀ r₁ 1*(1-(price : ℝ)*c) +
        (d+d^2)*binaryMoment w r₀ r₁ 2 := by
  simp [binaryThree,expected_three_eq,binaryMoment]
  ring

theorem binary_feedback_four_eq (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) :
    binaryFeedbackFour w r₀ r₁ c price d =
      binaryMoment w r₀ r₁ 1*(1-(price : ℝ)*c) +
        (d+d^2)*binaryMoment w r₀ r₁ 2 +
        d^3*(2*binaryMoment w r₀ r₁ 3-binaryMoment w r₀ r₁ 4) := by
  simp [binaryFeedbackFour,expected_feedback_four_eq,binaryMoment]
  ring

theorem persistent_minus_redrawn (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) :
    binaryTwo w r₀ r₁ c price d -
      expectedTwo (binaryMoment w r₀ r₁ 1) c price d =
      d*w*(1-w)*(r₀-r₁)^2 := by
  simp [binaryTwo,expected_two_eq,binaryMoment]
  ring

theorem population_backup_gain (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) :
    binaryThree w r₀ r₁ c price d - binaryRootThree w r₀ r₁ c price d =
      d^2*(w*r₀^2*(1-r₀)+(1-w)*r₁^2*(1-r₁)) := by
  simp [binaryThree,binaryRootThree,expected_three_eq,expected_root_three_eq]
  ring

theorem receipt_feedback_gain (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) :
    binaryFeedbackFour w r₀ r₁ c price d - binaryFixedFour w r₀ r₁ c price d =
      d^3*(w*r₀^3*(1-r₀)+(1-w)*r₁^3*(1-r₁)) := by
  simp [binaryFeedbackFour,binaryFixedFour,expected_feedback_four_eq,expected_fixed_four_eq]
  ring

/-- A genuine open parameter region of positive receipt-feedback value, at
the SAME tariff, objective, available addresses and total cost. The differing
policy receives no extra primitive observation. -/
theorem receipt_feedback_strict (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ)
    (hw : 0 < w ∧ w < 1) (hr₀ : 0 < r₀ ∧ r₀ < 1)
    (hr₁ : 0 < r₁ ∧ r₁ < 1) (hd : 0 < d) :
    binaryFixedFour w r₀ r₁ c price d < binaryFeedbackFour w r₀ r₁ c price d := by
  have hw' : 0 < 1-w := by linarith
  have h₀ : 0 < 1-r₀ := by linarith
  have h₁ : 0 < 1-r₁ := by linarith
  have hg : 0 < binaryFeedbackFour w r₀ r₁ c price d -
      binaryFixedFour w r₀ r₁ c price d := by
    rw [receipt_feedback_gain]
    exact mul_pos (pow_pos hd 3)
      (add_pos
        (mul_pos (mul_pos hw.1 (pow_pos hr₀.1 3)) h₀)
        (mul_pos (mul_pos hw' (pow_pos hr₁.1 3)) h₁))
  linarith

theorem gain_pos_iff (mu bonus p : ℝ) (hmu : 0 < mu) :
    0 < mu*(1-p)+bonus ↔ p < 1+bonus/mu := by
  constructor
  · intro h
    have hb : (p-1)*mu < bonus := by nlinarith
    have hh := (lt_div_iff₀ hmu).mpr hb
    linarith
  · intro h
    have hh : p-1 < bonus/mu := by linarith
    have hb := (lt_div_iff₀ hmu).mp hh
    nlinarith

theorem gain_nonpos_iff (mu bonus p : ℝ) (hmu : 0 < mu) :
    mu*(1-p)+bonus ≤ 0 ↔ 1+bonus/mu ≤ p := by
  simpa only [not_lt] using not_congr (gain_pos_iff mu bonus p hmu)

theorem two_repair_boundary (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ)
    (hm : 0 < binaryMoment w r₀ r₁ 1) :
    0 < binaryTwo w r₀ r₁ c price d ↔
      (price : ℝ)*c < 1+d*binaryMoment w r₀ r₁ 2/binaryMoment w r₀ r₁ 1 := by
  rw [binary_two_eq]
  exact gain_pos_iff _ _ _ hm

theorem four_repair_boundary (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ)
    (hm : 0 < binaryMoment w r₀ r₁ 1) :
    0 < binaryFeedbackFour w r₀ r₁ c price d ↔
      (price : ℝ)*c <
        1+((d+d^2)*binaryMoment w r₀ r₁ 2+
          d^3*(2*binaryMoment w r₀ r₁ 3-binaryMoment w r₀ r₁ 4)) /
          binaryMoment w r₀ r₁ 1 := by
  rw [binary_feedback_four_eq]
  rw [add_assoc]
  exact gain_pos_iff _ _ _ hm

/-- Exact source diagnostics. These are theorem-checked arithmetic after the
original Store path equalities, not expected numbers fed into a model. -/
theorem original_two_step_diagnostic :
    binaryTwo (1/2) (1/4) (3/4) 1 (13/10) (1/2) = 1/160 ∧
      expectedTwo (1/2) 1 (13/10) (1/2) = -1/40 := by
  norm_num [binaryTwo,expected_two_eq]

theorem population_three_step_diagnostic :
    binaryThree (1/2) (1/4) (3/4) 1 (7/4) (3/4) = 9/256 ∧
      binaryRootThree (1/2) (1/4) (3/4) 1 (7/4) (3/4) = -9/512 := by
  norm_num [binaryThree,binaryRootThree,expected_three_eq,expected_root_three_eq]

theorem receipt_four_step_diagnostic :
    binaryFeedbackFour (1/2) (3/4) (7/8) 1 (37/16) (3/4) = 39525/524288 ∧
      binaryFixedFour (1/2) (3/4) (7/8) 1 (37/16) (3/4) = 2325/65536 ∧
      binaryFeedbackFour (1/2) (3/4) (7/8) 1 (37/16) (3/4) -
        binaryFixedFour (1/2) (3/4) (7/8) 1 (37/16) (3/4) = 20925/524288 := by
  norm_num [binaryFeedbackFour,binaryFixedFour,expected_feedback_four_eq,expected_fixed_four_eq]

/-- This retry comparator uses exactly the first public birth receipt. It
retries once after a free fault and spends at most the same one-write wallet.
It models the concrete frozen-prior decision error in the example below. -/
def retryThreeRequests (c : NNReal) (b₀ b₁ b₂ l₀ l₁ l₂ : Bool) : List Request :=
  let q₀ := request 0 (some true) b₀ l₀
  let firstBirth := (child 0 (mechanism c) initial q₀).isSome
  [q₀,request 0 (if firstBirth then none else some true) b₁ l₁,
   request (if firstBirth then 1 else 0) none b₂ l₂]

theorem first_write_receipt_from_primitive (c : NNReal) (mode label : Bool) :
    RegisterJointDecisionSource.nativeObs
      (transaction 0 (mechanism c) initial (request 0 (some true) mode label)) =
        (mode,mode) := by
  cases mode <;>
    simp [RegisterJointDecisionSource.nativeObs,transaction,lookup,initial,founders,
      request,mechanism,RegisterTimestampedBirthSource.step,modeRecordStep,recordStep,
      birthEvent,repairEvent,execute_compiled,update]

theorem first_write_failure_iff (c : NNReal) (mode label : Bool) :
    RegisterJointDecisionSource.nativeObs
      (transaction 0 (mechanism c) initial (request 0 (some true) mode label)) =
        (false,false) ↔ mode = false := by
  rw [first_write_receipt_from_primitive]
  cases mode <;> simp

theorem retry_three_path_value (c price : NNReal) (d : ℝ)
    (b₀ b₁ b₂ l₀ l₁ l₂ : Bool) :
    nativeTotal c price d initial (retryThreeRequests c b₀ b₁ b₂ l₀ l₁ l₂) =
      if b₀ then 1-(price : ℝ)*c+d*(if b₁ then 1 else 0)+d^2*(if b₂ then 1 else 0)
      else d*(if b₁ then 1-(price : ℝ)*c+d*(if b₂ then 1 else 0) else 0) := by
  cases b₀ <;> cases b₁ <;> cases b₂ <;>
    simp [nativeTotal,nativeReward,retryThreeRequests,initial,request,mechanism,
      founders,next,transaction,lookup,child,RegisterTimestampedBirthSource.step,
      RegisterTimestampedBirthSource.eraseRecord,modeRecordStep,recordStep,
      payoff,childCount,cost,birthEvent,repairEvent,execute_compiled,update] <;> ring

def expectedRetryThree (r : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  ∑ b₀ : Bool, ∑ b₁ : Bool, ∑ b₂ : Bool,
    chance r b₀*chance r b₁*chance r b₂ *
      nativeTotal c price d initial (retryThreeRequests c b₀ b₁ b₂ false false false)

theorem expected_retry_three_eq (r : ℝ) (c price : NNReal) (d : ℝ) :
    expectedRetryThree r c price d =
      r*(1-(price : ℝ)*c)+(d+d^2)*r^2+
        d*(1-r)*(r*(1-(price : ℝ)*c)+d*r^2) := by
  simp only [expectedRetryThree,retry_three_path_value]
  simp [chance]
  ring

def binaryRetryThree (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ) : ℝ :=
  w*expectedRetryThree r₀ c price d+(1-w)*expectedRetryThree r₁ c price d

/-- The failure likelihood is 1-r by first_write_failure_iff. This is Bayes'
weight for the actually observed free-fault receipt, not a new draw of theta. -/
def failureMass (w r₀ r₁ : ℝ) : ℝ := 1-binaryMoment w r₀ r₁ 1
def failedWriteLowWeight (w r₀ r₁ : ℝ) : ℝ := w*(1-r₀)/failureMass w r₀ r₁

theorem failure_mass_eq (w r₀ r₁ : ℝ) :
    failureMass w r₀ r₁ = w*(1-r₀)+(1-w)*(1-r₁) := by
  simp [failureMass,binaryMoment]
  ring

theorem failure_moment (w r₀ r₁ : ℝ) (k : ℕ)
    (hf : failureMass w r₀ r₁ ≠ 0) :
    binaryMoment (failedWriteLowWeight w r₀ r₁) r₀ r₁ k =
      (binaryMoment w r₀ r₁ k-binaryMoment w r₀ r₁ (k+1))/failureMass w r₀ r₁ := by
  have hf' : 1-(w*r₀+(1-w)*r₁) ≠ 0 := by
    simpa only [failureMass,binaryMoment,pow_one] using hf
  simp only [failedWriteLowWeight,failureMass,binaryMoment,pow_one]
  rw [pow_succ,pow_succ]
  field_simp [hf']
  ring

theorem failed_two_value (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ)
    (hf : failureMass w r₀ r₁ ≠ 0) :
    binaryTwo (failedWriteLowWeight w r₀ r₁) r₀ r₁ c price d =
      ((binaryMoment w r₀ r₁ 1-binaryMoment w r₀ r₁ 2)*(1-(price : ℝ)*c)+
        d*(binaryMoment w r₀ r₁ 2-binaryMoment w r₀ r₁ 3))/failureMass w r₀ r₁ := by
  rw [binary_two_eq,failure_moment w r₀ r₁ 1 hf,failure_moment w r₀ r₁ 2 hf]
  ring

theorem failed_repair_boundary (w r₀ r₁ : ℝ) (c price : NNReal) (d : ℝ)
    (hf : 0 < failureMass w r₀ r₁)
    (hm : 0 < binaryMoment w r₀ r₁ 1-binaryMoment w r₀ r₁ 2) :
    0 < binaryTwo (failedWriteLowWeight w r₀ r₁) r₀ r₁ c price d ↔
      (price : ℝ)*c < 1+d*(binaryMoment w r₀ r₁ 2-binaryMoment w r₀ r₁ 3) /
        (binaryMoment w r₀ r₁ 1-binaryMoment w r₀ r₁ 2) := by
  rw [failed_two_value w r₀ r₁ c price d hf.ne']
  constructor
  · intro h
    rcases (div_pos_iff).mp h with h | h
    · exact (gain_pos_iff _ _ _ hm).mp h.1
    · linarith [h.2]
  · intro h
    exact div_pos ((gain_pos_iff _ _ _ hm).mpr h) hf

/-- Failure makes future paid repair strictly less attractive throughout a
nondegenerate parameter region. This is a source-specific information result,
not just inclusion of one policy class in another. -/
theorem failure_lowers_repair_threshold (w r₀ r₁ d : ℝ)
    (hw : 0 < w ∧ w < 1) (hr₀ : 0 < r₀ ∧ r₀ < 1)
    (hr₁ : 0 < r₁ ∧ r₁ < 1) (hne : r₀ ≠ r₁) (hd : 0 < d) :
    1+d*(binaryMoment w r₀ r₁ 2-binaryMoment w r₀ r₁ 3)/
      (binaryMoment w r₀ r₁ 1-binaryMoment w r₀ r₁ 2) <
        1+d*binaryMoment w r₀ r₁ 2/binaryMoment w r₀ r₁ 1 := by
  have hw' : 0 < 1-w := by linarith
  have h₀ : 0 < 1-r₀ := by linarith
  have h₁ : 0 < 1-r₁ := by linarith
  have hm : 0 < binaryMoment w r₀ r₁ 1 := by
    simpa [binaryMoment] using add_pos (mul_pos hw.1 hr₀.1) (mul_pos hw' hr₁.1)
  have hg : binaryMoment w r₀ r₁ 1-binaryMoment w r₀ r₁ 2 =
      w*r₀*(1-r₀)+(1-w)*r₁*(1-r₁) := by simp [binaryMoment]; ring
  have hden : 0 < binaryMoment w r₀ r₁ 1-binaryMoment w r₀ r₁ 2 := by
    rw [hg]
    exact add_pos (mul_pos (mul_pos hw.1 hr₀.1) h₀) (mul_pos (mul_pos hw' hr₁.1) h₁)
  have hdet : binaryMoment w r₀ r₁ 1*binaryMoment w r₀ r₁ 3-
      (binaryMoment w r₀ r₁ 2)^2 = w*(1-w)*r₀*r₁*(r₀-r₁)^2 := by
    simp [binaryMoment]
    ring
  have hdetpos : 0 < binaryMoment w r₀ r₁ 1*binaryMoment w r₀ r₁ 3-
      (binaryMoment w r₀ r₁ 2)^2 := by
    rw [hdet]
    exact mul_pos (mul_pos (mul_pos (mul_pos hw.1 hw') hr₀.1) hr₁.1)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  have hfrac : (binaryMoment w r₀ r₁ 2-binaryMoment w r₀ r₁ 3)/
      (binaryMoment w r₀ r₁ 1-binaryMoment w r₀ r₁ 2) <
      binaryMoment w r₀ r₁ 2/binaryMoment w r₀ r₁ 1 := by
    apply (div_lt_div_iff₀ hden hm).mpr
    nlinarith
  simpa only [mul_div_assoc,add_comm] using
    add_lt_add_left (mul_lt_mul_of_pos_left hfrac hd) 1

/-- The same damaged state, remaining two ticks and unchanged wallet require
opposite actions after this LEGAL informative zero-charge failure receipt. -/
theorem posterior_switch_diagnostic :
    failedWriteLowWeight (1/2) (1/4) (3/4) = 3/4 ∧
      (1+(1/2)*binaryMoment (1/2) (1/4) (3/4) 2/
        binaryMoment (1/2) (1/4) (3/4) 1 : ℝ) = 21/16 ∧
      (1+(1/2)*(binaryMoment (1/2) (1/4) (3/4) 2-
        binaryMoment (1/2) (1/4) (3/4) 3)/
        (binaryMoment (1/2) (1/4) (3/4) 1-
        binaryMoment (1/2) (1/4) (3/4) 2) : ℝ) = 5/4 ∧
      binaryTwo (3/4) (1/4) (3/4) 1 (13/10) (1/2) = -3/160 := by
  norm_num [failedWriteLowWeight,failureMass,binaryMoment,binaryTwo,expected_two_eq]

/-- A same-menu, same-wallet, full-cost frozen-prior retry loses actual value.
The best fixed initial repair / idle / child-idle workflow is still equivalent
to the joint optimum in this instance; no universal adaptive advantage follows. -/
theorem posterior_retry_diagnostic :
    binaryThree (1/2) (1/4) (3/4) 1 (13/10) (1/2) = 27/320 ∧
      binaryRetryThree (1/2) (1/4) (3/4) 1 (13/10) (1/2) = 51/640 ∧
      binaryThree (1/2) (1/4) (3/4) 1 (13/10) (1/2)-
        binaryRetryThree (1/2) (1/4) (3/4) 1 (13/10) (1/2) = 3/640 := by
  norm_num [binaryThree,expected_three_eq,binaryRetryThree,expected_retry_three_eq]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionBoundary

