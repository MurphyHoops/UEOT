import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RationalConditionedSource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RowwiseProbeSampling
import Mathlib.Tactic

/-! One real source for training, conditioning and noisy deployment. Training
reset/readout is separate from constant-observation deployment. Preparation is
one actual allowed operation, including its cemetery mass. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
open UEOT.V3.PathError UEOT.V3.FiniteDiscountedControl UEOT.V3.CoreOperationalAssembly
open FiniteActionRealizabilityCheck ConditionedActionTransportCheck
open scoped BigOperators
noncomputable section
abbrev State := Fin 3
abbrev Action := Fin 3
structure Param where
  r0 : ℝ
  r1 : ℝ
  e0 : ℝ
  e1 : ℝ

def Admissible (p : Param) : Prop :=
  0 < p.r0 ∧ p.r0 ≤ 1 ∧ 0 < p.r1 ∧ p.r1 ≤ 1 ∧
  0 ≤ p.e0 ∧ p.e0 ≤ 1 ∧ 0 ≤ p.e1 ∧ p.e1 ≤ 1

def Box (p : Param) : Prop :=
  (2/3 : ℝ) ≤ p.r0 ∧ p.r0 ≤ 5/6 ∧ (1/6 : ℝ) ≤ p.r1 ∧ p.r1 ≤ 1/3 ∧
  0 ≤ p.e0 ∧ p.e0 ≤ 1/20 ∧ 0 ≤ p.e1 ∧ p.e1 ≤ 1/20

theorem box_admissible {p : Param} (h : Box p) : Admissible p := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    h4, by linarith, h6, by linarith⟩

def transition (p : Param) (x : State) (a : Action) : State → ℝ :=
  if x = 2 then ![0,0,1] else
  if a = 0 then let r := if x = 0 then p.r0 else p.r1; ![r/2,r/2,1-r] else
  if a = 1 then ![1-p.e0,0,p.e0] else ![0,1-p.e1,p.e1]

theorem transition_nonneg (p : Param) (hp : Admissible p) (x a z : Fin 3) :
    0 ≤ transition p x a z := by
  rcases hp with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  fin_cases x <;> fin_cases a <;> fin_cases z <;> simp [transition] <;> linarith

theorem transition_sum_one (p : Param) (x a : Fin 3) :
    ∑ z, transition p x a z = 1 := by
  fin_cases x <;> fin_cases a <;> simp [transition, Fin.sum_univ_succ] <;> ring

def model (p : Param) (hp : Admissible p) : Model State (fun _ => Action) where
  transition := transition p
  reward := fun _ _ => 0
  rewardBound := 1
  discount := 1/2
  transition_nonneg := transition_nonneg p hp
  transition_sum_one := transition_sum_one p
  reward_abs_le := by intros; norm_num
  discount_pos := by norm_num
  discount_lt_one := by norm_num

def safePMF (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) : PMF State :=
  FiniteProbabilityRow.ofRealRow ![v,1-v,0]
    (by intro x; fin_cases x <;> simp <;> linarith [hv.1,hv.2])
    (by simp [Fin.sum_univ_succ])

@[simp] theorem safePMF_real (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) (x : State) :
    (safePMF v hv x).toReal = ![v,1-v,0] x :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

def initial : PMF State := safePMF (1/2) (by norm_num)
def fair : PMF State := initial

def tilt (p : Param) : ℝ := p.r0 / (p.r0+p.r1)

theorem tilt_valid (p : Param) (hp : Admissible p) : 0 ≤ tilt p ∧ tilt p ≤ 1 := by
  have hs : 0 < p.r0+p.r1 := add_pos hp.1 hp.2.2.1
  exact ⟨div_nonneg hp.1.le hs.le, (div_le_one hs).mpr (by linarith [hp.2.2.1])⟩

def nu (p : Param) (hp : Admissible p) : PMF State := safePMF (tilt p) (tilt_valid p hp)

/-- Same literal action weights; risk has zero mass. -/
def selection (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) : PMF Action :=
  FiniteProbabilityRow.ofRealRow ![0,v,1-v]
    (by intro a; fin_cases a <;> simp <;> linarith [hv.1,hv.2])
    (by simp [Fin.sum_univ_succ])

@[simp] theorem selection_real (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) (a : Action) :
    (selection v hv a).toReal = ![0,v,1-v] a :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

def observe (_ : State) : Unit := ()
def baseline (_ : Unit) : PMF Action := PMF.pure 0

def selectedRow (p : Param) (hp : Admissible p) (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1)
    (x : State) : PMF State := actionMixture ((model p hp).transitionPMF x) (selection v hv)

/-- Derived from the true source and one literal allowed preparation action;
this unknown law is not an input probability vector supplied to the learner. -/
def prepared (p : Param) (hp : Admissible p) (v : ℝ) (hv : 0 ≤ v ∧ v ≤ 1) : PMF State :=
  initial.bind (selectedRow p hp v hv)

def targetRow (p : Param) (hp : Admissible p) (T t : ℕ) (_ : State) : PMF State :=
  if t+1<T then nu p hp else fair

def target (p : Param) (hp : Admissible p) (T : ℕ) :=
  targetPath (if T=0 then initial else nu p hp) (targetRow p hp T) T

/-- Deterministic data-selected rule, with a shared fair final action. -/
def controller (estimate : Param) (he : Admissible estimate) (T t : ℕ) (_ : Unit) : PMF Action :=
  if t+1<T then selection (tilt estimate) (tilt_valid estimate he)
  else selection (1/2) (by norm_num)

/-- T+1 actual operations, projected to the complete post-preparation T-window.
Cemetery trajectories and preparation failure remain present. -/
def deployed (p : Param) (hp : Admissible p) (estimate : Param) (he : Admissible estimate)
    (T : ℕ) :=
  causalLaw (prepared p hp (tilt estimate) (tilt_valid estimate he))
    (timeMixtureKernel (model p hp) observe (controller estimate he T)) T

/-- Four Bernoulli probes in the frozen training order. -/
def probeParameter (p : Param) : Fin 4 → ℝ := ![p.r0,p.r1,p.e0,p.e1]
def Good (p estimate : Param) (d : ℝ) : Prop :=
  ∀ j, |probeParameter p j - probeParameter estimate j| ≤ d
end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteDataSource
