import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPriceProgram
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeInfinite

/-!
Original promise: finite purpose data must decide dynamic allowed-action control and the actual returned program, not just a one-step order.
Existing source: complete original two-write batch, birth/paid-cost-bin observations, original common birth-mean calibration and actual postProbeParent; all-price Bellman classification is proved.
Reduced premise: a NEW rational data-only selector brackets the true dynamic margin from observed cost bins and the complete goal-row birth mean; truth/means/epsilon/c never enter it.
Model/boundary: unchanged original N+N probes, failures, labels, source, actions, initial/program rights and evaluation; calibrated uncertainty or no informative birth yields UNKNOWN, not a retry.
Consumer: source-derived accepted literal AST is native GOD; joint accepted-wrong and separated-source UNKNOWN risks use the SAME original Hoeffding event. Actual post-probe infinite-record/P9 consumers follow in the narrow companion leaf.

Fee bins already measure actual paid costs. On an informative birth their bin
brackets c pointwise, so no new cost upper bound or fee-mean observation is
required. The complete goal-row birth mean estimates r without division by r.
This is a separate dynamic question/selector: the old select, threshold,
registered batches and one-step negative results remain unchanged. Formal
fixture registration: /tmp/ueot-dynamic-probe-preregistration.json.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbe
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.BoundedLossSampling
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultFinitePurposeProbe RegisterFaultDynamicPrice
open scoped BigOperators

/-- Complete observed row, rational arithmetic only. N=0 uses the native 0/0=0;
firstBirth on the empty registration still forces UNKNOWN. -/
def birthMean {N : ℕ} (data : Batch N) (b : Bool) : ℚ :=
  (∑ k : Fin N, if (data ⟨b,k⟩).1 then 1 else 0)/(N : ℚ)

def upperScore {N : ℕ} (price width d u : ℚ) (data : Batch N) (b : Bool) (k : ℕ) : ℚ :=
  price*((k+1 : ℕ) : ℚ)*width*(1-d*(birthMean data b-u))
def lowerScore {N : ℕ} (price width d u : ℚ) (data : Batch N) (b : Bool) (k : ℕ) : ℚ :=
  price*(k : ℚ)*width*(1-d*(birthMean data b+u))

def classify {N : ℕ} (price width d u : ℚ) (data : Batch N) : Verdict :=
  match firstBirth data (registration N) with
  | none=>.unknown
  | some (b,k)=>
    if upperScore price width d u data b k<1 then .repair b
    else if 1<lowerScore price width d u data b k then .idle b
    else .unknown

/-- Literal original allowed-action AST; UNKNOWN only supplies a fallback,
with no optimality assertion. No protected program is installed or changed. -/
def returnedAST {n : ℕ} (i : Fin n) : Verdict→Instruction n
  | .repair b=>compile i b
  | .idle _=>.emit none
  | .unknown=>.emit none

noncomputable section

theorem first_birth_source {N : ℕ} (m : Mechanism) (width : ℚ)
    (omega : Coordinate N→Bool×Bool) (js : List (Coordinate N)) (b : Bool) (k : ℕ)
    (h : firstBirth (sourceData m width omega) js=some (b,k)) :
    b=m.goal ∧ k=feeBin width m.writeCost := by
  induction js with
  | nil=>simp [firstBirth] at h
  | cons j js ih=>
    by_cases hb : (sourceData m width omega j).1=true
    · have he : (j.1,(sourceData m width omega j).2)=(b,k):=by simpa [firstBirth,hb] using h
      have hi:=informative_source m width omega j hb
      exact ⟨(congrArg Prod.fst he).symm.trans hi.1,(congrArg Prod.snd he).symm.trans hi.2⟩
    · exact ih (by simpa [firstBirth,hb] using h)

theorem birthMean_source {N : ℕ} (m : Mechanism) (width : ℚ)
    (omega : Coordinate N→Bool×Bool) (b : Bool) :
    (birthMean (sourceData m width omega) b : ℝ)=
      empiricalRisk birthScore (sourceSample m width b) omega := by
  simp only [birthMean,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,empiricalRisk]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  cases hb : (sourceData m width omega ⟨b,k⟩).1 <;> simp [birthScore,sourceSample,hb]

theorem good_repair_interval {N : ℕ} (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (width u : ℚ) (omega : Coordinate N→Bool×Bool)
    (hg : omega∈Good noise m epsilon he N width (u : ℝ)) :
    (birthMean (sourceData m width omega) m.goal : ℝ)-(u : ℝ)≤repairChance epsilon ∧
    repairChance epsilon≤(birthMean (sourceData m width omega) m.goal : ℝ)+(u : ℝ) := by
  have hb:=hg m.goal
  change |empiricalRisk birthScore (sourceSample m width m.goal) omega-
    trueRisk (row noise m epsilon he width m.goal).toMeasure birthScore|≤(u : ℝ) at hb
  rw [birth_mean,if_pos rfl,mul_one,←birthMean_source] at hb
  have hi:=abs_le.mp hb
  constructor <;> linarith

/-- Both sides bound the true margin from ONE common event and the actual
informative source bin. No division by a potentially zero r is performed. -/
theorem observed_margin_bounds {N : ℕ} (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1)
    (omega : Coordinate N→Bool×Bool) (b : Bool) (k : ℕ)
    (hb : firstBirth (sourceData m width omega) (registration N)=some (b,k))
    (hg : omega∈Good noise m epsilon he N width (u : ℝ)) :
    (lowerScore price width d u (sourceData m width omega) b k : ℝ)≤
      ((price : ℝ)*m.writeCost)*(1-(d : ℝ)*repairChance epsilon) ∧
    ((price : ℝ)*m.writeCost)*(1-(d : ℝ)*repairChance epsilon)≤
      (upperScore price width d u (sourceData m width omega) b k : ℝ) := by
  obtain ⟨hgoal,hbin⟩:=first_birth_source m width omega _ b k hb
  have hr:=good_repair_interval noise m epsilon he width u omega hg
  have hbox:=feeBin_bounds width hw m.writeCost m.writeCost.coe_nonneg
  rw [←hbin] at hbox
  have hpr : (0 : ℝ)≤price:=by exact_mod_cast hp
  have hwr : (0 : ℝ)<width:=by exact_mod_cast hw
  have hdr : 0<(d : ℝ) ∧ (d : ℝ)<1:=by exact_mod_cast hd
  have hden:=(idle_denominator_pos epsilon he (d : ℝ) hdr).le
  have hl : (price : ℝ)*(k : ℝ)*(width : ℝ)≤(price : ℝ)*m.writeCost := by
    nlinarith [mul_le_mul_of_nonneg_left hbox.1 hpr]
  have hh : (price : ℝ)*m.writeCost≤(price : ℝ)*((k : ℝ)+1)*(width : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hbox.2.le hpr]
  have hlpos : 0≤(price : ℝ)*(k : ℝ)*(width : ℝ):=by positivity
  have hhpos : 0≤(price : ℝ)*((k : ℝ)+1)*(width : ℝ):=by positivity
  have hfl : 1-(d : ℝ)*((birthMean (sourceData m width omega) b : ℝ)+(u : ℝ))≤1-(d : ℝ)*repairChance epsilon :=by
    rw [hgoal];nlinarith
  have hfh : 1-(d : ℝ)*repairChance epsilon≤1-(d : ℝ)*((birthMean (sourceData m width omega) b : ℝ)-(u : ℝ)) :=by
    rw [hgoal];nlinarith
  constructor
  · simp only [lowerScore,Rat.cast_mul,Rat.cast_sub,Rat.cast_add,Rat.cast_one,Rat.cast_natCast]
    exact (mul_le_mul_of_nonneg_left hfl hlpos).trans (mul_le_mul_of_nonneg_right hl hden)
  · simp only [upperScore,Rat.cast_mul,Rat.cast_sub,Nat.cast_add,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,Nat.cast_one]
    exact (mul_le_mul_of_nonneg_right hh hden).trans (mul_le_mul_of_nonneg_left hfh hhpos)

theorem classify_repair_sound {N : ℕ} (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (omega : Coordinate N→Bool×Bool)
    (hg : omega∈Good noise m epsilon he N width (u : ℝ)) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) :
    b=m.goal ∧ ((price : ℝ)*m.writeCost)*(1-(d : ℝ)*repairChance epsilon)<1 := by
  cases hx : firstBirth (sourceData m width omega) (registration N) with
  | none=>simp [classify,hx] at hs
  | some q=>
    rcases q with ⟨g,k⟩
    have hi:=first_birth_source m width omega _ g k hx
    have hm:=(observed_margin_bounds noise m epsilon he price width d u hp hw hd omega g k hx hg).2
    simp only [classify,hx] at hs
    split_ifs at hs with hc hn
    · have hb : g=b:=Verdict.repair.inj hs
      have hcr : (upperScore price width d u (sourceData m width omega) g k : ℝ)<1:=by exact_mod_cast hc
      exact ⟨hb.symm.trans hi.1,hm.trans_lt hcr⟩

theorem classify_idle_sound {N : ℕ} (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (omega : Coordinate N→Bool×Bool)
    (hg : omega∈Good noise m epsilon he N width (u : ℝ)) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.idle b) :
    b=m.goal ∧ 1<((price : ℝ)*m.writeCost)*(1-(d : ℝ)*repairChance epsilon) := by
  cases hx : firstBirth (sourceData m width omega) (registration N) with
  | none=>simp [classify,hx] at hs
  | some q=>
    rcases q with ⟨g,k⟩
    have hi:=first_birth_source m width omega _ g k hx
    have hm:=(observed_margin_bounds noise m epsilon he price width d u hp hw hd omega g k hx hg).1
    simp only [classify,hx] at hs
    split_ifs at hs with hc hn
    · have hb : g=b:=Verdict.idle.inj hs
      have hnr : (1 : ℝ)<(lowerScore price width d u (sourceData m width omega) g k : ℝ):=by exact_mod_cast hn
      exact ⟨hb.symm.trans hi.1,hnr.trans_le hm⟩

/-- Accepted actual data determine the SAME literal controller's native GOD,
including r0 weak ties; no positivity of r is inferred from an arbitrary tuple. -/
theorem good_accepted_god {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (omega : Coordinate N→Bool×Bool)
    (hg : omega∈Good noise m epsilon he N width (u : ℝ))
    (ha : classify price width d u (sourceData m width omega)≠.unknown) :
    IsBellmanGODSelector (model i noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd))
      (interpret (returnedAST i (classify price width d u (sourceData m width omega)))) := by
  have hdr : 0<(d : ℝ) ∧ (d : ℝ)<1:=by exact_mod_cast hd
  cases hv : classify price width d u (sourceData m width omega) with
  | unknown=>exact (ha hv).elim
  | repair b=>
    have hs:=classify_repair_sound noise m epsilon he price width d u hp hw hd omega hg b hv
    simp only [returnedAST]
    rw [hs.1]
    intro x
    rw [mem_bellmanGODCorrespondence_iff,←repair_value_eq_optimal i noise m (priceValue price hp) epsilon he (d : ℝ) hdr hs.2.le]
    exact compiled_attains_value i noise m (priceValue price hp) epsilon he (d : ℝ) hdr x
  | idle b=>
    have hs:=classify_idle_sound noise m epsilon he price width d u hp hw hd omega hg b hv
    intro x
    rw [mem_bellmanGODCorrespondence_iff,←idle_value_eq_optimal i noise m (priceValue price hp) epsilon he (d : ℝ) hdr hs.2.le]
    exact idle_attains_value i noise m (priceValue price hp) epsilon he (d : ℝ) hdr x

def Error {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon≤1) (price width d u : ℚ) (hp : 0≤price) (hd : 0<d ∧ d<1) : Set (Coordinate N→Bool×Bool) :=
  {omega | classify price width d u (sourceData m width omega)≠.unknown ∧
    ¬IsBellmanGODSelector (model i noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd))
      (interpret (returnedAST i (classify price width d u (sourceData m width omega))))}

theorem actual_joint_error_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) (hN : 0<N) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (hu : 0≤u) :
    (rawLaw noise epsilon he N).real (Error (N:=N) i noise m epsilon he price width d u hp hd)≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2)) := by
  have hsub : Error (N:=N) i noise m epsilon he price width d u hp hd⊆(Good noise m epsilon he N width (u : ℝ))ᶜ := by
    intro omega herr hg
    exact herr.2 (good_accepted_god i noise m epsilon he price width d u hp hw hd omega hg herr.1)
  exact (measureReal_mono hsub).trans (actual_probe_calibration noise m epsilon he N hN width (u : ℝ) (by exact_mod_cast hu)).2

/-- Source separation is only an analysis condition. It is never a selector
input. Twice the calibration radius accounts for estimating r and applying
one more conservative radius in the actual data certificate. -/
def DynamicallySeparated (m : Mechanism) (epsilon : NNReal) (price width d u : ℚ) : Prop :=
  let k:=feeBin width m.writeCost
  (price : ℝ)*((k : ℝ)+1)*(width : ℝ)*(1-(d : ℝ)*(repairChance epsilon-2*(u : ℝ)))<1 ∨
  1<(price : ℝ)*(k : ℝ)*(width : ℝ)*(1-(d : ℝ)*(repairChance epsilon+2*(u : ℝ)))

theorem good_decides {N : ℕ} (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon≤1) (price width d u : ℚ) (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1)
    (hsep : DynamicallySeparated m epsilon price width d u) (hr : (u : ℝ)<repairChance epsilon)
    (omega : Coordinate N→Bool×Bool) (hg : omega∈Good noise m epsilon he N width (u : ℝ)) :
    classify price width d u (sourceData m width omega)≠.unknown := by
  have hn : firstBirth (sourceData m width omega) (registration N)≠none := by
    intro hn
    have hs : select 0 width (sourceData m width omega)=.unknown:=by simp [select,hn]
    have hsep0 : RegisterFaultFinitePurposeProbe.Separated m 0 width:=by
      left
      simp
    exact (RegisterFaultFinitePurposeProbe.unknown_subset_bad noise m epsilon he N width 0 (u : ℝ) hsep0 hr hs) hg
  cases hx : firstBirth (sourceData m width omega) (registration N) with
  | none=>exact (hn hx).elim
  | some q=>
    rcases q with ⟨b,k⟩
    obtain ⟨hgoal,hbin⟩:=first_birth_source m width omega _ b k hx
    have hb:=good_repair_interval noise m epsilon he width u omega hg
    have hp' : (0 : ℝ)≤price:=by exact_mod_cast hp
    have hw' : (0 : ℝ)<width:=by exact_mod_cast hw
    have hd' : (0 : ℝ)<d:=by exact_mod_cast hd.1
    have hkl : 0≤(price : ℝ)*(k : ℝ)*(width : ℝ):=by positivity
    have hku : 0≤(price : ℝ)*((k : ℝ)+1)*(width : ℝ):=by positivity
    rcases hsep with hsep | hsep
    · have hupper : (upperScore price width d u (sourceData m width omega) b k : ℝ)<1 := by
        have hfac : 1-(d : ℝ)*((birthMean (sourceData m width omega) b : ℝ)-(u : ℝ))≤
            1-(d : ℝ)*(repairChance epsilon-2*(u : ℝ)):=by rw [hgoal];nlinarith
        have hh:=mul_le_mul_of_nonneg_left hfac hku
        simp only [upperScore,Rat.cast_mul,Rat.cast_sub,Nat.cast_add,Rat.cast_add,Rat.cast_one,Rat.cast_natCast,Nat.cast_one]
        exact hh.trans_lt (by simpa only [←hbin] using hsep)
      have hupperQ : upperScore price width d u (sourceData m width omega) b k<1:=by exact_mod_cast hupper
      simp [classify,hx,hupperQ]
    · have hlower : (1 : ℝ)<(lowerScore price width d u (sourceData m width omega) b k : ℝ) := by
        have hfac : 1-(d : ℝ)*(repairChance epsilon+2*(u : ℝ))≤
            1-(d : ℝ)*((birthMean (sourceData m width omega) b : ℝ)+(u : ℝ)):=by rw [hgoal];nlinarith
        have hh:=mul_le_mul_of_nonneg_left hfac hkl
        simp only [lowerScore,Rat.cast_mul,Rat.cast_sub,Rat.cast_add,Rat.cast_one,Rat.cast_natCast]
        have hs : 1<(price : ℝ)*(k : ℝ)*(width : ℝ)*(1-(d : ℝ)*(repairChance epsilon+2*(u : ℝ))) :=by
          simpa only [←hbin] using hsep
        exact hs.trans_le hh
      have hlowerQ : 1<lowerScore price width d u (sourceData m width omega) b k:=by exact_mod_cast hlower
      by_cases hc : upperScore price width d u (sourceData m width omega) b k<1 <;> simp [classify,hx,hc,hlowerQ]

theorem actual_unknown_bound (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon≤1) (N : ℕ) (hN : 0<N) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (hu : 0≤u)
    (hsep : DynamicallySeparated m epsilon price width d u) (hr : (u : ℝ)<repairChance epsilon) :
    (rawLaw noise epsilon he N).real {omega | classify price width d u (sourceData m width omega)=.unknown}≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2)) := by
  have hsub : {omega : Coordinate N→Bool×Bool | classify price width d u (sourceData m width omega)=.unknown}⊆
      (Good noise m epsilon he N width (u : ℝ))ᶜ := by
    intro omega hs hg
    exact good_decides noise m epsilon he price width d u hp hw hd hsep hr omega hg hs
  exact (measureReal_mono hsub).trans (actual_probe_calibration noise m epsilon he N hN width (u : ℝ) (by exact_mod_cast hu)).2

/-- The separated source gets one shared budget for UNKNOWN OR a wrong
accepted controller, rather than paying two unrelated error bounds. -/
theorem actual_undecided_or_wrong_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) (hN : 0<N) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (hu : 0≤u)
    (hsep : DynamicallySeparated m epsilon price width d u) (hr : (u : ℝ)<repairChance epsilon) :
    (rawLaw noise epsilon he N).real {omega |
      classify price width d u (sourceData m width omega)=.unknown ∨
      omega∈Error (N:=N) i noise m epsilon he price width d u hp hd}≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2)) := by
  have hsub : {omega : Coordinate N→Bool×Bool |
      classify price width d u (sourceData m width omega)=.unknown ∨
      omega∈Error (N:=N) i noise m epsilon he price width d u hp hd}⊆
      (Good noise m epsilon he N width (u : ℝ))ᶜ := by
    intro omega hbad hg
    rcases hbad with hunk | herr
    · exact good_decides noise m epsilon he price width d u hp hw hd hsep hr omega hg hunk
    · exact herr.2 (good_accepted_god i noise m epsilon he price width d u hp hw hd omega hg herr.1)
  exact (measureReal_mono hsub).trans (actual_probe_calibration noise m epsilon he N hN width (u : ℝ) (by exact_mod_cast hu)).2

@[simp] theorem zero_budget_unknown (price width d u : ℚ) (data : Batch 0) :
    classify price width d u data=.unknown :=by simp [classify,registration,firstBirth]

theorem total_fault_unknown_ae (noise : PMF Bool) (m : Mechanism) (N : ℕ) (price width d u : ℚ) :
    ∀ᵐ omega ∂rawLaw noise 1 (by norm_num) N,
      classify price width d u (sourceData m width omega)=.unknown := by
  filter_upwards [RegisterFaultFinitePurposeProbe.total_fault_unknown_ae noise m N 0 width] with omega h
  cases hx : firstBirth (sourceData m width omega) (registration N) with
  | none=>simp [classify,hx]
  | some q=>rcases q with ⟨b,k⟩;simp [select,hx] at h

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbe
