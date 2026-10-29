import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFeedbackResource

/-!
Original commitment: actual finite learning and its returned controller are payable in the SAME resource account.
Existing premise: open-resource deployment required reserve>=c; the original consecutive write probes were not funded.
Premise reduced: NEW fixed idle/write protocol derives all training-prefix balances and a deployment reserve from R0>=0.
Models: each original write is preceded by requested idle, then one final idle; 4N+1 genuine primitive draws, failures retained.
Consumers: original write-data law/selector, SAME actually retained terminal parent, original infinite optimum and P6 resource path.

This is a NEW registered full protocol using the existing allowed actions and
the explicitly NEW protected idle-request external resource port from the frozen
feedback source. It does not alter the original 2N-write protocol or any saved
data. Idle requests collect g even when physical execution is preempted by fault.
No retry, successful-birth filtering, reset, or code installation occurs. All idle
and write transactions, births, failures and fees remain in the full trace. Only
the selected WRITE readout has the old raw-law marginal; full paths differ.
Future objective evaluation begins at the actual deployment origin; no claim of
acquisition+deployment payoff optimality is made. Resource units are the original
abstract accounting units, with no additional physical energy interpretation.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFundedProbe
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.Compression.Objecthood.ResourceClosure
open VariableRegisteredSamples
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultControlModel RegisterFaultJointRecord RegisterFaultInfiniteRecord
open RegisterFaultFinitePurposeProbe RegisterFaultFeedbackResource
open scoped BigOperators ENNReal
noncomputable section

abbrev CompleteCoordinate (N : ℕ) := Coordinate N ⊕ Fin (2*N+1)
abbrev Raw (N : ℕ) := CompleteCoordinate N → Bool × Bool

/-- Complete NEW primitive product: all original write coordinates and every
idle coordinate have the SAME original mode/label law, independently. -/
def sourceLaw (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) : Measure (Raw N) :=
  Measure.pi (fun _ : CompleteCoordinate N => (primitiveLaw noise epsilon he).toMeasure)

instance sourceLaw_isProbability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) :
    IsProbabilityMeasure (sourceLaw noise epsilon he N) := by unfold sourceLaw; infer_instance

def writeDraw {N : ℕ} (omega : Raw N) (j : Coordinate N) : Bool × Bool := omega (.inl j)

/-- Totalization outside the frozen idle budget is never used by the registered
run; its chronological idle indices are 0,...,2N, including the final charge. -/
def idleDraw {N : ℕ} (omega : Raw N) (k : ℕ) : Bool × Bool :=
  if h : k < 2*N+1 then omega (.inr ⟨k,h⟩) else (false,false)

theorem idleDraw_registered {N : ℕ} (omega : Raw N) (k : Fin (2*N+1)) :
    idleDraw omega k = omega (.inr k) := by simp [idleDraw,k.isLt]

theorem primitive_count (N : ℕ) : Fintype.card (CompleteCoordinate N) = 4*N+1 := by
  simp [CompleteCoordinate,Coordinate,SampleCoordinate,Fintype.card_sigma]
  omega

/-- The actual selected WRITE primitive marginal is EXACTLY the old rawLaw.
This does not identify the new full trace with the original probeTrace. -/
theorem write_marginal (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) :
    (sourceLaw noise epsilon he N).map writeDraw = rawLaw noise epsilon he N := by
  let mu := (primitiveLaw noise epsilon he).toMeasure
  have hs := measurePreserving_sumPiEquivProdPi (fun _ : CompleteCoordinate N => mu)
  have hf : MeasurePreserving Prod.fst
      ((Measure.pi (fun _ : Coordinate N => mu)).prod (Measure.pi (fun _ : Fin (2*N+1) => mu)))
      (Measure.pi (fun _ : Coordinate N => mu)) := measurePreserving_fst
  exact (hf.comp hs).map_eq

/-- Literal parent-retaining interpreter: idle, forced write, recurse; the last
idle is always executed. No observation selects a different schedule. -/
def trace {n N : ℕ} (i : Fin n) (m : Mechanism) (writes : Coordinate N → Bool × Bool) (idles : ℕ → Bool × Bool) :
    Organism n → List (Coordinate N) → ℕ → List (ModeRecord n)
  | o,[],k => [modeRecordStep i m o none (idles k).1 (idles k).2]
  | o,j::js,k =>
      let r0 := modeRecordStep i m o none (idles k).1 (idles k).2
      let r1 := modeRecordStep i m r0.transaction.parentAfter (some j.1) (writes j).1 (writes j).2
      r0 :: r1 :: trace i m writes idles r1.transaction.parentAfter js (k+1)

/-- Complete 4N+1 transactions, including all idle-mode failures and fees. -/
def completeTrace {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Raw N) (o : Organism n) : List (ModeRecord n) :=
  trace i m (writeDraw omega) (idleDraw omega) o (registration N) 0

/-- Read only the forced-write positions from the preserved full trace. -/
def writeRecords {n : ℕ} : List (ModeRecord n) → List (ModeRecord n)
  | [] => []
  | [_] => []
  | _::r::rs => r :: writeRecords rs

/-- Actual deployment parent is the terminal parent of the NEW complete trace. -/
def terminalParent {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Raw N) (o : Organism n) : Organism n :=
  (completeTrace i m omega o).foldl (fun _ (r : ModeRecord n) => r.transaction.parentAfter) o

private theorem trace_length {n N : ℕ} (i : Fin n) (m : Mechanism) (writes : Coordinate N → Bool × Bool)
    (idles : ℕ → Bool × Bool) : ∀ o js k, (trace i m writes idles o js k).length = 2*js.length+1 := by
  intro o js
  induction js generalizing o with
  | nil => intro k; rfl
  | cons j js ih => intro k; simp only [trace,List.length_cons,ih]; omega

theorem completeTrace_length {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Raw N) (o : Organism n) :
    (completeTrace i m omega o).length = 4*N+1 := by
  rw [completeTrace,trace_length,registration_length]
  omega

private theorem trace_program {n N : ℕ} (i : Fin n) (m : Mechanism) (writes : Coordinate N → Bool × Bool)
    (idles : ℕ → Bool × Bool) : ∀ o js k,
      ((trace i m writes idles o js k).foldl (fun _ (r : ModeRecord n) => r.transaction.parentAfter) o).program = o.program := by
  intro o js
  induction js generalizing o with
  | nil => intro k; exact step_program i m o _ _ _
  | cons j js ih =>
    intro k
    change ((trace i m writes idles _ js (k+1)).foldl (fun _ (r : ModeRecord n) => r.transaction.parentAfter) _).program = _
    rw [ih,step_program,step_program]

theorem terminalParent_program {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Raw N) (o : Organism n) :
    (terminalParent i m omega o).program = o.program := trace_program i m _ _ o _ _

/-- Actual write-position readout, after every real intervening idle, still
has the same source feature. Parent independence is reused, not assumed. -/
theorem trace_write_observations {n N : ℕ} (i : Fin n) (m : Mechanism) (width : ℚ)
    (writes : Coordinate N → Bool × Bool) (idles : ℕ → Bool × Bool) :
    ∀ o, o.program = m.goal → ∀ js k,
      (writeRecords (trace i m writes idles o js k)).map (recordObservation width) =
        js.map (sourceData m width writes) := by
  intro o hp js
  induction js generalizing o with
  | nil => intro k; rfl
  | cons j js ih =>
    intro k
    simp only [trace,writeRecords,List.map_cons]
    rw [recordObservation_eq i m width _ ((step_program i m o _ _ _).trans hp)]
    rw [ih _ ((step_program i m _ _ _ _).trans ((step_program i m o _ _ _).trans hp))]
    rfl


/-- Coordinate lookup is fixed by the old complete registration, never by an
observed success. Every coordinate occurs in that registration. -/
def actualData {n N : ℕ} (i : Fin n) (m : Mechanism) (width : ℚ) (omega : Raw N) (o : Organism n) : Batch N :=
  fun j => (((writeRecords (completeTrace i m omega o)).map (recordObservation width))[(registration N).idxOf j]?).getD (false,0)

/-- The executable selector receives ACTUAL record readouts. The equality to
sourceData is a derived theorem and does not expose true parameters to select. -/
theorem actualData_eq {n N : ℕ} (i : Fin n) (m : Mechanism) (width : ℚ) (omega : Raw N)
    (o : Organism n) (ho : o.program = m.goal) : actualData i m width omega o = sourceData m width (writeDraw omega) := by
  funext j
  unfold actualData completeTrace
  rw [trace_write_observations i m width _ _ o ho]
  rw [List.getElem?_map,List.getElem?_idxOf (mem_registration j)]
  rfl

/-- Distribution of the actual selected batch, not a desired independent data
law. Added idle coordinates remain in the full primitive source and full trace. -/
theorem actualData_law {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (N : ℕ) (width : ℚ) (o : Organism n) (ho : o.program = m.goal) :
    (sourceLaw noise epsilon he N).map (fun omega => actualData i m width omega o) =
      (rawLaw noise epsilon he N).map (sourceData m width) := by
  have hf : (fun omega : Raw N => actualData i m width omega o) = sourceData m width ∘ writeDraw := by
    funext omega; exact actualData_eq i m width omega o ho
  rw [hf,← Measure.map_map (measurable_of_finite _) (measurable_of_finite _),write_marginal]

/-- Original finite-budget UNKNOWN guarantee transfers to the NEW actual
record readout by its proven old write marginal. No thresholds are changed. -/
theorem actual_unknown_probability_le {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (N : ℕ) (hN : 0 < N)
    (width price : ℚ) (u : ℝ) (hu : 0 ≤ u) (hsep : Separated m price width)
    (hr : u < repairChance epsilon) (o : Organism n) (ho : o.program = m.goal) :
    (sourceLaw noise epsilon he N).real
      {omega | select price width (actualData i m width omega o) = .unknown} ≤
      min 1 (4 * Real.exp (-2 * (N : ℝ) * u^2)) := by
  have hmap := congrArg (fun mu : Measure (Coordinate N → Bool × Bool) => mu.real
      {w | select price width (sourceData m width w) = .unknown}) (write_marginal noise epsilon he N)
  rw [Measure.real,Measure.map_apply (measurable_of_finite _) ((Set.toFinite _).measurableSet)] at hmap
  have hold := unknown_probability_le noise m epsilon he N hN width price u hu hsep hr
  rw [← hmap] at hold
  simpa only [actualData_eq i m width _ o ho,Set.preimage_ofPred_eq,Function.comp_apply,Measure.real] using hold

/-- Prefix balances include every preserved transaction. Taking beyond the
finite end just rechecks the actual terminal balance. -/
def PrefixFunded {n : ℕ} (reserve g : ℝ) (rs : List (ModeRecord n)) : Prop :=
  ∀ k : ℕ, 0 ≤ listBalance reserve g (rs.take k)

private theorem balance_cons {n : ℕ} (reserve g : ℝ) (r : ModeRecord n) (rs : List (ModeRecord n)) :
    listBalance reserve g (r::rs) = listBalance (reserve+idleInflow g r-r.transaction.expenditure) g rs := by
  simp only [listBalance,List.map_cons,List.sum_cons]
  ring

private theorem idle_fields {n : ℕ} (i : Fin n) (m : Mechanism) (g : ℝ) (o : Organism n) (mode label : Bool) :
    let r := modeRecordStep i m o none mode label
    r.transaction.expenditure = 0 ∧ idleInflow g r = g := by
  cases mode <;> simp [modeRecordStep,RegisterJointRecord.recordStep,cost,idleInflow]

private theorem write_fields {n : ℕ} (i : Fin n) (m : Mechanism) (g : ℝ) (o : Organism n) (bit mode label : Bool) :
    let r := modeRecordStep i m o (some bit) mode label
    0 ≤ r.transaction.expenditure ∧ r.transaction.expenditure ≤ m.writeCost ∧ idleInflow g r = 0 := by
  cases mode <;> simp [modeRecordStep,RegisterJointRecord.recordStep,cost,idleInflow,m.writeCost.coe_nonneg]

private theorem balance_single {n : ℕ} (reserve g : ℝ) (r : ModeRecord n) :
    listBalance reserve g [r] = reserve+idleInflow g r-r.transaction.expenditure := by
  rw [balance_cons]
  simp [listBalance]

private theorem trace_funded {n N : ℕ} (i : Fin n) (m : Mechanism)
    (writes : Coordinate N → Bool × Bool) (idles : ℕ → Bool × Bool)
    (g : ℝ) (hg : (m.writeCost : ℝ) ≤ g) :
    ∀ o js k reserve, 0 ≤ reserve →
      PrefixFunded reserve g (trace i m writes idles o js k) ∧
        (m.writeCost : ℝ) ≤ listBalance reserve g (trace i m writes idles o js k) := by
  intro o js
  induction js generalizing o with
  | nil =>
    intro k reserve hR
    let r := modeRecordStep i m o none (idles k).1 (idles k).2
    have hi : r.transaction.expenditure = 0 ∧ idleInflow g r = g := idle_fields i m g o _ _
    change PrefixFunded reserve g [r] ∧ (m.writeCost : ℝ) ≤ listBalance reserve g [r]
    have hb : (m.writeCost : ℝ) ≤ reserve+g := by linarith
    refine ⟨?_,?_⟩
    · intro ell
      cases ell with
      | zero => simpa [listBalance] using hR
      | succ ell =>
        simp only [List.take_succ_cons,List.take_nil]
        rw [balance_single,hi.1,hi.2]
        linarith [m.writeCost.coe_nonneg]
    · rw [balance_single,hi.1,hi.2]
      linarith
  | cons j js ih =>
    intro k reserve hR
    let r0 := modeRecordStep i m o none (idles k).1 (idles k).2
    let r1 := modeRecordStep i m r0.transaction.parentAfter (some j.1) (writes j).1 (writes j).2
    have hi : r0.transaction.expenditure = 0 ∧ idleInflow g r0 = g := idle_fields i m g o _ _
    have hw : 0 ≤ r1.transaction.expenditure ∧ r1.transaction.expenditure ≤ m.writeCost ∧ idleInflow g r1 = 0 :=
      write_fields i m g r0.transaction.parentAfter _ _ _
    have hR' : 0 ≤ reserve+g-r1.transaction.expenditure := by linarith [hw.2.1]
    have htail := ih r1.transaction.parentAfter (k+1) (reserve+g-r1.transaction.expenditure) hR'
    refine ⟨?_,?_⟩
    · intro ell
      cases ell with
      | zero => simpa [listBalance] using hR
      | succ ell =>
        cases ell with
        | zero =>
          change 0 ≤ listBalance reserve g [r0]
          rw [balance_single,hi.1,hi.2]
          linarith [m.writeCost.coe_nonneg]
        | succ ell =>
          change 0 ≤ listBalance reserve g (r0::r1::(trace i m writes idles r1.transaction.parentAfter js (k+1)).take ell)
          rw [balance_cons,balance_cons,hi.1,hi.2,hw.2.2]
          simpa only [sub_zero,add_zero] using htail.1 ell
    · change (m.writeCost : ℝ) ≤ listBalance reserve g
        (r0::r1::trace i m writes idles r1.transaction.parentAfter js (k+1))
      rw [balance_cons,balance_cons,hi.1,hi.2,hw.2.2]
      simpa only [sub_zero,add_zero] using htail.2

/-- All actual training prefixes are funded from R0>=0, and the final actual
remaining reserve is >=c for the SAME retained parent's returned controller. -/
theorem complete_training_funded {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Raw N) (o : Organism n)
    (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g) (hR : 0 ≤ reserve) :
    PrefixFunded reserve g (completeTrace i m omega o) ∧
      (m.writeCost : ℝ) ≤ listBalance reserve g (completeTrace i m omega o) :=
  trace_funded i m _ _ g hg o _ _ reserve hR


def idleRecords {n : ℕ} : List (ModeRecord n) → List (ModeRecord n)
  | [] => []
  | [r] => [r]
  | r::_::rs => r :: idleRecords rs

def primitives {n : ℕ} (r : ModeRecord n) : Bool × Bool := (r.repairMode,r.transaction.label)

@[simp] private theorem step_primitives {n : ℕ} (i : Fin n) (m : Mechanism) (o : Organism n)
    (a : Action) (mode label : Bool) : primitives (modeRecordStep i m o a mode label) = (mode,label) := by
  cases mode <;> rfl

private theorem trace_idle_primitives {n N : ℕ} (i : Fin n) (m : Mechanism)
    (writes : Coordinate N → Bool × Bool) (idles : ℕ → Bool × Bool) :
    ∀ o js k, (idleRecords (trace i m writes idles o js k)).map primitives =
      List.ofFn (fun j : Fin (js.length+1) => idles (k+j)) := by
  intro o js
  induction js generalizing o with
  | nil => intro k; simp [trace,idleRecords,List.ofFn_succ]
  | cons j js ih =>
    intro k
    simp only [trace,idleRecords,List.map_cons,step_primitives]
    rw [ih]
    simp only [List.length_cons,List.ofFn_succ,Fin.val_zero,Fin.val_succ,Nat.add_zero]
    simp only [Nat.add_left_comm,Nat.add_comm]

/-- The registered idle budget is actually consumed once in chronological
order, including the final idle; out-of-budget totalization is never used. -/
theorem complete_idle_primitive_readout {n N : ℕ} (i : Fin n) (m : Mechanism) (omega : Raw N) (o : Organism n) :
    (idleRecords (completeTrace i m omega o)).map primitives =
      List.ofFn (fun k : Fin (2*N+1) => omega (.inr k)) := by
  simpa only [completeTrace,registration_length,zero_add,Fin.val_cast,idleDraw_registered] using
    trace_idle_primitives i m (writeDraw omega) (idleDraw omega) o (registration N) 0

variable {n : ℕ}
local instance : MeasurableSpace (ModeRecord n) := ⊤
local instance : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _ => trivial⟩

/-- Actual future record kernel seeded at the NEW complete protocol's retained
terminal parent, with the SAME controller computed from its actual write data. -/
def futureKernel {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (price width : ℚ) (o : Organism n) : Kernel (Raw N) (ℕ → ModeRecord n) :=
  Kernel.ofFunOfCountable (fun omega =>
    let parent := terminalParent i m omega o
    let sigma := returnedPolicy i (select price width (actualData i m width omega o))
    recordPathLaw i noise m epsilon he sigma ⟨0,parent.physical,parent⟩)

instance futureKernel_isMarkov {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (price width : ℚ) (o : Organism n) :
    IsMarkovKernel (futureKernel (N:=N) i noise m epsilon he price width o) where
  isProbabilityMeasure omega := by
    change IsProbabilityMeasure (recordPathLaw i noise m epsilon he _ _)
    infer_instance

set_option maxHeartbeats 1000000 in
/-- Common actual-source consumer: the complete training is funded from R0>=0,
its computed remainder funds the SAME infinite returned controller, and the
integrable actual future payoff is its original all-causal optimum. No old
postProbeParent or independently desired future law is substituted. -/
theorem accepted_training_and_deployment {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (omega : Raw N) (b : Bool)
    (o : Organism n) (ho : o.program = m.goal)
    (hs : select price width (actualData i m width omega o) = .repair b)
    (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g) (hR : 0 ≤ reserve) :
    let parent := terminalParent i m omega o
    let remaining := listBalance reserve g (completeTrace i m omega o)
    let mu := futureKernel i noise m epsilon he price width o omega
    let p := priceValue price hp
    let M := RegisterFaultControlModel.model i noise m p epsilon he d hd
    PrefixFunded reserve g (completeTrace i m omega o) ∧ (m.writeCost : ℝ) ≤ remaining ∧
      Integrable (streamPayoff p d) mu ∧
      (∫ rs, streamPayoff p d rs ∂mu) = M.optimalValue parent.physical ∧
      ∀ᵐ rs ∂mu, ResourceViable remaining (fun t => idleInflow g (rs t))
        (fun t => (rs t).transaction.expenditure) := by
  let parent := terminalParent i m omega o
  let sigma := returnedPolicy i (select price width (actualData i m width omega o))
  have hparent : parent.program = m.goal := (terminalParent_program i m omega o).trans ho
  have hf := complete_training_funded i m omega o g reserve hg hR
  have hs' : select price width (sourceData m width (writeDraw omega)) = .repair b := by
    rw [← actualData_eq i m width omega o ho]
    exact hs
  have hopt := (returned_positive_optimal.{0} i noise m epsilon he price width hp hw d hd (writeDraw omega) b hs').1
    parent.physical
  rw [← actualData_eq i m width omega o ho] at hopt
  refine ⟨hf.1,hf.2,actual_recordPath_payoff_integrable i noise m epsilon he sigma (priceValue price hp) d hd
    ⟨0,parent.physical,parent⟩,?_,?_⟩
  · exact (actual_recordPath_integral_eq_policy_value i noise m epsilon he sigma parent.physical parent
      (priceValue price hp) d hd rfl hparent).trans hopt
  · have hc := select_repair_sound m price width hp hw (writeDraw omega) b hs'
    change ∀ᵐ rs ∂recordPathLaw i noise m epsilon he sigma ⟨0,parent.physical,parent⟩,
      ResourceViable (listBalance reserve g (completeTrace i m omega o))
        (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)
    dsimp only [sigma]
    rw [hs]
    simp only [returnedPolicy,returnedSelector]
    rw [hc.1]
    exact actual_recordPath_resource_viable i noise m epsilon he g _ hg hf.2 parent


/-- Preserve the full finite training record in front of the actual future
stream. This changes neither the training transactions nor the future seed. -/
def prepend {n : ℕ} : List (ModeRecord n) → (ℕ → ModeRecord n) → ℕ → ModeRecord n
  | [],rs,k => rs k
  | r::_,_,0 => r
  | _::pre,rs,k+1 => prepend pre rs k

@[fun_prop] theorem measurable_prepend (pre : List (ModeRecord n)) : Measurable (prepend pre) := by
  induction pre with
  | nil => exact measurable_id
  | cons r pre ih =>
    apply measurable_pi_lambda
    intro k
    cases k with
    | zero => exact measurable_const
    | succ k => exact (measurable_pi_apply k).comp ih

private theorem cumulative_prepend_succ (reserve g : ℝ) (r : ModeRecord n)
    (pre : List (ModeRecord n)) (rs : ℕ → ModeRecord n) (k : ℕ) :
    cumulativeResourceBalance reserve (fun t => idleInflow g (prepend (r::pre) rs t))
      (fun t => (prepend (r::pre) rs t).transaction.expenditure) (k+1) =
    cumulativeResourceBalance (reserve+idleInflow g r-r.transaction.expenditure)
      (fun t => idleInflow g (prepend pre rs t)) (fun t => (prepend pre rs t).transaction.expenditure) k := by
  unfold cumulativeResourceBalance
  rw [Finset.sum_range_succ',Finset.sum_range_succ']
  simp only [prepend]
  ring

/-- The actual terminal training balance is the starting balance of future
P6 accounting, so the joined path is funded under ONE continuous ledger. -/
theorem prepend_resource_viable (reserve g : ℝ) (pre : List (ModeRecord n)) (rs : ℕ → ModeRecord n)
    (hpre : PrefixFunded reserve g pre)
    (hfuture : ResourceViable (listBalance reserve g pre)
      (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)) :
    ResourceViable reserve (fun t => idleInflow g (prepend pre rs t))
      (fun t => (prepend pre rs t).transaction.expenditure) := by
  induction pre generalizing reserve with
  | nil => simpa [listBalance,prepend] using hfuture
  | cons r pre ih =>
    have hpre' : PrefixFunded (reserve+idleInflow g r-r.transaction.expenditure) g pre := by
      intro k
      have h := hpre (k+1)
      simpa only [List.take_succ_cons,balance_cons] using h
    have hfuture' : ResourceViable
        (listBalance (reserve+idleInflow g r-r.transaction.expenditure) g pre)
        (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) := by
      simpa only [balance_cons] using hfuture
    have htail := ih _ hpre' hfuture'
    intro k
    cases k with
    | zero => simpa [cumulativeResourceBalance,listBalance] using hpre 0
    | succ k => rw [cumulative_prepend_succ]; exact htail k

private theorem funding_event_measurable (reserve g : ℝ) :
    MeasurableSet {rs : ℕ → ModeRecord n | ResourceViable reserve
      (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)} := by
  have heq : {rs : ℕ → ModeRecord n | ResourceViable reserve
      (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)} =
      ⋂ k : ℕ, {rs | 0 ≤ cumulativeResourceBalance reserve
        (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) k} := by
    ext rs; simp [ResourceViable]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le measurable_const
  unfold cumulativeResourceBalance
  have hgain (t : ℕ) : Measurable (fun rs : ℕ → ModeRecord n => idleInflow g (rs t)) :=
    (show Measurable (idleInflow (n:=n) g) from fun _ _ => trivial).comp (measurable_pi_apply t)
  have hcost (t : ℕ) : Measurable (fun rs : ℕ → ModeRecord n => (rs t).transaction.expenditure) :=
    (show Measurable (fun r : ModeRecord n => r.transaction.expenditure) from fun _ _ => trivial).comp (measurable_pi_apply t)
  exact (measurable_const.add (Finset.measurable_sum (Finset.range k) (fun t _ => hgain t))).sub
    (Finset.measurable_sum (Finset.range k) (fun t _ => hcost t))

/-- Genuine complete conditional path law, including every training record. -/
def wholeKernel {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (price width : ℚ) (o : Organism n) : Kernel (Raw N) (ℕ → ModeRecord n) :=
  Kernel.ofFunOfCountable (fun omega =>
    (futureKernel i noise m epsilon he price width o omega).map (prepend (completeTrace i m omega o)))

instance wholeKernel_isMarkov {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (price width : ℚ) (o : Organism n) :
    IsMarkovKernel (wholeKernel (N:=N) i noise m epsilon he price width o) where
  isProbabilityMeasure _omega := Measure.isProbabilityMeasure_map (measurable_prepend _).aemeasurable

set_option maxHeartbeats 1000000 in
/-- One actual complete conditional path is funded across training AND future,
from the original nonnegative reserve. Future conditioning selects no successes. -/
theorem accepted_whole_path_funded {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (omega : Raw N) (b : Bool)
    (o : Organism n) (ho : o.program = m.goal)
    (hs : select price width (actualData i m width omega o) = .repair b)
    (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g) (hR : 0 ≤ reserve) :
    ∀ᵐ rs ∂wholeKernel i noise m epsilon he price width o omega,
      ResourceViable reserve (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure) := by
  have h := accepted_training_and_deployment i noise m epsilon he price width hp hw d hd omega b o ho hs g reserve hg hR
  change ∀ᵐ rs ∂(futureKernel i noise m epsilon he price width o omega).map
      (prepend (completeTrace i m omega o)),
    ResourceViable reserve (fun t => idleInflow g (rs t)) (fun t => (rs t).transaction.expenditure)
  apply (ae_map_iff (measurable_prepend _).aemeasurable (funding_event_measurable reserve g)).mpr
  filter_upwards [h.2.2.2.2] with rs hrs
  exact prepend_resource_viable reserve g _ rs h.1 hrs

/-- The new complete primitive source is followed by its actual conditional
record kernel, so deployment is correlated with its actual data and retained
parent. No independent desired joint process is supplied. -/
def jointLaw {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (price width : ℚ) (o : Organism n) : Measure (Raw N × (ℕ → ModeRecord n)) :=
  sourceLaw noise epsilon he N ⊗ₘ wholeKernel i noise m epsilon he price width o

instance jointLaw_isProbability {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal)
    (he : epsilon ≤ 1) (price width : ℚ) (o : Organism n) :
    IsProbabilityMeasure (jointLaw (N:=N) i noise m epsilon he price width o) := by unfold jointLaw; infer_instance

/-- Genuine joint statement: whenever the SAME actual-data selector returns
repair, its FULL retained-record experiment is resource viable almost surely.
This does not assert any optimum for training+deployment combined payoff. -/
theorem joint_resource_viable_on_repair {N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon ≤ 1) (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width)
    (d : ℝ) (hd : 0 < d ∧ d < 1) (o : Organism n) (ho : o.program = m.goal)
    (g reserve : ℝ) (hg : (m.writeCost : ℝ) ≤ g) (hR : 0 ≤ reserve) :
    ∀ᵐ wp ∂jointLaw (N:=N) i noise m epsilon he price width o,
      (∃ b, select price width (actualData i m width wp.1 o) = .repair b) →
        ResourceViable reserve (fun t => idleInflow g (wp.2 t)) (fun t => (wp.2 t).transaction.expenditure) := by
  have ha : MeasurableSet {omega : Raw N | ∃ b, select price width (actualData i m width omega o) = .repair b} :=
    (Set.toFinite _).measurableSet
  have hmeas : MeasurableSet {wp : Raw N × (ℕ → ModeRecord n) |
      (∃ b, select price width (actualData i m width wp.1 o) = .repair b) →
        ResourceViable reserve (fun t => idleInflow g (wp.2 t)) (fun t => (wp.2 t).transaction.expenditure)} := by
    convert (ha.preimage measurable_fst).compl.union
      ((funding_event_measurable (n:=n) reserve g).preimage measurable_snd) using 1
    ext wp
    simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_preimage,Set.mem_ofPred_eq,imp_iff_not_or]
  apply Measure.ae_compProd_of_ae_ae hmeas
  filter_upwards [] with omega
  by_cases hs : ∃ b, select price width (actualData i m width omega o) = .repair b
  · obtain ⟨b,hb⟩ := hs
    have h := accepted_whole_path_funded i noise m epsilon he price width hp hw d hd omega b o ho hb g reserve hg hR
    exact h.mono (fun _ hrs _ => hrs)
  · exact Filter.Eventually.of_forall (fun _ hh => False.elim (hs hh))


/-- A formal registered five-draw example, not a new empirical batch. Four
faults remain in the full trace; the one actual paid write certifies goal false. -/
def witnessRaw : Raw 1 := fun j => match j with
  | .inl j => if j.1 then (false,true) else (true,true)
  | .inr _ => (false,true)
def witnessMechanism : Mechanism := ⟨false,1⟩
def witnessParent : Organism 1 := ⟨[],fun _ => false,false⟩

theorem funded_training_witness :
    let rs := completeTrace (0 : Fin 1) witnessMechanism witnessRaw witnessParent
    (rs.map ModeRecord.repairMode = [false,true,false,false,false]) ∧
      (rs.map (fun r => r.transaction.expenditure)).sum = 1 ∧
      listBalance 0 1 rs = 2 ∧
      (terminalParent (0 : Fin 1) witnessMechanism witnessRaw witnessParent).physical 0 = true := by
  norm_num [completeTrace,trace,writeDraw,idleDraw,registration,List.finRange,
    witnessRaw,witnessMechanism,witnessParent,modeRecordStep,RegisterJointRecord.recordStep,cost,
    listBalance,idleInflow,terminalParent,show (some false : Action) ≠ none from by decide,
    show (some true : Action) ≠ none from by decide]

theorem funded_training_witness_accepts :
    select (1/2) (1/4) (actualData (0 : Fin 1) witnessMechanism (1/4) witnessRaw witnessParent) = .repair false := by
  rw [actualData_eq (0 : Fin 1) witnessMechanism (1/4) witnessRaw witnessParent rfl]
  norm_num [select,firstBirth,registration,List.finRange,sourceData,feature,feeBin,
    witnessRaw,witnessMechanism,writeDraw]


/-- The formal accepted witness has positive mass under the NEW complete
same-noise product source at nonzero hazard; it is not an unsupported tuple. -/
theorem funded_training_witness_mass :
    (sourceLaw (PMF.uniformOfFintype Bool) (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)) 1).real {witnessRaw} = 3/32768 := by
  rw [Measure.real,sourceLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  norm_num [Fintype.prod_sum_type,Fintype.prod_sigma,Fintype.prod_bool,Fin.prod_univ_succ,witnessRaw,
    primitiveLaw_apply,ENNReal.toReal_mul,modeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal,
    modeProbability,repairChance,PMF.uniformOfFintype_apply]

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFundedProbe
