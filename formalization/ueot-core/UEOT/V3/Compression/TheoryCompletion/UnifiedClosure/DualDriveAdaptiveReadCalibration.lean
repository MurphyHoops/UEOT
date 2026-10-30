import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveFiniteCalibrationCoverage
import Mathlib.Data.List.OfFn

/-!
Original commitment: data-selected read counts must bind the SAME measured inverse and returned action to one actual source risk.
Existing result: original four-row sensor/select/Good and separated-source coverage use fixed independent row prefixes.
Premise reduced: derive actual fresh read counters, retained complete history, min-read-prefix decoding and a single all-prefix Good risk.
Model/witness: NEW preregistered m-warmup plus K past-data-routed reads on SAME independent latent row streams; no true parameters/Good/unread raw exposed.
Consumer: ORIGINAL select joint wrong risk and correct acceptance, with correlated common-shock limits kept separate; old32/128batch unchanged.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.DualDriveAdaptiveReadCalibration
open MeasureTheory ProbabilityTheory Set Filter
open DualDriveFiniteNoisyCalibration DualDriveFiniteCalibrationCoverage VariableRegisteredSamples
open UEOT.V3.HilbertMeanProductBlockIndependence
open scoped BigOperators ENNReal

/-- Only an ACTUALLY read row/index/value enters router history. -/
structure Read where
  row : Row
  index : ℕ
  value : ℚ
  deriving DecidableEq, Repr

structure ReadState where
  trace : List Read
  observed : Row → List ℚ

def empty : ReadState := ⟨[],fun _ => []⟩

/-- Totalization is never reached by the registered execution; that is proved
from the actual per-row counter bound, not assumed by the selector. -/
def sourceRead {N : ℕ} (data : Data N) (j : Row) (k : ℕ) : ℚ :=
  if hk : k < N then data ⟨j,⟨k,hk⟩⟩ else 0

def readStep {N : ℕ} (data : Data N) (s : ReadState) (j : Row) : ReadState :=
  let k := (s.observed j).length
  let v := sourceRead data j k
  ⟨s.trace ++ [⟨j,k,v⟩],fun row => if row=j then s.observed row ++ [v] else s.observed row⟩

/-- A router receives only prior actual observations, never data or source truth. -/
abbrev Router := List Read → Row

def adaptive {N : ℕ} (data : Data N) (route : Router) : ℕ → ReadState → ReadState
  | 0,s => s
  | k+1,s => adaptive data route k (readStep data s (route s.trace))

/-- Each registered warmup round reads rows0/1/2/3 exactly once, all retained. -/
def round {N : ℕ} (data : Data N) (s : ReadState) : ReadState :=
  readStep data (readStep data (readStep data (readStep data s 0) 1) 2) 3

def warmup {N : ℕ} (data : Data N) : ℕ → ReadState
  | 0 => empty
  | m+1 => round data (warmup data m)

def run (m K : ℕ) (route : Router) (data : Data (m+K)) : ReadState :=
  adaptive data route K (warmup data m)

def minCount (s : ReadState) : ℕ :=
  min (min (s.observed 0).length (s.observed 1).length)
    (min (s.observed 2).length (s.observed 3).length)

def decoded (s : ReadState) : Data (minCount s) :=
  fun q => (s.observed q.1).getD q.2 0

def returned (m K : ℕ) (route : Router) (data : Data (m+K)) : Option Bool :=
  select (decoded (run m K route data))

/-- Actual list-only router: a negative adaptive read persists row0; otherwise
balance observed row counts. The warmup is registered, not inferred from truth. -/
def traceCount (trace : List Read) (j : Row) : ℕ := (trace.filter (fun r => r.row=j)).length

def leastRow (trace : List Read) : Row :=
  if traceCount trace 0 ≤ traceCount trace 1 ∧ traceCount trace 0 ≤ traceCount trace 2 ∧ traceCount trace 0 ≤ traceCount trace 3 then 0 else
  if traceCount trace 1 ≤ traceCount trace 2 ∧ traceCount trace 1 ≤ traceCount trace 3 then 1 else
  if traceCount trace 2 ≤ traceCount trace 3 then 2 else 3

def feedbackRouter (m : ℕ) (trace : List Read) : Row :=
  if (trace.drop (4*m)).any (fun r => decide (r.value < 0)) then 0 else leastRow trace

/-- NEW registration frozen in ueot-c5-adaptive-read-registration-20261030.json
before evaluation; all544 latent slots are declared, although only520 are read. -/
def adaptiveWarmup : ℕ := 128
def adaptiveExtra : ℕ := 8
def adaptiveRegisteredRaw : Raw (adaptiveWarmup+adaptiveExtra) :=
  fun q => if (q.2 : ℕ) < adaptiveWarmup then decide ((q.2 : ℕ)%2=0) else true
/-- Independently preregistered count-dependence word, not a replacement/retry. -/
def adaptiveCountRaw : Raw (adaptiveWarmup+adaptiveExtra) :=
  fun q => if q.1=2 ∧ (q.2 : ℕ)=adaptiveWarmup then false else adaptiveRegisteredRaw q

@[simp] theorem readStep_length {N : ℕ} (data : Data N) (s : ReadState) (j row : Row) :
    ((readStep data s j).observed row).length=(s.observed row).length+if row=j then 1 else 0 := by
  by_cases h : row=j <;> simp [readStep,h]

@[simp] theorem readStep_trace_length {N : ℕ} (data : Data N) (s : ReadState) (j : Row) :
    (readStep data s j).trace.length=s.trace.length+1 := by simp [readStep]

theorem round_length {N : ℕ} (data : Data N) (s : ReadState) (j : Row) :
    ((round data s).observed j).length=(s.observed j).length+1 := by
  fin_cases j <;> simp [round]

theorem warmup_count {N : ℕ} (data : Data N) (m : ℕ) (j : Row) :
    ((warmup data m).observed j).length=m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [warmup,round_length,ih]

theorem adaptive_count_bounds {N : ℕ} (data : Data N) (route : Router) (k : ℕ) (s : ReadState) (j : Row) :
    (s.observed j).length ≤ ((adaptive data route k s).observed j).length ∧
      ((adaptive data route k s).observed j).length ≤ (s.observed j).length+k := by
  induction k generalizing s with
  | zero => simp [adaptive]
  | succ k ih =>
    have h := ih (readStep data s (route s.trace))
    rw [adaptive]
    simp only [readStep_length] at h
    constructor <;> split_ifs at h <;> omega

theorem run_count_bounds (m K : ℕ) (route : Router) (data : Data (m+K)) (j : Row) :
    m ≤ ((run m K route data).observed j).length ∧ ((run m K route data).observed j).length ≤ m+K := by
  simpa only [run,warmup_count] using adaptive_count_bounds data route K (warmup data m) j

theorem minCount_le (s : ReadState) (j : Row) : minCount s ≤ (s.observed j).length := by
  fin_cases j
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

theorem run_minCount_bounds (m K : ℕ) (route : Router) (data : Data (m+K)) :
    m ≤ minCount (run m K route data) ∧ minCount (run m K route data) ≤ m+K := by
  have h0 := run_count_bounds m K route data 0
  have h1 := run_count_bounds m K route data 1
  have h2 := run_count_bounds m K route data 2
  have h3 := run_count_bounds m K route data 3
  simp only [minCount]
  omega

/-- Prefix invariant is a theorem of reads, not a desired decoded-data field. -/
def PrefixCorrect {N : ℕ} (data : Data N) (s : ReadState) : Prop :=
  ∀ j k, k < (s.observed j).length → (s.observed j).getD k 0=sourceRead data j k

theorem readStep_prefix {N : ℕ} (data : Data N) (s : ReadState) (j : Row) (hs : PrefixCorrect data s) :
    PrefixCorrect data (readStep data s j) := by
  intro row k hk
  by_cases h : row=j
  · subst row
    simp only [readStep,ite_true]
    have hk' : k < (s.observed j).length+1 := by simpa only [readStep_length,eq_self_iff_true,ite_true] using hk
    by_cases hlt : k < (s.observed j).length
    · rw [List.getD_append _ _ _ _ hlt]
      exact hs j k hlt
    · have he : k=(s.observed j).length := by omega
      subst k
      simp [List.getD]
  · have hk' : k < (s.observed row).length := by simpa only [readStep_length,if_neg h,Nat.add_zero] using hk
    simpa only [readStep,if_neg h] using hs row k hk'

theorem warmup_prefix {N : ℕ} (data : Data N) (m : ℕ) : PrefixCorrect data (warmup data m) := by
  induction m with
  | zero => intro j k hk; simp [warmup,empty] at hk
  | succ m ih => exact readStep_prefix data _ _ (readStep_prefix data _ _ (readStep_prefix data _ _ (readStep_prefix data _ _ ih)))

theorem adaptive_prefix {N : ℕ} (data : Data N) (route : Router) (k : ℕ) (s : ReadState)
    (hs : PrefixCorrect data s) : PrefixCorrect data (adaptive data route k s) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih _ (readStep_prefix data s _ hs)

/-- Every decoded value was actually read; minCount is data-dependent and
only common observed prefixes are retained. No unread latent slot enters select. -/
theorem decoded_prefix (m K : ℕ) (route : Router) (data : Data (m+K)) (q : Index (minCount (run m K route data))) :
    decoded (run m K route data) q = data ⟨q.1,⟨q.2,(q.2.isLt.trans_le (minCount_le _ q.1)).trans_le (run_count_bounds m K route data q.1).2⟩⟩ := by
  let s := run m K route data
  have hp : PrefixCorrect data s := adaptive_prefix data route K (warmup data m) (warmup_prefix data m)
  have hlen : (q.2 : ℕ) < (s.observed q.1).length := q.2.isLt.trans_le (minCount_le s q.1)
  change (s.observed q.1).getD q.2 0=_
  rw [hp q.1 q.2 hlen]
  unfold sourceRead
  rw [dif_pos (hlen.trans_le (run_count_bounds m K route data q.1).2)]




/-- Complete chronological trace and the cache contain the SAME actual values. -/
def TraceCorrect (s : ReadState) : Prop :=
  ∀ j, ((s.trace.filter (fun r => r.row=j)).map Read.value)=s.observed j

def TraceFresh (s : ReadState) : Prop :=
  ∀ j, ((s.trace.filter (fun r => r.row=j)).map Read.index)=List.range (s.observed j).length

def TraceSource {N : ℕ} (data : Data N) (s : ReadState) : Prop :=
  ∀ r ∈ s.trace, r.value=sourceRead data r.row r.index

theorem readStep_trace_correct {N : ℕ} (data : Data N) (s : ReadState) (j : Row) (hs : TraceCorrect s) :
    TraceCorrect (readStep data s j) := by
  intro row
  by_cases h : j=row
  · subst row
    simp [readStep,List.filter_append,hs j]
  · have h' : row ≠ j := Ne.symm h
    simpa [readStep,List.filter_append,h,h'] using hs row

theorem readStep_trace_fresh {N : ℕ} (data : Data N) (s : ReadState) (j : Row) (hs : TraceFresh s) :
    TraceFresh (readStep data s j) := by
  intro row
  by_cases h : j=row
  · subst row
    simpa [readStep,List.filter_append,List.range_succ] using congrArg (fun l => l ++ [(s.observed j).length]) (hs j)
  · have h' : row ≠ j := Ne.symm h
    simpa [readStep,List.filter_append,h,h'] using hs row

theorem readStep_trace_source {N : ℕ} (data : Data N) (s : ReadState) (j : Row) (hs : TraceSource data s) :
    TraceSource data (readStep data s j) := by
  intro r hr
  have h : r ∈ s.trace ∨ r=⟨j,(s.observed j).length,sourceRead data j (s.observed j).length⟩ := by
    simpa [readStep] using hr
  rcases h with h | h
  · exact hs r h
  · subst r; rfl

theorem warmup_trace {N : ℕ} (data : Data N) (m : ℕ) :
    TraceCorrect (warmup data m) ∧ TraceFresh (warmup data m) ∧ TraceSource data (warmup data m) := by
  induction m with
  | zero => exact ⟨fun _ => rfl,fun _ => rfl,fun r h => False.elim (List.not_mem_nil h)⟩
  | succ m ih =>
    exact ⟨readStep_trace_correct data _ _ (readStep_trace_correct data _ _ (readStep_trace_correct data _ _ (readStep_trace_correct data _ _ ih.1))),
      readStep_trace_fresh data _ _ (readStep_trace_fresh data _ _ (readStep_trace_fresh data _ _ (readStep_trace_fresh data _ _ ih.2.1))),
      readStep_trace_source data _ _ (readStep_trace_source data _ _ (readStep_trace_source data _ _ (readStep_trace_source data _ _ ih.2.2)))⟩

theorem adaptive_trace {N : ℕ} (data : Data N) (route : Router) (k : ℕ) (s : ReadState)
    (hs : TraceCorrect s ∧ TraceFresh s ∧ TraceSource data s) :
    TraceCorrect (adaptive data route k s) ∧ TraceFresh (adaptive data route k s) ∧ TraceSource data (adaptive data route k s) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih _ ⟨readStep_trace_correct data s _ hs.1,readStep_trace_fresh data s _ hs.2.1,readStep_trace_source data s _ hs.2.2⟩

theorem run_trace (m K : ℕ) (route : Router) (data : Data (m+K)) :
    TraceCorrect (run m K route data) ∧ TraceFresh (run m K route data) ∧ TraceSource data (run m K route data) :=
  adaptive_trace data route K _ (warmup_trace data m)

theorem adaptive_trace_length {N : ℕ} (data : Data N) (route : Router) (k : ℕ) (s : ReadState) :
    (adaptive data route k s).trace.length=s.trace.length+k := by
  induction k generalizing s with
  | zero => simp [adaptive]
  | succ k ih => rw [adaptive,ih,readStep_trace_length]; omega

theorem warmup_trace_length {N : ℕ} (data : Data N) (m : ℕ) : (warmup data m).trace.length=4*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [warmup,round,readStep_trace_length,ih]; omega

theorem run_trace_length (m K : ℕ) (route : Router) (data : Data (m+K)) :
    (run m K route data).trace.length=4*m+K := by
  rw [run,adaptive_trace_length,warmup_trace_length]

/-- Every retained read index is fresh and inside its original latent stream;
totalization cannot create an unobserved placeholder in this experiment. -/
theorem run_all_reads_actual (m K : ℕ) (route : Router) (data : Data (m+K))
    (r : Read) (hr : r ∈ (run m K route data).trace) :
    ∃ h : r.index < m+K, r.value=data ⟨r.row,⟨r.index,h⟩⟩ := by
  have ht := run_trace m K route data
  have hmem : r ∈ (run m K route data).trace.filter (fun q => q.row=r.row) := by simp [hr]
  have hi : r.index ∈ ((run m K route data).trace.filter (fun q => q.row=r.row)).map Read.index :=
    List.mem_map.mpr ⟨r,hmem,rfl⟩
  rw [ht.2.1 r.row,List.mem_range] at hi
  have hN : r.index < m+K := hi.trans_le (run_count_bounds m K route data r.row).2
  refine ⟨hN,?_⟩
  rw [ht.2.2 r hr,sourceRead,dif_pos hN]

/-- Restrict SAME latent row streams to their original prefixes; no redraw. -/
def prefixRaw {n N : ℕ} (hn : n ≤ N) (omega : Raw N) : Raw n :=
  fun q => omega ⟨q.1,⟨q.2,q.2.isLt.trans_le hn⟩⟩

noncomputable section

theorem raw_prefix_law {n N : ℕ} (hn : n ≤ N) :
    (rawLaw N).map (prefixRaw hn)=rawLaw n := by
  let e : Index n → Index N := fun q => ⟨q.1,⟨q.2,q.2.isLt.trans_le hn⟩⟩
  have he : Function.Injective e := by
    rintro ⟨j,k⟩ ⟨l,h⟩ hab
    have hj : j=l := congrArg Sigma.fst hab
    subst l
    have hk : k=h := Fin.ext (congrArg (fun q : Index N => q.2.val) hab)
    subst h
    rfl
  have hi := (coordinate_iIndep (fun _ : Index N => (PMF.uniformOfFintype Bool).toMeasure)).precomp he
  have hm (q : Index n) : Measurable (fun omega : Raw N => omega (e q)) := measurable_pi_apply (e q)
  have hl (q : Index n) : (rawLaw N).map (fun omega => omega (e q))=(PMF.uniformOfFintype Bool).toMeasure :=
    (measurePreserving_eval (fun _ : Index N => (PMF.uniformOfFintype Bool).toMeasure) (e q)).map_eq
  have h := hi.map_fun_eq_pi_map (fun q => (hm q).aemeasurable)
  change (rawLaw N).map (prefixRaw hn)=Measure.pi (fun q : Index n => (rawLaw N).map (fun omega => omega (e q))) at h
  simp_rw [hl] at h
  exact h

theorem prefix_good_congr {n v N : ℕ} (he : n=v) (hn : n ≤ N) (hv : v ≤ N) (omega : Raw N) :
    prefixRaw hn omega ∈ Good n ↔ prefixRaw hv omega ∈ Good v := by
  subst v
  rfl

theorem prefix_bad_probability_le {n N : ℕ} (hn : n ≤ N) (hpos : 0 < n) :
    (rawLaw N).real {omega | prefixRaw hn omega ∉ Good n} ≤ 8*Real.exp (-(n : ℝ)/8) := by
  have he := map_measureReal_apply (μ := rawLaw N) (measurable_of_finite (prefixRaw hn))
    ((Set.toFinite (Good n)ᶜ).measurableSet)
  calc
    _ = ((rawLaw N).map (prefixRaw hn)).real (Good n)ᶜ := he.symm
    _ = (rawLaw n).real (Good n)ᶜ := by rw [raw_prefix_law hn]
    _ ≤ _ := bad_good_probability_le n hpos

def AllGood (m K : ℕ) : Set (Raw (m+K)) :=
  {omega | ∀ q : Fin (K+1), prefixRaw (show m+(q : ℕ) ≤ m+K by omega) omega ∈ Good (m+q)}

theorem allGood_at (m K : ℕ) (omega : Raw (m+K)) (hg : omega ∈ AllGood m K)
    (n : ℕ) (hm : m ≤ n) (hn : n ≤ m+K) : prefixRaw hn omega ∈ Good n := by
  let q : Fin (K+1) := ⟨n-m,by omega⟩
  have he : m+(q : ℕ)=n := by dsimp [q]; omega
  exact (prefix_good_congr he _ hn omega).mp (hg q)


theorem allGood_prefix_failure_le (m K : ℕ) (hm : 0 < m) (q : Fin (K+1)) :
    (rawLaw (m+K)).real {omega | prefixRaw (show m+(q : ℕ) ≤ m+K by omega) omega ∉ Good (m+q)} ≤
      8*Real.exp (-(m : ℝ)/8) := by
  let hq : m+(q : ℕ) ≤ m+K := by omega
  have hb := prefix_bad_probability_le hq (by omega)
  have hcast : (m : ℝ) ≤ ((m+(q : ℕ) : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_add_right m (q : ℕ))
  have hexp : Real.exp (-((m+(q : ℕ) : ℕ) : ℝ)/8) ≤ Real.exp (-(m : ℝ)/8) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hcast) (by positivity))
  exact hb.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

theorem allGood_complement (m K : ℕ) : (AllGood m K)ᶜ=⋃ q : Fin (K+1),
    {omega | prefixRaw (show m+(q : ℕ) ≤ m+K by omega) omega ∉ Good (m+q)} := by
  classical
  ext omega
  constructor
  · intro h
    obtain ⟨q,hq⟩ := not_forall.mp h
    exact Set.mem_iUnion.mpr ⟨q,hq⟩
  · intro h hgood
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp h
    exact hq (hgood q)

theorem constant_prefix_sum (K : ℕ) (c : ℝ) :
    (∑ _ : Fin (K+1), c)=((K+1 : ℕ) : ℝ)*c := by
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem allGood_probability_le (m K : ℕ) (hm : 0 < m) :
    (rawLaw (m+K)).real (AllGood m K)ᶜ ≤ 8*((K+1 : ℕ) : ℝ)*Real.exp (-(m : ℝ)/8) := by
  rw [allGood_complement]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _ : Fin (K+1), (8*Real.exp (-(m : ℝ)/8)) :=
      Finset.sum_le_sum (fun q _ => allGood_prefix_failure_le m K hm q)
    _ = _ := by rw [constant_prefix_sum]; ring


/-- The DATA returned to the old selector is EXACTLY the same latent-stream
prefix, whose length is computed from the ACTUAL read history. -/
theorem decoded_source_prefix (m K : ℕ) (route : Router) (p : Parameters) (omega : Raw (m+K)) :
    decoded (run m K route (sourceData p omega)) =
      sourceData p (prefixRaw (run_minCount_bounds m K route (sourceData p omega)).2 omega) := by
  funext q
  rw [decoded_prefix]
  rfl

theorem good_returned_correct (m K : ℕ) (hm : 0 < m) (route : Router) (p : Parameters) (hp : Valid p)
    (omega : Raw (m+K)) (hg : omega ∈ AllGood m K) (chosen : Bool)
    (hs : returned m K route (sourceData p omega)=some chosen) :
    ∀ a : Bool, a ≠ chosen → p.latent a < p.latent chosen := by
  let s := run m K route (sourceData p omega)
  have hb := run_minCount_bounds m K route (sourceData p omega)
  have hpos : 0 < minCount s := hm.trans_le hb.1
  have hgood := allGood_at m K omega hg (minCount s) hb.1 hb.2
  have hsel : select (sourceData p (prefixRaw hb.2 omega))=some chosen := by
    rw [← decoded_source_prefix m K route p omega]
    exact hs
  exact good_selected_action_correct p hp _ hpos hgood chosen hsel

def ActualWrong (m K : ℕ) (route : Router) (p : Parameters) (omega : Raw (m+K)) : Prop :=
  ∃ chosen : Bool, returned m K route (sourceData p omega)=some chosen ∧
    ¬ ∀ a : Bool, a ≠ chosen → p.latent a < p.latent chosen

/-- Whole-source joint risk; final n* is NOT conditioned on or fed as a
registered fixed count. ALL original data-selected outcomes remain in the law. -/
theorem actual_joint_risk_le (m K : ℕ) (hm : 0 < m) (route : Router) (p : Parameters) (hp : Valid p) :
    (rawLaw (m+K)).real {omega | ActualWrong m K route p omega} ≤
      8*((K+1 : ℕ) : ℝ)*Real.exp (-(m : ℝ)/8) := by
  apply (measureReal_mono ?_).trans (allGood_probability_le m K hm)
  intro omega hbad hgood
  obtain ⟨chosen,hs,hwrong⟩ := hbad
  exact hwrong (good_returned_correct m K hm route p hp omega hgood chosen hs)

/-- Same actual data-only artifact accepts the true separated best action on
ONE all-prefix Good; true gain/order are proof hypotheses, never router inputs. -/
theorem good_returned_separated (m K : ℕ) (hm : 0 < m) (route : Router) (p : Parameters)
    (omega : Raw (m+K)) (hg : omega ∈ AllGood m K) (hgain : ∀ i, 1 ≤ p.gain i)
    (best : Bool) (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :
    returned m K route (sourceData p omega)=some best := by
  have hb := run_minCount_bounds m K route (sourceData p omega)
  have hg' := allGood_at m K omega hg _ hb.1 hb.2
  unfold returned
  rw [decoded_source_prefix]
  exact good_selects_separated p _ (hm.trans_le hb.1) hg' hgain best hgap

theorem actual_not_best_probability_le (m K : ℕ) (hm : 0 < m) (route : Router) (p : Parameters)
    (hgain : ∀ i, 1 ≤ p.gain i) (best : Bool) (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :
    (rawLaw (m+K)).real {omega | returned m K route (sourceData p omega) ≠ some best} ≤
      8*((K+1 : ℕ) : ℝ)*Real.exp (-(m : ℝ)/8) := by
  apply (measureReal_mono ?_).trans (allGood_probability_le m K hm)
  intro omega hbad hgood
  exact hbad (good_returned_separated m K hm route p omega hgood hgain best hgap)

/-- SAME registered source/route/returned select, useful correct acceptance;
no conditional-on-selected-count or conditional-on-acceptance probability. -/
theorem actual_best_accept_probability_ge (m K : ℕ) (hm : 0 < m) (route : Router) (p : Parameters)
    (hgain : ∀ i, 1 ≤ p.gain i) (best : Bool) (hgap : (1/2 : ℚ) ≤ p.latent best-p.latent (!best)) :
    1-8*((K+1 : ℕ) : ℝ)*Real.exp (-(m : ℝ)/8) ≤
      (rawLaw (m+K)).real {omega | returned m K route (sourceData p omega)=some best} := by
  have hb := actual_not_best_probability_le m K hm route p hgain best hgap
  have hc := measureReal_compl (μ := rawLaw (m+K))
    ((Set.toFinite {omega | returned m K route (sourceData p omega)=some best}).measurableSet)
  simp only [probReal_univ] at hc
  change (rawLaw (m+K)).real ({omega | returned m K route (sourceData p omega)=some best}ᶜ) ≤ _ at hb
  rw [hc] at hb
  linarith

theorem adaptive_registered_risk (p : Parameters) (hp : Valid p) :
    (rawLaw (adaptiveWarmup+adaptiveExtra)).real
      {omega | ActualWrong adaptiveWarmup adaptiveExtra (feedbackRouter adaptiveWarmup) p omega} ≤
      72*Real.exp (-16) := by
  have h := actual_joint_risk_le adaptiveWarmup adaptiveExtra (by decide) (feedbackRouter adaptiveWarmup) p hp
  norm_num [adaptiveWarmup,adaptiveExtra] at h
  exact h

theorem adaptive_registered_nonvacuous : 72*Real.exp (-16) < 1 := by
  have h8 : (9 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have h16 : (81 : ℝ) ≤ Real.exp 16 := by
    have he : Real.exp (16 : ℝ)=Real.exp 8*Real.exp 8 := by rw [← Real.exp_add]; norm_num
    rw [he]
    nlinarith [Real.exp_pos (8 : ℝ)]
  rw [Real.exp_neg]
  have hp : 0 < Real.exp (16 : ℝ) := Real.exp_pos _
  have he : 72* (Real.exp (16 : ℝ))⁻¹=72/Real.exp 16 := by rw [div_eq_mul_inv]
  rw [he]
  exact (div_lt_one hp).mpr (by linarith)

/-- Actual useful source outcome on the NEW complete protocol and SAME old
selector; this does not depend on a favorable formal word or selected count. -/
theorem adaptive_registered_positive_acceptance :
    0 < (rawLaw (adaptiveWarmup+adaptiveExtra)).real
      {omega | returned adaptiveWarmup adaptiveExtra (feedbackRouter adaptiveWarmup)
        (sourceData regularParameters omega)=some true} := by
  have h := actual_best_accept_probability_ge adaptiveWarmup adaptiveExtra (by decide)
    (feedbackRouter adaptiveWarmup) regularParameters
    (by intro i; norm_num [regularParameters]) true (by norm_num [regularParameters])
  norm_num [adaptiveWarmup,adaptiveExtra] at h
  have hb := adaptive_registered_nonvacuous
  change 0 < (rawLaw (adaptiveWarmup+adaptiveExtra)).real
    {omega | returned adaptiveWarmup adaptiveExtra (feedbackRouter 128)
      (sourceData regularParameters omega)=some true}
  linarith

end
end DualDriveAdaptiveReadCalibration
