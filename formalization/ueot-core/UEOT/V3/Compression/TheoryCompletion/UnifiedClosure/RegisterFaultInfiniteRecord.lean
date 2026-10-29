import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultJointRecord
import UEOT.V3.Compression.Objecthood.ExactPathLawDiscountedHittingTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual infinite source is the Markov interpreter on growing literal
input words. Its countable state does not impose measurability or finiteness on
the given causal policy's internal memory: that memory is deterministically
replayed from the actual word. No failed stage is removed. -/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultInfiniteRecord
open MeasureTheory ProbabilityTheory
open UEOT.V3.FiniteDiscountedControl UEOT.V3.DynamicsKernel UEOT.V3.PathError
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultControlModel RegisterFaultJointRecord
open scoped ENNReal BigOperators
noncomputable section

abbrev Event := Action × Bool × Bool
instance : MeasurableSpace Event := ⊤
instance : MeasurableSingletonClass Event := ⟨fun _ => trivial⟩
instance : MeasurableSpace (List Event) := ⊤
instance : MeasurableSingletonClass (List Event) := ⟨fun _ => trivial⟩

variable {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
variable (epsilon : NNReal) (he : epsilon ≤ 1)
variable (pi : CausalPolicy.{0,0,0} (State n) (fun _ => Action))

abbrev Config := Σ t, pi.Memory t × Organism n

def advance (c : Config pi) (e : Event) : Config pi :=
  let r := modeRecordStep i m c.2.2 e.1 e.2.1 e.2.2
  ⟨c.1+1, pi.advance c.2.1 e.1 r.transaction.parentAfter.physical, r.transaction.parentAfter⟩

def run (c : Config pi) (es : List Event) : Config pi := es.foldl (advance i m pi) c

def trace (c : Config pi) : List Event → List (ModeRecord n)
  | [] => []
  | e :: es => modeRecordStep i m c.2.2 e.1 e.2.1 e.2.2 ::
      trace (advance i m pi c e) es

def tapeEvents : (k : ℕ) → Tape k → List Event
  | 0, _ => []
  | k+1, (a,mode,label,w) => (a,mode,label) :: tapeEvents k w

def snoc : (k : ℕ) → Tape k → Event → Tape (k+1)
  | 0, _, (a,mode,label) => (a,mode,label,())
  | k+1, (a,mode,label,w), e => (a,mode,label,snoc k w e)

@[simp] theorem tapeEvents_snoc : ∀ k (w : Tape k) (e : Event),
    tapeEvents (k+1) (snoc k w e) = tapeEvents k w ++ [e] := by
  intro k
  induction k with
  | zero => rintro ⟨⟩ ⟨a,mode,label⟩; rfl
  | succ k ih =>
      rintro ⟨a,mode,label,w⟩ e
      change (a,mode,label) :: tapeEvents (k+1) (snoc k w e) = _
      rw [ih]
      rfl

@[simp] theorem trace_tapeEvents : ∀ k {t} (h : pi.Memory t) (o : Organism n) (w : Tape k),
    trace i m pi ⟨t,h,o⟩ (tapeEvents k w) = records i m pi k h o w := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih => rintro t h o ⟨a,mode,label,w⟩; simp [trace,tapeEvents,records,advance,ih]

private theorem pmf_sum_real (q : PMF Bool) : ∑ b, (q b).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe q)
  rw [tsum_fintype, ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ b)] at h
  simpa using h

def eventWeight (c : Config pi) (e : Event) : ℝ :=
  pi.actionProb c.2.1 e.1 * (modeLaw epsilon he e.2.1).toReal * (noise e.2.2).toReal

theorem eventWeight_nonneg (c : Config pi) (e : Event) :
    0 ≤ eventWeight noise epsilon he pi c e :=
  mul_nonneg (mul_nonneg (pi.actionProb_nonneg _ _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg

theorem eventWeight_sum (c : Config pi) : ∑ e, eventWeight noise epsilon he pi c e = 1 := by
  simp only [eventWeight,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, pmf_sum_real, mul_one]
  simp_rw [← Finset.mul_sum, pmf_sum_real, mul_one]
  exact pi.actionProb_sum_one c.2.1

def eventLaw (c : Config pi) : PMF Event :=
  FiniteProbabilityRow.ofRealRow (eventWeight noise epsilon he pi c)
    (eventWeight_nonneg noise epsilon he pi c) (eventWeight_sum noise epsilon he pi c)

@[simp] theorem eventLaw_toReal (c : Config pi) (e : Event) :
    (eventLaw noise epsilon he pi c e).toReal = eventWeight noise epsilon he pi c e :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

theorem weight_snoc : ∀ k {t} (h : pi.Memory t) (o : Organism n) (w : Tape k) (e : Event),
    weight i noise m epsilon he pi (k+1) h o (snoc k w e) =
      weight i noise m epsilon he pi k h o w *
        eventWeight noise epsilon he pi (run i m pi ⟨t,h,o⟩ (tapeEvents k w)) e := by
  intro k
  induction k with
  | zero => rintro t h o ⟨⟩ ⟨a,mode,label⟩; simp [weight,snoc,eventWeight,run,tapeEvents]
  | succ k ih =>
      rintro t h o ⟨a,mode,label,w⟩ e
      change (pi.actionProb h a * (modeLaw epsilon he mode).toReal * (noise label).toReal) *
        weight i noise m epsilon he pi (k+1)
          (pi.advance h a (modeRecordStep i m o a mode label).transaction.parentAfter.physical)
          (modeRecordStep i m o a mode label).transaction.parentAfter (snoc k w e) = _
      rw [ih]
      change _ = (pi.actionProb h a * (modeLaw epsilon he mode).toReal * (noise label).toReal) *
        weight i noise m epsilon he pi k
          (pi.advance h a (modeRecordStep i m o a mode label).transaction.parentAfter.physical)
          (modeRecordStep i m o a mode label).transaction.parentAfter w * _
      simp only [run,tapeEvents,List.foldl_cons,advance]
      ring

/-- Rebracket a finite literal tape as its prefix and last sampled event. -/
def snocEquiv : (k : ℕ) → Tape k × Event ≃ Tape (k+1)
  | 0 =>
      { toFun := fun p => (p.2.1,p.2.2.1,p.2.2.2,())
        invFun := fun w => ((),w.1,w.2.1,w.2.2.1)
        left_inv := by rintro ⟨⟨⟩,a,mode,label⟩; rfl
        right_inv := by rintro ⟨a,mode,label,⟨⟩⟩; rfl }
  | k+1 =>
      { toFun := fun p => (p.1.1,p.1.2.1,p.1.2.2.1,snocEquiv k (p.1.2.2.2,p.2))
        invFun := fun w =>
          let p := (snocEquiv k).symm w.2.2.2
          ((w.1,w.2.1,w.2.2.1,p.1),p.2)
        left_inv := by
          rintro ⟨⟨a,mode,label,w⟩,e⟩
          simp only [Equiv.symm_apply_apply]
        right_inv := by
          rintro ⟨a,mode,label,w⟩
          change (a,mode,label,(snocEquiv k) ((snocEquiv k).symm w)) = _
          rw [Equiv.apply_symm_apply] }

@[simp] theorem snocEquiv_apply : ∀ k (w : Tape k) (e : Event),
    snocEquiv k (w,e) = snoc k w e := by
  intro k
  induction k with
  | zero => rintro ⟨⟩ ⟨a,mode,label⟩; rfl
  | succ k ih => rintro ⟨a,mode,label,w⟩ e; change (a,mode,label,snocEquiv k (w,e)) = _; rw [ih]; rfl

private theorem pmf_map_equiv {α β : Type*} (e : α ≃ β) (p : PMF α) (b : β) :
    p.map e b = p (e.symm b) := by
  classical
  rw [PMF.map_apply]
  have hb (a : α) : b = e a ↔ a = e.symm b := by
    rw [e.eq_symm_apply,eq_comm]
  simp_rw [hb]
  simp

theorem tapeLaw_snoc {t : ℕ} (h : pi.Memory t) (o : Organism n) (k : ℕ) :
    tapeLaw i noise m epsilon he pi (k+1) h o =
      (pmfExtend (tapeLaw i noise m epsilon he pi k h o)
        (fun w => eventLaw noise epsilon he pi (run i m pi ⟨t,h,o⟩ (tapeEvents k w)))).map
          (snocEquiv k) := by
  classical
  apply PMF.ext
  intro w
  obtain ⟨⟨v,e⟩,rfl⟩ := (snocEquiv k).surjective w
  rw [pmf_map_equiv,Equiv.symm_apply_apply,pmfExtend_apply]
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul,eventLaw_toReal]
  simp only [tapeLaw,FiniteProbabilityRow.ofRealRow_apply_toReal]
  rw [snocEquiv_apply,weight_snoc]

def wordLaw (c : Config pi) (k : ℕ) : PMF (List Event) :=
  (tapeLaw i noise m epsilon he pi k c.2.1 c.2.2).map (tapeEvents k)

def wordRow (c : Config pi) (es : List Event) : PMF (List Event) :=
  (eventLaw noise epsilon he pi (run i m pi c es)).map (fun e => es ++ [e])

theorem wordLaw_succ (c : Config pi) (k : ℕ) :
    wordLaw i noise m epsilon he pi c (k+1) =
      (wordLaw i noise m epsilon he pi c k).bind (wordRow i noise m epsilon he pi c) := by
  rw [wordLaw,tapeLaw_snoc,PMF.map_comp]
  unfold pmfExtend
  rw [PMF.map_bind]
  change _ = ((tapeLaw i noise m epsilon he pi k c.2.1 c.2.2).map (tapeEvents k)).bind _
  rw [PMF.bind_map]
  congr 1
  funext w
  rw [PMF.map_comp]
  change _ = (eventLaw noise epsilon he pi (run i m pi c (tapeEvents k w))).map _
  congr 1
  funext e
  change tapeEvents (k+1) (snocEquiv k (w,e)) = _
  rw [snocEquiv_apply,tapeEvents_snoc]

/-- Actual next-event source, replaying only the original physical/action
memory. Labels/modes are recorded but never passed to `pi.advance`. -/
def wordKernel (c : Config pi) : Kernel (List Event) (List Event) :=
  Kernel.ofFunOfCountable fun es => (wordRow i noise m epsilon he pi c es).toMeasure

instance wordKernel_isMarkov (c : Config pi) : IsMarkovKernel (wordKernel i noise m epsilon he pi c) where
  isProbabilityMeasure es := by change IsProbabilityMeasure (wordRow i noise m epsilon he pi c es).toMeasure; infer_instance

/-- Genuine infinite Ionescu--Tulcea law of the same literal interpreter. -/
def wordPathLaw (c : Config pi) : Measure (ℕ → List Event) :=
  homTrajMeasure (Measure.dirac []) (wordKernel i noise m epsilon he pi c)

instance wordPathLaw_isProbability (c : Config pi) :
    IsProbabilityMeasure (wordPathLaw i noise m epsilon he pi c) := by unfold wordPathLaw; infer_instance

private theorem wordLaw_succ_measure (c : Config pi) (k : ℕ) :
    (wordLaw i noise m epsilon he pi c (k+1)).toMeasure =
      wordKernel i noise m epsilon he pi c ∘ₘ (wordLaw i noise m epsilon he pi c k).toMeasure := by
  ext s hs
  rw [wordLaw_succ,PMF.toMeasure_bind_apply _ _ _ hs,
    Measure.bind_apply hs (Kernel.aemeasurable _),lintegral_countable']
  apply tsum_congr
  intro es
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton es)]
  exact mul_comm _ _

theorem actual_word_prefix_law (c : Config pi) : ∀ k,
    (wordPathLaw i noise m epsilon he pi c).map (fun z => z k) =
      (wordLaw i noise m epsilon he pi c k).toMeasure := by
  intro k
  induction k with
  | zero =>
      rw [wordPathLaw,UEOT.V3.Compression.Objecthood.homTrajMeasure_time_zero_general]
      have hz : wordLaw i noise m epsilon he pi c 0 = PMF.pure [] := by
        apply PMF.ext
        intro es
        simp [wordLaw,tapeEvents,PMF.map_apply,tapeLaw,
          FiniteProbabilityRow.ofRealRow,weight,PMF.pure_apply]
      rw [hz,PMF.toMeasure_pure]
  | succ k ih =>
      rw [wordPathLaw,UEOT.V3.Compression.Objecthood.homTrajMeasure_time_succ_general]
      change wordKernel i noise m epsilon he pi c ∘ₘ
        (wordPathLaw i noise m epsilon he pi c).map (fun z => z k) = _
      rw [ih,wordLaw_succ_measure]

/-- Every transition appends exactly one sampled event, including failure. -/
theorem wordKernel_ae_append (c : Config pi) (es : List Event) :
    ∀ᵐ ys ∂wordKernel i noise m epsilon he pi c es,
      ∃ e : Event, ys = es ++ [e] := by
  change ∀ᵐ ys ∂(wordRow i noise m epsilon he pi c es).toMeasure, _
  rw [wordRow,← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  apply (ae_map_iff (measurable_of_finite _).aemeasurable
    ((Set.to_countable _).measurableSet)).2
  exact ae_of_all _ fun e => ⟨e,rfl⟩

/-- The infinite source almost surely retains its whole earlier literal word;
this proves compatibility, rather than postulating unrelated prefix laws. -/
theorem wordPathLaw_ae_append (c : Config pi) (k : ℕ) :
    ∀ᵐ z ∂wordPathLaw i noise m epsilon he pi c,
      ∃ e : Event, z (k+1) = z k ++ [e] := by
  let Q := wordKernel i noise m epsilon he pi c
  let μp := wordPathLaw i noise m epsilon he pi c
  let : ∀ j, IsMarkovKernel (homHistoryKernel Q j) :=
    fun j => isMarkovKernel_homHistoryKernel Q j
  have hstep : (μp.map (Preorder.frestrictLe k)) ⊗ₘ homHistoryKernel Q k =
      μp.map (fun z => (Preorder.frestrictLe k z,z (k+1))) := by
    simpa only [μp,wordPathLaw,Q,homTrajMeasure] using
      (Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X:=fun _ : ℕ => List Event) (μ₀:=Measure.dirac [])
        (κ:=homHistoryKernel Q) (a:=k))
  have hg : ∀ᵐ p ∂((μp.map (Preorder.frestrictLe k)) ⊗ₘ homHistoryKernel Q k),
      ∃ e : Event, p.2 = p.1 (lastHistoryIndex k) ++ [e] := by
    apply Measure.ae_compProd_of_ae_ae ((Set.to_countable _).measurableSet)
    apply ae_of_all
    intro h
    exact wordKernel_ae_append i noise m epsilon he pi c (h (lastHistoryIndex k))
  rw [hstep] at hg
  have hh := ae_of_ae_map (by fun_prop : Measurable
      (fun z : ℕ → List Event => (Preorder.frestrictLe k z,z (k+1)))).aemeasurable hg
  simpa only [Preorder.frestrictLe_apply,lastHistoryIndex] using hh

/-- One probability-one set contains the actual empty start and every retained
prefix extension. Arbitrary Type0 causal memories remain allowed. -/
theorem wordPathLaw_ae_coherent (c : Config pi) :
    ∀ᵐ z ∂wordPathLaw i noise m epsilon he pi c,
      z 0 = [] ∧ ∀ k, ∃ e : Event, z (k+1) = z k ++ [e] := by
  have hzero : ∀ᵐ z ∂wordPathLaw i noise m epsilon he pi c, z 0 = [] := by
    have hz := UEOT.V3.Compression.Objecthood.homTrajMeasure_time_zero_general
      (Measure.dirac ([] : List Event)) (wordKernel i noise m epsilon he pi c)
    have ha : ∀ᵐ es ∂(wordPathLaw i noise m epsilon he pi c).map (fun z => z 0), es = [] := by
      rw [wordPathLaw,hz]
      simp
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable ha
  have hall : ∀ᵐ z ∂wordPathLaw i noise m epsilon he pi c,
      ∀ k, ∃ e : Event, z (k+1) = z k ++ [e] := by
    rw [ae_all_iff]
    exact wordPathLaw_ae_append i noise m epsilon he pi c
  exact hzero.and hall


/-- The nth literal event read from the growing record, with an arbitrary
fallback only on impossible/noncoherent words. -/
def eventAt (z : ℕ → List Event) (k : ℕ) : Event :=
  (z (k+1)).getLastD (none,false,false)

def recordAt (c : Config pi) (z : ℕ → List Event) (k : ℕ) : ModeRecord n :=
  let e := eventAt z k
  let o := (run i m pi c (z k)).2.2
  modeRecordStep i m o e.1 e.2.1 e.2.2

private theorem trace_append (c : Config pi) (es fs : List Event) :
    trace i m pi c (es ++ fs) =
      trace i m pi c es ++ trace i m pi (run i m pi c es) fs := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append,trace,run,List.foldl_cons,List.cons_append]
      rw [ih]
      rfl

/-- On the proved probability-one coherent set, the recorded prefix is the
first k entries of one actual infinite transaction stream. -/
theorem coherent_trace_eq_stream (c : Config pi) (z : ℕ → List Event)
    (hz : z 0 = []) (hext : ∀ k, ∃ e : Event, z (k+1) = z k ++ [e]) :
    ∀ k, trace i m pi c (z k) = List.ofFn (fun j : Fin k => recordAt i m pi c z j) := by
  intro k
  induction k with
  | zero => simp [hz,trace]
  | succ k ih =>
      obtain ⟨e,he⟩ := hext k
      have hev : eventAt z k = e := by rw [eventAt,he,List.getLastD_concat]
      rw [he,trace_append,ih,List.ofFn_succ']
      simp only [trace,List.concat_eq_append,Fin.val_castSucc,Fin.val_last]
      simp only [recordAt,hev]


def stageAt (price : NNReal) (c : Config pi) (z : ℕ → List Event) (k : ℕ) : ℝ :=
  RegisterJointRecord.payoff price (recordAt i m pi c z k).transaction

@[fun_prop] theorem measurable_stageAt (price : NNReal) (c : Config pi) (k : ℕ) :
    Measurable (fun z => stageAt i m pi price c z k) := by
  let F : List Event × List Event → ℝ := fun p =>
    let e := p.2.getLastD (none,false,false)
    RegisterJointRecord.payoff price
      (modeRecordStep i m (run i m pi c p.1).2.2 e.1 e.2.1 e.2.2).transaction
  change Measurable (F ∘ (fun z : ℕ → List Event => (z k,z (k+1))))
  exact (measurable_of_countable F).comp
    ((measurable_pi_apply k).prodMk (measurable_pi_apply (k+1)))

theorem step_abs_bound (price : NNReal) (o : Organism n) (a : Action) (mode label : Bool) :
    |RegisterJointRecord.payoff price (modeRecordStep i m o a mode label).transaction| ≤
      1 + (price : ℝ) * m.writeCost := by
  have hp := price.coe_nonneg
  have hc := m.writeCost.coe_nonneg
  cases mode with
  | false => simp [modeRecordStep,RegisterJointRecord.payoff,childCount]; positivity
  | true =>
      cases a <;>
        simp only [modeRecordStep,if_true,RegisterJointRecord.payoff,RegisterJointRecord.recordStep,cost] <;>
        split_ifs <;> simp only [childCount,mul_zero,sub_zero] <;>
        rw [abs_le] <;> constructor <;> nlinarith

theorem stage_abs_bound (price : NNReal) (c : Config pi) (z : ℕ → List Event) (k : ℕ) :
    |stageAt i m pi price c z k| ≤ 1 + (price : ℝ) * m.writeCost :=
  step_abs_bound i m price _ _ _ _

def discountedTerm (price : NNReal) (d : ℝ) (c : Config pi)
    (k : ℕ) (z : ℕ → List Event) : ℝ := d^k * stageAt i m pi price c z k

def infinitePayoff (price : NNReal) (d : ℝ) (c : Config pi) (z : ℕ → List Event) : ℝ :=
  ∑' k, discountedTerm i m pi price d c k z

theorem term_norm_bound (price : NNReal) (d : ℝ) (hd : 0 ≤ d)
    (c : Config pi) (k : ℕ) (z : ℕ → List Event) :
    ‖discountedTerm i m pi price d c k z‖ ≤
      d^k * (1 + (price : ℝ) * m.writeCost) := by
  rw [discountedTerm,Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hd _)]
  exact mul_le_mul_of_nonneg_left (stage_abs_bound i m pi price c z k) (pow_nonneg hd _)

private theorem bound_summable (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) :
    Summable (fun k => d^k * (1 + (price : ℝ) * m.writeCost)) := by
  have hg : Summable (fun k : ℕ => d^k) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs,abs_of_pos hd.1]; exact hd.2)
  exact hg.mul_right _

/-- The literal infinite sum is absolutely summable on every interpreter path,
including paths containing infinitely many failed transactions. -/
theorem actual_payoff_summable (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (c : Config pi) (z : ℕ → List Event) :
    Summable (fun k => discountedTerm i m pi price d c k z) :=
  (bound_summable m price d hd).of_norm_bounded (fun k => term_norm_bound i m pi price d hd.1.le c k z)

/-- Integrability of the actual infinite discounted payoff is derived from the
uniform source bound; it is not an evaluation certificate supplied by a caller. -/
theorem infinite_payoff_integrable (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (c : Config pi) : Integrable (infinitePayoff i m pi price d c)
      (wordPathLaw i noise m epsilon he pi c) := by
  have hm : Measurable (infinitePayoff i m pi price d c) := by
    apply Measurable.tsum
    intro k
    exact measurable_const.mul (measurable_stageAt i m pi price c k)
  apply (integrable_const (∑' k, d^k * (1 + (price : ℝ) * m.writeCost))).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun z => tsum_of_norm_bounded (bound_summable m price d hd).hasSum
    (fun k => term_norm_bound i m pi price d hd.1.le c k z)

private theorem discountedPayoff_append (price : NNReal) (d : ℝ)
    (rs ss : List (ModeRecord n)) :
    discountedPayoff price d (rs ++ ss) =
      discountedPayoff price d rs + d^rs.length * discountedPayoff price d ss := by
  induction rs with
  | nil => simp [discountedPayoff]
  | cons r rs ih => simp only [List.cons_append,discountedPayoff,List.length_cons,ih,pow_succ]; ring

theorem stream_prefix_payoff_sum (price : NNReal) (d : ℝ) (c : Config pi)
    (z : ℕ → List Event) : ∀ k,
    discountedPayoff price d (List.ofFn (fun j : Fin k => recordAt i m pi c z j)) =
      ∑ j ∈ Finset.range k, discountedTerm i m pi price d c j z := by
  intro k
  induction k with
  | zero => simp [discountedPayoff]
  | succ k ih =>
      rw [List.ofFn_succ',List.concat_eq_append,discountedPayoff_append]
      simp only [List.length_ofFn,discountedPayoff,Fin.val_castSucc,Fin.val_last,mul_zero,add_zero]
      rw [ih,Finset.sum_range_succ]
      rfl


/-- Actual infinite execution fees, with no zero padding or terminal cutoff. -/
theorem actual_infinite_resource_viable (c : Config pi) (z : ℕ → List Event)
    (initial supply : ℝ) (hi : 0 ≤ initial) (hs : (m.writeCost : ℝ) ≤ supply) :
    UEOT.V3.Compression.Objecthood.ResourceClosure.ResourceViable initial (fun _ => supply)
      (fun k => (recordAt i m pi c z k).transaction.expenditure) := by
  have hcost (k : ℕ) : (recordAt i m pi c z k).transaction.expenditure =
      if (recordAt i m pi c z k).repairMode then
        cost m (recordAt i m pi c z k).transaction.action else 0 := by
    unfold recordAt
    cases hevent : eventAt z k with
    | mk a rest => cases rest with
      | mk mode label => cases mode <;> rfl
  have heq : (fun k => (recordAt i m pi c z k).transaction.expenditure) =
      (fun k => if (recordAt i m pi c z k).repairMode then
        cost m (recordAt i m pi c z k).transaction.action else 0) := funext hcost
  rw [heq]
  exact RegisterResourceSource.action_schedule_resource_viable m
    (fun k => (recordAt i m pi c z k).transaction.action)
    (fun k => (recordAt i m pi c z k).repairMode) initial supply hi hs


section RecordReadout
local instance : MeasurableSpace (ModeRecord n) := ⊤
local instance : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _ => trivial⟩


@[fun_prop] theorem measurable_recordStream (c : Config pi) :
    Measurable (fun z k => recordAt i m pi c z k) := by
  apply measurable_pi_lambda
  intro k
  let F : List Event × List Event → ModeRecord n := fun p =>
    let e := p.2.getLastD (none,false,false)
    modeRecordStep i m (run i m pi c p.1).2.2 e.1 e.2.1 e.2.2
  change Measurable (F ∘ (fun z : ℕ → List Event => (z k,z (k+1))))
  exact (measurable_of_countable F).comp
    ((measurable_pi_apply k).prodMk (measurable_pi_apply (k+1)))

/-- Probability law of one infinite complete transaction record, constructed
by literal readout of the actual interpreter trajectory. -/
def recordPathLaw (c : Config pi) : Measure (ℕ → ModeRecord n) :=
  (wordPathLaw i noise m epsilon he pi c).map (fun z k => recordAt i m pi c z k)

instance recordPathLaw_isProbability (c : Config pi) :
    IsProbabilityMeasure (recordPathLaw i noise m epsilon he pi c) :=
  Measure.isProbabilityMeasure_map (measurable_recordStream i m pi c).aemeasurable

/-- A total finite-prefix representation. Its default is never used on the
actual length-k recordLaw. It does not discard failed transactions. -/
def listPrefix (c : Config pi) (k : ℕ) (rs : List (ModeRecord n)) : Fin k → ModeRecord n :=
  fun j => (rs[j]?).getD (modeRecordStep i m c.2.2 none false false)

/-- Read the actual complete transaction prefix from the infinite interpreter.
The same finite `recordLaw`, including fault records and failed births, results. -/
theorem actual_record_prefix_law {t : ℕ} (h : pi.Memory t) (o : Organism n) (k : ℕ) :
    (wordPathLaw i noise m epsilon he pi ⟨t,h,o⟩).map
      (fun z => trace i m pi ⟨t,h,o⟩ (z k)) =
        (recordLaw i noise m epsilon he pi k h o).toMeasure := by
  have hm : Measurable (trace i m pi ⟨t,h,o⟩) := measurable_of_countable _
  have hmap := Measure.map_map (μ:=wordPathLaw i noise m epsilon he pi ⟨t,h,o⟩)
    hm (measurable_pi_apply k)
  apply hmap.symm.trans
  rw [actual_word_prefix_law,PMF.toMeasure_map _ _ hm]
  unfold wordLaw recordLaw
  rw [PMF.map_comp]
  congr 2
  funext w
  exact trace_tapeEvents i m pi k h o w


/-- Complete finite cylinder law of the actual infinite transaction stream. -/
theorem actual_stream_prefix_law {t : ℕ} (h : pi.Memory t) (o : Organism n) (k : ℕ) :
    (wordPathLaw i noise m epsilon he pi ⟨t,h,o⟩).map
      (fun z => List.ofFn (fun j : Fin k => recordAt i m pi ⟨t,h,o⟩ z j)) =
        (recordLaw i noise m epsilon he pi k h o).toMeasure := by
  rw [← actual_record_prefix_law i noise m epsilon he pi h o k]
  apply Measure.map_congr
  filter_upwards [wordPathLaw_ae_coherent i noise m epsilon he pi ⟨t,h,o⟩] with z hz
  exact (coherent_trace_eq_stream i m pi ⟨t,h,o⟩ z hz.1 hz.2 k).symm


/-- The infinite record probability law has exactly the existing finite
recordLaw at every prefix, using its length-k list/Fin-k representation. -/
theorem actual_recordPath_prefix_law {t : ℕ} (h : pi.Memory t) (o : Organism n) (k : ℕ) :
    (recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩).map
      (fun (rs : ℕ → ModeRecord n) (j : Fin k) => rs j) =
        ((recordLaw i noise m epsilon he pi k h o).map (listPrefix i m pi ⟨t,h,o⟩ k)).toMeasure := by
  have hp : Measurable (listPrefix i m pi ⟨t,h,o⟩ k) := by intro s hs; trivial
  rw [recordPathLaw,Measure.map_map (by fun_prop) (measurable_recordStream i m pi ⟨t,h,o⟩)]
  calc
    _ = (wordPathLaw i noise m epsilon he pi ⟨t,h,o⟩).map
        (fun z => listPrefix i m pi ⟨t,h,o⟩ k (trace i m pi ⟨t,h,o⟩ (z k))) := by
      apply Measure.map_congr
      filter_upwards [wordPathLaw_ae_coherent i noise m epsilon he pi ⟨t,h,o⟩] with z hz
      rw [coherent_trace_eq_stream i m pi ⟨t,h,o⟩ z hz.1 hz.2 k]
      funext j
      simp [listPrefix,j.isLt]
    _ = ((wordPathLaw i noise m epsilon he pi ⟨t,h,o⟩).map
        (fun z => trace i m pi ⟨t,h,o⟩ (z k))).map (listPrefix i m pi ⟨t,h,o⟩ k) :=
      (Measure.map_map hp ((measurable_of_countable _).comp (measurable_pi_apply k))).symm
    _ = _ := by rw [actual_record_prefix_law,PMF.toMeasure_map _ _ hp]

/-- Every finite discounted actual-path prefix has the given policy value,
with no replacement policy or independent process supplied. -/
theorem actual_path_prefix_integral {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1) (k : ℕ)
    (hx : o.physical = pi.current h) (hp : o.program = m.goal) :
    (∫ z, discountedPayoff price d (trace i m pi ⟨t,h,o⟩ (z k))
      ∂wordPathLaw i noise m epsilon he pi ⟨t,h,o⟩) =
        pi.truncatedValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) k h := by
  have hr := actual_record_prefix_law i noise m epsilon he pi h o k
  have hm : Measurable (fun z : ℕ → List Event => trace i m pi ⟨t,h,o⟩ (z k)) :=
    (measurable_of_countable _).comp (measurable_pi_apply k)
  have hf : Measurable (discountedPayoff (n:=n) price d) := by intro s hs; trivial
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,hr]
  exact actual_record_integral_eq_policy_value i noise m epsilon he pi price d hd k h o hx hp

/-- Actual infinite discounted-path evaluation equals the SAME original causal
policy's infiniteValue for the SAME environmental fault model. -/
theorem actual_infinite_integral_eq_policy_value {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (hx : o.physical = pi.current h) (hp : o.program = m.goal) :
    (∫ z, infinitePayoff i m pi price d ⟨t,h,o⟩ z
      ∂wordPathLaw i noise m epsilon he pi ⟨t,h,o⟩) =
        pi.infiniteValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) h := by
  let c : Config pi := ⟨t,h,o⟩
  let μ := wordPathLaw i noise m epsilon he pi c
  let F := discountedTerm i m pi price d c
  let B := fun k : ℕ => d^k * (1 + (price : ℝ) * m.writeCost)
  have hf (k : ℕ) : Measurable (F k) :=
    measurable_const.mul (measurable_stageAt i m pi price c k)
  have hb (k : ℕ) : ∀ᵐ z ∂μ, ‖F k z‖ ≤ B k :=
    ae_of_all _ fun z => term_norm_bound i m pi price d hd.1.le c k z
  have hint (k : ℕ) : Integrable (F k) μ := (integrable_const (B k)).mono' (hf k).aestronglyMeasurable (hb k)
  have hs := hasSum_integral_of_dominated_convergence (fun k _ => B k)
    (fun k => (hf k).aestronglyMeasurable) hb
    (ae_of_all μ (fun _ => bound_summable m price d hd))
    (integrable_const (∑' k, B k))
    (ae_of_all μ (fun z => (actual_payoff_summable i m pi price d hd c z).hasSum))
  have hprefix (k : ℕ) : (∑ j ∈ Finset.range k, ∫ z, F j z ∂μ) =
      pi.truncatedValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) k h := by
    rw [← integral_finsetSum _ (fun j _ => hint j)]
    rw [← actual_path_prefix_integral i noise m epsilon he pi h o price d hd k hx hp]
    apply integral_congr_ae
    filter_upwards [wordPathLaw_ae_coherent i noise m epsilon he pi c] with z hz
    rw [coherent_trace_eq_stream i m pi c z hz.1 hz.2 k,
      stream_prefix_payoff_sum i m pi price d c z k]
  have hv := CausalPolicy.truncatedValue_tendsto_infiniteValue pi
    (RegisterFaultControlModel.model i noise m price epsilon he d hd) (t:=t) h
  have hv' : Filter.Tendsto (fun k => ∑ j ∈ Finset.range k, ∫ z, F j z ∂μ)
      Filter.atTop (nhds (pi.infiniteValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) h)) :=
    hv.congr' (Filter.Eventually.of_forall fun k => (hprefix k).symm)
  exact tendsto_nhds_unique hs.tendsto_sum_nat hv'

/-- The actual infinite execution of the compiled retained program attains the
original all-causal control optimum, without selecting a different policy. -/
theorem compiled_actual_infinite_integral_optimal (price : NNReal) (d : ℝ)
    (hd : 0 < d ∧ d < 1) (hc : (price : ℝ) * m.writeCost ≤ 1)
    (o : Organism n) (hp : o.program = m.goal) :
    let sigma := selectorPolicy ((substrate i).execute m.goal)
    let M := RegisterFaultControlModel.model i noise m price epsilon he d hd
    (∫ z, infinitePayoff i m sigma price d ⟨0,o.physical,o⟩ z
      ∂wordPathLaw i noise m epsilon he sigma ⟨0,o.physical,o⟩) = M.optimalValue o.physical := by
  dsimp only
  rw [actual_infinite_integral_eq_policy_value i noise m epsilon he
    (selectorPolicy ((substrate i).execute m.goal)) o.physical o price d hd rfl hp]
  exact (compiled_optimal_against_all_causal.{0} i noise m price epsilon he d hd hc).1 (t:=0) o.physical



def streamPayoff (price : NNReal) (d : ℝ) (rs : ℕ → ModeRecord n) : ℝ :=
  ∑' k, d^k * RegisterJointRecord.payoff price (rs k).transaction

@[fun_prop] theorem measurable_streamPayoff (price : NNReal) (d : ℝ) :
    Measurable (streamPayoff (n:=n) price d) := by
  apply Measurable.tsum
  intro k
  apply measurable_const.mul
  have hp : Measurable (fun r : ModeRecord n => RegisterJointRecord.payoff price r.transaction) := by
    intro s hs; trivial
  exact hp.comp (measurable_pi_apply k)

/-- The infinite record payoff is integrable for the actual record probability
law, with no caller-supplied integrability or evaluation certificate. -/
theorem actual_recordPath_payoff_integrable (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (c : Config pi) : Integrable (streamPayoff (n:=n) price d)
      (recordPathLaw i noise m epsilon he pi c) := by
  rw [recordPathLaw]
  apply (integrable_map_measure (measurable_streamPayoff price d).aestronglyMeasurable
    (measurable_recordStream i m pi c).aemeasurable).mpr
  exact infinite_payoff_integrable i noise m epsilon he pi price d hd c

/-- Evaluation of the actual infinite complete-record probability law equals
this same causal policy's value under the original common fault source. -/
theorem actual_recordPath_integral_eq_policy_value {t : ℕ} (h : pi.Memory t) (o : Organism n)
    (price : NNReal) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (hx : o.physical = pi.current h) (hp : o.program = m.goal) :
    (∫ rs, streamPayoff price d rs ∂recordPathLaw i noise m epsilon he pi ⟨t,h,o⟩) =
      pi.infiniteValue (RegisterFaultControlModel.model i noise m price epsilon he d hd) h := by
  rw [recordPathLaw,integral_map (measurable_recordStream i m pi ⟨t,h,o⟩).aemeasurable
    (measurable_streamPayoff price d).aestronglyMeasurable]
  exact actual_infinite_integral_eq_policy_value i noise m epsilon he pi h o price d hd hx hp

/-- Nonzero-noise common realization: the actual infinite executions of the
same compiled program have distinct positive values from the two initial states. -/
theorem positive_actual_infinite_values (noise : PMF Bool) (history : List Bool) :
    let m : Mechanism := ⟨true,1⟩
    let sigma := selectorPolicy ((substrate (0 : Fin 1)).execute true)
    let e : NNReal := 1/4
    let he : e ≤ 1 := by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1)
    (∫ z, infinitePayoff 0 m sigma (1/2) (1/2)
      ⟨0,(fun _ => true),(⟨history,(fun _ => true),true⟩ : Organism 1)⟩ z
      ∂wordPathLaw 0 noise m e he sigma
        ⟨0,(fun _ => true),(⟨history,(fun _ => true),true⟩ : Organism 1)⟩) = 45/32 ∧
    (∫ z, infinitePayoff 0 m sigma (1/2) (1/2)
      ⟨0,(fun _ => false),(⟨history,(fun _ => false),true⟩ : Organism 1)⟩ z
      ∂wordPathLaw 0 noise m e he sigma
        ⟨0,(fun _ => false),(⟨history,(fun _ => false),true⟩ : Organism 1)⟩) = 33/32 := by
  dsimp only
  constructor
  · rw [compiled_actual_infinite_integral_optimal (0 : Fin 1) noise
      (⟨true,1⟩ : Mechanism) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1))
      (1/2) (1/2) (by norm_num) (by norm_num)
      (⟨history,(fun _ => true),true⟩ : Organism 1) rfl]
    exact (positive_noise_values noise).1
  · rw [compiled_actual_infinite_integral_optimal (0 : Fin 1) noise
      (⟨true,1⟩ : Mechanism) (1/4) (by exact_mod_cast (by norm_num : (1/4 : ℝ) ≤ 1))
      (1/2) (1/2) (by norm_num) (by norm_num)
      (⟨history,(fun _ => false),true⟩ : Organism 1) rfl]
    exact (positive_noise_values noise).2


end RecordReadout

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultInfiniteRecord
