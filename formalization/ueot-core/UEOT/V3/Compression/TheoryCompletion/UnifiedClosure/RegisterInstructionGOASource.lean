import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGODScale
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionHomeostasis
import UEOT.V3.Compression.TheoryCompletion.GOA

/-!
Original promise: GOA must be a source-derived actual long-run structure, not another name for GOD/argmax or physical safety.
Existing premise: actual submitted/returned ASTs preserve complete records/value; restoration is an executable actual-update check, but no original invariant-law GOA was derived from this continuing mechanism.
Reduced premise: derive the real reset row, one-step actual physical law, stationary finite-kernel law and original InvariantLawGOA/P9 from the SAME fresh mode/label product and retained seed.
Family/boundary: original restoring ASTs and actual synthesize output, unchanged parent/history/actions/fault/price/cost; passive registers persist, so fine invariant laws need not be unique.
Consumer: original selectorInvariantGoaSet/InvariantLawGOA and PreservesGOA, alongside the SAME compiled GOD/value consumer; not a chosen greedy tie-break, universal GOA type, all-six closure or energy funding.

The stationary distribution is computed from the actual initial physical seed
and original modeLaw, not supplied as a desired invariant-law field. The actual
physical marginal after EVERY positive time is derived from literal retained-
parent recursion under the original declared fresh IID primitive product.
Neither physical stationarity nor GOD membership is identified with permanent
legitimacy or purpose-value equality. In particular, the existing always-paid
versus compiled strict value boundary remains unchanged. No action, observation,
initialization, protected program, resource port or empirical sample is added.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGOASource
open MeasureTheory ProbabilityTheory Function
open UEOT.V3
open UEOT.V3.FiniteDiscountedControl
open UEOT.V3.FiniteDobrushin
open UEOT.V3.Compression.TheoryCompletion
open UEOT.V3.Compression.GoaGaugeInvariance
open UEOT.V3.Compression.InvariantSetGaugeInvariance
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterInstructionPurposeScale RegisterInstructionRecoveryScale RegisterInstructionGODScale
open RegisterSemanticInstructionInfinite RegisterInstructionHomeostasis
open scoped ENNReal BigOperators
noncomputable section
noncomputable local instance {n : ℕ} : DecidableEq (State n) := Classical.decEq _

/-- Actual mode outcome after a restoring instruction. Passive registers retain
this SAME physical seed; resetState is a derived update, not a reset action. -/
def resetState {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) (mode : Bool) : State n :=
  Function.update x i (if mode then m.goal else !m.goal)

@[simp] theorem reset_reset {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) (a b : Bool) :
    resetState i m (resetState i m x a) b=resetState i m x b := by
  ext j
  by_cases hj : j=i
  · subst j; simp [resetState]
  · simp [resetState,Function.update_of_ne hj]

def sourceLaw {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) (x : State n) : PMF (State n) :=
  (RegisterFaultControlModel.modeLaw epsilon he).map (resetState i m x)

theorem actual_mode_next {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (x : State n) (mode : Bool) :
    RegisterFaultControlModel.modeNext i m x (interpret p x) mode=resetState i m x mode := by
  cases mode
  · rfl
  · change update i x (interpret p x)=Function.update x i m.goal
    exact checked_update_eq_write i m.goal p hc x

/-- SAME original actual P5 source row, with no independently requested law. -/
theorem actual_physical_row {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1)
    (p : Instruction n) (hc : restorationCheck i m.goal p=true) (x : State n) :
    RegisterFaultControlSource.physicalSource i m epsilon he x (interpret p x)=sourceLaw i m epsilon he x := by
  rw [←RegisterFaultControlModel.modeLaw_next_eq_physicalSource]
  unfold sourceLaw
  congr 1
  funext mode
  exact actual_mode_next i m p hc x mode

@[simp] theorem sourceLaw_reset {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1)
    (x : State n) (mode : Bool) :
    sourceLaw i m epsilon he (resetState i m x mode)=sourceLaw i m epsilon he x := by
  unfold sourceLaw
  congr 1
  funext mode'
  exact reset_reset i m x mode mode'

/-- Source-derived idempotence of the actual law on this retained passive
fiber. It does not say all initial passive fibers have the SAME invariant law. -/
theorem sourceLaw_stationary {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) (x : State n) :
    (sourceLaw i m epsilon he x).bind (sourceLaw i m epsilon he)=sourceLaw i m epsilon he x := by
  change ((RegisterFaultControlModel.modeLaw epsilon he).map (resetState i m x)).bind (sourceLaw i m epsilon he)=_
  rw [PMF.bind_map]
  change (RegisterFaultControlModel.modeLaw epsilon he).bind
    (fun mode => sourceLaw i m epsilon he (resetState i m x mode))=_
  simp only [sourceLaw_reset,PMF.bind_const]

/-- Literal actual parent physical state at positive time, on EVERY primitive
stream. No path, fault or paid write is discarded to obtain the distribution. -/
theorem actual_parent_reset {n : ℕ} (i : Fin n) (m : Mechanism) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (o : Organism n) (w : Stream) (t : ℕ) :
    (parentAt i m p o w (t+1)).physical=resetState i m o.physical (w t).1 := by
  induction t with
  | zero =>
    rw [parentAt_succ,recordAt,step_physical,actual_mode_next i m p hc]
    rfl
  | succ t ih =>
    rw [parentAt_succ,recordAt,step_physical,actual_mode_next i m p hc,ih,reset_reset]


@[fun_prop] theorem measurable_actual_positive_physical {n : ℕ} (i : Fin n) (m : Mechanism)
    (p : Instruction n) (hc : restorationCheck i m.goal p=true) (o : Organism n) (t : ℕ) :
    Measurable (fun w => (parentAt i m p o w (t+1)).physical) := by
  simp_rw [actual_parent_reset i m p hc o]
  exact (measurable_of_finite (resetState i m o.physical)).comp
    (measurable_fst.comp (measurable_pi_apply t))

/-- The actual marginal is a genuine probability pushforward, not a pair of
nonmeasurable readouts whose maps happened to be zero. -/
theorem actual_positive_time_probability {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (hc : restorationCheck i m.goal p=true)
    (o : Organism n) (t : ℕ) :
    IsProbabilityMeasure ((iidSource noise epsilon he).map (fun w => (parentAt i m p o w (t+1)).physical)) :=
  Measure.isProbabilityMeasure_map (measurable_actual_positive_physical i m p hc o t).aemeasurable

/-- The real physical marginal after EVERY positive time is this computed law
under the original same IID primitive source; it is not an assumed GOA field. -/
theorem actual_positive_time_law {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) (hc : restorationCheck i m.goal p=true)
    (o : Organism n) (t : ℕ) :
    (iidSource noise epsilon he).map (fun w => (parentAt i m p o w (t+1)).physical)=
      (sourceLaw i m epsilon he o.physical).toMeasure := by
  simp_rw [actual_parent_reset i m p hc o]
  change (iidSource noise epsilon he).map ((resetState i m o.physical) ∘ (fun w : Stream => (w t).1))=_
  rw [←Measure.map_map (measurable_of_finite _) (by fun_prop),source_mode_law,
    PMF.toMeasure_map _ _ (measurable_of_finite _)]
  rfl

/-- Minimal finite PMF/simplex representation adapter for the original GOA API. -/
private def pmfSimplex {S : Type} [Fintype S] (q : PMF S) : stdSimplex ℝ S := by
  refine ⟨fun x => (q x).toReal,fun _ => ENNReal.toReal_nonneg,?_⟩
  have h:=congrArg ENNReal.toReal (PMF.tsum_coe q)
  rw [tsum_fintype,ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top _ x)] at h
  simpa using h

private theorem simplexPMF_pmfSimplex {S : Type} [Fintype S] (q : PMF S) : simplexPMF (pmfSimplex q)=q := by
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [simplexPMF_toReal]
  rfl

def sourceSimplex {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) (x : State n) : stdSimplex ℝ (State n) :=
  pmfSimplex (sourceLaw i m epsilon he x)

@[simp] theorem sourceSimplex_pmf {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) (x : State n) :
    simplexPMF (sourceSimplex i m epsilon he x)=sourceLaw i m epsilon he x :=
  simplexPMF_pmfSimplex _

/-- The GOA matrix is the ORIGINAL source under this literal AST, with exactly
the same model reward/cost/discount parameters, not an independent kernel. -/
def actualMatrix {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (p : Instruction n) : Matrix (State n) (State n) ℝ :=
  selectorClosedLoopMatrix (RegisterFaultControlModel.model i noise m price epsilon he d hd) (interpret p)

theorem actualMatrix_stochastic {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (p : Instruction n) :
    actualMatrix i noise m price epsilon he d hd p∈Matrix.rowStochastic ℝ (State n) :=
  selectorClosedLoopMatrix_rowStochastic _ _

theorem actualMatrix_row {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (p : Instruction n) (hc : restorationCheck i m.goal p=true) (x : State n) :
    rowPMF (actualMatrix i noise m price epsilon he d hd p) (actualMatrix_stochastic i noise m price epsilon he d hd p) x=
      sourceLaw i m epsilon he x := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [rowPMF_toReal,actualMatrix,selectorClosedLoopMatrix_apply,
    RegisterFaultControlModel.model_transition_eq_physicalSource,actual_physical_row i m epsilon he p hc]

/-- Original invariant-law GOA is derived from the actual mechanism. This is
NOT an argmax renaming, claimed unique global attractor or perpetual safety. -/
theorem actual_invariant_goa {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (p : Instruction n) (hc : restorationCheck i m.goal p=true) (x : State n) :
    InvariantLawGOA (actualMatrix i noise m price epsilon he d hd p)
      (actualMatrix_stochastic i noise m price epsilon he d hd p) (sourceSimplex i m epsilon he x) := by
  have hpmf : simplexPMF (FiniteDobrushin.step (actualMatrix i noise m price epsilon he d hd p)
      (actualMatrix_stochastic i noise m price epsilon he d hd p) (sourceSimplex i m epsilon he x))=
      simplexPMF (sourceSimplex i m epsilon he x) := by
    rw [simplexPMF_step_eq_bind,sourceSimplex_pmf]
    have hr : rowPMF (actualMatrix i noise m price epsilon he d hd p)
        (actualMatrix_stochastic i noise m price epsilon he d hd p)=sourceLaw i m epsilon he := by
      funext y
      exact actualMatrix_row i noise m price epsilon he d hd p hc y
    rw [hr]
    exact sourceLaw_stationary i m epsilon he x
  change FiniteDobrushin.step _ _ _=_
  apply Subtype.ext
  funext y
  have h:=congrArg (fun q : PMF (State n) => (q y).toReal) hpmf
  simpa only [simplexPMF_toReal] using h

@[simp] theorem reset_projection {n : ℕ} (i : Fin n) (m : Mechanism) (x : State n) (mode : Bool) :
    projectState i (resetState i m x mode)=resetState (0 : Fin 1) m (projectState i x) mode :=
  project_set i x _

/-- Actual normalized stationary law commutes with the SAME physical map. -/
theorem actual_sourceLaw_projection {n : ℕ} (i : Fin n) (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) (x : State n) :
    (sourceLaw i m epsilon he x).map (projectState i)=sourceLaw (0 : Fin 1) m epsilon he (projectState i x) := by
  unfold sourceLaw
  rw [PMF.map_comp]
  congr 1
  funext mode
  exact reset_projection i m x mode

abbrev GOAObject {n : ℕ} (i : Fin n) (b : Bool) := Organism n × RecoveringPair i b

def goaScale {n : ℕ} (i : Fin n) (b : Bool) :
    ObjectScaleMap (State n) (State 1) (GOAObject i b) (Organism 1 × Instruction 1) :=
  ⟨projectState i,fun obj => (projectOrganism i obj.1,obj.2.val.val.2)⟩

def ActualGOA {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (obj : Organism n × Instruction n) : Prop :=
  InvariantLawGOA (actualMatrix i noise m price epsilon he d hd obj.2)
    (actualMatrix_stochastic i noise m price epsilon he d hd obj.2)
    (sourceSimplex i m epsilon he obj.1.physical)

/-- Original PreservesGOA uses real invariant-law semantics and this actual
returned program; the computed stationary law is tied by projection above. -/
theorem actual_preserves_goa {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) :
    PreservesGOA (goaScale i m.goal)
      (fun obj => ActualGOA i noise m price epsilon he d hd (obj.1,obj.2.val.val.1))
      (ActualGOA (0 : Fin 1) noise m price epsilon he d hd) := by
  intro obj _
  exact actual_invariant_goa 0 noise m price epsilon he d hd obj.2.val.val.2
    ((returned_restoration_iff i m.goal _ _ obj.2.val.property).mp obj.2.property) _

/-- Source constructs the fine invariant property and invokes the original P9
consumer for the actual coarse parent/controller; no GOA certificate is input. -/
theorem p9_actual_returned_goa {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (obj : GOAObject i m.goal) :
    ActualGOA (0 : Fin 1) noise m price epsilon he d hd ((goaScale i m.goal).objectMap obj) :=
  transport_object_property (goaScale i m.goal)
    (fun obj => ActualGOA i noise m price epsilon he d hd (obj.1,obj.2.val.val.1))
    (ActualGOA (0 : Fin 1) noise m price epsilon he d hd)
    (fine:=obj) (coarse:=((goaScale i m.goal).objectMap obj)) rfl
    (actual_preserves_goa i noise m price epsilon he d hd)
    (actual_invariant_goa i noise m price epsilon he d hd obj.2.val.val.1 obj.2.property obj.1.physical)

/-- Coarse active state has no remaining passive-coordinate memory. -/
theorem coarse_sourceLaw_constant (m : Mechanism) (epsilon : NNReal) (he : epsilon≤1) (x y : State 1) :
    sourceLaw (0 : Fin 1) m epsilon he x=sourceLaw (0 : Fin 1) m epsilon he y := by
  unfold sourceLaw
  congr 1
  funext mode j
  have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
  subst j
  simp [resetState]

/-- On the coarse one-bit source this actual invariant law is unique. This is
proved from the real constant row, not assumed as a Dobrushin/GOA certificate. -/
theorem coarse_invariant_unique (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (p : Instruction 1)
    (hc : restorationCheck (0 : Fin 1) m.goal p=true) (x : State 1) (mu : stdSimplex ℝ (State 1))
    (hinv : InvariantLawGOA (actualMatrix 0 noise m price epsilon he d hd p)
      (actualMatrix_stochastic 0 noise m price epsilon he d hd p) mu) :
    mu=sourceSimplex 0 m epsilon he x := by
  change FiniteDobrushin.step _ _ mu=mu at hinv
  have hpmf:=congrArg simplexPMF hinv
  rw [simplexPMF_step_eq_bind] at hpmf
  have hr : rowPMF (actualMatrix 0 noise m price epsilon he d hd p)
      (actualMatrix_stochastic 0 noise m price epsilon he d hd p)=fun _ => sourceLaw 0 m epsilon he x := by
    funext y
    rw [actualMatrix_row 0 noise m price epsilon he d hd p hc]
    exact coarse_sourceLaw_constant m epsilon he y x
  rw [hr,PMF.bind_const] at hpmf
  apply Subtype.ext
  funext y
  have h:=congrArg (fun q : PMF (State 1) => (q y).toReal) hpmf
  change mu.1 y=((sourceLaw 0 m epsilon he x) y).toReal
  simpa only [simplexPMF_toReal] using h.symm

/-- An actually forgotten passive bit is retained forever by this source. -/
theorem actual_passive_marginal {n : ℕ} (i j : Fin n) (hj : j≠i) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (x : State n) :
    (sourceLaw i m epsilon he x).map (fun y => y j)=PMF.pure (x j) := by
  unfold sourceLaw
  rw [PMF.map_comp]
  have hf : ((fun y : State n => y j) ∘ resetState i m x)=fun _ : Bool => x j := by
    funext mode
    simp [resetState,Function.update_of_ne hj]
  rw [hf]
  exact PMF.map_const _ _

/-- Strict native GOA boundary: forgetting a passive register collapses
DISTINCT actual fine invariant laws, even with the SAME compiled program. -/
theorem fine_invariant_nonunique (noise : PMF Bool) (price epsilon : NNReal) (he : epsilon≤1)
    (d : ℝ) (hd : 0<d ∧ d<1) :
    ∃ mu nu : stdSimplex ℝ (State 2), mu≠nu ∧
      InvariantLawGOA (actualMatrix 0 noise ⟨true,1⟩ price epsilon he d hd (compile 0 true))
        (actualMatrix_stochastic 0 noise ⟨true,1⟩ price epsilon he d hd (compile 0 true)) mu ∧
      InvariantLawGOA (actualMatrix 0 noise ⟨true,1⟩ price epsilon he d hd (compile 0 true))
        (actualMatrix_stochastic 0 noise ⟨true,1⟩ price epsilon he d hd (compile 0 true)) nu := by
  let mu:=sourceSimplex (0 : Fin 2) ⟨true,1⟩ epsilon he (passiveInitial false).physical
  let nu:=sourceSimplex (0 : Fin 2) ⟨true,1⟩ epsilon he (passiveInitial true).physical
  have hc : restorationCheck (0 : Fin 2) true (compile 0 true)=true := by
    rw [restorationCheck_iff]
    intro x
    rw [same_repair_different_value_physical]
    simp [interpret,RegisterRepairSource.update]
  refine ⟨mu,nu,?_,actual_invariant_goa 0 noise ⟨true,1⟩ price epsilon he d hd _ hc _,
    actual_invariant_goa 0 noise ⟨true,1⟩ price epsilon he d hd _ hc _⟩
  intro hh
  have h:=congrArg (fun law : stdSimplex ℝ (State 2) => (simplexPMF law).map (fun x => x 1)) hh
  dsimp only [mu,nu] at h
  rw [sourceSimplex_pmf,sourceSimplex_pmf,
    actual_passive_marginal 0 1 (by decide),actual_passive_marginal 0 1 (by decide)] at h
  have hp:=congrArg (fun q : PMF Bool => q false) h
  simp [passiveInitial] at hp


/-- Membership of the original actual-selector invariant GOA set. The chosen
compiled GOD selector is not replaced by an arbitrary canonical greedy tie. -/
theorem actual_selector_goa {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (p : Instruction n)
    (hc : restorationCheck i m.goal p=true) (x : State n) :
    sourceSimplex i m epsilon he x∈selectorInvariantGoaSet
      (RegisterFaultControlModel.model i noise m price epsilon he d hd) (interpret p) :=
  actual_invariant_goa i noise m price epsilon he d hd p hc x

/-- Original compiler actually passes the executable restoration check. -/
theorem actual_compiled_restores {n : ℕ} (i : Fin n) (b : Bool) :
    restorationCheck i b (compile i b)=true := by
  rw [restorationCheck_iff]
  intro x
  rw [same_repair_different_value_physical]
  simp [interpret,RegisterRepairSource.update]

/-- SAME parent, actual returned q and source: original GOD, actual optimal
birth/fee value, and genuine original invariant-law GOA are jointly consumed.
These are distinct conclusions; no optimality-to-restoration reverse is used. -/
theorem actual_compiled_god_goa {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism) (price epsilon : NNReal)
    (he : epsilon≤1) (d : ℝ) (hd : 0<d ∧ d<1) (hc : (price : ℝ)*m.writeCost≤1)
    (o : Organism n) (hp : o.program=m.goal) :
    IsBellmanGODSelector (RegisterFaultControlModel.model (0 : Fin 1) noise m price epsilon he d hd)
      (interpret (returnedProgram i (compile i m.goal))) ∧
    actualValue (0 : Fin 1) noise m epsilon he price d (projectOrganism i o) (returnedProgram i (compile i m.goal))=
      (RegisterFaultControlModel.model i noise m price epsilon he d hd).optimalValue o.physical ∧
    ActualGOA (0 : Fin 1) noise m price epsilon he d hd (projectOrganism i o,returnedProgram i (compile i m.goal)) := by
  have hg:=compiled_actual_p9_god i noise m price epsilon he d hd hc o hp
  let comp : Accepted i:=⟨(compile i m.goal,returnedProgram i (compile i m.goal)),compiled_synthesis i m.goal⟩
  let recovering : RecoveringPair i m.goal:=⟨comp,actual_compiled_restores i m.goal⟩
  have hgoa:=p9_actual_returned_goa i noise m price epsilon he d hd (o,recovering)
  exact ⟨hg.1,hg.2,hgoa⟩

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionGOASource
