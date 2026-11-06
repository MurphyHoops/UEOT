import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionSource
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Complete real-randomized finite tables

A finite outer table is a contingent plan, not a hidden-world sensor. A raw
causal kernel can be sampled once into a complete such table, independently of
the environment. The law is allowed arbitrary real action probabilities.
The unused receipt branches are integrated out in the realization proof.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismTableLaw

open scoped BigOperators
open RegisterJointDecisionSource (Act Obs Noise)
open RegisterMechanismDecisionSource
open RegisterJointDecisionExecution (prepend)
open FiniteJointDecisionSolver (Table Model)
open FiniteJointDecisionSupportedPolicy (RawCausalPolicy)
open UEOT.V3.FiniteDiscountedControl

/-- Finite contingent plans include every row, with all four receipt outcomes. -/
def tableSuccEquiv (H : ℕ) : Table Act Obs (H+1) ≃ (Act × (Obs → Table Act Obs H)) where
  toFun := fun t => match t with | .node a children => (a,children)
  invFun := fun p => .node p.1 p.2
  left_inv := by intro t; cases t; rfl
  right_inv := by intro p; cases p; rfl

instance tableFintype (H : ℕ) : Fintype (Table Act Obs H) := by
  induction H with
  | zero =>
      exact Fintype.ofEquiv Unit {
        toFun := fun _ => .halt
        invFun := fun _ => ()
        left_inv := by intro u; cases u; rfl
        right_inv := by intro t; cases t; rfl }
  | succ H ih =>
      letI := ih
      exact Fintype.ofEquiv (Act × (Obs → Table Act Obs H)) (tableSuccEquiv H).symm

/-- Draw one independent contingent continuation at each possible receipt.
This does not observe any counterfactual result. -/
noncomputable def sampleChildren {T : Type*} (p : Obs → PMF T) : PMF (Obs → T) :=
  (p (false,false)).bind fun t00 =>
  (p (false,true)).bind fun t01 =>
  (p (true,false)).bind fun t10 =>
  (p (true,true)).map fun t11 =>
    fun o => if o.1 then (if o.2 then t11 else t10) else (if o.2 then t01 else t00)

/-- Only the actually observed branch is consumed. All unused random draws
sum to one, which is the finite behavioral-to-mixed policy identity. -/
theorem sampleChildren_bind {T V : Type*} (p : Obs → PMF T) (o : Obs) (f : T → PMF V) :
    (sampleChildren p).bind (fun children => f (children o)) = (p o).bind f := by
  rcases o with ⟨x,y⟩
  cases x <;> cases y <;>
    simp [sampleChildren, PMF.bind_map, PMF.bind_bind, Function.comp_def]

theorem sampleChildren_map {T : Type*} (p : Obs → PMF T) (o : Obs) :
    (sampleChildren p).map (fun children => children o) = p o := by
  change (sampleChildren p).bind (fun children => PMF.pure (children o)) = p o
  rw [sampleChildren_bind, PMF.bind_pure]

theorem sampleChildren_support {T : Type*} (p : Obs → PMF T) (children : Obs → T)
    (hc : children ∈ (sampleChildren p).support) (o : Obs) : children o ∈ (p o).support := by
  rw [← sampleChildren_map p o]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨children,hc,rfl⟩

variable {I : Type*} {M : Model I Act Obs}

noncomputable def actionLaw (pi : RawCausalPolicy M) (h : pi.Memory) : PMF Act :=
  FiniteProbabilityRow.ofRealRow (pi.actionProb h) (pi.actionProb_nonneg h) (pi.actionProb_sum_one h)

@[simp] theorem actionLaw_toReal (pi : RawCausalPolicy M) (h : pi.Memory) (a : Act) :
    (actionLaw pi h a).toReal = pi.actionProb h a :=
  FiniteProbabilityRow.ofRealRow_apply_toReal _ _ _ _

/-- Sample the entire finite policy without consulting the world or mechanism.
The original causal kernel may use all allowed history and real probabilities. -/
noncomputable def sampleTable (pi : RawCausalPolicy M) :
    (H : ℕ) → pi.Memory → PMF (Table Act Obs H)
  | 0, _ => PMF.pure .halt
  | H+1, h => (actionLaw pi h).bind fun a =>
      (sampleChildren (fun o => sampleTable pi H (pi.advance h a o))).map (Table.node a)

/-- A positive sampled complete tree preserves the ORIGINAL supported-only
legality condition. Impossible receipt rows need not be made legal. -/
theorem sampleTable_supported (pi : RawCausalPolicy M) :
    ∀ H (h : pi.Memory) (t : Table Act Obs H),
      FiniteJointDecisionSupportedPolicy.SupportedAdmissible M pi H h →
      t ∈ (sampleTable pi H h).support →
      FiniteJointDecisionSupportedPolicy.SupportedFeasible M (pi.info h) t := by
  intro H
  induction H with
  | zero => intro h t hh ht; cases t; trivial
  | succ H ih =>
      intro h t hh ht
      obtain ⟨a,ha,hta⟩ := (PMF.mem_support_bind_iff _ _ _).mp ht
      obtain ⟨children,hc,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hta
      subst t
      have hprob : pi.actionProb h a ≠ 0 := by
        intro hz
        have hp : actionLaw pi h a = 0 := by
          calc
            actionLaw pi h a = ENNReal.ofReal ((actionLaw pi h a).toReal) :=
              (ENNReal.ofReal_toReal (PMF.apply_ne_top (actionLaw pi h) a)).symm
            _ = 0 := by rw [actionLaw_toReal,hz]; simp
        exact ((PMF.mem_support_iff _ _).mp ha) hp
      obtain ⟨hlegal,hnext⟩ := hh a hprob
      refine ⟨hlegal, ?_⟩
      intro o ho
      have hs := ih (pi.advance h a o) (children o) (hnext o ho)
        (sampleChildren_support _ children hc o)
      simpa only [pi.info_advance] using hs

/-- Fixed independent primitive law. For a source Parameters P use
`noiseLaw P` below, which is the actual four-branch original law. -/
noncomputable def noiseLaw (P : Parameters) : PMF Noise :=
  FiniteProbabilityRow.ofRealRow
    (fun z => (RegisterJointDecisionSource.primitiveWeight (fun _ => P.normal)
      (initialWorld P.goal .S) z : ℝ))
    (by intro z; exact_mod_cast (RegisterJointDecisionSource.primitiveWeight_nonneg
      (fun _ : FaultMechanism => P.normal) (fun _ => P.normal_bounds) (initialWorld P.goal .S) z))
    (by exact_mod_cast (RegisterJointDecisionSource.primitiveWeight_sum_one
      (fun _ : FaultMechanism => P.normal) (initialWorld P.goal .S)))

@[simp] theorem noiseLaw_toReal (P : Parameters) (w : World) (z : Noise) :
    (noiseLaw P z).toReal = ((source P).chance w z : ℝ) := by
  simp [noiseLaw, FiniteProbabilityRow.ofRealRow_apply_toReal, source,
    RegisterJointDecisionSource.primitiveWeight]

/-- Independent full primitive tape, preserving each label as well as mode. -/
noncomputable def tapeLaw (p : PMF Noise) : (H : ℕ) → PMF (Fin H → Noise)
  | 0 => PMF.pure Fin.elim0
  | H+1 => p.bind fun z => (tapeLaw p H).map (Fin.cases z)

/-- Actual table history law under the same primitive at every tick. -/
noncomputable def tableHistoryLaw (goal : Bool) (p : PMF Noise) :
    {H : ℕ} → Table Act Obs H → World → PMF (List (Act × Obs))
  | _, .halt, _ => PMF.pure []
  | H+1, .node a children, w => p.bind fun z =>
      (tableHistoryLaw goal p (children (observe goal w a z)) (step goal w a z)).map
        (List.cons (a,observe goal w a z))

/-- The direct original raw causal-kernel experiment, with no hidden field
passed into actionLaw or advance. Admissibility can restrict its supported rows. -/
noncomputable def rawHistoryLaw (goal : Bool) (p : PMF Noise) (pi : RawCausalPolicy M) :
    ℕ → pi.Memory → World → PMF (List (Act × Obs))
  | 0, _, _ => PMF.pure []
  | H+1, h, w => (actionLaw pi h).bind fun a => p.bind fun z =>
      (rawHistoryLaw goal p pi H (pi.advance h a (observe goal w a z)) (step goal w a z)).map
        (List.cons (a,observe goal w a z))

/-- The sampled mixed table realizes the raw kernel on every world. The SAME
sampleTable distribution therefore works simultaneously for S and G. No model
label, future mode, physical bit, ancestry or birth label enters its sampling. -/
theorem sampled_table_historyLaw_eq_raw (goal : Bool) (p : PMF Noise)
    (pi : RawCausalPolicy M) : ∀ H (h : pi.Memory) (w : World),
      (sampleTable pi H h).bind (fun t => tableHistoryLaw goal p t w) =
        rawHistoryLaw goal p pi H h w := by
  intro H
  induction H with
  | zero => intro h w; simp [sampleTable, rawHistoryLaw, tableHistoryLaw]
  | succ H ih =>
      intro h w
      simp only [sampleTable, rawHistoryLaw, PMF.bind_bind, PMF.bind_map,
        Function.comp_def]
      apply congrArg (PMF.bind (actionLaw pi h))
      funext a
      simp only [tableHistoryLaw]
      rw [PMF.bind_comm]
      apply congrArg (PMF.bind p)
      funext z
      rw [sampleChildren_bind (fun o => sampleTable pi H (pi.advance h a o))
        (observe goal w a z)
        (fun t => (tableHistoryLaw goal p t (step goal w a z)).map
          (List.cons (a,observe goal w a z)))]
      rw [← PMF.map_bind, ih]

/-- The interpreter is exactly the pushforward of the independent full tape. -/
theorem tableHistoryLaw_eq_tape (goal : Bool) (p : PMF Noise) :
    ∀ {H : ℕ} (t : Table Act Obs H) (w : World),
      tableHistoryLaw goal p t w =
        (tapeLaw p H).map (fun z => (packedExecute goal t w z).history) := by
  intro H
  induction H with
  | zero => intro t w; cases t; simp [tableHistoryLaw, tapeLaw, packedExecute, PMF.pure_map]
  | succ H ih =>
      intro t w
      cases t with
      | node a children =>
          simp only [tableHistoryLaw, tapeLaw, PMF.map_bind]
          apply congrArg (PMF.bind p)
          funext z
          rw [ih, PMF.map_comp, PMF.map_comp]
          rfl

/-- This form is consumed by the source-path coupling theorems. -/
theorem rawHistoryLaw_eq_seed_tape (goal : Bool) (p : PMF Noise)
    (pi : RawCausalPolicy M) (H : ℕ) (h : pi.Memory) (w : World) :
    rawHistoryLaw goal p pi H h w =
      (sampleTable pi H h).bind (fun t =>
        (tapeLaw p H).map (fun z => (packedExecute goal t w z).history)) := by
  rw [← sampled_table_historyLaw_eq_raw]
  apply congrArg (PMF.bind (sampleTable pi H h))
  funext t
  exact tableHistoryLaw_eq_tape goal p t w

end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismTableLaw
