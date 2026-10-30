import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbe
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
Original promise: finite-data dynamic purpose evidence belongs to the same actual post-probe organism, returned AST and infinite execution.
Existing source: original full probeTrace/postProbeParent, new data-only classify with original common calibration, all-price actual GOD/P9 and original infinite complete-record law.
Reduced premise: derive same-parent program/probe-readout binding, actual returned-q optimal native integral on Good, and a genuine joint training/deployment probability law with unchanged training marginal.
Model/boundary: original fixed complete probes followed by fresh original mode/label execution of the data-returned allowed controller; no new action/reset/install/observation/source parameter input or retry.
Consumer: original P9/GOD/actualValue and recordPathLaw/integrability/prefix interface, with joint accepted-wrong risk bounded by the original single calibration budget.

Evaluation starts after all 2N probes, from their literal terminal parent.
All probe failures/births/fees remain in probeTrace; they are not silently
charged zero or included in a different deployment-origin optimum. This leaf
does not prove training/deployment resource funding. Raw modes remain analysis
variables, not selector inputs. The fresh continuation is the source's original
registered environmental mode/label law, with the same unknown parameters.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeInfinite
open MeasureTheory ProbabilityTheory Set
open UEOT.V3.FiniteDiscountedControl UEOT.V3.Compression.TheoryCompletion
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultControlModel
open RegisterFaultJointRecord RegisterFaultInfiniteRecord RegisterFaultFinitePurposeProbe
open RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe RegisterFaultDynamicPriceProgram
open RegisterSemanticInstructionScale RegisterInstructionPurposeScale RegisterActuatorScaleSource
noncomputable section

local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

theorem returned_synthesis {n : ℕ} (i : Fin n) (v : Verdict) :
    synthesize i (returnedAST i v)=some (returnedProgram i (returnedAST i v)) := by
  cases v with
  | repair b=>exact compiled_synthesis i b
  | idle b=>simp [returnedAST,synthesize,finiteCheck,interpret]
  | unknown=>simp [returnedAST,synthesize,finiteCheck,interpret]

/-- The actual data-selected controller/returned coarse controller consume
native P9 and the SAME post-probe complete-record infinite payoff integral. -/
theorem actual_good_returned_program {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1)
    (omega : Coordinate N→Bool×Bool) (o : Organism n) (ho : o.program=m.goal)
    (hg : omega∈Good noise m epsilon he N width (u : ℝ))
    (ha : classify price width d u (sourceData m width omega)≠.unknown) :
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let q:=returnedProgram i p
    let M:=model i noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd)
    synthesize i p=some q ∧
    IsBellmanGODSelector M (interpret p) ∧
    IsBellmanGODSelector (model (0 : Fin 1) noise m (priceValue price hp) epsilon he (d : ℝ) (by exact_mod_cast hd)) (interpret q) ∧
    Integrable (streamPayoff (priceValue price hp) (d : ℝ))
      (recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,parent.physical,parent⟩) ∧
    actualValue i noise m epsilon he (priceValue price hp) (d : ℝ) parent p=M.optimalValue parent.physical ∧
    actualValue (0 : Fin 1) noise m epsilon he (priceValue price hp) (d : ℝ) (projectOrganism i parent) q=
      M.optimalValue parent.physical := by
  let parent:=postProbeParent i m omega o
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  let q:=returnedProgram i p
  have hdr : 0<(d : ℝ) ∧ (d : ℝ)<1:=by exact_mod_cast hd
  have hparent : parent.program=m.goal:=(postProbeParent_program i m omega o).trans ho
  have hs:=returned_synthesis i (classify price width d u (sourceData m width omega))
  have hf:=good_accepted_god i noise m epsilon he price width d u hp hw hd omega hg ha
  let pq : RegisterSemanticInstructionScale.Accepted i:=⟨(p,q),hs⟩
  have hq : IsBellmanGODSelector (model (0 : Fin 1) noise m (priceValue price hp) epsilon he (d : ℝ) hdr) (interpret q) :=
    transport_object_property (RegisterInstructionGODScale.godScale i)
      (fun obj=>IsBellmanGODSelector (model i noise m (priceValue price hp) epsilon he (d : ℝ) hdr) (interpret obj.2.val.1))
      (fun obj=>IsBellmanGODSelector (model (0 : Fin 1) noise m (priceValue price hp) epsilon he (d : ℝ) hdr) (interpret obj.2))
      (fine:=(parent,pq)) (coarse:=((RegisterInstructionGODScale.godScale i).objectMap (parent,pq))) rfl
      (actual_all_price_preserves_god i noise m (priceValue price hp) epsilon he (d : ℝ) hdr) hf
  have hv:=RegisterInstructionGODScale.actual_god_value i noise m (priceValue price hp) epsilon he (d : ℝ) hdr parent hparent p hf
  exact ⟨hs,hf,hq,actual_value_integrable i noise m epsilon he (priceValue price hp) (d : ℝ) hdr parent p,
    hv,(actual_value_transport i noise m epsilon he (priceValue price hp) (d : ℝ) parent p q hs).symm.trans hv⟩

/-- Literal continuation law, computed from all the original training draws,
actual terminal parent and the data-only returned AST. -/
def deploymentKernel {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    Kernel (Coordinate N→Bool×Bool) (ℕ→ModeRecord n) where
  toFun:=fun omega=>
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    recordPathLaw i noise m epsilon he (astPolicy p) ⟨0,parent.physical,parent⟩
  measurable':=measurable_of_finite _

/-- Every finite prefix is the original complete recordLaw of THIS data
returned program at THIS actual terminal parent. -/
theorem actual_deployment_prefix {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n)
    (omega : Coordinate N→Bool×Bool) (k : ℕ) :
    let parent:=postProbeParent i m omega o
    let p:=returnedAST i (classify price width d u (sourceData m width omega))
    let sigma:=astPolicy p
    (deploymentKernel i noise m epsilon he price width d u o omega).map
      (fun (rs : ℕ→ModeRecord n) (j : Fin k)=>rs j)=
      ((recordLaw i noise m epsilon he sigma k (t:=0) parent.physical parent).map
        (listPrefix i m sigma ⟨0,parent.physical,parent⟩ k)).toMeasure :=
  actual_recordPath_prefix_law i noise m epsilon he _ _ _ k

instance deploymentKernel_markov {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    IsMarkovKernel (deploymentKernel (N:=N) i noise m epsilon he price width d u o) :=
  ⟨fun _=>by dsimp [deploymentKernel];infer_instance⟩

def jointLaw {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    Measure ((Coordinate N→Bool×Bool)×(ℕ→ModeRecord n)) :=
  rawLaw noise epsilon he N ⊗ₘ deploymentKernel i noise m epsilon he price width d u o

instance jointLaw_probability {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    IsProbabilityMeasure (jointLaw (N:=N) i noise m epsilon he price width d u o) := by
  unfold jointLaw
  infer_instance

/-- No successful training episodes or future paths are filtered out. -/
theorem actual_joint_training_marginal {n N : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ) (o : Organism n) :
    (jointLaw (N:=N) i noise m epsilon he price width d u o).fst=rawLaw noise epsilon he N :=
  Measure.fst_compProd _ _

/-- The risk is P(Accept AND returned program not GOD) under the genuine joint
law, not a conditional error rate among accepted/selected-success experiments. -/
theorem actual_joint_accepted_wrong_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) (hN : 0<N) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (hu : 0≤u) (o : Organism n) :
    (jointLaw (N:=N) i noise m epsilon he price width d u o).real
      (Prod.fst ⁻¹' Error (N:=N) i noise m epsilon he price width d u hp hd)≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2)) := by
  rw [measureReal_def]
  rw [←Measure.fst_apply (Set.toFinite _).measurableSet,actual_joint_training_marginal]
  exact actual_joint_error_bound i noise m epsilon he N hN price width d u hp hw hd hu

/-- For separated sources the SAME joint law has one budget for UNKNOWN OR
accepted-wrong, since both are excluded by the one original common Good. -/
theorem actual_joint_undecided_or_wrong_bound {n : ℕ} (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (N : ℕ) (hN : 0<N) (price width d u : ℚ)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (hu : 0≤u) (o : Organism n)
    (hsep : DynamicallySeparated m epsilon price width d u) (hr : (u : ℝ)<repairChance epsilon) :
    (jointLaw (N:=N) i noise m epsilon he price width d u o).real
      (Prod.fst ⁻¹' {omega | classify price width d u (sourceData m width omega)=.unknown ∨
        omega∈Error (N:=N) i noise m epsilon he price width d u hp hd})≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2)) := by
  rw [measureReal_def,←Measure.fst_apply (Set.toFinite _).measurableSet,actual_joint_training_marginal]
  exact actual_undecided_or_wrong_bound i noise m epsilon he N hN price width d u hp hw hd hu hsep hr

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeInfinite
