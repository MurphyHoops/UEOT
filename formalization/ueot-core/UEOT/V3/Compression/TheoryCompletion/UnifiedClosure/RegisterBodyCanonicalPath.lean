import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockReturnTransport
import UEOT.V3.RecoveryHittingBound
import Mathlib.Probability.Process.HittingTime

/-!
Original promise: P10 first-recovery expectations must concern the actual ongoing body source, not an unrelated homogeneous chain.
Existing source: original compiler/round execution, full-past independent fresh rounds, genuine block transport and exact no-return windows.
Premise reduced: construct the actual macro physical kernel and derive the whole canonical homTrajMeasure law from the real retained-parent path.
Model/boundary: finite body, original mode/label draws and FinRange sweep; one macro step is k literal transactions; k0 is empty physical execution.
Consumer: original RecoveryHittingBound.p_rec_04, with its actual homogeneous-kernel semantics; no desired path-law/mean/optional-stopping certificate field.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBodyCanonicalPath
open MeasureTheory ProbabilityTheory Set Filter
open UEOT.V3.DynamicsKernel
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterRotatingBodyReturns
open scoped ENNReal Topology
noncomputable section

/-- Actual one-round physical response law, derived below from roundParent. -/
def bodyLaw (k : ℕ) (b : Bool) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) : Measure (State k):=
  (roundLaw k noise epsilon he).map (bodyState b)
instance bodyLaw_probability (k : ℕ) (b : Bool) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) :
    IsProbabilityMeasure (bodyLaw k b noise epsilon he):=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def bodyKernel (k : ℕ) (b : Bool) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) : Kernel (State k) (State k):=
  Kernel.const (State k) (bodyLaw k b noise epsilon he)
instance bodyKernel_markov (k : ℕ) (b : Bool) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) :
    IsMarkovKernel (bodyKernel k b noise epsilon he) :=by unfold bodyKernel;infer_instance

/-- It is exactly the actual allowed-compiler physical transition from THIS
initial parent; the constant row is a conclusion of literal round execution. -/
theorem kernel_actual_round {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism k) :
    bodyKernel k b noise epsilon he o.physical=
      (roundLaw k noise epsilon he).map (fun z=>(roundParent b fee z o).physical) :=by
  change (roundLaw k noise epsilon he).map (bodyState b)=_
  congr 1
  funext z
  ext j
  exact (round_physical b fee z o j).symm

/-- Actual physical marginal of the retained parent at every real macro step. -/
def physicalPath {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (w : RoundStream k) : ℕ→State k:=
  fun r=>(RegisterRotatingBodyReturns.parentAt b fee o w r).physical

/-- The physical source reads only already completed real rounds. -/
theorem physical_adapted {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) :
    Adapted (RegisterRotatingBodyP10.fullPast k) (fun r w=>physicalPath b fee o w r) :=by
  intro r
  cases r with
  | zero=>simpa only [physicalPath,RegisterRotatingBodyReturns.parentAt] using
      (measurable_const : Measurable[RegisterRotatingBodyP10.fullPast k 0] (fun _ : RoundStream k=>o.physical))
  | succ r=>
    change Measurable[RegisterRotatingBodyP10.fullPast k (r+1)]
      (fun w=>(RegisterRotatingBodyReturns.parentAt b fee o w (r+1)).physical)
    simp only [RegisterRotatingBodyReturns.actual_parent_closed,RegisterRotatingBodyReturns.closedParent]
    exact (measurable_of_finite (bodyState b)).comp (RegisterRotatingBodyP10.previous_raw_measurable (Nat.lt_succ_self r))

@[fun_prop] theorem measurable_physicalPath {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) : Measurable (physicalPath b fee o) :=by
  apply measurable_pi_lambda
  intro r
  cases r with
  | zero=>simpa only [physicalPath,RegisterRotatingBodyReturns.parentAt] using
      (measurable_const : Measurable (fun _ : RoundStream k=>o.physical))
  | succ r=>
    change Measurable (fun w=>(RegisterRotatingBodyReturns.parentAt b fee o w (r+1)).physical)
    simp only [RegisterRotatingBodyReturns.actual_parent_closed,RegisterRotatingBodyReturns.closedParent]
    exact (measurable_of_finite (bodyState b)).comp (measurable_pi_apply r)

private theorem prefix_past {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (r : ℕ) :
    Measurable[RegisterRotatingBodyP10.fullPast k r] (fun w=>Preorder.frestrictLe r (physicalPath b fee o w)) :=by
  let : MeasurableSpace (RoundStream k):=RegisterRotatingBodyP10.fullPast k r
  apply measurable_pi_lambda
  intro j
  have hj : j.val ≤ r:=Finset.mem_Iic.mp j.property
  cases hval : j.val with
  | zero=>simpa only [Preorder.frestrictLe_apply,hval,physicalPath,RegisterRotatingBodyReturns.parentAt] using
      (measurable_const : Measurable[RegisterRotatingBodyP10.fullPast k r] (fun _ : RoundStream k=>o.physical))
  | succ s=>
    have hs : s<r:=by omega
    change Measurable[RegisterRotatingBodyP10.fullPast k r] (fun w=>physicalPath b fee o w j.val)
    simp only [hval,physicalPath,RegisterRotatingBodyReturns.actual_parent_closed,RegisterRotatingBodyReturns.closedParent]
    exact (measurable_of_finite (bodyState b)).comp (RegisterRotatingBodyP10.previous_raw_measurable hs)

private theorem prefix_append {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (w : RoundStream k) (r : ℕ) :
    Preorder.frestrictLe (r+1) (physicalPath b fee o w)=
      appendHistory r (Preorder.frestrictLe r (physicalPath b fee o w),bodyState b (w r)) :=by
  ext j
  by_cases hj : j.val ≤ r
  · simp [appendHistory,IicProdIoc_def,Preorder.frestrictLe_apply,hj]
  · have hje : j.val=r+1:=by have hh:=Finset.mem_Iic.mp j.property;omega
    have hi : j=⟨r+1,Finset.mem_Iic.mpr le_rfl⟩:=Subtype.ext hje
    subst j
    simp [appendHistory,IicProdIoc_def,Preorder.frestrictLe_apply,MeasurableEquiv.piSingleton,
      physicalPath,RegisterRotatingBodyReturns.actual_parent_closed,RegisterRotatingBodyReturns.closedParent]

private theorem prefix_law {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1)
    (o : Organism k) : ∀ r,
    (infiniteLaw k noise epsilon he).map (fun w=>Preorder.frestrictLe r (physicalPath b fee o w))=
      (homTrajMeasure (Measure.dirac o.physical) (bodyKernel k b noise epsilon he)).map (Preorder.frestrictLe r) :=by
  intro r
  induction r with
  | zero=>
    rw [homTrajMeasure_prefix_zero,Measure.map_dirac' (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0=>State k)).symm.measurable]
    have hf : (fun w=>Preorder.frestrictLe 0 (physicalPath b fee o w))=
        fun _ : RoundStream k=>(MeasurableEquiv.piUnique (fun _ : Finset.Iic 0=>State k)).symm o.physical :=by
      funext w j
      have hj : j.val=0:=by have h:=Finset.mem_Iic.mp j.property;omega
      simp [Preorder.frestrictLe_apply,hj,physicalPath,MeasurableEquiv.piUnique,RegisterRotatingBodyReturns.parentAt]
    rw [hf,Measure.map_const]
    simp
  | succ r ih=>
    let mu:=infiniteLaw k noise epsilon he
    let H:=fun w : RoundStream k=>Preorder.frestrictLe r (physicalPath b fee o w)
    let Y:=fun w : RoundStream k=>bodyState b (w r)
    have hH : Measurable H :=(Preorder.measurable_frestrictLe r).comp (measurable_physicalPath b fee o)
    have hY : Measurable Y :=(measurable_of_finite (bodyState b)).comp (measurable_pi_apply r)
    have hpair : IndepFun H Y mu :=by
      change Indep (MeasurableSpace.comap H inferInstance) (MeasurableSpace.comap Y inferInstance) mu
      have hy : Measurable[MeasurableSpace.comap (fun w : RoundStream k=>w r) inferInstance] Y :=
        (measurable_of_finite (bodyState b)).comp (Measurable.of_comap_le le_rfl)
      exact indep_of_indep_of_le (RegisterRotatingBodyP10.current_indep_fullPast k noise epsilon he r).symm
        (prefix_past b fee o r).comap_le hy.comap_le
    have hYL : mu.map Y=bodyLaw k b noise epsilon he :=by
      change (infiniteLaw k noise epsilon he).map ((bodyState b)∘(fun w=>w r))=_
      rw [←Measure.map_map (measurable_of_finite (bodyState (n:=k) b))
        (measurable_pi_apply r : Measurable (fun w : RoundStream k=>w r)),actual_round_law]
      rfl
    have hjoint:=hpair.map_prod_eq_prod_map_map hH.aemeasurable hY.aemeasurable
    rw [hYL] at hjoint
    have hk : homHistoryKernel (bodyKernel k b noise epsilon he) r=
        Kernel.const ((j : Finset.Iic r)→State k) (bodyLaw k b noise epsilon he) :=by
      ext h s hs
      rfl
    rw [←homTrajMeasure_prefix_succ,←ih,hk,Measure.compProd_const]
    rw [←hjoint,Measure.map_map (measurable_appendHistory r) (hH.prodMk hY)]
    congr 1
    funext w
    exact prefix_append b fee o w r

/-- Actual whole physical path equals the ORIGINAL canonical kernel path.
All prefix/source independence obligations are proved above, not input fields. -/
theorem actual_canonical_path_law {k : ℕ} (b : Bool) (fee : NNReal) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism k) :
    (infiniteLaw k noise epsilon he).map (physicalPath b fee o)=
      homTrajMeasure (Measure.dirac o.physical) (bodyKernel k b noise epsilon he) :=by
  let : IsProbabilityMeasure ((infiniteLaw k noise epsilon he).map (physicalPath b fee o)):=
    Measure.isProbabilityMeasure_map (measurable_physicalPath b fee o).aemeasurable
  apply pathMeasure_eq_of_prefix_eq
  intro r
  rw [Measure.map_map (Preorder.measurable_frestrictLe r) (measurable_physicalPath b fee o)]
  exact prefix_law b fee noise epsilon he o r

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBodyCanonicalPath
