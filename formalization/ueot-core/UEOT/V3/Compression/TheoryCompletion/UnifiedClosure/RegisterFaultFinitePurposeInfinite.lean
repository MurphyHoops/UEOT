import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeProbe
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultInfiniteRecord

/-!
Original commitment: finite purpose evidence controls the SAME actual infinite complete-record experiment.
Existing result: executable finite probe selector, its literal controller optimum, and genuine infinite record-path laws.
Premise reduced: replace a finite-integral-limit-only consumer by the actual infinite payoff integral equality.
Model: SAME source, complete registered probes, actual retained parent, allowed-action controller; no reset or installation.
Consumer: common finite-prefix, integrability, SAME-policy value and original optimum on one actual infinite record law.

Deployment is evaluated from its registered origin after all probes. The
physical parent is retained, and past probe transactions/fees stay in probeTrace.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeInfinite
open MeasureTheory
open UEOT.V3.FiniteDiscountedControl
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultControlModel RegisterFaultJointRecord RegisterFaultInfiniteRecord RegisterFaultFinitePurposeProbe
noncomputable section

/-- Actual retained parent after every registered probe transaction, in the
same fixed order as probeTrace. No fresh parent or physical reset is inserted. -/
def postProbeParent {n N : ℕ} (i : Fin n) (m : Mechanism)
    (ω : Coordinate N → Bool × Bool) (o : Organism n) : Organism n :=
  (registration N).foldl (fun parent j =>
    (modeRecordStep i m parent (some j.1) (ω j).1 (ω j).2).transaction.parentAfter) o

/-- The deployment seed is exactly the terminal parent of the existing actual
complete probe trace, including every failed transaction. -/
theorem postProbeParent_trace {n N : ℕ} (i : Fin n) (m : Mechanism)
    (ω : Coordinate N → Bool × Bool) (o : Organism n) :
    postProbeParent i m ω o = (probeTrace i m ω o (registration N)).foldl
      (fun _ r => r.transaction.parentAfter) o := by
  have h (js : List (Coordinate N)) (parent : Organism n) :
      (probeTrace i m ω parent js).foldl (fun _ r => r.transaction.parentAfter) parent =
        js.foldl (fun p j => (modeRecordStep i m p (some j.1) (ω j).1 (ω j).2).transaction.parentAfter) parent := by
    induction js generalizing parent with
    | nil => rfl
    | cons j js ih => exact ih _
  exact (h _ _).symm

@[simp] theorem postProbeParent_program {n N : ℕ} (i : Fin n) (m : Mechanism)
    (ω : Coordinate N → Bool × Bool) (o : Organism n) :
    (postProbeParent i m ω o).program = o.program := by
  have h (js : List (Coordinate N)) (parent : Organism n) :
      (js.foldl (fun p j =>
        (modeRecordStep i m p (some j.1) (ω j).1 (ω j).2).transaction.parentAfter) parent).program = parent.program := by
    induction js generalizing parent with
    | nil => rfl
    | cons j js ih => exact (ih _).trans (step_program i m parent _ _ _)
  exact h _ _

variable {n : ℕ}
local instance : MeasurableSpace (ModeRecord n) := ⊤
local instance : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (List (ModeRecord n)) := ⊤
local instance : MeasurableSingletonClass (List (ModeRecord n)) := ⟨fun _ => trivial⟩

/-- One common actual record consumer. The sourceData-selected literal policy
starts at the physical state of the SAME parent after ALL probes. Its infinite
law retains every fault/failed birth, has the existing finite recordLaw at each
prefix, and its integrable actual payoff equals both its own value and V*.
No independent desired process, integrability certificate or replacement policy
is supplied; all infinite-path facts reuse RegisterFaultInfiniteRecord. -/
theorem returned_positive_actual_infinite_record {N : ℕ}
    (i : Fin n) (noise : PMF Bool) (m : Mechanism) (epsilon : NNReal) (he : epsilon ≤ 1)
    (price width : ℚ) (hp : 0 ≤ price) (hw : 0 < width) (d : ℝ) (hd : 0 < d ∧ d < 1)
    (ω : Coordinate N → Bool × Bool) (b : Bool)
    (hs : select price width (sourceData m width ω) = .repair b)
    (o : Organism n) (ho : o.program = m.goal) :
    let parent := postProbeParent i m ω o
    let sigma := returnedPolicy i (select price width (sourceData m width ω))
    let c : Config sigma := ⟨0,parent.physical,parent⟩
    let μ := recordPathLaw i noise m epsilon he sigma c
    let p := priceValue price hp
    let M := RegisterFaultControlModel.model i noise m p epsilon he d hd
    (∀ k : ℕ, μ.map (fun (rs : ℕ → ModeRecord n) (j : Fin k) => rs j) =
      ((RegisterFaultJointRecord.recordLaw i noise m epsilon he sigma k (t:=0) parent.physical parent).map
        (listPrefix i m sigma c k)).toMeasure) ∧
    Integrable (streamPayoff p d) μ ∧
    (∫ rs, streamPayoff p d rs ∂μ) = sigma.infiniteValue M (t:=0) parent.physical ∧
    (∫ rs, streamPayoff p d rs ∂μ) = M.optimalValue parent.physical := by
  let parent := postProbeParent i m ω o
  let sigma := returnedPolicy i (select price width (sourceData m width ω))
  have hparent : parent.program = m.goal := (postProbeParent_program i m ω o).trans ho
  refine ⟨fun k => actual_recordPath_prefix_law i noise m epsilon he sigma parent.physical parent k,
    actual_recordPath_payoff_integrable i noise m epsilon he sigma (priceValue price hp) d hd ⟨0,parent.physical,parent⟩,
    actual_recordPath_integral_eq_policy_value i noise m epsilon he sigma parent.physical parent
      (priceValue price hp) d hd rfl hparent,?_⟩
  have hc := select_repair_sound m price width hp hw ω b hs
  rw [hs]
  simp only [returnedPolicy,returnedSelector]
  rw [hc.1]
  rw [recordPathLaw,integral_map (measurable_recordStream i m
    (selectorPolicy ((substrate i).execute m.goal)) ⟨0,parent.physical,parent⟩).aemeasurable
      (measurable_streamPayoff (priceValue price hp) d).aestronglyMeasurable]
  exact compiled_actual_infinite_integral_optimal i noise m epsilon he
    (priceValue price hp) d hd hc.2.le parent hparent

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeInfinite
