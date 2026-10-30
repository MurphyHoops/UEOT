import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionRecoveryScale
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFinitePurposeProbe
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
Original promise: the SAME actual restoring program must have a source-derived long-run maintenance law under recurring faults.
Existing result: actual next legitimacy iff the real mode is repair, full countable records and source-derived P9 repairability for the SAME synthesized q.
Reduced premise: derive exact maintained marginals and almost-sure empirical rate from the original fresh IID mode/label product, not an external homeostasis certificate.
Model/boundary: epsilon is the original fault probability; protected target/program, original initial parent/actions/observations and fees are unchanged, no resource supply added.
Consumer: actual quantitative PreservesHomeostasis/P9 for returned q; positive faults refute original eventual-permanent legitimacy, with frequency maintenance explicitly a different conclusion.

Fresh IID draws are the declared source condition used here, exactly the old
primitiveLaw of modeLaw and label noise; arbitrary correlated stream results
remain as previously proved and are not promoted to IID. Failed births, faults
and paid actions remain in the full process. This is retained-parent frequency
maintenance, not finite-resource viability, population growth or an optimizer.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionHomeostasis
open MeasureTheory ProbabilityTheory Filter Set
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord RegisterFaultControlModel
open RegisterFaultFinitePurposeProbe (primitiveLaw)
open RegisterActuatorScaleSource RegisterInstructionScaleSource RegisterSemanticInstructionScale
open RegisterSemanticInstructionInfinite RegisterInstructionRecoveryScale
open UEOT.V3.Compression.TheoryCompletion
open scoped ENNReal NNReal Topology ProbabilityTheory MeasureTheory
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n) := ⊤
local instance {n : ℕ} (i : Fin n) (o : Organism n) : Decidable (Legitimate i o) :=
  inferInstanceAs (Decidable (o.physical i=o.program))
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n) := ⟨fun _ => trivial⟩

/-- ONE complete infinite source of the existing mode/label draws. Epsilon
is fault rate, so true repair modes have probability 1-epsilon. -/
def iidSource (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) : Measure Stream :=
  Measure.infinitePi (fun _ : ℕ => (primitiveLaw noise epsilon he).toMeasure)
instance iidSource_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    IsProbabilityMeasure (iidSource noise epsilon he) := by unfold iidSource; infer_instance

/-- The old actual primitive source has exactly its declared mode marginal. -/
theorem primitive_mode (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    (primitiveLaw noise epsilon he).map Prod.fst=modeLaw epsilon he := by
  unfold primitiveLaw
  rw [PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (modeLaw epsilon he)]
  congr 1
  funext mode
  rw [PMF.map_comp]
  exact PMF.map_const noise mode

def repairScore (z : Bool×Bool) : ℝ := if z.1 then 1 else 0
def score (t : ℕ) (w : Stream) : ℝ := repairScore (w t)

@[fun_prop] theorem measurable_score (t : ℕ) : Measurable (score t) :=
  (measurable_of_finite repairScore).comp (measurable_pi_apply t)
theorem score_bound (t : ℕ) (w : Stream) : ‖score t w‖≤(1 : ℝ) := by
  unfold score repairScore
  split_ifs <;> norm_num

theorem score_law (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (t : ℕ) :
    (iidSource noise epsilon he).map (score t)=
      (primitiveLaw noise epsilon he).toMeasure.map repairScore := by
  change (Measure.infinitePi (fun _ : ℕ => (primitiveLaw noise epsilon he).toMeasure)).map
    (repairScore ∘ (fun w : Stream => w t))=_
  rw [← Measure.map_map (measurable_of_finite repairScore) (measurable_pi_apply t),Measure.infinitePi_map_eval]

theorem score_identDistrib (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (t : ℕ) :
    IdentDistrib (score t) (score 0) (iidSource noise epsilon he) (iidSource noise epsilon he) :=
  ⟨(measurable_score t).aemeasurable,(measurable_score 0).aemeasurable,
    (score_law noise epsilon he t).trans (score_law noise epsilon he 0).symm⟩

theorem score_independent (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    iIndepFun score (iidSource noise epsilon he) :=
  iIndepFun_infinitePi (fun _ => measurable_of_finite repairScore)

theorem score_mean (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    (∫ w, score 0 w ∂iidSource noise epsilon he)=1-(epsilon : ℝ) := by
  have hp : (∫ z, repairScore z ∂(primitiveLaw noise epsilon he).toMeasure)=1-(epsilon : ℝ) := by
    change (∫ z, (fun mode : Bool => if mode then (1 : ℝ) else 0) (Prod.fst z)
      ∂(primitiveLaw noise epsilon he).toMeasure)=_
    rw [← integral_map measurable_fst.aemeasurable (measurable_of_finite (fun mode : Bool => if mode then (1 : ℝ) else 0)).aestronglyMeasurable,
      PMF.toMeasure_map Prod.fst (primitiveLaw noise epsilon he) measurable_fst,primitive_mode,PMF.integral_eq_sum]
    simp [modeLaw,modeProbability,repairChance,UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow_apply_toReal]
  calc
    (∫ w,score 0 w ∂iidSource noise epsilon he)=
        ∫ x : ℝ,x ∂(iidSource noise epsilon he).map (score 0) :=
      (integral_map (measurable_score 0).aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ x : ℝ,x ∂(primitiveLaw noise epsilon he).toMeasure.map repairScore := by rw [score_law]
    _ = ∫ z,repairScore z ∂(primitiveLaw noise epsilon he).toMeasure :=
      integral_map (measurable_of_finite repairScore).aemeasurable measurable_id.aestronglyMeasurable
    _ = _ := hp

/-- Native strong law of the actual fresh source, including epsilon0/1. -/
theorem actual_mode_frequency (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    ∀ᵐ w ∂iidSource noise epsilon he, Tendsto
      (fun N : ℕ => (∑ t∈Finset.range N,score t w)/(N : ℝ)) atTop (𝓝 (1-(epsilon : ℝ))) := by
  have hi : Integrable (score 0) (iidSource noise epsilon he) :=
    Integrable.of_bound (measurable_score 0).aestronglyMeasurable 1 (ae_of_all _ (score_bound 0))
  have h:=strong_law_ae_real score hi (fun i j hij => (score_independent noise epsilon he).indepFun hij)
    (score_identDistrib noise epsilon he)
  rwa [score_mean] at h

/-- Actual post-transaction legitimacy in the complete ongoing execution.
The initial parent is kept; every transaction, including faults, is counted. -/
def postLegitimate {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (o : Organism n) (t : ℕ) (w : Stream) : ℝ :=
  if Legitimate i (recordAt i ⟨b,cost⟩ p o w t).transaction.parentAfter then 1 else 0

@[fun_prop] theorem measurable_postLegitimate {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (p : Instruction n) (o : Organism n) (t : ℕ) : Measurable (postLegitimate i b cost p o t) := by
  let F : ModeRecord n → ℝ := fun r => if Legitimate i r.transaction.parentAfter then 1 else 0
  exact (show Measurable F by intro S hS; trivial).comp (measurable_recordAt i ⟨b,cost⟩ p o t)

/-- Source-derived equality, not an observation/independence certificate. -/
theorem actual_post_eq_score {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (hp : o.program=b) (t : ℕ) (w : Stream) :
    postLegitimate i b cost p o t w=score t w := by
  change (if Legitimate i (parentAt i ⟨b,cost⟩ p o w (t+1)) then (1 : ℝ) else 0)=_
  simp only [actual_stream_legitimacy i b cost p hc o hp w t]
  cases h:(w t).1 <;> simp [score,repairScore,h]

theorem source_mode_law (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (t : ℕ) :
    (iidSource noise epsilon he).map (fun w => (w t).1)=(modeLaw epsilon he).toMeasure := by
  change (iidSource noise epsilon he).map (Prod.fst ∘ (fun w : Stream => w t))=_
  rw [← Measure.map_map measurable_fst (measurable_pi_apply t),iidSource,
    Measure.infinitePi_map_eval,PMF.toMeasure_map Prod.fst (primitiveLaw noise epsilon he) measurable_fst,primitive_mode]

theorem source_repair_probability (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (t : ℕ) :
    iidSource noise epsilon he {w | (w t).1=true}=ENNReal.ofReal (1-(epsilon : ℝ)) := by
  change iidSource noise epsilon he ((fun w : Stream => (w t).1) ⁻¹' ({true} : Set Bool))=_
  rw [← Measure.map_apply (by fun_prop : Measurable (fun w : Stream => (w t).1)) (measurableSet_singleton true),
    source_mode_law,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true)]
  simp [modeLaw,modeProbability,repairChance,UEOT.V3.FiniteDiscountedControl.FiniteProbabilityRow.ofRealRow]

/-- Exact stationary LEGITIMACY marginal after each transaction; no claim
that growing offspring/journals or whole populations have stationary laws. -/
theorem actual_maintained_probability {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (hp : o.program=b)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (t : ℕ) :
    iidSource noise epsilon he {w | Legitimate i (parentAt i ⟨b,cost⟩ p o w (t+1))}=
      ENNReal.ofReal (1-(epsilon : ℝ)) := by
  have hs : {w | Legitimate i (parentAt i ⟨b,cost⟩ p o w (t+1))}={w | (w t).1=true} := by
    ext w
    exact actual_stream_legitimacy i b cost p hc o hp w t
  rw [hs]
  exact source_repair_probability noise epsilon he t

/-- Actual full-source empirical maintenance rate. This derives a new
frequency conclusion; it does not rename eventual-permanent safety. -/
theorem actual_maintenance_frequency {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (hp : o.program=b)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    ∀ᵐ w ∂iidSource noise epsilon he, Tendsto
      (fun N : ℕ => (∑ t∈Finset.range N,postLegitimate i b cost p o t w)/(N : ℝ)) atTop (𝓝 (1-(epsilon : ℝ))) := by
  simpa only [actual_post_eq_score i b cost p hc o hp] using actual_mode_frequency noise epsilon he

private theorem average_of_eventually_constant (f : ℕ → ℝ) (a : ℝ)
    (h : ∀ᶠ t in atTop,f t=a) :
    Tendsto (fun N : ℕ => (∑ t∈Finset.range N,f t)/(N : ℝ)) atTop (𝓝 a) := by
  have hf : Tendsto f atTop (𝓝 a) := (tendsto_congr' h).mpr tendsto_const_nhds
  simpa only [div_eq_mul_inv,mul_comm] using hf.cesaro

/-- Strict boundary for the ORIGINAL permanence event: any positive IID
fault rate makes eventual permanent legitimacy false almost surely. -/
theorem actual_no_eventual_permanence {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (hp : o.program=b)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (hepos : 0<epsilon) :
    ∀ᵐ w ∂iidSource noise epsilon he,
      ¬ ∃ N : ℕ, ∀ t≥N, Legitimate i (parentAt i ⟨b,cost⟩ p o w t) := by
  filter_upwards [actual_maintenance_frequency i b cost p hc o hp noise epsilon he] with w hrate
  rintro ⟨N,hN⟩
  have hone : ∀ᶠ t in atTop,postLegitimate i b cost p o t w=1 := by
    filter_upwards [Ici_mem_atTop N] with t ht
    change N≤t at ht
    change (if Legitimate i (parentAt i ⟨b,cost⟩ p o w (t+1)) then (1 : ℝ) else 0)=1
    exact if_pos (hN (t+1) (by omega))
  have h:=tendsto_nhds_unique hrate (average_of_eventually_constant _ 1 hone)
  have heR : 0<(epsilon : ℝ) := by exact_mod_cast hepos
  linarith

/-- With a genuine chance of repair, the actual SAME retained parent
returns infinitely often, even though positive faults prevent permanence. -/
theorem actual_returns_forever {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (hp : o.program=b)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon<1) :
    ∀ᵐ w ∂iidSource noise epsilon he.le,
      ∀ N : ℕ, ∃ t≥N, Legitimate i (parentAt i ⟨b,cost⟩ p o w t) := by
  filter_upwards [actual_maintenance_frequency i b cost p hc o hp noise epsilon he.le] with w hrate
  intro N
  by_contra hn
  have hz : ∀ᶠ t in atTop,postLegitimate i b cost p o t w=0 := by
    filter_upwards [Ici_mem_atTop N] with t ht
    change N≤t at ht
    change (if Legitimate i (parentAt i ⟨b,cost⟩ p o w (t+1)) then (1 : ℝ) else 0)=0
    exact if_neg (fun h => hn ⟨t+1,by omega,h⟩)
  have h:=tendsto_nhds_unique hrate (average_of_eventually_constant _ 0 hz)
  have heR : (epsilon : ℝ)<1 := by exact_mod_cast he
  linarith

/-- Named new quantitative homeostasis problem, explicitly combining actual
marginals and empirical frequency; not the old permanent-safety event. -/
def QuantitativeHomeostasis {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (o : Organism n) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) (p : Instruction n) : Prop :=
  (∀ t, iidSource noise epsilon he {w | Legitimate i (parentAt i ⟨b,cost⟩ p o w (t+1))}=
    ENNReal.ofReal (1-(epsilon : ℝ))) ∧
  ∀ᵐ w ∂iidSource noise epsilon he, Tendsto
    (fun N : ℕ => (∑ t∈Finset.range N,postLegitimate i b cost p o t w)/(N : ℝ)) atTop (𝓝 (1-(epsilon : ℝ)))

theorem actual_quantitative_homeostasis {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal) (p : Instruction n)
    (hc : restorationCheck i b p=true) (o : Organism n) (hp : o.program=b)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    QuantitativeHomeostasis i b cost o noise epsilon he p :=
  ⟨actual_maintained_probability i b cost p hc o hp noise epsilon he,
    actual_maintenance_frequency i b cost p hc o hp noise epsilon he⟩

/-- Original P9 Homeostasis preservation, now produced by the actual source
and native strong law for the computed returning program, with no hpres input. -/
theorem actual_preserves_homeostasis {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (o : Organism n) (hp : o.program=b) (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    PreservesHomeostasis (recoveryScale i b)
      (fun pq => QuantitativeHomeostasis i b cost o noise epsilon he pq.val.val.1)
      (QuantitativeHomeostasis (0 : Fin 1) b cost (projectOrganism i o) noise epsilon he) := by
  intro pq _
  exact actual_quantitative_homeostasis 0 b cost _
    ((returned_restoration_iff i b _ _ pq.val.property).mp pq.property) (projectOrganism i o) hp noise epsilon he

/-- The SAME actual synthesized q consumes original P9 together with its
source-derived quantitative homeostasis. No alternate controller is chosen. -/
theorem p9_actual_returned_homeostasis {n : ℕ} (i : Fin n) (b : Bool) (cost : NNReal)
    (pq : RecoveringPair i b) (o : Organism n) (hp : o.program=b)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1) :
    QuantitativeHomeostasis (0 : Fin 1) b cost (projectOrganism i o) noise epsilon he pq.val.val.2 :=
  transport_object_property (recoveryScale i b)
    (fun r => QuantitativeHomeostasis i b cost o noise epsilon he r.val.val.1)
    (QuantitativeHomeostasis (0 : Fin 1) b cost (projectOrganism i o) noise epsilon he)
    rfl (actual_preserves_homeostasis i b cost o hp noise epsilon he)
    (actual_quantitative_homeostasis i b cost _ pq.property o hp noise epsilon he)

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionHomeostasis
