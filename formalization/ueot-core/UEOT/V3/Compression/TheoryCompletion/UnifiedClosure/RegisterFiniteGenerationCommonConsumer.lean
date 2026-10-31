import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationFiniteEpisodeResource
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeParentDiscovery
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultNativeOrganization
import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicProbeP9Terminal

/-!
Original promise: finite-generation P12 roles share THIS returned program, actual parent and source.
Existing results: literal owner/phase execution, original P8, actual Price, original P9, maintained-parent and marked discovery.
Reduced premise: derive owner matching and ONE prepaid wallet from the same full Batch/future/read input; neither parent truth nor fee viability is an input certificate.
Family: single registered founder, actual plan [0,0,h], all training/fault/None outcomes, additional marked-owner sensor with B paid reads.
Consumers: original P12 discovery/maintained-parent, P8 and P9 roles; finite accounting does not fund infinite maintenance or assert global population GOD.

Read accounting proofs below reuse the independently checked preparatory
CommonWalletAcceptance caller by the marked-discovery author. Lookup is WORLD
semantics of an already executed birth, never an estimator input or a new
post-read action. Retained-parent evaluation, finite population phase and
finite observation accounting are distinct registered protocols. Positive
birth is a realized output condition, not a removed event or zero-risk claim.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFiniteGenerationCommonConsumer
open Set MeasureTheory ProbabilityTheory Filter Topology
open UEOT.V3.Compression.Objecthood.ResourceClosure
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose
open RegisterFaultFinitePurposeProbe RegisterFaultFinitePurposeInfinite RegisterFaultDynamicProbe
open RegisterPopulationFiniteEpisodeResource
open RegisterPopulationHistorySource (Store Request)
open RegisterTimestampedBirthSource (ClockedOrganism ClockedRecord)
open scoped BigOperators
noncomputable section

/-- Read schedule AFTER the original finite write trace, not an extra wallet. -/
def readCost (L B : ℕ) (r : NNReal) (k : ℕ) : ℝ := if L≤k ∧ k<L+B then r else 0

theorem read_prefix_le (L B : ℕ) (r : NNReal) (K : ℕ) :
    (∑k∈Finset.range K,readCost L B r k)≤(B : ℝ)*r :=by
  let s:=(Finset.range K).filter (fun k=>L≤k ∧ k<L+B)
  have hs : s⊆Finset.Ico L (L+B) :=by
    intro k hk
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hk).2
  have hc : s.card≤B :=by
    have hh:=Finset.card_le_card hs
    simpa using hh
  have he : (∑k∈Finset.range K,readCost L B r k)=(s.card : ℝ)*r :=by
    simp only [readCost,←Finset.sum_filter]
    simp [s]
  rw [he]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) r.coe_nonneg

theorem read_total_exact (L B : ℕ) (r : NNReal) :
    (∑k∈Finset.range (L+B),readCost L B r k)=(B : ℝ)*r :=by
  have hs : (Finset.range (L+B)).filter (fun k=>L≤k ∧ k<L+B)=Finset.Ico L (L+B) :=by
    ext k
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    tauto
  simp only [readCost,←Finset.sum_filter]
  rw [hs]
  simp

def fullCost {n : ℕ} (rs : List (Option (ClockedRecord n))) (B : ℕ) (r : NNReal) (k : ℕ) : ℝ :=
  costStream rs k+readCost rs.length B r k

/-- P6 for the SAME initial wallet, no read-credit or additional reserve. -/
theorem one_initial_wallet {n : ℕ} (rs : List (Option (ClockedRecord n))) (B : ℕ) (r : NNReal)
    (writeReserve reserve : ℝ) (hw : ResourceViable writeReserve (fun _=>0) (costStream rs))
    (hb : writeReserve+(B : ℝ)*r≤reserve) :
    ResourceViable reserve (fun _=>0) (fullCost rs B r) :=by
  rw [resourceViable_iff_cumulative_cost_le]
  intro K
  have hp:=(resourceViable_iff_cumulative_cost_le _ _ _).mp hw K
  simp only [Finset.sum_const_zero,add_zero] at hp
  simp only [Finset.sum_const_zero,add_zero,fullCost,Finset.sum_add_distrib]
  exact (add_le_add hp (read_prefix_le rs.length B r K)).trans hb

/-- Affordability is before each write/read, including erroneous/None reads. -/
theorem one_wallet_prepay {n : ℕ} (rs : List (Option (ClockedRecord n))) (B : ℕ) (r : NNReal)
    (reserve : ℝ) (hv : ResourceViable reserve (fun _=>0) (fullCost rs B r)) (k : ℕ) :
    fullCost rs B r k≤cumulativeResourceBalance reserve (fun _=>0) (fullCost rs B r) k :=by
  have hp:=(resourceViable_iff_cumulative_cost_le _ _ _).mp hv (k+1)
  simp only [Finset.sum_range_succ,Finset.sum_const_zero,add_zero] at hp
  simp only [cumulativeResourceBalance,Finset.sum_const_zero,add_zero]
  linarith


variable {n N : ℕ} (i : Fin n) (m : Mechanism) (price width d u : ℚ)
  (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) (h : Bool) (w : Fin 3→Bool×Bool) (e : Fin 3)

/-- Starts at the real clocked post-probe organism, not an unrelated founder. -/
theorem actual_owner_initial :
    RegisterPopulationOwnerClockTransport.storeView o.identity (o.clock+2*N)
      (RegisterFaultDynamicProbePopulation.registeredParent i m omega o.organism)=
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)] :=
  RegisterPopulationOwnerClockTransport.actual_registered_postClocked i m omega o

/-- THIS literal plan and AST execute the same requests at the true owner. -/
theorem actual_owner_requests :
    RegisterPopulationOwnerClockTransport.astEpisode
      (returnedAST i (classify price width d u (sourceData m width omega))) i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.plan h w)=
      RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w := by
  rw [←actual_owner_initial i m omega o,RegisterPopulationOwnerClockTransport.ast_episode_view]
  rfl

/-- Same actual clocked source gives EXACTLY the learned serial owner mark. -/
theorem actual_clocked_parent_mark :
    RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w e)=
      RegisterFaultDynamicProbeParentDiscovery.targetParent i m price width d u omega o.organism h w e := by
  rw [←actual_owner_initial i m omega o]
  exact (RegisterPopulationOwnerClockTransport.actual_ID_parent_view i m.writeCost o.identity (o.clock+2*N)
    (RegisterFaultDynamicProbePopulation.registeredParent i m omega o.organism) _ _).2

/-- The original complete joint risk is transported to the true clocked
source parent mark, without adding a truth/observed-law assumption. -/
theorem actual_clocked_joint_bound (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ) :
    (RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B).real {z |
      RegisterFaultDynamicProbeParentDiscovery.estimate
        (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u z.1.1 o.organism h z.1.2 e z.2)≠
      RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N)
        [some (RegisterFaultDynamicProbeClocked.postClocked i m z.1.1 o)]
        (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u z.1.1 o.organism h z.1.2)
        (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u z.1.1 o.organism h z.1.2 e)}≤
      Real.exp (-(B : ℝ)/8) := by
  have hsame (z : RegisterFaultDynamicProbeParentDiscovery.Sample N B):=
    actual_clocked_parent_mark i m price width d u z.1.1 o h z.1.2 e
  simp_rw [hsame]
  exact RegisterFaultDynamicProbeParentDiscovery.target_joint_parent_risk_le i noise m epsilon he price width d u o.organism h e confuser B

/-- The actual operational output is a mark, including None. No lookup or
actualParent is inserted inside the majority selector. -/
theorem good_mark_is_actual_clocked_parent {B : ℕ}
    (reads : RegisterPopulationJournalLearning.Raw RegisterFaultDynamicProbeParentDiscovery.Class B)
    (hg : reads∈RegisterPopulationJournalLearning.Good B) :
    RegisterFaultDynamicProbeParentDiscovery.estimate
      (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u omega o.organism h w e reads)=
    RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w e) :=
  (RegisterFaultDynamicProbeParentDiscovery.good_target_estimate_actual i m price width d u omega o.organism h w e reads hg).trans
    (actual_clocked_parent_mark i m price width d u omega o h w e).symm

/-- WORLD-side execution meaning of the returned mark at this actual event.
A real chosen birth yields its real clocked parent and original P8 OffspringOf
relation. The estimator never reads this lookup; it has already returned its
mark. No extra resolver or post-read physical action is executed here. -/
theorem selected_mark_dispatch_real_parent {B : ℕ}
    (reads : RegisterPopulationJournalLearning.Raw RegisterFaultDynamicProbeParentDiscovery.Class B)
    (hg : reads∈RegisterPopulationJournalLearning.Good B)
    (child : ClockedOrganism n)
    (hc : RegisterPopulationOwnerClockTransport.childAt i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w e)=some child) :
    let es:=RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w
    let k:=RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w e
    let s:=RegisterPopulationOwnerClockTransport.run i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)] (es.take k)
    let q:=RegisterPopulationHistorySource.requestAt es k
    ∃parent,
      (RegisterFaultDynamicProbeParentDiscovery.estimate
        (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u omega o.organism h w e reads)).bind
          (RegisterPopulationHistorySource.lookup s)=some parent ∧
      (RegisterTimestampedBirthSource.lineage i (RegisterOwnProgramPopulation.mechanism m.writeCost s q)).OffspringOf
        {parent with clock:=o.clock+2*N+s.length} child ∧ child.clock=0 := by
  dsimp only
  obtain ⟨parent,hp,hbirth,hzero⟩:=RegisterPopulationOwnerClockTransport.actual_birth_source i m.writeCost
    (o.clock+2*N) _ _ child hc
  refine ⟨parent,?_,hbirth,hzero⟩
  have hm:=good_mark_is_actual_clocked_parent i m price width d u omega o h w e reads hg
  rw [hm]
  simp only [RegisterPopulationOwnerClockTransport.actualParent,hc,Option.map_some,Option.bind_some]
  exact hp


/-- The literal writes and ALL B observations debit one registered zero-income
wallet. This holds pointwise, including absent children and incorrect reads. -/
theorem complete_finite_wallet (B : ℕ) (r : NNReal) (cap reserve : ℝ)
    (hc : (m.writeCost : ℝ)≤cap)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) :
    ResourceViable reserve (fun _=>0)
      (fullCost (wholeTrace i m price width d u omega o
        (RegisterFaultDynamicProbeParentDiscovery.plan h w)) B r) :=by
  apply one_initial_wallet _ B r (((2*N+3 : ℕ) : ℝ)*cap) reserve
  · exact actual_whole_p6 i m price width d u omega o _ 3
      (by simp [RegisterFaultDynamicProbeParentDiscovery.plan]) cap _ hc le_rfl
  · exact hr

theorem complete_finite_prepay (B : ℕ) (r : NNReal) (cap reserve : ℝ)
    (hc : (m.writeCost : ℝ)≤cap)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) (k : ℕ) :
    fullCost (wholeTrace i m price width d u omega o
      (RegisterFaultDynamicProbeParentDiscovery.plan h w)) B r k≤
    cumulativeResourceBalance reserve (fun _=>0)
      (fullCost (wholeTrace i m price width d u omega o
        (RegisterFaultDynamicProbeParentDiscovery.plan h w)) B r) k :=
  one_wallet_prepay _ B r reserve
    (complete_finite_wallet i m price width d u omega o h w B r cap reserve hc hr) k

/-- Exactly the original registered measurement bill, with no None or wrong
answer discount. Reads follow, and do not replace, the full write trace. -/
theorem complete_read_bill (B : ℕ) (r : NNReal) :
    (∑k∈Finset.range ((wholeTrace i m price width d u omega o
      (RegisterFaultDynamicProbeParentDiscovery.plan h w)).length+B),
      readCost (wholeTrace i m price width d u omega o
        (RegisterFaultDynamicProbeParentDiscovery.plan h w)).length B r k)=
    RegisterFaultDynamicProbeParentDiscovery.readCharge r B :=by
  rw [read_total_exact,RegisterFaultDynamicProbeParentDiscovery.readCharge_exact]

/-- Source-level P6/prepay uses the SAME complete original training, future3
and read law. No conditioning on accepted repair, birth or correct estimate. -/
theorem same_source_wallet (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class)
    (B : ℕ) (r : NNReal) (cap reserve : ℝ) (hc : (m.writeCost : ℝ)≤cap)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) :
    ∀ᵐ z ∂ RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B,
      ResourceViable reserve (fun _=>0)
        (fullCost (wholeTrace i m price width d u z.1.1 o
          (RegisterFaultDynamicProbeParentDiscovery.plan h z.1.2)) B r) ∧
      ∀ k,fullCost (wholeTrace i m price width d u z.1.1 o
          (RegisterFaultDynamicProbeParentDiscovery.plan h z.1.2)) B r k≤
        cumulativeResourceBalance reserve (fun _=>0)
          (fullCost (wholeTrace i m price width d u z.1.1 o
            (RegisterFaultDynamicProbeParentDiscovery.plan h z.1.2)) B r) k :=by
  exact ae_of_all _ (fun z=>⟨complete_finite_wallet i m price width d u z.1.1 o h z.1.2 B r cap reserve hc hr,
    complete_finite_prepay i m price width d u z.1.1 o h z.1.2 B r cap reserve hc hr⟩)

/-- Original mandatory P12 discovery is consumed on THIS episode. The limit
ranges over separately funded experiments, not infinite free reads at one R. -/
theorem same_episode_p12_discovery
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) :
    Tendsto (fun B=>(RegisterPopulationJournalLearning.rawLaw (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1) : (1/4 : NNReal)≤1) confuser B).real {reads |
        RegisterFaultDynamicProbeParentDiscovery.estimate
          (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u omega o.organism h w e reads)≠
        RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N)
          [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
          (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
          (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w e)})
      atTop (𝓝 0) :=by
  simp_rw [actual_clocked_parent_mark]
  exact RegisterFaultDynamicProbeParentDiscovery.target_episode_p12 i m price width d u omega o.organism h w e confuser

/-- First registered event: the semantic owner is the actual post-probe
founder. No second founder, ID oracle or equality-by-program is supplied. -/
theorem first_birth_same_founder
    (child : ClockedOrganism n)
    (hc : RegisterPopulationOwnerClockTransport.childAt i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w 0)=some child) :
    let q:=RegisterPopulationHistorySource.requestAt
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w 0)
    let founder:=RegisterFaultDynamicProbeClocked.postClocked i m omega o
    let actor:={founder with clock:=o.clock+2*N+1}
    (RegisterTimestampedBirthSource.lineage i
      (RegisterOwnProgramPopulation.mechanism m.writeCost [some founder] q)).OffspringOf actor child ∧
    (RegisterTimestampedBirthSource.lineage i m).SameObject actor founder ∧
    child.clock=0 :=by
  dsimp only
  have hz : ((RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w 0) : ℕ)=0:=rfl
  have hq:=RegisterFaultDynamicProbeParentDiscovery.target_dispatch i m price width d u omega o.organism h w 0
  simp only [hz,Fin.val_zero,Nat.reduceLT,ite_true] at hq
  unfold RegisterPopulationOwnerClockTransport.childAt at hc
  simp only [hz,List.take_zero,RegisterPopulationOwnerClockTransport.run] at hc
  obtain ⟨parent,hp,hbirth,hzero⟩:=RegisterPopulationOwnerClockTransport.actual_birth_source i m.writeCost
    (o.clock+2*N) _ _ child hc
  rw [hq] at hp
  have hp' : parent=RegisterFaultDynamicProbeClocked.postClocked i m omega o:=by
    simpa [RegisterPopulationHistorySource.lookup] using hp.symm
  subst parent
  exact ⟨by simpa only [hz,List.length_singleton] using hbirth,rfl,hzero⟩

/-- A born child cannot be substituted for the founder in the same-parent
roles, even though its protected program is inherited unchanged. -/
theorem first_child_not_founder (child : ClockedOrganism n)
    (hc : RegisterPopulationOwnerClockTransport.childAt i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w 0)=some child) :
    ¬(RegisterTimestampedBirthSource.lineage i m).SameObject child
      (RegisterFaultDynamicProbeClocked.postClocked i m omega o) :=by
  have hb:=first_birth_same_founder i m price width d u omega o h w child hc
  intro hbad
  exact hb.1.2 (hb.2.1.trans hbad.symm)

/-- First-birth absence is an actual None answer, including false-positive
Some0 mistakes in the original risk event. No success filtering occurs. -/
theorem first_no_birth_none
    (hc : RegisterPopulationOwnerClockTransport.childAt i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w 0)=none) :
    RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N)
      [some (RegisterFaultDynamicProbeClocked.postClocked i m omega o)]
      (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w)
      (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w 0)=none :=by
  simp only [RegisterPopulationOwnerClockTransport.actualParent,hc,Option.map_none]

/-- Exactly two original error events: source calibration and THIS chosen
parent mark. No-birth is not called a calibration error or removed. -/
theorem same_source_two_event_bound
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class)
    (hN : 0<N) (hu : 0≤(u : ℝ)) (B : ℕ) :
    (RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B).real {z |
      z.1.1∉RegisterFaultFinitePurposeProbe.Good noise m epsilon he N width (u : ℝ) ∨
      RegisterFaultDynamicProbeParentDiscovery.estimate
        (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u z.1.1 o.organism h z.1.2 e z.2)≠
      RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N)
        [some (RegisterFaultDynamicProbeClocked.postClocked i m z.1.1 o)]
        (RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u z.1.1 o.organism h z.1.2)
        (RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u z.1.1 o.organism h z.1.2 e)}≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2))+Real.exp (-(B : ℝ)/8) :=by
  have hp : (RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B).real
      {z | z.1.1∉RegisterFaultFinitePurposeProbe.Good noise m epsilon he N width (u : ℝ)}≤
      min 1 (4*Real.exp (-2*(N : ℝ)*(u : ℝ)^2)) :=by
    have hset : {z : RegisterFaultDynamicProbeParentDiscovery.Sample N B |
        z.1.1∉RegisterFaultFinitePurposeProbe.Good noise m epsilon he N width (u : ℝ)}=
      ((RegisterFaultFinitePurposeProbe.Good noise m epsilon he N width (u : ℝ))ᶜ×ˢSet.univ)×ˢSet.univ :=by
      ext z
      simp
    calc
      _=(RegisterFaultFinitePurposeProbe.rawLaw noise epsilon he N).real
          (RegisterFaultFinitePurposeProbe.Good noise m epsilon he N width (u : ℝ))ᶜ :=by
        rw [Measure.real,RegisterFaultDynamicProbeParentDiscovery.jointLaw,hset,
          RegisterFaultDynamicProbeHistoryPrice.experimentLaw,Measure.prod_prod,Measure.prod_prod,
          measure_univ,mul_one]
        simp only [measure_univ,mul_one]
        rfl
      _≤_ :=(actual_probe_calibration noise m epsilon he N hN width (u : ℝ) hu).2
  exact (measureReal_union_le _ _).trans (add_le_add hp
    (actual_clocked_joint_bound i m price width d u o h e noise epsilon he confuser B))

/-- P9 is the original retained-parent evaluation certificate on THIS actual
post-probe object and returned AST/q. It is not finite-episode global GOD. -/
theorem same_founder_retained_p9
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon<1)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1)
    (ho : o.organism.program=m.goal)
    (hgood : omega∈RegisterFaultFinitePurposeProbe.Good noise m epsilon he.le N width (u : ℝ))
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b) :
    RegisterFaultDynamicProbeP9Terminal.Six (0 : Fin 1) noise m (priceValue price hp) epsilon he.le
      (d : ℝ) (by exact_mod_cast hd) o.identity (o.clock+2*N)
      ((RegisterFaultDynamicProbeP9Terminal.clockedScale i).objectMap
        (RegisterFaultDynamicProbeP9Terminal.dataObject i m price width d u omega o)) :=
  RegisterFaultDynamicProbeP9Terminal.data_actual_p9_six i noise m epsilon he price width d u hp hw hd
    omega o ho hgood b hs

section MaintainedParent
variable [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/- The ORIGINAL maintained-parent P12 consumer is instantiated with the
actual post-training organism, including a damaged final probe state. This is
a maintenance-family certificate, not a claim that the finite wallet pays an
infinite native future. -/
open UEOT.V3.Compression.Objecthood
open UEOT.V3.Compression.Objecthood.RepairLawSelfReconstruction
open UEOT.V3.Compression.Objecthood.JointHomeostasis
open UEOT.V3.Compression.Objecthood.OntogeneticConstruction UEOT.V3.ViabilityKernel
open RegisterFaultSource
local instance : Fintype (RepairOrganizationState (State n) Action Bool) := repairOrganizationStateFintype
local instance : MeasurableSpace (RepairOrganizationState (State n) Action Bool) := ⊤
local instance : MeasurableSingletonClass (RepairOrganizationState (State n) Action Bool) := ⟨fun _=>trivial⟩

/-- Specific original P12 maintenance-family role at this source parent. -/
def MaintainedAt (i : Fin n) (m : Mechanism) (omega : Coordinate N→Bool×Bool)
    (o : ClockedOrganism n) (epsilon : NNReal) (he : epsilon≤1) : Prop :=
    let parent:=postProbeParent i m omega o.organism
    let seed : OntogeneticSeed (State n) Bool:=⟨parent.physical,m.goal⟩
    let initial:=PMF.pure (assembleRepairOrganization (substrate i) codec seed)
    let S:=finiteJointRecurrentHomeostasisSystem
      (physical i) (target i m.goal) (target_fixed i m.goal) (certificate i m.goal)
      (substrate i) codec m.goal (compiled_dynamics_implements i m.goal)
      (fault i) epsilon he (actual_fault_envelope i m.goal)
    RegisterFaultDynamicProbeLifecycle.parentView o.organism.history
      (assembleRepairOrganization (substrate i) codec seed)=parent ∧
    StaysIn initial S.carrier ∧
    ∀ k s,s∈(homeostaticMarginal S.mixedKernel initial k).support→
      (RegisterRepairHistory.lineage i).SameObject
        (RegisterFaultDynamicProbeLifecycle.parentView o.organism.history s) parent

/-- No carrier or parent-matching certificate is supplied by the caller. -/
theorem same_founder_maintained (epsilon : NNReal) (he : epsilon≤1)
    (ho : o.organism.program=m.goal) : MaintainedAt i m omega o epsilon he :=
  RegisterFaultDynamicProbeLifecycle.actual_post_parent_p12_carrier i m epsilon he omega o.organism ho

/-- Owner metadata is the actual registered founder's source identity. This
is an organizational representation, with a fixed registration timestamp;
it is NOT a clock/law for an executed native continuation. -/
def organizationOwnerView (N : ℕ) (o : ClockedOrganism n)
    (s : RepairOrganizationState (State n) Action Bool) : ClockedOrganism n :=
  ⟨RegisterFaultDynamicProbeLifecycle.parentView o.organism.history s,o.identity,o.clock+2*N⟩

/-- The assembled organization represents EXACTLY the source post-parent,
and every organizational state retains that SAME registered owner. No Bool
program/history value is substituted for owner identity. -/
theorem same_founder_organization_owner (epsilon : NNReal) (he : epsilon≤1)
    (ho : o.organism.program=m.goal) :
    let parent:=postProbeParent i m omega o.organism
    let seed : OntogeneticSeed (State n) Bool:=⟨parent.physical,m.goal⟩
    organizationOwnerView N o (assembleRepairOrganization (substrate i) codec seed)=
      RegisterFaultDynamicProbeClocked.postClocked i m omega o ∧
    ∀s : RepairOrganizationState (State n) Action Bool,
      (RegisterTimestampedBirthSource.lineage i m).SameObject (organizationOwnerView N o s)
        (RegisterFaultDynamicProbeClocked.postClocked i m omega o) :=by
  dsimp only
  have hm:=(same_founder_maintained i m omega o epsilon he ho).1
  refine ⟨?_,?_⟩
  · have heq : RegisterFaultDynamicProbeClocked.postClocked i m omega o=
        ⟨postProbeParent i m omega o.organism,o.identity,o.clock+2*N⟩ :=by
      have hx:=RegisterFaultDynamicProbeClocked.actual_post_erase i m omega o
      have hi:=RegisterFaultDynamicProbeClocked.actual_post_identity i m omega o
      have ht:=RegisterFaultDynamicProbeClocked.actual_post_clock i m omega o
      cases hobj : RegisterFaultDynamicProbeClocked.postClocked i m omega o with
      | mk org id clock=>
        simp only [hobj] at hx hi ht
        cases hx
        cases hi
        cases ht
        rfl
    rw [heq]
    exact congrArg (fun org : Organism n=>
      (⟨org,o.identity,o.clock+2*N⟩ : ClockedOrganism n)) hm
  · intro s
    exact (RegisterFaultDynamicProbeClocked.actual_post_identity i m omega o).symm

/-- Original retained-parent NATIVE continuation contract, started at THIS
actual damaged or healthy post-probe state with THIS returned AST. It is a
separate registered continuation protocol, not the population episode's tail
or a continuation financed by its finite zero-income wallet. -/
def NativeMaintainedAt (i : Fin n) (noise : PMF Bool) (m : Mechanism)
    (epsilon : NNReal) (he : epsilon≤1) (price width d u : ℚ)
    (omega : Coordinate N→Bool×Bool) (o : ClockedOrganism n) : Prop :=
  let parent:=postProbeParent i m omega o.organism
  let p:=returnedAST i (classify price width d u (sourceData m width omega))
  ∀ᵐ rs ∂ RegisterFaultInfiniteRecord.recordPathLaw i noise m epsilon he (RegisterInstructionPurposeScale.astPolicy p) ⟨0,parent.physical,parent⟩,
    ∀t : ℕ,RegisterFaultNativeOrganization.readRecord i (rs t)∈
      (RegisterFaultNativeOrganization.system i m epsilon he).carrier ∧
      (RegisterRepairHistory.lineage i).SameObject
        (RegisterFaultDynamicProbeLifecycle.parentView o.organism.history
          (RegisterFaultNativeOrganization.readRecord i (rs t))) parent

omit [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)] in
theorem same_founder_native_continuation (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (ho : o.organism.program=m.goal) (b : Bool)
    (hs : classify price width d u (sourceData m width omega)=.repair b) :
    NativeMaintainedAt i noise m epsilon he price width d u omega o :=
  RegisterFaultNativeOrganization.actual_post_parent_p12_native i noise m epsilon he price width d u omega o.organism ho b hs

end MaintainedParent

section CommonConsumer
variable [MeasurableSpace (State n)] [MeasurableSingletonClass (State n)]

/-- Finite-generation replacement of the incompatible finite normalized
strict-lineage terminal: original roles on ONE actual first-birth parent.
All conclusions are constructed, not supplied as independent certificates.
The explicit Good/birth implications are not almost-sure full success. -/
theorem actual_finite_generation
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon<1)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1)
    (ho : o.organism.program=m.goal)
    (hgood : omega∈RegisterFaultFinitePurposeProbe.Good noise m epsilon he.le N width (u : ℝ))
    (b : Bool) (hs : classify price width d u (sourceData m width omega)=.repair b)
    (B : ℕ) (reads : RegisterPopulationJournalLearning.Raw RegisterFaultDynamicProbeParentDiscovery.Class B)
    (hg : reads∈RegisterPopulationJournalLearning.Good B)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class)
    (r : NNReal) (cap reserve : ℝ) (hc : (m.writeCost : ℝ)≤cap)
    (hr : ((2*N+3 : ℕ) : ℝ)*cap+(B : ℝ)*r≤reserve) :
    let es:=RegisterFaultDynamicProbeParentDiscovery.episode i m price width d u omega o.organism h w
    let k:=RegisterFaultDynamicProbeParentDiscovery.eventIndex i m price width d u omega o.organism h w 0
    let founder:=RegisterFaultDynamicProbeClocked.postClocked i m omega o
    let actor:={founder with clock:=o.clock+2*N+1}
    let q:=RegisterPopulationHistorySource.requestAt es k
    let bill:=fullCost (wholeTrace i m price width d u omega o
      (RegisterFaultDynamicProbeParentDiscovery.plan h w)) B r
    ResourceViable reserve (fun _=>0) bill ∧
    (∀t,bill t≤cumulativeResourceBalance reserve (fun _=>0) bill t) ∧
    RegisterFaultDynamicProbeP9Terminal.Six (0 : Fin 1) noise m (priceValue price hp) epsilon he.le
      (d : ℝ) (by exact_mod_cast hd) o.identity (o.clock+2*N)
      ((RegisterFaultDynamicProbeP9Terminal.clockedScale i).objectMap
        (RegisterFaultDynamicProbeP9Terminal.dataObject i m price width d u omega o)) ∧
    MaintainedAt i m omega o epsilon he.le ∧
    RegisterFaultDynamicProbeParentDiscovery.estimate
      (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u omega o.organism h w 0 reads)=
      RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N) [some founder] es k ∧
    (∀child,RegisterPopulationOwnerClockTransport.childAt i m.writeCost (o.clock+2*N) [some founder] es k=some child→
      (RegisterTimestampedBirthSource.lineage i
        (RegisterOwnProgramPopulation.mechanism m.writeCost [some founder] q)).OffspringOf actor child ∧
      (RegisterTimestampedBirthSource.lineage i m).SameObject actor founder ∧ child.clock=0) ∧
    Tendsto (fun K=>(RegisterPopulationJournalLearning.rawLaw (1/4)
      (by exact_mod_cast (by norm_num : (1/4 : ℝ)≤1) : (1/4 : NNReal)≤1) confuser K).real {rr |
        RegisterFaultDynamicProbeParentDiscovery.estimate
          (RegisterFaultDynamicProbeParentDiscovery.targetSensed i m price width d u omega o.organism h w 0 rr)≠
        RegisterPopulationOwnerClockTransport.actualParent i m.writeCost (o.clock+2*N) [some founder] es k})
      atTop (𝓝 0) ∧
    NativeMaintainedAt i noise m epsilon he.le price width d u omega o :=by
  dsimp only
  exact ⟨complete_finite_wallet i m price width d u omega o h w B r cap reserve hc hr,
    complete_finite_prepay i m price width d u omega o h w B r cap reserve hc hr,
    same_founder_retained_p9 i m price width d u omega o noise epsilon he hp hw hd ho hgood b hs,
    same_founder_maintained i m omega o epsilon he.le ho,
    good_mark_is_actual_clocked_parent i m price width d u omega o h w 0 reads hg,
    first_birth_same_founder i m price width d u omega o h w,
    same_episode_p12_discovery i m price width d u omega o h w 0 confuser,
    same_founder_native_continuation i m price width d u omega o noise epsilon he.le ho b hs⟩

end CommonConsumer

/-- No true-hazard guard is added to the selector. On the SAME full input
law, an actually returned repair entails non-total fault almost everywhere;
impossible zero-mass training words are not pointwise parameter evidence. -/
theorem same_source_repair_non_total_ae (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ) :
    ∀ᵐ z ∂ RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B,
      ∀b : Bool,classify price width d u (sourceData m width z.1.1)=.repair b→epsilon<1 :=by
  have hraw:=RegisterFaultDynamicProbeP9Terminal.repair_non_total_ae noise m epsilon he N price width d u
  rw [←RegisterFaultDynamicProbeHistoryPrice.experimentLaw_training_marginal noise epsilon he N] at hraw
  have hw:=ae_of_ae_map measurable_fst.aemeasurable hraw
  rw [←RegisterFaultDynamicProbeParentDiscovery.jointLaw_episode_marginal noise epsilon he confuser N B] at hw
  exact ae_of_ae_map measurable_fst.aemeasurable hw

/-- Actual source P9 consumer eliminates the independent non-total-fault
premise, with no acceptance or success conditioning of the input law. -/
theorem same_source_p9_six (noise : PMF Bool) (epsilon : NNReal) (he : epsilon≤1)
    (hp : 0≤price) (hw : 0<width) (hd : 0<d ∧ d<1) (ho : o.organism.program=m.goal)
    (confuser : PMF RegisterFaultDynamicProbeParentDiscovery.Class) (B : ℕ) :
    ∀ᵐ z ∂ RegisterFaultDynamicProbeParentDiscovery.jointLaw noise epsilon he confuser N B,
      z.1.1∈RegisterFaultFinitePurposeProbe.Good noise m epsilon he N width (u : ℝ)→∀b : Bool,
        classify price width d u (sourceData m width z.1.1)=.repair b→
        RegisterFaultDynamicProbeP9Terminal.Six (0 : Fin 1) noise m (priceValue price hp) epsilon he
          (d : ℝ) (by exact_mod_cast hd) o.identity (o.clock+2*N)
          ((RegisterFaultDynamicProbeP9Terminal.clockedScale i).objectMap
            (RegisterFaultDynamicProbeP9Terminal.dataObject i m price width d u z.1.1 o)) :=by
  filter_upwards [same_source_repair_non_total_ae m price width d u noise epsilon he confuser B] with z hz
  intro hg b hb
  exact same_founder_retained_p9 i m price width d u z.1.1 o noise epsilon (hz b hb) hp hw hd ho hg b hb

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFiniteGenerationCommonConsumer
