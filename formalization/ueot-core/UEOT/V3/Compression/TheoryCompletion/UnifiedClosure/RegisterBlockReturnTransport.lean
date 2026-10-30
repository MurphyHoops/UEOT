import UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockInfiniteTransport

/-!
Original promise: actual ongoing C4 transport must feed original return/P10 conclusions for the SAME object and goal.
Existing source: literal retained-parent/prefix/countable record transport and true infinite product-source pushforward, not a desired conditional-law field.
Premise reduced: derive actual block-return/P10 event probabilities and the precise missing passive-body permission from that source.
Model/boundary: exactly k transactions per registered embedded sweep; hidden unvisited coordinates stay at their initial values; neither full-n sweep nor a new policy/GOD/resource theorem.
Consumer: original actual_no_return_tail/actual_returns_forever/original_p10_body_tail; exact full-body iff and hidden-information obstruction retain their original event/source meaning.
-/
namespace UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockReturnTransport
open MeasureTheory ProbabilityTheory Set Filter
open RegisterRepairSource RegisterRepairHistory RegisterMechanismPurpose RegisterFaultJointRecord
open RegisterRotatingBodySource RegisterRotatingBodyReturns RegisterBlockFormationTransport
open RegisterBlockInfiniteTransport
open scoped NNReal ENNReal Topology
noncomputable section
local instance {n : ℕ} : MeasurableSpace (ModeRecord n):=⊤
local instance {n : ℕ} : MeasurableSingletonClass (ModeRecord n):=⟨fun _=>trivial⟩

/-- Actual service-block goal on the original fine retained parent. -/
def blockGoal {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) : Prop:=
  BodyGoal b (state e (RegisterBlockInfiniteTransport.parentAt e b fee o w r).physical)

/-- This is an explicit initial-state condition on coordinates never executed. -/
def PassiveReady {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (o : Organism n) : Prop:=
  ∀l,l∉Set.range e → o.physical l=b

theorem goal_transport {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    blockGoal e b fee o w r ↔ BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee (organism e o) (stream e w) r).physical :=by
  change BodyGoal b (organism e (RegisterBlockInfiniteTransport.parentAt e b fee o w r)).physical ↔ _
  rw [RegisterBlockInfiniteTransport.parent_transport]

theorem full_goal_iff {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n) (w : RoundStream n) (r : ℕ) :
    BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee o w r).physical ↔
      blockGoal e b fee o w r ∧ PassiveReady e b o :=by
  constructor
  · intro h
    refine ⟨fun j=>h (e j),?_⟩
    intro l hl
    have hh:=h l
    rwa [unvisited_preserved e b fee o w r l hl] at hh
  · rintro ⟨hb,hp⟩ l
    by_cases hl : l∈Set.range e
    · obtain ⟨j,rfl⟩:=hl
      exact hb j
    · rw [unvisited_preserved e b fee o w r l hl]
      exact hp l hl

/-- Missing passive readiness is an actual never-full-body obstruction,
valid at EVERY actual clock and stream, not merely failure of a proof search. -/
theorem not_passive_never_full {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (o : Organism n)
    (hp : ¬PassiveReady e b o) (w : RoundStream n) (r : ℕ) :
    ¬BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee o w r).physical :=
  fun h=>hp ((full_goal_iff e b fee o w r).mp h).2

private theorem measurable_macro_goal {k : ℕ} (b : Bool) (fee : NNReal) (o : Organism k) (r : ℕ) :
    MeasurableSet {w : RoundStream k | BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee o w (r+1)).physical} :=by
  simp_rw [actual_macro_goal_iff]
  exact (good_measurable k).preimage (measurable_pi_apply r)

/-- Exact service-block mass at every positive macro clock, on the genuine
fine n-product source. The exponent is k visited ports, not n. -/
theorem actual_block_mass {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) (r : ℕ) :
    infiniteLaw n noise epsilon he {w | blockGoal e b fee o w (r+1)}=successMass k epsilon :=by
  have hE : {w | blockGoal e b fee o w (r+1)}=stream e ⁻¹'
      {v | BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee (organism e o) v (r+1)).physical} :=by
    ext w
    exact goal_transport e b fee o w (r+1)
  rw [hE,raw_event_transport e noise epsilon he _ (measurable_macro_goal b fee (organism e o) r)]
  exact actual_body_mass b fee noise epsilon he (organism e o) r

/-- Exact no-return window, counted in R complete embedded k-transaction
rounds. This does not change any micro-time discount or resource unit. -/
theorem actual_block_no_return_tail {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) (N R : ℕ) :
    infiniteLaw n noise epsilon he {w | ∀r∈Finset.range R,¬blockGoal e b fee o w (N+r+1)}=
      (1-successMass k epsilon)^R :=by
  let S : Set (RoundStream k):={v | ∀r∈Finset.range R,¬BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee (organism e o) v (N+r+1)).physical}
  have hm : MeasurableSet S :=by
    have hE : S=⋂r : ℕ,⋂(_ : r∈Finset.range R),{v | ¬BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee (organism e o) v (N+r+1)).physical} :=by
      ext v
      simp [S]
    rw [hE]
    exact MeasurableSet.iInter (fun r=>MeasurableSet.iInter (fun _=>(measurable_macro_goal b fee (organism e o) (N+r)).compl))
  have hE : {w | ∀r∈Finset.range R,¬blockGoal e b fee o w (N+r+1)}=stream e ⁻¹' S :=by
    ext w
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,S,goal_transport]
  rw [hE,raw_event_transport e noise epsilon he S hm]
  exact actual_no_return_tail b fee noise epsilon he (organism e o) N R

/-- Actual returns are transported on ONE full-measure event; no successful
round is selected for a restart and no path is replaced. -/
theorem actual_block_returns_forever {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon<1) (o : Organism n) :
    ∀ᵐ w ∂infiniteLaw n noise epsilon he.le,∀N : ℕ,∃r≥N,blockGoal e b fee o w (r+1) :=by
  have hh:=RegisterRotatingBodyReturns.actual_returns_forever b fee noise epsilon he (organism e o)
  rw [←source_law e noise epsilon he.le] at hh
  have hf:=ae_of_ae_map (measurable_stream e).aemeasurable hh
  filter_upwards [hf] with w hw
  intro N
  obtain ⟨r,hr,hg⟩:=hw N
  exact ⟨r,hr,(goal_transport e b fee o w (r+1)).mpr hg⟩

/-- Original P10 is genuinely consumed on the SAME actual block event via
its exact original source transport; no new drift-certificate field appears. -/
theorem original_p10_block_tail {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal) (noise : PMF Bool)
    (epsilon : NNReal) (he : epsilon ≤ 1) (o : Organism n) (r : ℕ) :
    (infiniteLaw n noise epsilon he).real {w | ¬blockGoal e b fee o w (r+1)}≤(RegisterRotatingBodyP10.failureRate k epsilon : ℝ) :=by
  have hE : {w | ¬blockGoal e b fee o w (r+1)}=stream e ⁻¹'
      {v | ¬BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee (organism e o) v (r+1)).physical} :=by
    ext w
    exact not_congr (goal_transport e b fee o w (r+1))
  have hm : MeasurableSet {v | ¬BodyGoal b (RegisterRotatingBodyReturns.parentAt b fee (organism e o) v (r+1)).physical} :=
    (measurable_macro_goal b fee (organism e o) r).compl
  rw [hE,measureReal_def,raw_event_transport e noise epsilon he _ hm]
  exact RegisterRotatingBodyP10.original_p10_body_tail b fee noise epsilon he (organism e o) r

/-- Two actual initial seeds differ ONLY at one unvisited physical coordinate. -/
def readySeed (n : ℕ) (b : Bool) : Organism n:=⟨[],fun _=>b,b⟩
def hiddenSeed {n : ℕ} (b : Bool) (l : Fin n) : Organism n:=⟨[],fun v=>if v=l then !b else b,b⟩

/-- Even the ENTIRE projected countable record cannot recover missing passive
initial information uniformly over these actual seeds. This is a positive-mass
SOURCE-AE obstruction, not just a zero-probability all-success raw word. A known
PassiveReady initial condition is additional information and is not refuted. -/
theorem hidden_body_not_ae_decodable {k n : ℕ} (e : Fin k ↪ Fin n) (b : Bool) (fee : NNReal)
    (noise : PMF Bool) (epsilon : NNReal) (he : epsilon<1) (l : Fin n) (hl : l∉Set.range e) :
    ¬∃ D : (ℕ→Fin k→ModeRecord k)→Prop,
      (∀ᵐ w ∂infiniteLaw n noise epsilon he.le,
        BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee (readySeed n b) w 1).physical ↔
          D (projectedRecords e (infiniteRecords e b fee (readySeed n b) w))) ∧
      (∀ᵐ w ∂infiniteLaw n noise epsilon he.le,
        BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee (hiddenSeed b l) w 1).physical ↔
          D (projectedRecords e (infiniteRecords e b fee (hiddenSeed b l) w))) :=by
  have hs : organism e (readySeed n b)=organism e (hiddenSeed b l) :=by
    have hstate : state e (readySeed n b).physical=state e (hiddenSeed b l).physical :=by
      ext j
      have hj : e j≠l:=fun h=>hl ⟨j,h⟩
      simp only [state,readySeed,hiddenSeed,if_neg hj]
    change (⟨[],state e (readySeed n b).physical,b⟩ : Organism k)=⟨[],state e (hiddenSeed b l).physical,b⟩
    rw [hstate]
  have hpaths (w : RoundStream n) :
      projectedRecords e (infiniteRecords e b fee (readySeed n b) w)=
        projectedRecords e (infiniteRecords e b fee (hiddenSeed b l) w) :=by
    funext r j
    change modeRecord e (RegisterBlockInfiniteTransport.recordAt e b fee (readySeed n b) r j w)=
      modeRecord e (RegisterBlockInfiniteTransport.recordAt e b fee (hiddenSeed b l) r j w)
    rw [RegisterBlockInfiniteTransport.record_transport,RegisterBlockInfiniteTransport.record_transport,hs]
  have hp : PassiveReady e b (readySeed n b):=fun _ _=>rfl
  have hn : ¬PassiveReady e b (hiddenSeed b l) :=by
    intro h
    have hh:=h l hl
    simp [hiddenSeed] at hh
  have hmass : infiniteLaw n noise epsilon he.le
      {w | BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee (readySeed n b) w 1).physical}=successMass k epsilon :=by
    have hE : {w | BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee (readySeed n b) w 1).physical}=
        {w | blockGoal e b fee (readySeed n b) w 1} :=by
      ext w
      simp only [full_goal_iff,hp,and_true]
    rw [hE]
    exact actual_block_mass e b fee noise epsilon he.le (readySeed n b) 0
  rintro ⟨D,hready,hhidden⟩
  have hnever : ∀ᵐ w ∂infiniteLaw n noise epsilon he.le,
      ¬BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee (readySeed n b) w 1).physical :=by
    filter_upwards [hready,hhidden] with w hR hH
    intro hG
    have hD:=hR.mp hG
    rw [hpaths w] at hD
    exact not_passive_never_full e b fee (hiddenSeed b l) hn w 1 (hH.mpr hD)
  have hz : infiniteLaw n noise epsilon he.le
      {w | BodyGoal b (RegisterBlockInfiniteTransport.parentAt e b fee (readySeed n b) w 1).physical}=0 :=by
    simpa only [not_not] using ae_iff.mp hnever
  rw [hmass] at hz
  exact (successMass_pos k epsilon he).ne' hz

end
end UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterBlockReturnTransport
