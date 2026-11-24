/-!
# TC-NEW-01: Certified Development Viability Theorem Family (Proposed Track)

CONJECTURE / NEW_FORMALIZATION_TRACK (`TC-NEW-01`, `research_only`).
- Not counted in the frozen 106 P-IDs or 4 generators of UEOT Core v3.0.
- Does not import or mutate `UEOT Core`, `SOURCE_LOCK.json`, or `GI-R0-02` ledgers.

Per UEOT-GI Frontier Development Spec v3.0 (§14 & `V3_IMPLEMENTATION_BACKLOG.yaml`),
this module proposes and machine-checks the finite certified-development viability
theorem family together with non-circular migration, risk composition, concrete
growth, and anti-circularity no-go counterexamples:

1. `micro_step_preserves_viable_domain`
2. `certified_upgrade_preserves_constitutive_domain`
3. `finite_migration_path_viable`
4. `development_risk_union_bound` & `development_risk_within_cap`
5. `unsafe_upgrade_no_go`
6. `improvement_not_implied_by_persistence`
7. `circular_certificate_no_go`
8. `concrete_nonvacuous_certified_growth_witness`
-/

namespace UEOT.V3.Compression.TheoryCompletion.Proposed.CertifiedDevelopmentViability

/-- Exact finite controlled process with spend-before-replenish resources,
constitutive identity, authority epoch, and explicit stop-fence predicate. -/
structure FiniteControlledProcess (X A : Type) where
  states : List X
  actions : List A
  support : X → A → List X
  safe : X → Prop
  identityOf : X → Nat
  authorityEpochOf : X → Nat
  stopFlag : X → Bool
  cost : X → A → Nat
  supply : X → A → Nat
  support_nonempty : ∀ x a, x ∈ states → a ∈ actions → support x a ≠ []
  support_subset : ∀ x a x', x' ∈ support x a → x' ∈ states

/-- Viable domain under fixed process & stop fence:
every state is inside the declared state space and safe, and any non-stopped
state has at least one in-domain transition preserving identity and
non-decreasing authority epoch. Stopped states halt lawfully (`SAFE_STOP`). -/
def ViableDomain {X A : Type}
    (P : FiniteControlledProcess X A) (V : X → Prop) : Prop :=
  (∀ x, V x → x ∈ P.states ∧ P.safe x) ∧
  (∀ x, V x → P.stopFlag x = false →
    ∃ a, a ∈ P.actions ∧ ∀ x', x' ∈ P.support x a →
      V x' ∧ P.identityOf x' = P.identityOf x ∧ P.authorityEpochOf x' ≥ P.authorityEpochOf x)

/-- Admissible action satisfying stop fence, support closure in `V`, identity &
authority preservation, and pre-action resource reserve solvency (`cost + reserve ≤ budget`). -/
def AdmissibleSafeAction {X A : Type}
    (P : FiniteControlledProcess X A) (V : X → Prop) (reserve budget : Nat)
    (x : X) (a : A) : Prop :=
  P.stopFlag x = false ∧
  a ∈ P.actions ∧
  (∀ x', x' ∈ P.support x a →
    V x' ∧ P.identityOf x' = P.identityOf x ∧ P.authorityEpochOf x' ≥ P.authorityEpochOf x) ∧
  P.cost x a + reserve ≤ budget

/-- Checkable external migration witness from `P_old` to `P_new`.
Crucially, this structure does NOT assume `ViableDomain P_new _` as an axiom;
viability of `transportedDomain` on `P_new` is proved from checkable premises. -/
structure ExplicitMigrationSource
    {X_old A_old X_new A_new : Type}
    (P_old : FiniteControlledProcess X_old A_old)
    (P_new : FiniteControlledProcess X_new A_new) where
  sourceId : Nat
  failedSources : List Nat
  source_independent : sourceId ∉ failedSources
  mapState : X_old → X_new
  mapAction : A_old → A_new
  state_in_new : ∀ x, x ∈ P_old.states → mapState x ∈ P_new.states
  action_in_new : ∀ a, a ∈ P_old.actions → mapAction a ∈ P_new.actions
  preserves_identity : ∀ x, P_new.identityOf (mapState x) = P_old.identityOf x
  preserves_authority_ge : ∀ x, P_new.authorityEpochOf (mapState x) ≥ P_old.authorityEpochOf x
  preserves_authority_mono :
    ∀ x x', P_old.authorityEpochOf x' ≥ P_old.authorityEpochOf x →
      P_new.authorityEpochOf (mapState x') ≥ P_new.authorityEpochOf (mapState x)
  preserves_stop_fence : ∀ x, P_old.stopFlag x = true → P_new.stopFlag (mapState x) = true
  preserves_safety : ∀ x, P_old.safe x → P_new.safe (mapState x)
  support_simulation :
    ∀ x a y', y' ∈ P_new.support (mapState x) (mapAction a) →
      ∃ x', x' ∈ P_old.support x a ∧ y' = mapState x'
  migrationCost : Nat
  rollbackReserve : Nat

/-- Derived image domain in `P_new` transported from `V_old`. -/
def transportedDomain {X_old A_old X_new A_new : Type}
    {P_old : FiniteControlledProcess X_old A_old}
    {P_new : FiniteControlledProcess X_new A_new}
    (M : ExplicitMigrationSource P_old P_new)
    (V_old : X_old → Prop) : X_new → Prop :=
  fun y => ∃ x, V_old x ∧ y = M.mapState x

/-- Theorem 1 (`micro_step_preserves_viable_domain`):
Under fixed source and admissible safe action, any positive-support micro-step
stays inside `V`, remains safe, preserves identity and monotonic authority epoch,
and maintains the spend-before-replenish resource reserve bound. -/
theorem micro_step_preserves_viable_domain {X A : Type}
    (P : FiniteControlledProcess X A) (V : X → Prop)
    (reserve budget : Nat) (x x' : X) (a : A)
    (hV : ViableDomain P V)
    (_hxV : V x)
    (hAdm : AdmissibleSafeAction P V reserve budget x a)
    (hx' : x' ∈ P.support x a) :
    V x' ∧
    P.safe x' ∧
    P.identityOf x' = P.identityOf x ∧
    P.authorityEpochOf x' ≥ P.authorityEpochOf x ∧
    budget - P.cost x a + P.supply x a ≥ reserve := by
  have hStep := hAdm.2.2.1 x' hx'
  have hx'Safe := (hV.1 x' hStep.1).2
  have hBudget : P.cost x a + reserve ≤ budget := hAdm.2.2.2
  refine ⟨hStep.1, hx'Safe, hStep.2.1, hStep.2.2, ?_⟩
  omega

/-- Theorem 2 (`certified_upgrade_preserves_constitutive_domain`):
Derives target viability of `transportedDomain M V_old` from `ExplicitMigrationSource`
premises without circularly assuming target viability, while transporting safety,
identity, authority epoch, stop-fence compliance, and independent source provenance. -/
theorem certified_upgrade_preserves_constitutive_domain
    {X_old A_old X_new A_new : Type}
    (P_old : FiniteControlledProcess X_old A_old)
    (P_new : FiniteControlledProcess X_new A_new)
    (V_old : X_old → Prop)
    (hV : ViableDomain P_old V_old)
    (M : ExplicitMigrationSource P_old P_new) :
    ViableDomain P_new (transportedDomain M V_old) ∧
    (∀ x, V_old x →
      transportedDomain M V_old (M.mapState x) ∧
      P_new.safe (M.mapState x) ∧
      P_new.identityOf (M.mapState x) = P_old.identityOf x ∧
      P_new.authorityEpochOf (M.mapState x) ≥ P_old.authorityEpochOf x ∧
      M.sourceId ∉ M.failedSources) := by
  have hNewViable : ViableDomain P_new (transportedDomain M V_old) := by
    refine ⟨?_, ?_⟩
    · intro y hy
      rcases hy with ⟨x, hxV, rfl⟩
      have hx := hV.1 x hxV
      exact ⟨M.state_in_new x hx.1, M.preserves_safety x hx.2⟩
    · intro y hy hStopNew
      rcases hy with ⟨x, hxV, rfl⟩
      have hStopOld : P_old.stopFlag x = false := by
        cases hSO : P_old.stopFlag x with
        | false => rfl
        | true =>
          have hSN := M.preserves_stop_fence x hSO
          rw [hSN] at hStopNew
          contradiction
      rcases hV.2 x hxV hStopOld with ⟨a, haAct, haSucc⟩
      refine ⟨M.mapAction a, M.action_in_new a haAct, ?_⟩
      intro y' hy'
      rcases M.support_simulation x a y' hy' with ⟨x', hx'Supp, rfl⟩
      have hx' := haSucc x' hx'Supp
      exact ⟨
        ⟨x', hx'.1, rfl⟩,
        by rw [M.preserves_identity x', M.preserves_identity x, hx'.2.1],
        M.preserves_authority_mono x x' hx'.2.2
      ⟩
  refine ⟨hNewViable, ?_⟩
  intro x hxV
  have hxSafe := (hV.1 x hxV).2
  exact ⟨
    ⟨x, hxV, rfl⟩,
    M.preserves_safety x hxSafe,
    M.preserves_identity x,
    M.preserves_authority_ge x,
    M.source_independent
  ⟩

/-- Bundled runtime/development configuration at a point along a finite path. -/
structure VersionedState where
  X : Type
  A : Type
  proc : FiniteControlledProcess X A
  domain : X → Prop
  state : X
  budget : Nat
  reserve : Nat
  rootIdentity : Nat
  rootAuthorityEpoch : Nat

/-- Constitutive invariants preserved along valid development trajectories. -/
def ValidVersionedState (s : VersionedState) : Prop :=
  ViableDomain s.proc s.domain ∧
  s.domain s.state ∧
  s.proc.safe s.state ∧
  s.proc.identityOf s.state = s.rootIdentity ∧
  s.proc.authorityEpochOf s.state ≥ s.rootAuthorityEpoch ∧
  s.budget ≥ s.reserve

/-- One certified step along a finite development trajectory: either an admissible
micro-step within fixed process `P` or an explicit non-circular version migration. -/
inductive FiniteDevStep : VersionedState → VersionedState → Prop where
  | microStep
      {X A : Type} {P : FiniteControlledProcess X A}
      {V : X → Prop} {x x' : X} {a : A}
      {budget reserve rootId rootEpoch : Nat} :
      AdmissibleSafeAction P V reserve budget x a →
      x' ∈ P.support x a →
      FiniteDevStep
        ⟨X, A, P, V, x, budget, reserve, rootId, rootEpoch⟩
        ⟨X, A, P, V, x', budget - P.cost x a + P.supply x a, reserve, rootId, rootEpoch⟩
  | migrateStep
      {X_old A_old X_new A_new : Type}
      {P_old : FiniteControlledProcess X_old A_old}
      {P_new : FiniteControlledProcess X_new A_new}
      {V_old : X_old → Prop} {x : X_old}
      {budget reserve rootId rootEpoch : Nat}
      (M : ExplicitMigrationSource P_old P_new) :
      M.migrationCost + M.rollbackReserve ≤ budget →
      reserve ≤ M.rollbackReserve →
      FiniteDevStep
        ⟨X_old, A_old, P_old, V_old, x, budget, reserve, rootId, rootEpoch⟩
        ⟨X_new, A_new, P_new, transportedDomain M V_old, M.mapState x,
          budget - M.migrationCost, reserve, rootId, rootEpoch⟩

private theorem finite_dev_step_preserves_valid
    {s1 s2 : VersionedState}
    (hStep : FiniteDevStep s1 s2)
    (hValid : ValidVersionedState s1) :
    ValidVersionedState s2 ∧
    s2.rootIdentity = s1.rootIdentity ∧
    s2.rootAuthorityEpoch = s1.rootAuthorityEpoch := by
  cases hStep with
  | @microStep X A P V x x' a budget reserve rootId rootEpoch hAdm hx' =>
    rcases hValid with ⟨hV, hxV, _hxSafe, hxId, hxAuth, _hBud⟩
    have hMicro := micro_step_preserves_viable_domain P V reserve budget x x' a hV hxV hAdm hx'
    refine ⟨⟨hV, hMicro.1, hMicro.2.1, ?_, ?_, hMicro.2.2.2.2⟩, rfl, rfl⟩
    · dsimp only at hxId ⊢
      exact hMicro.2.2.1.trans hxId
    · dsimp only at hxAuth ⊢
      have ha1 := hMicro.2.2.2.1
      omega
  | @migrateStep X_old A_old X_new A_new P_old P_new V_old x budget reserve rootId rootEpoch M hMigBud hMigRes =>
    rcases hValid with ⟨hVOld, hxVOld, _hxSafeOld, hxIdOld, hxAuthOld, _hBudOld⟩
    have hUp := certified_upgrade_preserves_constitutive_domain P_old P_new V_old hVOld M
    have hxProp := hUp.2 x hxVOld
    refine ⟨⟨hUp.1, hxProp.1, hxProp.2.1, ?_, ?_, ?_⟩, rfl, rfl⟩
    · dsimp only at hxIdOld ⊢
      exact hxProp.2.2.1.trans hxIdOld
    · dsimp only at hxAuthOld ⊢
      have ha2 := hxProp.2.2.2.1
      omega
    · dsimp only
      omega

/-- Finite alternating sequence of admissible micro-steps and explicit
certified version migrations. -/
inductive FiniteDevPath : VersionedState → VersionedState → Prop where
  | nil (s : VersionedState) : FiniteDevPath s s
  | step {s1 s2 s3 : VersionedState} :
      FiniteDevStep s1 s2 → FiniteDevPath s2 s3 → FiniteDevPath s1 s3

/-- Theorem 3 (`finite_migration_path_viable`):
Induction over arbitrary finite alternating micro-step and certified-migration paths
preserving domain viability, safety, root identity, monotonic authority, and reserve solvency. -/
theorem finite_migration_path_viable
    {s0 sn : VersionedState}
    (hStart : ValidVersionedState s0)
    (hPath : FiniteDevPath s0 sn) :
    ValidVersionedState sn ∧
    sn.rootIdentity = s0.rootIdentity ∧
    sn.rootAuthorityEpoch = s0.rootAuthorityEpoch := by
  induction hPath with
  | nil s =>
    exact ⟨hStart, rfl, rfl⟩
  | step hOne _hRest ih =>
    have hMid := finite_dev_step_preserves_valid hOne hStart
    rcases ih hMid.1 with ⟨hEnd, hId, hAuth⟩
    exact ⟨hEnd, hId.trans hMid.2.1, hAuth.trans hMid.2.2⟩

/-- Exact finite sum over a list of elements mapped to natural weights. -/
def sumList {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => f x + sumList rest f

/-- Discrete probability mass (numerator over shared total sample weight)
of boolean failure event `ev` on sample space `samples`. -/
def eventMass {Ω : Type} (samples : List Ω) (w : Ω → Nat) (ev : Ω → Bool) : Nat :=
  sumList samples (fun ω => if ev ω then w ω else 0)

/-- Union of finite boolean events along a sequence of development checks. -/
def anyEvent {Ω : Type} (evs : List (Ω → Bool)) (ω : Ω) : Bool :=
  match evs with
  | [] => false
  | e :: rest => e ω || anyEvent rest ω

private theorem eventMass_or_le {Ω : Type} (samples : List Ω) (w : Ω → Nat)
    (e1 e2 : Ω → Bool) :
    eventMass samples w (fun ω => e1 ω || e2 ω) ≤
      eventMass samples w e1 + eventMass samples w e2 := by
  induction samples with
  | nil =>
    simp [eventMass, sumList]
  | cons ω rest ih =>
    simp only [eventMass, sumList] at *
    have hHead :
        (if (e1 ω || e2 ω) = true then w ω else 0) ≤
          (if e1 ω = true then w ω else 0) + (if e2 ω = true then w ω else 0) := by
      cases e1 ω <;> cases e2 ω <;> simp
    omega

private theorem eventMass_false_eq_zero {Ω : Type} (samples : List Ω) (w : Ω → Nat) :
    eventMass samples w (fun _ => false) = 0 := by
  induction samples with
  | nil => rfl
  | cons ω rest ih =>
    simp [eventMass, sumList] at *
    exact ih

private theorem eventMass_anyEvent_le_sum {Ω : Type} (samples : List Ω) (w : Ω → Nat)
    (events : List (Ω → Bool)) :
    eventMass samples w (anyEvent events) ≤
      sumList events (fun ev => eventMass samples w ev) := by
  induction events with
  | nil =>
    have h0 := eventMass_false_eq_zero samples w
    have heq : anyEvent ([] : List (Ω → Bool)) = (fun _ => false) := rfl
    rw [heq, sumList, h0]
    exact Nat.le_refl 0
  | cons ev rest ih =>
    have hStep := eventMass_or_le samples w ev (anyEvent rest)
    have heq : anyEvent (ev :: rest) = (fun ω => ev ω || anyEvent rest ω) := rfl
    rw [heq, sumList]
    omega

/-- Conditionally valid per-step risk certificate bound on a shared sample space,
requiring explicit `evidenceDigest` attribution and `eventMass ≤ alphaMass`. -/
structure RiskStep {Ω : Type} (samples : List Ω) (w : Ω → Nat) where
  stepId : Nat
  evidenceDigest : Nat
  failureEvent : Ω → Bool
  alphaMass : Nat
  bound_holds : eventMass samples w failureEvent ≤ alphaMass

private theorem sumList_risk_bounds {Ω : Type} (samples : List Ω) (w : Ω → Nat)
    (steps : List (RiskStep samples w)) :
    sumList (steps.map (·.failureEvent)) (fun ev => eventMass samples w ev) ≤
      sumList steps (·.alphaMass) := by
  induction steps with
  | nil =>
    simp [sumList]
  | cons s rest ih =>
    simp only [List.map_cons, sumList] at *
    have hs := s.bound_holds
    omega

/-- Theorem 4 (`development_risk_union_bound`):
Union bound across dependent conditional history steps on a shared finite probability
space: total failure mass does not exceed the sum of attributed step `alphaMass` bounds. -/
theorem development_risk_union_bound {Ω : Type} (samples : List Ω) (w : Ω → Nat)
    (steps : List (RiskStep samples w)) :
    eventMass samples w (anyEvent (steps.map (·.failureEvent))) ≤
      sumList steps (·.alphaMass) := by
  have h1 := eventMass_anyEvent_le_sum samples w (steps.map (·.failureEvent))
  have h2 := sumList_risk_bounds samples w steps
  omega

/-- Corollary (`development_risk_within_cap`):
When total attributed alpha stays within an explicit budget `alphaCap`, joint failure
mass is strictly bounded by `alphaCap`. -/
theorem development_risk_within_cap {Ω : Type} (samples : List Ω) (w : Ω → Nat)
    (steps : List (RiskStep samples w)) (alphaCap : Nat)
    (hCap : sumList steps (·.alphaMass) ≤ alphaCap) :
    eventMass samples w (anyEvent (steps.map (·.failureEvent))) ≤ alphaCap := by
  have hUnion := development_risk_union_bound samples w steps
  omega

/-! ## Concrete No-Go Counterexamples & Non-Circularity Witness (§14.2) -/

/-- Broken upgrade target where state `false` appears safe locally, yet its only
action immediately transitions into unsafe state `true` (`safe true := False`). -/
def unsafeTargetProc : FiniteControlledProcess Bool Bool where
  states := [false, true]
  actions := [false]
  support := fun _ _ => [true]
  safe := fun s => s = false
  identityOf := fun _ => 1
  authorityEpochOf := fun _ => 1
  stopFlag := fun _ => false
  cost := fun _ _ => 0
  supply := fun _ _ => 0
  support_nonempty := by
    intro _ _ _ _
    simp
  support_subset := by
    intro _ _ x' hx'
    simp at hx'
    subst hx'
    simp

/-- Theorem 5 (`unsafe_upgrade_no_go`):
An upgrade omitting `support_simulation` fails target domain viability on a concrete
2-state process even when start state safety, identity, and authority match. -/
theorem unsafe_upgrade_no_go :
    ¬ ViableDomain unsafeTargetProc (fun s => s = false) := by
  intro ⟨_hSafe, hStep⟩
  have hF := hStep false rfl rfl
  rcases hF with ⟨a, _haAct, haSucc⟩
  have hx := haSucc true (by simp [unsafeTargetProc])
  have : (true : Bool) = false := hx.1
  contradiction

/-- Helper deterministic 1-state safe process parametrized by action cost. -/
def mkSingleSafeProc (actionCost : Nat) : FiniteControlledProcess Bool Bool where
  states := [false]
  actions := [false]
  support := fun _ _ => [false]
  safe := fun s => s = false
  identityOf := fun _ => 42
  authorityEpochOf := fun _ => 1
  stopFlag := fun _ => false
  cost := fun _ _ => actionCost
  supply := fun _ _ => 0
  support_nonempty := by
    intro _ _ _ _
    simp
  support_subset := by
    intro _ _ x' hx'
    simp at hx'
    subst hx'
    simp

def persistentBaseProc : FiniteControlledProcess Bool Bool := mkSingleSafeProc 4
def persistentNoGainProc : FiniteControlledProcess Bool Bool := mkSingleSafeProc 4

def persistentNoGainMigration :
    ExplicitMigrationSource persistentBaseProc persistentNoGainProc where
  sourceId := 10
  failedSources := [99]
  source_independent := by decide
  mapState := fun s => s
  mapAction := fun a => a
  state_in_new := by intro x hx; exact hx
  action_in_new := by intro a ha; exact ha
  preserves_identity := by intro _; rfl
  preserves_authority_ge := by intro _; exact Nat.le_refl _
  preserves_authority_mono := by intro _ _ h; exact h
  preserves_stop_fence := by intro _ h; exact h
  preserves_safety := by intro _ h; exact h
  support_simulation := by
    intro x a y' hy'
    exact ⟨y', hy', rfl⟩
  migrationCost := 0
  rollbackReserve := 1

/-- Independent evaluation score (higher is better = budget ceiling minus step cost). -/
def evalCostUtility {X A : Type}
    (P : FiniteControlledProcess X A) (x : X) (a : A) : Nat :=
  10 - P.cost x a

/-- Theorem 6 (`improvement_not_implied_by_persistence`):
Concrete witness showing persistence + valid certified migration alone do NOT imply
strict evaluation improvement (`evalCostUtility` stays `6 = 6`, not `> 6`). -/
theorem improvement_not_implied_by_persistence :
    ViableDomain persistentNoGainProc
      (transportedDomain persistentNoGainMigration (fun s => s = false)) ∧
    evalCostUtility persistentNoGainProc false false =
      evalCostUtility persistentBaseProc false false ∧
    ¬ (evalCostUtility persistentNoGainProc false false >
      evalCostUtility persistentBaseProc false false) := by
  have hBaseViable : ViableDomain persistentBaseProc (fun s => s = false) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      subst hx
      simp [persistentBaseProc, mkSingleSafeProc]
    · intro x hx _hStop
      subst hx
      refine ⟨false, by simp [persistentBaseProc, mkSingleSafeProc], ?_⟩
      intro x' hx'
      simp [persistentBaseProc, mkSingleSafeProc] at hx'
      subst hx'
      exact ⟨rfl, rfl, Nat.le_refl _⟩
  have hCert := certified_upgrade_preserves_constitutive_domain
    persistentBaseProc persistentNoGainProc (fun s => s = false)
    hBaseViable persistentNoGainMigration
  refine ⟨hCert.1, rfl, ?_⟩
  simp [evalCostUtility, persistentNoGainProc, persistentBaseProc, mkSingleSafeProc]

/-- Vacuous self-declared certificate omitting checkable simulation witnesses.
Mandatory TC-NEW-01 negative control schema. -/
structure SelfDeclaredUpgrade (X A : Type) where
  targetProc : FiniteControlledProcess X A
  claimedDomain : X → Prop
  selfDeclaredCertified : Bool

/-- Concrete invalid candidate claiming `selfDeclaredCertified = true` over
`unsafeTargetProc` whose transition breaks viability. -/
def brokenSelfCertifiedCandidate : SelfDeclaredUpgrade Bool Bool where
  targetProc := unsafeTargetProc
  claimedDomain := fun s => s = false
  selfDeclaredCertified := true

/-- Theorem 7 (`circular_certificate_no_go`):
Mandatory negative control proving why taking "certified upgrade ⇒ safe/viable" as
an axiom is circular and unsound: a self-declared `certified = true` candidate can
fail `ViableDomain` concretely. -/
theorem circular_certificate_no_go :
    ∃ u : SelfDeclaredUpgrade Bool Bool,
      u.selfDeclaredCertified = true ∧ ¬ ViableDomain u.targetProc u.claimedDomain := by
  exact ⟨brokenSelfCertifiedCandidate, rfl, unsafe_upgrade_no_go⟩

/-- Upgraded process constructed from observed high-cost inefficiency (`cost=4` → `cost=1`),
paired with non-circular migration witness `growthMigration`. -/
def growthUpgradedProc : FiniteControlledProcess Bool Bool := mkSingleSafeProc 1

def growthMigration :
    ExplicitMigrationSource persistentBaseProc growthUpgradedProc where
  sourceId := 101
  failedSources := [99]
  source_independent := by decide
  mapState := fun s => s
  mapAction := fun a => a
  state_in_new := by intro x hx; exact hx
  action_in_new := by intro a ha; exact ha
  preserves_identity := by intro _; rfl
  preserves_authority_ge := by intro _; exact Nat.le_refl _
  preserves_authority_mono := by intro _ _ h; exact h
  preserves_stop_fence := by intro _ h; exact h
  preserves_safety := by intro _ h; exact h
  support_simulation := by
    intro x a y' hy'
    exact ⟨y', hy', rfl⟩
  migrationCost := 1
  rollbackReserve := 1

/-- Theorem 8 (`concrete_nonvacuous_certified_growth_witness`):
Non-vacuous finite witness required by §14.2: from an observed cost bottleneck (`cost=4`),
constructs a candidate `growthUpgradedProc` (`cost=1`) with an independent migration witness,
derives `ViableDomain` of the transported domain, and proves strict independent utility gain (`9 > 6`). -/
theorem concrete_nonvacuous_certified_growth_witness :
    ViableDomain growthUpgradedProc
      (transportedDomain growthMigration (fun s => s = false)) ∧
    growthMigration.sourceId ∉ growthMigration.failedSources ∧
    evalCostUtility growthUpgradedProc false false >
      evalCostUtility persistentBaseProc false false := by
  have hBaseViable : ViableDomain persistentBaseProc (fun s => s = false) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      subst hx
      simp [persistentBaseProc, mkSingleSafeProc]
    · intro x hx _hStop
      subst hx
      refine ⟨false, by simp [persistentBaseProc, mkSingleSafeProc], ?_⟩
      intro x' hx'
      simp [persistentBaseProc, mkSingleSafeProc] at hx'
      subst hx'
      exact ⟨rfl, rfl, Nat.le_refl _⟩
  have hCert := certified_upgrade_preserves_constitutive_domain
    persistentBaseProc growthUpgradedProc (fun s => s = false)
    hBaseViable growthMigration
  refine ⟨hCert.1, growthMigration.source_independent, ?_⟩
  simp [evalCostUtility, growthUpgradedProc, persistentBaseProc, mkSingleSafeProc]


end UEOT.V3.Compression.TheoryCompletion.Proposed.CertifiedDevelopmentViability
