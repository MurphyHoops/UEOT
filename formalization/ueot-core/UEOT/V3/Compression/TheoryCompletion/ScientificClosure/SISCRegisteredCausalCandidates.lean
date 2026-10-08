import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.C2IntervalDecision
import UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISCFiniteStochasticQuotient
import UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.Identifiability
import Mathlib.Tactic

/-!
# SISC N3 — finite evidence-limited causal successor discovery without chosen tp

Reuse C2 abstaining interval decisions, inverse-Objecthood's distinction
between observational and ontic identity, and the N1 controlled finite
stochastic kernel. No successor transporter or claimed correct candidate
is an input to the decision procedure.

All decisions are relative to a finite independently registered candidate
universe and an externally audited causal admissibility relation. A unique
result requires one certified candidate and NO other causal candidate still
statistically possible. If a possible candidate remains unresolved, we
must abstain. An empty possible set means **model noncoverage**, not death.

The deterministic soundness theorems assume calibrated simultaneous
intervals. No independence / concentration / provenance oracle is hidden in
the solver: these are separate empirical obligations.
-/

namespace UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC

open UEOT.V3.Compression.TheoryCompletion.ScientificClosure

universe uX uA uC uO

/-- A registered finite decision problem. The parent is held fixed in
the causality predicate `causal`, and the world source is `source`.
There is deliberately *no* chosen successor transport `tp`. -/
structure RegisteredCausalCandidateProtocol
    (X : Type uX) (A : Type uA) (C : Type uC) (O : Type uO)
    [Fintype X] [Fintype O] where
  kernel : FiniteControlledStochasticKernel X A
  source : X
  action : A
  read : X → O → ℝ
  prediction : C → O → ℝ
  registered : Finset C
  causal : C → Prop
  tolerance : ℝ
  interval : C → IntervalCertificate
  observed_nonempty : Nonempty O

/-- The true registered test mismatch is computed from the *post-action*
microscopic transition law. It is not an independently assumed formation
oracle: the only inferential uncertainty enters through the registered
interval estimators. -/
noncomputable def registeredCandidateRisk
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A C O) (c : C) : ℝ :=
  ∑ j : O, |(∑ y : X,
    P.kernel.mass P.source P.action y * P.read y j) - P.prediction c j|

/-- Good-event calibration is a *separate empirical contract*.
The finite decision solver does not infer this assumption from its inputs. -/
def RegisteredCausalCandidateProtocol.Calibrated
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A C O) : Prop :=
  ∀ c ∈ P.registered,
    |(P.interval c).estimate - registeredCandidateRisk P c| ≤
      (P.interval c).totalRadius

/-- A genuinely acceptable *registered* causal candidate. Truth is still
relative to the supplied K/read/model and does not assert physical sameness. -/
def RegisteredCausalCandidateProtocol.TrulyCompatible
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A C O) (c : C) : Prop :=
  c ∈ P.registered ∧ P.causal c ∧
    registeredCandidateRisk P c ≤ P.tolerance

/-- A candidate remains possible unless C2 has soundly rejected it.
This intentionally includes C2's statistical ambiguous result. -/
noncomputable def registeredPossible
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O) : Finset C := by
  classical
  exact P.registered.filter (fun c =>
    P.causal c ∧ decideAt (P.interval c) P.tolerance ≠ .rejected)

/-- A certified candidate has independently registered causal provenance
and a C2 interval completely below the declared risk threshold. -/
noncomputable def registeredCertified
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O) : Finset C := by
  classical
  exact P.registered.filter (fun c =>
    P.causal c ∧ decideAt (P.interval c) P.tolerance = .certified)

/-- The three operational outcomes; `uncovered` concerns the registered
model only, and `ambiguous` includes statistically undecided singletons. -/
inductive CausalCandidateResolution (C : Type uC) where
  | unique (candidate : C)
  | ambiguous
  | uncovered
  deriving DecidableEq, Repr

/-- No selected tp, no tie-breaking disguised as object identity.
Only a *single possible* candidate with a genuine C2 certificate is unique.
If any other candidate is undecided, the algorithm returns `ambiguous`. -/
noncomputable def resolveRegisteredCandidates
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O) :
      CausalCandidateResolution C := by
  classical
  exact if h : ∃ c : C,
       registeredPossible P = {c} ∧
       decideAt (P.interval c) P.tolerance = .certified then
    .unique (Classical.choose h)
  else if (registeredPossible P).Nonempty then .ambiguous
  else .uncovered

/-- The declared output can only certify a genuine, model-admitted
candidate. It excludes *all other truly compatible registered causal
candidates*, but it does not exclude unregistered physical systems. -/
theorem unique_resolution_sound
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (hcal : P.Calibrated) (c : C)
    (hout : resolveRegisteredCandidates P = .unique c) :
    P.TrulyCompatible c ∧
    ∀ d, P.TrulyCompatible d → d = c := by
  classical
  unfold resolveRegisteredCandidates at hout
  split at hout
  · rename_i h
    obtain ⟨hsingle, hcert⟩ := Classical.choose_spec h
    have hc : c = Classical.choose h := by
      cases hout
      rfl
    subst c
    have hsingleton_subset : ({Classical.choose h} : Finset C) ⊆
        registeredPossible P := Finset.subset_of_eq hsingle.symm
    have hin : Classical.choose h ∈ registeredPossible P :=
      hsingleton_subset (Finset.mem_singleton_self _)
    have hregistered : Classical.choose h ∈ P.registered :=
      (Finset.mem_filter.mp hin).1
    have hcausal : P.causal (Classical.choose h) :=
      (Finset.mem_filter.mp hin).2.1
    have htrue : registeredCandidateRisk P (Classical.choose h) ≤ P.tolerance :=
      decideAt_certified_sound
        (P.interval (Classical.choose h)) P.tolerance
        (registeredCandidateRisk P (Classical.choose h))
        (hcal _ hregistered) hcert
    constructor
    · exact ⟨hregistered, hcausal, htrue⟩
    · intro d hd
      have hnreject : decideAt (P.interval d) P.tolerance ≠ .rejected := by
        intro hrejected
        have hfalse : P.tolerance < registeredCandidateRisk P d :=
          decideAt_rejected_sound (P.interval d) P.tolerance
            (registeredCandidateRisk P d) (hcal d hd.1) hrejected
        exact (not_lt_of_ge hd.2.2) hfalse
      have hdpossible : d ∈ registeredPossible P := by
        exact Finset.mem_filter.mpr ⟨hd.1, hd.2.1, hnreject⟩
      have hsubset : registeredPossible P ⊆
          ({Classical.choose h} : Finset C) := Finset.subset_of_eq hsingle
      exact Finset.mem_singleton.mp (hsubset hdpossible)
  · split at hout <;> cases hout

/-- A registered and truly compatible parent successor can never be
silently classified as `uncovered` on the simultaneous good event. -/
theorem uncovered_excludes_registered_truth
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (hcal : P.Calibrated)
    (hout : resolveRegisteredCandidates P = .uncovered) :
    ¬ ∃ c, P.TrulyCompatible c := by
  classical
  rintro ⟨c, hc⟩
  have hnreject : decideAt (P.interval c) P.tolerance ≠ .rejected := by
    intro hrejected
    have hfalse := decideAt_rejected_sound
      (P.interval c) P.tolerance (registeredCandidateRisk P c)
      (hcal c hc.1) hrejected
    exact (not_lt_of_ge hc.2.2) hfalse
  have hm : c ∈ registeredPossible P :=
    Finset.mem_filter.mpr ⟨hc.1, hc.2.1, hnreject⟩
  unfold resolveRegisteredCandidates at hout
  split at hout
  · cases hout
  · split at hout
    · cases hout
    · rename_i hpossible
      exact hpossible ⟨c, hm⟩

/-- Two different actually compatible candidates make `unique` impossible.
This prevents a statistically overconfident tie-breaker. -/
theorem two_compatible_force_nonunique
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (hcal : P.Calibrated)
    {c d : C} (hc : P.TrulyCompatible c)
    (hd : P.TrulyCompatible d) (hne : c ≠ d) :
    ∀ z, resolveRegisteredCandidates P ≠ .unique z := by
  intro z hz
  obtain ⟨_, huniq⟩ := unique_resolution_sound P hcal z hz
  exact hne ((huniq c hc).trans (huniq d hd).symm)

/-- The actual response-risk function is nonnegative, because it is a
finite sum of absolute response deviations. The tolerance is not an
arbitrary signed threshold once a candidate has been soundly certified. -/
theorem registered_candidate_risk_nonnegative
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O]
    (P : RegisteredCausalCandidateProtocol X A C O) (c : C) :
    0 ≤ registeredCandidateRisk P c := by
  unfold registeredCandidateRisk
  exact Finset.sum_nonneg (fun j _ => abs_nonneg _)

/-- If two distinct causal candidates remain statistically *possible*,
the resolver MUST abstain even if one (or both) candidates are certified.
This is stronger than selecting the first passing candidate. -/
theorem two_possible_candidates_force_ambiguity
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    {c d : C} (hc : c ∈ registeredPossible P)
    (hd : d ∈ registeredPossible P) (hne : c ≠ d) :
    resolveRegisteredCandidates P = .ambiguous := by
  classical
  have hno : ¬ ∃ z : C,
      registeredPossible P = {z} ∧
      decideAt (P.interval z) P.tolerance = .certified := by
    rintro ⟨z, hsingle, _⟩
    have hsubset : registeredPossible P ⊆ ({z} : Finset C) :=
      Finset.subset_of_eq hsingle
    have hcz : c = z := Finset.mem_singleton.mp (hsubset hc)
    have hdz : d = z := Finset.mem_singleton.mp (hsubset hd)
    exact hne (hcz.trans hdz.symm)
  have hnonempty : (registeredPossible P).Nonempty := ⟨c, hc⟩
  simp [resolveRegisteredCandidates, hno, hnonempty]

/-- Conversely, statistical undecided status on the *sole* possible
candidate is **not** a unique-object certificate. -/
theorem undecided_singleton_force_ambiguity
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (c : C) (hsingle : registeredPossible P = {c})
    (huncert : decideAt (P.interval c) P.tolerance ≠ .certified) :
    resolveRegisteredCandidates P = .ambiguous := by
  classical
  have hno : ¬ ∃ z : C,
      registeredPossible P = {z} ∧
      decideAt (P.interval z) P.tolerance = .certified := by
    rintro ⟨z, hset, hcert⟩
    have hc : c ∈ registeredPossible P := hsingle.symm.subset (Finset.mem_singleton_self _)
    have hz : c = z := Finset.mem_singleton.mp (hset.subset hc)
    exact huncert (hz ▸ hcert)
  have hc : c ∈ registeredPossible P := hsingle.symm.subset (Finset.mem_singleton_self _)
  have hn : (registeredPossible P).Nonempty := ⟨c, hc⟩
  simp [resolveRegisteredCandidates, hno, hn]

/-- Reuse the existing P4 inverse-Objecthood identification predicate:
a unique, calibrated operational successor identifies a *literal candidate*
class among truly compatible registered candidates. The evidence map here
is the candidate's response fingerprint; the theorem does **not** infer
ontic identity outside the validity class or candidate registry. -/
theorem unique_candidate_recovers_inverse_objecthood_valid_class
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    (hcal : P.Calibrated) (c : C)
    (hout : resolveRegisteredCandidates P = .unique c) :
    UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.ObjectClassIdentifiedByEvidenceAmongValid
      P.TrulyCompatible P.prediction
      (UEOT.V3.Compression.TheoryCompletion.InverseObjecthood.equalitySetoid C) := by
  obtain ⟨_, hunique⟩ := unique_resolution_sound P hcal c hout
  intro a b ha hb _
  exact (hunique a ha).trans (hunique b hb).symm

/-- Any wrong unique decision on another genuinely compatible *registered*
causal candidate refutes the simultaneous good-event calibration assumption.
This makes the statistical-failure pathway explicit for subsequent P-STAT
high-probability bounds without pretending the probability was proved here. -/
theorem wrong_unique_implies_calibration_failure
    {X : Type uX} {A : Type uA} {C : Type uC} {O : Type uO}
    [Fintype X] [Fintype O] [DecidableEq C]
    (P : RegisteredCausalCandidateProtocol X A C O)
    {c d : C} (hout : resolveRegisteredCandidates P = .unique c)
    (hd : P.TrulyCompatible d) (hne : d ≠ c) :
    ¬ P.Calibrated := by
  intro hcal
  obtain ⟨_, hunique⟩ := unique_resolution_sound P hcal c hout
  exact hne (hunique d hd)

end UEOT.V3.Compression.TheoryCompletion.ScientificClosure.SISC
