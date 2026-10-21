# Finite-memory typed reuse and scope review

**Status:** source-typed review CLEAR; actual native stored-type checks remain pending.

- Baseline: `299a4e3a71914af064ccd7916bb285bac201f62a`.
- Complete source identity: `179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6`.
- Scope: 684 source modules; 35 new public source declarations; six nonempty lexical hint groups and seven old-declaration pairs.
- Every old source was read from the immutable baseline Git object and independently matched to the current old-file bytes. Every candidate declaration and the complete source corpus was hash-bound to the final frozen manifest.

## Decisions

### 1. `FiniteMemoryCheckWitness.source_support_exact`

**Compared old declarations:** `SupportViabilityClosure.SafePrefixDeadend.supportTable_exact`.

Both declarations identify a finite relation with an actual deterministic PMF support. The old source is pure (if n = 0 then a else x), with a time-indexed supportTable; the new source is pure (!x), with the fixed flipRelation. The iff orientation is reversible, but the source functions are different. For n=0, x=false, a=false, z=false, the old relation holds and the new one does not.

**Reuse decision.** Retain the new same-source identity, proved by simplifying the existing PMF.support_pure theorem and the actual flip source/relation definitions. The old example is not a theorem parameterized by an arbitrary deterministic transition and cannot be instantiated with the new source.

**Scope.** A small concrete representation adapter. It is not an independent general support theorem or a claim of novel probability theory.

### 2. `FiniteMemorySeparation.trace_support_eq_memory_singleton`

**Compared old declarations:** `SupportViabilityClosure.SafePrefixDeadend.deadend_trace_support_eq`.

The old theorem concerns one named history at time 1, under uniform initial Bool and the action-then-stay source, concluding traceSupport = {true}. The new theorem quantifies over every n and complete observed record, under pure-false initial law and the flip source, and identifies the trace with the replayed Boolean controller memory.

**Reuse decision.** Reuse traceSupport, initialSupport, successorSupport and PMF.support_pure; establish the all-time statement by induction over the existing causal record recursion. A fixed one-record theorem cannot supply this induction or change its source and initial law.

**Scope.** The witness is an explicit same-source separation from stationary current-observation randomized feedback. Its all-record source-trace identity is not an identity of arbitrary policies or path measures.

### 3. `SupportViabilityClosure.initialSupport_mem_arena`

**Compared old declarations:** `SupportViabilityClosure.SafePrefixDeadend.initial_support_eq_univ`.

The new statement has arbitrary types X/Y, initial PMF and observation, and assumes a nonempty initial observation fiber; it concludes that this fiber belongs to the newly defined nonempty observation-homogeneous arena. The old statement is the equality to Set.univ for uniform Bool and constant Unit observation.

**Reuse decision.** Use the existing initialSupport definition directly: the supplied nonemptiness and the observation equality already stored in membership give the two arena fields. The old uniform example can be combined with this lemma when desired, but cannot prove the general fiber result.

**Scope.** An elementary interface lemma packaging existing membership data; no general mathematical novelty claim is made.

### 4. `SupportViabilityClosure.finiteRelationSuccessor_coe_eq_relationSuccessor`

**Compared old declarations:** `SupportViabilityClosure.finiteRelationSuccessor_eq`, `SupportViabilityClosure.finiteSuccessor_coe_eq`.

The new statement identifies the Set coercion of the existing finiteRelationSuccessor for a fixed decidable R with relationSuccessor, with no PMF parameter. The first old theorem identifies finite relation and PMF successor computations assuming an actual P, a support decider and exact relation/support matching. The second old theorem coerces that actual PMF successor to successorSupport. Composing them is valid only after supplying those extra source hypotheses.

**Reuse decision.** Keep the existing finiteRelationSuccessor program and prove its relation-only coercion equality by extensionality and unfolding. Do not manufacture a PMF realization for arbitrary R: for a nonempty state type an empty successor relation need not be the support of a PMF. At the actual-law boundary SupportMemoryCheck explicitly reuses finiteRelationViabilityCheck_correct with hR, followed by viable_iff_homogeneous_relation and the fixed-point equivalence.

**Scope.** This is an adapter/generalization of the existing finite representation mechanism, not a new finite-horizon recursion, an alternative checker implementation, executable action synthesis, or a complexity theorem.

### 5. `SupportViabilityClosure.supportPre_mono`

**Compared old declarations:** `UEOT.V3.Compression.TopologyChangingGoaSemantics.supportFace_mono`.

The new operator acts on families Set (Set X), retains arena supports, and requires a common certified action and membership of every nonempty observed successor in the supplied family. The old operator maps a carrier Set S to the face of the real probability simplex supported on it; its inclusion result has no action, observation successor or candidate-family quantifier.

**Reuse decision.** Carry the same arena/action/certification witnesses across V subset W and apply that inclusion to each successor. The simplex-face theorem cannot provide the target quantified action witnesses or the required operator type.

**Scope.** The basic monotonicity mechanism is shared mathematical background. The theorem is only a typed local step for the support fixed point, and does not assert that supportPre W is a subset of W for arbitrary W.

### 6. `SupportViabilityClosure.supportMemoryController_memory_eq_traceSupport`

**Compared old declarations:** `SupportViabilityClosure.SafePrefixDeadend.deadend_trace_support_eq`.

The new theorem concerns arbitrary finite X, observations/actions, original p0, complete possibly time-varying P, fixed R/C, and fixed fallback. Its hR identifies the supports of P with R at every time/state/action/successor. It quantifies over every time and complete record and identifies the support-valued controller memory with the actual source trace. The old theorem has no memory controller or homogeneity premise and states a single concrete trace identity.

**Reuse decision.** Reuse the generic memory replay recursion and existing traceSupport recursion. At each induction step apply successorSupport_eq_relation_of_homogeneous, which is derived from hR. Do not identify the resulting controller with old finite-horizon or infiniteViablePolicy selectors.

**Scope.** Global hR justifies equality on all records, including null records. This theorem alone does not establish physical safety, numerical kernel homogeneity, equality of reference-policy behavior, or a reduced reference check budget.

## Evidence and remaining gates

All six lexical hint groups are discharged by exact source/type/scope comparisons and explicit reuse choices. No blocker or redundant drop-in declaration was found among these seven old hint pairs. Existing checker and actual-law correctness APIs are reused at their proper boundaries.

- This is an independent review of declared source types and proof bodies, not an executed Lean stored-type comparison.
- The raw native complete-registry and pairwise isDefEq checks remain required. They test exact stored-type definitional equality under the exporter protocol, not arbitrary logical equivalence.
- Lexical hints are only candidate selection. Clearing these six groups does not prove mathematical novelty or that no useful related result exists elsewhere.
- No full-build, native axiom/census/dependency, fixed-edge replay, registration or canonical publication acceptance is asserted in this receipt.
- The frozen P-ID categories, four counted generators, and NOT_ESTABLISHED strong global-closure status are unchanged.

The accompanying JSON preserves the exact declaration statements, line positions, source hashes, immutable baseline, frozen-manifest hash, and source-preflight hash. Prior review receipts remain unchanged.
