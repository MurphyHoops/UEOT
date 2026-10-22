# Path-realization source-semantic reuse review

**Status: SOURCE_SEMANTIC_REUSE_CLEAR_NATIVE_PENDING.**

Exact immutable baseline: `d503586107974c56e0773b4ea106b41a7d144b43`. The source-only preparation executed the
unchanged baseline declaration parser and the exact Git-object baseline
consumer. Its historical 684-module / 4,272-public / 10-overlay input was
reconstructed and matched to the actual baseline source set and hashes.
That reconstruction is not a freshness certificate for the new live tree.

The current snapshot has 691 source modules and **77 public source candidates**.
The unchanged lexical heuristic returned **26 nonempty groups, 63 old-candidate
pairs, and 40 different old declarations**. Every pair is assessed below.
These are observed source-discovery quantities; no native ownership, axiom,
stored-type equality, compiled direct-edge count, or fixed certificate is
asserted by this document.

Complete source fingerprint at hint preparation:
`c344bf6657ab31a32c46fba9feff6d5c04846b8f061d444aec8accb4994ad41b`.
All seven source hashes and exact declarations, together with immutable old
declaration bodies, are bound in the accompanying JSON. The only old Lean
source change at that preparation checkpoint was the public root import list.

The earlier `source-hints-01` snapshot remains preserved. The final
`source-hints-02` rebinds the Window helper after its sole private type
annotation changed from unavailable `ℝ≥0∞` notation to explicit `ENNReal`.
Reversing that one occurrence reproduces the exact prior full-file hash.
The full lexical hint artifact is byte-identical between the two runs;
all public declarations and conclusions are unchanged. A source-hash guard
rejected issuance of this review against the superseded source snapshot.

The reviewer authored C3 and independently read the other six modules. C3
also retains its separate independent source review in
`C3_AND_DOOB_WITNESS_REVIEW.md`; this document does not relabel self-review
of C3 as an independent authorship review. It independently assesses what
the lexical hints actually mean, rather than treating similarity as proof.

## Pair-by-pair decisions

Names below omit the common leading `UEOT.V3` and long compression path where
unambiguous. The JSON retains every full name and the exact source evidence.

### 1. `C3ExecutableSearch.search_eq_firstGoodIndex`

The executable short-circuit scan, with an explicit Bool oracle matching Good on the registered table, returns the existing family minimum. This is an executable-to-specification bridge, not a second abstract minimum construction.

| Existing candidate | Semantic comparison |
|---|---|
| `NestedCandidateFamily.firstGoodIndex_good` | The old theorem says the abstract minimum is Good, assuming nonempty goodIndices. It does not identify the result of a Bool-oracle program or account for queries. The new proof deliberately consumes the stronger old chain-minimality theorem. |

**Reuse decision.** The proof calls the already registered firstGoodIndex_chainMinimal through search_found_iff. The earlier firstGoodIndex_good is used within that established family API; no choose/min operation is put into the executable oracle or search.

**Scope.** Oracle matching is an external premise. The result is minimal within the registered finite family and does not enumerate all carriers, prove physical deletion safety, or require Good monotonicity.

### 2. `FiniteMemoryPhysicalSafety.stateHistoryEquiv_map`

Naturality of the existing recursive-history to finite-coordinate equivalence under an arbitrary state map f; the conclusion is equality of the complete mapped histories.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceInfinitePrefixCheck.stateHistoryEquiv_last` | The old result evaluates only the last coordinate of one history; the target commutes an arbitrary f with every coordinate. |
| `SameSourceInfinitePrefixCheck.stateHistoryEquiv_succ` | The old recursion equation is the structural mechanism used in the successor step. It does not itself quantify over a state map or prove the full naturality equation. |
| `SameSourceInfinitePrefixCheck.stateHistoryEquiv_zero` | The old base-case equivalence agrees with the new proof at n=0. It alone supplies neither the arbitrary-time induction nor mapping naturality. |
| `SameSourceSafePrefixCheck.stateHistoryEquiv_survival_iff` | The old statement transports a particular survival predicate to coordinate histories. It has a safe set and membership equivalence, not an arbitrary map f or equality of histories. |

**Reuse decision.** Keep stateHistoryEquiv, riskHistoryMap, appendHistory and the new elementary mapHistory representation. Induction uses mapHistory_appendHistory and the existing equivalence recursion; it does not introduce a second history equivalence.

**Scope.** The statement itself asserts no path-law equality, measurability of an arbitrary f, physical safety, or Markov property.

### 3. `FiniteMemoryPhysicalSafety.actual_state_prefix_eq`

Equality of the complete actual state-prefix distribution and the prefix of the projected augmented trajectory for one finite-memory controller, original p0, observation q and arbitrary numeric sequence P n.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceInfinitePrefixCheck.actual_state_prefix_eq_homogeneous_prefix` | The old source fixes a Model and current-observation sigma, and its target is homTrajMeasure of the resulting homogeneous state row. The new controller may need memory and P may vary with time, so those source hypotheses cannot be silently supplied. |
| `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass` | The old theorem evaluates one finite-prefix event for the same stationary source. The target is equality of measures for a different, constructed finite-memory trajectory; the old event theorem does not construct that law. |
| `SameSourceInfinitePrefixCheck.state_history_eq_homogeneous_prefix` | This old generic history theorem has a fixed J : X -> PMF X. The new augmented J is indexed by n, and an arbitrary unbounded time sequence is not a finite homogeneous state row. |
| `SourcePolicyPathBridgeCheck.actual_state_path_eq_stationary_path` | The old theorem erases actions from a stationary observation-feedback experiment into its state-only causal law. The new source erases memory only after constructing the actual augmented law; memory is not generally recoverable from the current state. |

**Reuse decision.** Project the newly proved actual_augmented_prefix_eq through Prod.fst, using PMF/Measure map composition, stateHistoryEquiv_map and eraseMemory_augmentHistory. Existing history representations and action erasure are retained.

**Scope.** The projected state process need not be Markov. A fixed numerical kernel and current-observation stationary feedback are not assumed; no reference-process policy identity follows.

### 4. `FiniteMemoryPhysicalSafety.actual_state_prefix_event_mass`

Event-level consumer of the new finite-memory state-prefix measure identity, with the original microscopic event and finite measurable action/state histories.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass` | The old result has Model, sigma and a homogeneous state trajectory; the new one has a finite-memory controller, arbitrary P n and stateTrajMeasure projected from the augmented law. The statement types and actual source constructions differ despite the identical short name. |

**Reuse decision.** Apply the measure identity to B and use the existing PMF.toMeasure_map_apply and Measure.map_apply. The common evaluation pattern is an adapter; the new source law is supplied by actual_state_prefix_eq.

**Scope.** An identical short theorem name does not identify source processes. This event adapter adds no separate stationary or reference-process assumption.

### 5. `FiniteMemoryPhysicalSafety.stateTrajMeasure_coordinate_mass`

Identifies time-n event mass of the projected finite-memory trajectory with the original microscopic terminal-state event at the same n.

| Existing candidate | Semantic comparison |
|---|---|
| `ViabilityTrajectory.stationaryTrajMeasure_coordinate` | The old theorem identifies the pushforward of a homogeneous deterministic state-feedback trajectory with stationaryStateLaw. The new theorem handles randomized memory feedback and time-varying P, and its right side remains the actual action-history law. |

**Reuse decision.** Specialize the full state-prefix event identity to the last coordinate; reuse stateHistoryEquiv_last and the action-erasure last-state identity. No new coordinate-law construction is assumed.

**Scope.** Finite X, memory and A plus measurable singletons are retained. This is a marginal identity derived from a stronger complete-prefix identity, not a proof that the state projection is Markov.

### 6. `FiniteMemoryRealization.augmentHistory_last`

The last state of the constructed augmented history is the pair of the actual microscopic last state and the controller memory replayed from the original observed record.

| Existing candidate | Semantic comparison |
|---|---|
| `MeasureProtocol.Markov.measurable_historyLast` | The vendored-adapted theorem proves measurability of evaluation on coordinate histories. It states no equality for the newly constructed state-memory pair and cannot supply the target. |
| `StatisticalRiskWitness.class_history_last` | The old concrete witness maps a Class history to a Bool class bit. The new arbitrary-controller equation includes replayed memory and a different history map; both are small definitional last-coordinate adapters. |

**Reuse decision.** This is a two-case definitional identity for augmentHistory. It reuses the established controller.memory and projectHistory definitions; it is not a new probability theorem.

**Scope.** No finite or measurable-space assumptions, probability identity, or independent memory-state input are needed for this structural equality.

### 7. `FiniteMemoryRealization.state_history_eq_sequence_prefix`

For a numeric sequence J n : S -> PMF S, identify the original recursive finite history PMF with the prefix of the actual nonautonomous sequence trajectory.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceInfinitePrefixCheck.state_history_eq_homogeneous_prefix` | The old theorem quantifies over a single J and targets homTrajMeasure. The new theorem quantifies over J : Nat -> S -> PMF S and targets sequenceTrajMeasure. Its successor proof must use J n and sequenceHistoryKernel J n. |

**Reuse decision.** Retain the old stateHistoryEquiv and PMF extension mechanism, and use the sequence prefix-zero/prefix-successor identities supplied by the same Ionescu-Tulcea construction. The induction genuinely supplies the time-indexed row boundary.

**Scope.** The old homogeneous result is a special-case pattern. Instantiating a fixed J with a time-varying row is invalid; finite support homogeneity does not make numerical rows equal.

### 8. `FiniteMemoryRealization.actual_augmented_prefix_eq`

Complete state-memory prefix identity for the actual original controller experiment, not only equality of one-time marginal laws.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceInfinitePrefixCheck.actual_state_prefix_eq_homogeneous_prefix` | The old theorem retains only state and assumes homogeneous current-observation feedback. The new target alphabet is X x M and its source includes an arbitrary P n. The finite augmented-law identity is extra work absent from the old result. |

**Reuse decision.** Compose actual_augmented_history_law, which proves the finite same-source PMF identity, with state_history_eq_sequence_prefix. Initial memory and updates come from the same controller and observed records.

**Scope.** The target retains memory but may erase actions that cannot be reconstructed. The theorem alone does not identify arbitrary action-dependent events or a different controller.

### 9. `FiniteMemoryRealization.actual_augmented_prefix_event_mass`

Evaluate a measurable finite state-memory prefix event in the same original experiment and augmented infinite trajectory.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass` | The old B is state-valued and its source is homogeneous stationary observation feedback. The new B is state-memory-valued and belongs to the nonautonomous augmented law, so the old source-specific result cannot be used directly. |

**Reuse decision.** Evaluate actual_augmented_prefix_eq on B and apply existing map-measure identities. The repeated argument is an elementary source-specific event adapter, not a separate general extension theorem.

**Scope.** B is a set of coordinate histories valued in X x M. It does not become a statement about arbitrary erased-action events.

### 10. `FiniteMemorySafetyWitness.safe_source_all_times_mass_one`

A nonempty concrete Bool/Unit source verifies the new physical-safety bridge using the original safe initial atom, actual source closure and the same controller zero occupancy.

| Existing candidate | Semantic comparison |
|---|---|
| `ViabilityPath.all_times_safe_eq_one` | This is the canonical general countable probability-one intersection theorem, and the new generic physical-safety theorem explicitly uses it. The witness additionally discharges actual controller/source premises. |
| `ViabilityTrajectory.all_times_safe_of_coordinate_one` | The old wrapper fixes a stationary deterministic policy trajectory and assumes coordinate safety. The new witness travels through the more general finite-memory realization and physical support proof; the shared intersection mechanism is already reused below both wrappers. |

**Reuse decision.** Directly instantiate controller_all_times_physical_safe. Its generic proof reuses ViabilityPath.all_times_safe_eq_one after establishing every actual coordinate mass; the witness does not reprove countable-intersection continuity.

**Scope.** This witness validates source premises. It is not an independent general probability-one theorem or the separate example proving memory improves control power.

### 11. `FiniteWindowDoobCheck.doobRowPMF_apply_toReal`

A small PMF representation adapter for the already established positive-eigenvector h-transform row.

| Existing candidate | Semantic comparison |
|---|---|
| `FiniteDobrushin.rowPMF_toReal` | This old wrapper represents a row of an arbitrary row-stochastic matrix. The new row is the existing hTransform D i and directly reuses their shared lower-level ofRealRow theorem, avoiding a second stochastic-matrix wrapper. |
| `UnifiedClosure.finiteKernelRowPMF_apply_toReal` | The old wrapper takes a FiniteControlledStochasticKernel and an action. The new row has positive eigen data and no control-kernel record; both use the same canonical real-row conversion. |
| `FiniteDiscountedControl.Model.transitionPMF_apply_toReal` | The old wrapper takes a full discounted-control Model and action. Constructing rewards, discount and a model merely to convert a Doob row is unnecessary; the shared primitive is used directly. |
| `CoreOperationalAssembly.policyTransitionPMF_apply_toReal` | The old target is the stationary-policy transition mixture of a Model. The new h-transform row need not be presented by that control data; its conversion uses the same primitive. |
| `FiniteDiscountedControl.pushforwardTransitionPMF_apply_toReal` | This old theorem computes a quotient-fiber sum after mapping a controlled transition. The new result is a direct atom identity with no quotient map or fiber sum. |

**Reuse decision.** The PMF constructor uses existing hTransform_nonneg and hTransform_row_sum; the theorem directly invokes the canonical FiniteProbabilityRow.ofRealRow_apply_toReal.

**Scope.** The adapter does not re-establish eigenvector existence or claim new normalization theory. Strictly positive right-eigenvector/scale data and Q nonnegativity remain inputs.

### 12. `FiniteWindowDoobCheck.tiltedInitialPMF_apply_toReal`

Convert the actual normalized initial h-tilt eta(i) h(i) / <eta,h> to a PMF atom identity, allowing eta to retain original unnormalized safe mass.

| Existing candidate | Semantic comparison |
|---|---|
| `FiniteDiscountedControl.Model.transitionPMF_apply_toReal` | The old row belongs to a Model transition indexed by state/action; the new vector is an initial distribution. Both should use the shared canonical real-row conversion. |
| `CoreOperationalAssembly.policyTransitionPMF_apply_toReal` | The old statement converts a policy-averaged transition row, not an initial h-tilt. The new implementation reuses the common conversion without manufacturing a policy. |
| `FiniteDiscountedControl.pushforwardTransitionPMF_apply_toReal` | A pushed transition mass is a sum over a quotient fiber. The new numerator is pointwise eta times h and the denominator is its positive pairing; no pushforward operation is claimed. |
| `FiniteDobrushin.rowPMF_toReal` | The old wrapper expects a stochastic matrix and a chosen row. The initial vector is already supplied directly to the lower-level canonical PMF constructor. |
| `FiniteDobrushin.simplexPMF_toReal` | The old wrapper takes a certified simplex vector. The new normalized vector could be packaged that way, but directly uses the same underlying ofRealRow proof rather than adding an intermediate simplex record. |

**Reuse decision.** The implementation directly invokes FiniteProbabilityRow.ofRealRow_apply_toReal. Positivity and normalization are supplied for this specific tilted vector, not assumed for eta itself.

**Scope.** A positive pairing is mandatory. This initial h-tilt is not generally the initial distribution conditional on finite-window survival.

### 13. `FiniteWindowDoobCheck.safeInitialRow_nonneg`

Expose nonnegativity of the existing unnormalized safeInitialRow at its original type for PMF construction.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceQSDBindingCheck.safeInitialRow_map_subtype` | The old equality applies when p0 is explicitly r.map Subtype.val for a PMF on K, hence safe-supported and normalized. The new statement covers arbitrary original p0, including unsafe mass, and only asserts nonnegativity. |

**Reuse decision.** The proof is the canonical ENNReal.toReal_nonneg fact. The named adapter preserves the row expression when passed as a dependent proof argument.

**Scope.** No safe-support assumption or normalization of the restricted initial mass is introduced; this is not a new mathematical positivity result.

### 14. `FiniteWindowDoobCheck.actual_survival_mass_eq_initial_remaining_sum`

Express the already proved actual total survival mass as the original safe initial row paired with Q^T 1.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceKilledPathCheck.actual_survival_mass_eq_killed_pow_sum` | The old right side sums terminal indices after applying eta Q^T. The new side first sums Q^T along each initial row and then weights by eta. Finite-sum commutation is the precise additional step. |

**Reuse decision.** Directly rewrite using actual_survival_mass_eq_killed_pow_sum, unfold rowApply and remainingSurvival, and interchange finite sums. The probability/source identity is inherited from the old theorem.

**Scope.** This is an algebraic endpoint adapter; it neither renormalizes initial safe mass nor establishes positive infinite survival.

### 15. `FiniteWindowDoobWitnessCheck.safeLaw_mass`

Each atom of the actual uniform safe-law PMF, transported from Bool through safeEquiv into the safe subtype of Option Bool, has real mass 1/2.

| Existing candidate | Semantic comparison |
|---|---|
| `AbsorbingLeakage.safe_mass_closed` | The old quantity is the time-n mass of the sole safe Bool state of a leakage process, equal to (1-epsilon)^n. The new quantity is a time-independent atom of a PMF on two safe states. |
| `AbsorbingLeakage.safe_mass_succ` | The old result is a transition recurrence for safe-state mass. The new result evaluates the fixed initial safe-law construction and has no time recursion. |
| `StatisticalRiskBoundary.trainingLaw_mass` | The old theorem computes the atom of a two-action product training experiment. The new law is a uniform safe-state PMF; neither the sample coordinates nor the product source are shared. |
| `FiniteBayesBelief.observationLaw_mass` | The old identity concerns a finite belief observation distribution and Bayesian evidence for a model/action. The new quantity has no belief update or observation-likelihood model. |

**Reuse decision.** Reuse pmf_map_injective_atom for the actual equivalence and PMF.uniformOfFintype_apply. No path-law, survival recurrence or data-generating experiment is inferred from the shared word mass.

**Scope.** This is a concrete finite PMF calculation, not a general support or survival theorem.

### 16. `FiniteWindowDoobWitnessCheck.initial_safe_mass`

Evaluate the existing unnormalized safeInitialRow of the actual three-state witness initial PMF at each safe state.

| Existing candidate | Semantic comparison |
|---|---|
| `AbsorbingLeakage.safe_mass_closed` | The old source has a single safe Bool atom and a time-indexed leakage law. It cannot identify either of the two initial safe subtype atoms in the new three-state source. |
| `AbsorbingLeakage.safe_mass_succ` | The old step recurrence concerns future leakage. The new equality instead follows from subtype pushforward of the chosen initial PMF, using an already existing source identity. |

**Reuse decision.** Directly apply the canonical safeInitialRow_map_subtype, then safeLaw_mass. This retains the exact original initial PMF rather than independently postulating a row vector.

**Scope.** The two safe atoms each have mass 1/2; this is initial-state bookkeeping, not time-n total safe mass.

### 17. `FiniteWindowDoobWitnessCheck.actual_survival`

Specialize the established same-source QSD survival formula to the actual three-state model, its uniform safe law and the verified left eigenvalue 1/2.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceQSDBindingCheck.actual_qsd_survival_pos` | The old positivity corollary follows from the mass formula plus rho>0. The new theorem records the exact value for rho=1/2; positivity is then available without a new theorem of that kind. |
| `SameSourceConditionedTerminalCheck.actual_survival_mass_empty` | The old result is zero survival for an empty safe set. The new safe subtype has two states and verified positive finite survival, so the degenerate specialization is inapplicable. |
| `SameSourceQSDBindingCheck.actual_qsd_survival_mass` | This exact generic old theorem is applied directly to the new same-source left-QSD witness; no parallel survival proof is introduced. |
| `SameSourceQSDBindingCheck.actual_qsd_survival_support` | The old theorem derives existence of a supported surviving history from positive QSD survival. The new target is the exact scalar mass, which is used before that support-existence step. |

**Reuse decision.** The entire proof directly invokes actual_qsd_survival_mass with source_left_qsd. This is a concrete consumer of accepted QSD theory, used to calculate the witness normalization.

**Scope.** The formula is finite-horizon survival (1/2)^T. It does not imply positive infinite survival, and a left QSD does not identify the conditioned complete path with a fixed Doob process.

### 18. `SameSourceFiniteWindowCheck.remainingSurvival_zero`

For an arbitrary finite real matrix, the row sum of Q^0 is one at every state.

| Existing candidate | Semantic comparison |
|---|---|
| `QSDTVLimit.qSurvival_zero` | The old result concerns a KilledSemigroup and a ProbabilityMeasure, and uses the semigroup time-zero identity. The new matrix statement has weaker data and a pointwise initial-state output; an arbitrary real matrix is not supplied with a killed-semigroup realization. |

**Reuse decision.** Use the existing matrix power-zero and identity-matrix sum simplifications. This is elementary matrix algebra, with no new semigroup theory.

**Scope.** The statement does not require Q nonnegative or substochastic. Probability meaning is only supplied later by the same-source killed matrix.

### 19. `SameSourceFiniteWindowCheck.state_prefix_survival_mass`

Factor the joint mass of a fixed safe complete prefix through t and survival through t+r into that prefix atom and its actual remaining-survival row sum.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass` | The old theorem transports any state-prefix event to an infinite homogeneous path measure; it does not evaluate the joint prefix/future-survival event or derive the Q^r 1 factor. It supplies representation, not this factorization. |

**Reuse decision.** Use the original causal PMF recursion, existing killedMatrix, finite_event_mass adapter and weightedPrefixMass_eq. The finite suffix summation is the new source calculation needed for the conditional-prefix formula.

**Scope.** The event fixes the entire prefix and constrains a later horizon. It is not merely a coordinate event or transfer to an infinite-path representation.

### 20. `SameSourceFiniteWindowCheck.finiteWindowRowPMF_apply_toReal`

A PMF atom adapter for Q(i,j) g_r(j) / g_(r+1)(i), under nonnegative Q and a strictly positive current remaining-survival denominator.

| Existing candidate | Semantic comparison |
|---|---|
| `UnifiedClosure.finiteKernelRowPMF_apply_toReal` | The old controlled-kernel wrapper converts a normalized input row. The new row is normalized from the survival recurrence and then uses the same generic conversion. |
| `FiniteDobrushin.rowPMF_toReal` | The old wrapper takes a whole row-stochastic matrix. At a fixed r the new construction requires positivity only at the chosen i, so it need not provide probability rows at all other states. |
| `UnifiedClosure.finiteKernelRowPMF_map_toReal` | The old result computes a quotient-class pushforward sum. The new target is an atom at j of a conditioned row with no quotient map or equivalence class. |
| `FiniteDiscountedControl.Model.transitionPMF_apply_toReal` | The old wrapper belongs to a full controlled Model. The new finite-window row already has its own normalization and needs no reward/discount/control structure. |
| `CoreOperationalAssembly.policyTransitionPMF_apply_toReal` | The old target is a stationary-policy mixture row. The finite-window row includes a remaining-horizon tilt and only local denominator positivity; conversion still reuses the same primitive. |

**Reuse decision.** The row normalization proof uses the proved remaining-survival recurrence; the PMF conversion directly uses canonical FiniteProbabilityRow.ofRealRow_apply_toReal.

**Scope.** No PMF is assigned on a null conditioning row. r is the remaining-step parameter in this definition, not evidence of a homogeneous conditional process.

### 21. `SameSourceFiniteWindowCheck.actual_prefix_survival_mass`

Bind the finite prefix/future-survival factorization to the original action/state experiment under the same Model, q, sigma, p0 and safe set.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceConditionedTerminalCheck.actual_survival_mass_empty` | This old empty-safe-set boundary is a scalar zero statement. It cannot evaluate the nonempty fixed-prefix event and remaining-horizon weight. |
| `SameSourceQSDBindingCheck.actual_qsd_survival_mass` | The old formula assumes a normalized safe-supported left QSD initial law and returns total rho^n. The new result accepts arbitrary p0 and identifies each complete prefix. |
| `SameSourceConditionedTerminalCheck.actual_survival_mass_at_zero` | The old theorem handles the single time-zero total safe event. The new result allows t and r arbitrary and keeps the prefix atom and its future survival factor. |
| `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass` | The old identity transfers prefix-event measure to the homogeneous infinite source without computing it. The new theorem evaluates a joint event constrained through the later horizon t+r. |
| `SameSourceQSDBindingCheck.actual_qsd_survival_terminal_mass` | The old result fixes only the terminal state and uses a left eigenrelation. A terminal marginal does not determine the joint probability of an arbitrary earlier complete prefix, and no QSD premise is assumed here. |

**Reuse decision.** Use the exact action-erasure pushforward theorem actual_state_path_eq_stationary_path and the prefix survival factorization. The event-preimage equality is derived from definitions, not assumed as a source-matching field.

**Scope.** The theorem retains an arbitrary original initial PMF and a complete prefix, with no left-eigenvector or QSD premise.

### 22. `SameSourceFiniteWindowCheck.actual_conditioned_prefix_support`

A supported prefix of the actual experiment conditioned on survival to t+r must itself survive through t.

| Existing candidate | Semantic comparison |
|---|---|
| `PosteriorSupportStrictWitness.actualPrefix_support_iff` | The old concrete control-coverage example has exactly two named supported microscopic histories. It is neither a generic filtering theorem nor a result about conditioning on future survival. |
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_support` | The old generic theorem says the retained terminal state lies in K. The new target retains every coordinate of an earlier prefix and must show all of them safe; a terminal marginal cannot supply that full-path property. |

**Reuse decision.** Unpack PMF.mem_support_map_iff and PMF.mem_support_filter_iff, reuse actual_survival_pos_iff_support, and propagate safety through the actual action erasure and prefix truncation.

**Scope.** Positive total survival remains required to define the conditional PMF. Full prefix safety is stronger than membership of its terminal state in K.

### 23. `SameSourceFiniteWindowCheck.actual_conditioned_prefix_eq_zero_of_not_survives`

The actual conditioned-prefix PMF gives zero mass to any history that is unsafe anywhere in its retained prefix.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_eq_zero_of_notMem` | The old zero atom is indexed by one state x outside K. The new atom is a whole history and its exclusion premise is failure of all-time prefix safety, including unsafe intermediate states. |

**Reuse decision.** Use the just-proved prefix-support inclusion and the canonical PMF.apply_eq_zero_iff equivalence. This is a support-to-zero-mass adapter.

**Scope.** A history can end inside K while having failed earlier; a theorem excluding only terminal states outside K would not suffice.

### 24. `SameSourceFiniteWindowCheck.actual_conditioned_prefix_mass`

For each safe complete prefix ending at i, derive its conditional mass as original prefix weight times g_r(i), divided by the original total survival s_(t+r).

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_mass` | The old quantity is the terminal state marginal eta Q^n(v)/s_n, obtained after summing all safe prefixes. The new law retains the complete prefix and a remaining-horizon factor, which terminal marginal data do not determine. |
| `SameSourceInfinitePrefixCheck.actual_state_prefix_event_mass` | The old measure-transport theorem is unconditional and does not normalize a survival-conditioned law or calculate a suffix survival weight. |
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_mass_at_zero` | The old time-zero conditioning only restricts X0 to K and divides by p0(K). The new t=0 specialization can condition on a later horizon and hence multiplies by g_T(i). |

**Reuse decision.** Filter and map the actual original PMF; use public PMF outer-measure map/singleton identities and the actual_prefix_survival_mass theorem. The older private filter/map helper is not callable, and the revised source uses the public outer-measure chain rather than copying that proof.

**Scope.** The denominator is the actual original survival mass and must be positive. No QSD or right-eigenvector data are needed for this finite-window conditional law.

### 25. `SameSourceFiniteWindowCheck.actual_conditioned_initial_mass`

Identify the original initial state distribution conditional on survival to T: eta(i) g_T(i) / s_T.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_mass` | The old target is X_T given survival to T. The new target is X_0 under that same later survival event, so the matrix weight appears as eta(i) times a row sum rather than a terminal column mass. |
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_mass_at_zero` | The old theorem conditions on survival only at horizon zero. It is the T=0 boundary of the new formula, but it cannot supply g_T for a later conditioning horizon. |
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_support` | The old support inclusion gives membership in K only. It says neither the initial conditional weights nor the horizon-dependent reweighting. |
| `SameSourceQSDBindingCheck.actual_qsd_conditioned_terminal_law` | The old equality to r concerns the terminal marginal under a left-QSD start. It does not identify the retrospective initial conditional law, which may be tilted even for that QSD source. |

**Reuse decision.** Specialize actual_conditioned_prefix_mass to retained prefix length zero and use the original safeInitialRow definition. This is a required source-specific endpoint, not an independent Bayes rule.

**Scope.** At T=0 it reduces to initial safety conditioning; for T>0 it carries a future-survival tilt. A left QSD stabilizes the conditioned terminal marginal and generally does not remove this tilt at time zero.

### 26. `SameSourceFiniteWindowCheck.actual_conditioned_safe_path_mass`

Identify each actual complete safe path atom after conditioning on survival to T with matrixPathWeight eta Q T divided by s_T.

| Existing candidate | Semantic comparison |
|---|---|
| `SameSourceConditionedTerminalCheck.actual_conditioned_terminal_mass` | The old result sums over all safe paths ending at one v. It loses intermediate states and cannot by itself determine the atom of a specified complete safe history; the new path-product proof supplies precisely that missing information. |

**Reuse decision.** Specialize the prefix formula to no remaining suffix, use remainingSurvival_zero, the existing original state-path recursion and the proved safe-path atom identity. The original p0 and its unnormalized safe restriction are retained.

**Scope.** A full path weight determines later marginals by summation; the converse recovery from one terminal marginal is invalid. This endpoint is what supports the subsequent exact Doob path comparison.

## Assessment and remaining evidence

No unresolved reuse blocker was found among the 63 candidate pairs. Several
endpoints deliberately specialize or algebraically adapt established
canonical theorems, and the review identifies those direct uses rather
than describing each new declaration as independent mathematical novelty.
The PMF conversion endpoints all use the existing general finite real-row
conversion. QSD survival is consumed directly in the concrete witness.
The additional substantive work concerns actual memory/source path identity,
complete prefix and finite-window conditioning, exact Doob path comparison,
and the registered-family executable-search bridge.

The 51 source candidates without a lexical hit are outside this name-hint
pair list; absence of a hit is not evidence of novelty or lack of useful
related theorems. Their mathematical source review remains in the module
contracts and independent source reviews. The original private filter/map
proof-copy issue was resolved by public PMF outer-measure reuse; historical
diagnostics remain preserved and the final full clone gate is still separate.

Actual Lean full build, complete native theorem ownership and axiom audit,
raw stored-type comparisons against all 4,272 existing registered public
theorems and among the new candidates, compiled direct-edge replay, fixed
native equality, registration, current-source consumer verification and
the complete clone scan remain required. Their execution receipts must bind
the same final sources; this source review supplies no guessed native hashes
or counts and cannot certify successful execution of those gates.

All ten old overlays, the immutable 68-row clone table, the four counted
generators and the frozen P-ID categories remain unchanged. Strong global
mathematical closure remains `NOT_ESTABLISHED`.
