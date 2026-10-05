# UEOT Theory Completion — P0 Semantic Constitution

Status: **P0 LOCAL COMPLETE / UNMERGED**
Tracker: **#268**
Canonical base: `0ce13ad7f2a6dc1a04376f875fe7479a0fa22e4e`

This is the P0 terminal definition/theorem graph. It maps UEOT philosophical terms to the smallest typed semantic objects introduced or selected by P0, then to canonical theorem families that instantiate them.

| UEOT term | P0 formal semantic object | Canonical instantiation / evidence | Remaining bridge or boundary |
|---|---|---|---|
| World Process | existing history/process/kernel interfaces; no new universal wrapper | `HistoryMachine`, `p_proc_01_history_markovization`, `homHistoryKernel` | no claim that every discrete/continuous process is one universal structure |
| Protocol | existing protocol closure/factorization interfaces | `ProtocolClosureAt`, `CommonProtocolClosure`, `p_int_01` | protocol is not Object, Purpose, or World Process |
| Predictive State | `PredictiveIdentity C R := InputFiberCompatible C R` | recursive sufficient-state / prediction / exact-closure theorems | P2 must bind the effective state to the same Objecthood object's own history |
| Object Candidate | `FormedProvenance` | `FormedCandidate`, response-generated candidate family | provenance alone fails Object semantics |
| Object Boundary / delimitation | `InteractionDelimitedAt` | pairwise interaction separation implies object-specific delimitation | abstract Markov boundary and interaction delimitation remain distinct unless bridged |
| Persistence | `ConstitutivelyPersists` | `ConstitutivePersistenceCertificate` via `constitutivelyPersists_of_certificate` | persistence alone is not repair, purpose, or agency |
| Recovery / self-maintenance | `PhysicallyRecoverableOn` | `PhysicalRepairCertificate` + explicit nonempty finite-potential basin witness; `SelfRepairingOperationalParent` adapter under the same witness | unified organizational fault/resource/autopoiesis semantics are later P5–P7/P12 work |
| Semantic identity | `SemanticFiberIdentity` | `SemanticallyStableSelfRepairingOperationalParent.selected_parent_in_fiber` | literal representation equality is not required; same-object P2 guards remain |
| Purpose | `NumericalObjective`, `InducedPreference`, `PolicyOrderingEquivalent`, `MaximizerSet`, `ChoiceRepresentationClass` | canonical teleological equivalence, DDH gauge, hierarchy separation | P1 must construct `TeleologicalContract`; no unique reward is implied |
| Agency | canonical control/decision structures; P0 does not duplicate them | `FeasibleDecision`, `HistoryControlSpec`, `agency_god_goa_from_history` | P2 must construct this control model from the same object and P1 contract |
| GOD | `LocalChoiceCorrespondence`, `BellmanGODCorrespondence`, `IsBellmanGODSelector` | `greedyAction_spec`, history-derived model adapter | correspondence may be non-singleton; unique gradient requires extra domain structure |
| GOA | `FixedPointGOA`, `InvariantLawGOA`, `CesaroLimitGOA`, `RecurrentGOAStructure`, `KilledQSDGOA`, `GreedyInvariantGOASet` | occupation-limit, recurrent decomposition, QSD/Perron, greedy closed-loop theorems | GOA is plural; uniqueness/convergence are certificate-dependent |
| Composition | existing child/parent formation and identifiability theorem families | P-COMP, Track H/X formation and parent-binding results | child consistency/forward stability do not universally identify one parent |
| Scale | `IsQuotientMap`, `ClosureCoarseGraining`, nonvacuous probability-valued measurable `ExactDynamicScaleIntertwining`, `ObjectScaleMap`, `ObjectScaleTransport` | exact control quotient, closure resolution, P-DYN-04 | P9 must prove preservation of identity/purpose/GOD/GOA/etc.; Wilsonian RG bridge absent |
| Evolution | existing population/operator semantics | Price, Perron growth, reproductive value/martingale | P8 must define object-level offspring/lineage before composition with population evolution |

## P0 proved boundary graph

- carrier/provenance ⇏ full Object delimitation: `formedProvenance_does_not_imply_interactionDelimitation`;
- carrier alone ⇏ unique teleological choice class: `carrier_does_not_determine_choiceRepresentationClass` (the stronger full-Objecthood no-go remains P1.0);
- Bellman GOD ⇏ unique local action: `bellmanGOD_can_be_nonunique`;
- GOA invariant semantics ⇏ singleton/unique fixed point: `invariantGOA_can_be_nonunique`;
- surjective quotient map ⇏ exact dynamic scale intertwining: `quotientMap_does_not_imply_dynamicIntertwining`.

## P0 constructive adapters

- pairwise interaction separation → `InteractionDelimitedAt`;
- constitutive persistence certificate → `ConstitutivelyPersists`;
- physical repair certificate + explicit nonempty repair-basin witness → `PhysicallyRecoverableOn`;
- hardened same-parent Objecthood certificate → `SemanticFiberIdentity`;
- positive-affine teleological equivalence → policy-ordering equivalence → maximizer equivalence;
- DDH gauge → one `ChoiceRepresentationClass`;
- finite Bellman model → nonempty `BellmanGODCorrespondence`;
- `HistoryControlSpec.toModel` → nonempty Bellman GOD at every state;
- finite Cesàro limit → invariant-law GOA;
- finite killed-kernel QSD predicate → all-step conditional QSD identity and `rho ≤ 1`;
- finite Bellman-greedy closed loop → nonempty invariant-law GOA set;
- exact finite control quotient → `IsQuotientMap`;
- nested closure systems → compositional `ClosureCoarseGraining`;
- nonempty microscopic source + nonempty action type + microscopic probability transition law + exact pushforwards + measurable scale map → nonempty probability-valued reachable-set `ExactDynamicScaleIntertwining`.

## P0 terminal conclusion

The formal system now has explicit semantic types/predicates for the P0 target concepts without collapsing them into one theorem-shaped package. The central scientific gap is narrowed to two sequential tasks:

1. **P1:** represent purpose over admissible futures as a teleological equivalence/representation problem and construct a reusable `TeleologicalContract`;
2. **P2:** prove that one and the same endogenous, persistent, self-maintaining object supplies its own history/effective state, P1 contract, induced control model, GOD and GOA, with explicit identity guards and viability compatibility.

P0 does **not** alter Core v3, counted compression, minimal-core membership, or S/H/X/O theorem source.
