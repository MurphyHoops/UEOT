# UEOT-MINCORE Research Report v1

Mission: Mathematical Unification, Proof Compression & Scientific Closure
Tracker context: Issue #146 (Compression) + Issue #302 (Unified Mathematical Closure)
Base/current-main at start: 1ebf78a2d1e496033a7c86389f316444f539c5cc
Branch status at first write: LOCAL_PROVED / REVIEW_PENDING / UNCOUNTED

## A. Recovery report

The recovery pass found one canonical local repository at /Users/murphyhoops/Documents/ueotlean. Local main, origin/main, and HEAD were all exactly 1ebf78a2d1e496033a7c86389f316444f539c5cc. The tracked tree was clean. Only pre-existing local caches .cos-test/, formalization/ueot-core/.cos-test/, and formalization/ueot-core/.lake/ were untracked and were not removed or counted as research changes.

There were no open pull requests. The live recovery/science trackers are Issue #146 and Issue #302; this package does not create a duplicate mission.

Frozen Core remains 106/106 FULL-GREEN. COMPRESSION_LEDGER.yaml remains 106 analyzed / 106 final dispositions, 11 generated, 89 retained_adapter, 6 retained_boundary, 0 unresolved, with exactly four counted generators: M-QD-01, M-TC-01, M-PE-01, M-OI-01.

The reuse/FKRG layer is already closed infrastructure, not a target for redevelopment. On this exact current main the reuse navigator revalidated 633 modules (622 UEOT-maintained + 11 adapted upstream), 3,793 public authored theorem proofs, 37 equal-type groups / 77 names, 15 near-type pairs and 68 cross-file clone candidates. Its 13 regression tests passed.

The current resulting-main Compression Guard for 1ebf78a2 is run 38060116959, SUCCESS. The last scientific UMC merge had both full Core Lean and Compression Guard resulting-main SUCCESS; later changes through the current main were FKRG/governance changes and did not modify frozen Core-106 theorem sources or the counted ledger.

## B. Duplication and proof-reuse results

The canonical 37-group / 15-pair / 68-clone scan was reused rather than recomputed lexically. MINCORE_DUPLICATION_MATRIX_V1.json preserves the complete elaborated type for every one of the 37 strict clusters, all member paths/lines and direct proof edges. A fresh build-aware run of VERIFY_40_TYPE_EQUIVALENCES.lean on current main exited 0.

### E1 — TV symmetry

Source/canonical reusable helper: UEOT.V3.InformationPacking.tvDist_symm.

Duplicate public helper: UEOT.V3.StatisticalDefect.tvDist_symm.

Classification: EXACT-TYPE + DIRECT-COROLLARY + ORDINARY-HELPER.

Temporary full-module replacement of the StatisticalDefect proof by the InformationPacking theorem compiled with exit 0. The replacement import graph is acyclic in the tested current environment. The public StatisticalDefect name can therefore be preserved as a thin alias if a future frozen-Core maintenance refactor is authorized.

Scientific judgment: this is ordinary proof duplication, not an independent generator witness. The mathematical assumptions are unchanged. The likely maintenance benefit is real but small; this L1 package deliberately does not pay L3 governance cost to rewrite frozen Core merely to remove this helper.

### E2 — finite PMF TV = half L1

Source reusable theorem: UEOT.V3.FiniteRecurrentDecompositionStability.pmf_tv_eq_half_sum_abs.

Target duplicate: UEOT.V3.SymmetricKilledSpectralStability.pmf_tv_eq_half_sum_abs.

Closed elaborated types: not definitionally equal. Classification: BRIDGE-REQUIRED + DIRECT-COROLLARY.

Temporary replacement by an exact call to the source theorem in the complete target module compiled successfully. The target's original local proof body is 37 physical lines.

The difference is therefore contextual/implicit rather than a different finite-probability identity. A future neutral probability-distance helper could remove the duplication while keeping both public APIs. It is not scientifically necessary for this MINCORE package and would touch frozen source, so no refactor is made here.

### The other exact-type groups

Of the 37 clusters, 23 already contained 26 direct proof-dependency edges. The remaining 14 had no in-cluster direct source reference; the canonical temporary replacement suite was rerun on current main and all 14 replacements compiled. Their scientific roles remain distinct:

- eight source-facing routes are counted-family witness derivations in M-OI/M-TC, including the intermediate Feller result, and must not be collapsed into terminal aliases when claiming independent generator evidence;
- four are uncounted retained-adapter experiments, M-VA/M-CF;
- one is E1, the low-risk TV helper;
- one is a domain-named alias/no-go surface.

Thus theorem-type/proof reuse and scientific-generation evidence remain two different axes.

All 15 heuristic near-type pairs remain NEAR-BUT-DISTINCT: 0/15 passed closed Meta.isDefEq. No implication is inferred without a separate bridge.

## C. Candidate selection for the main unification experiment

Two serious candidates were considered.

1. Relation + separately supplied defect presentation. This is the one legitimate route explicitly left open by the previous second-order Structural Defect feasibility audit. It attempts to place M-QD exact descent, M-TC quantitative transport, and M-OI exact limit closure above one lower relation/certificate interface.
2. Contractive fixed-point calculus. This candidate is already formalized as M-CF: it is a genuine Bellman/GOA bridge with an out-of-sample geometric contraction consequence, but prior audit already established that it does not construct either domain operator/existence machinery and does not replace a counted generator.

The first candidate was selected because it attacks the only recorded second-order 4-to-3 reduction route that had not yet received Lean evidence. Re-running M-CF would duplicate completed research.

## D. New formal no-go: exact relation does not determine quantitative defect

New additive module: UEOT/V3/Compression/TheoryCompletion/MinCore/RelationDefectNoGo.lean.

It defines an independent common structure RelationDefectPresentation X with:

- an exact relation rel : X -> X -> Prop;
- a nonnegative defect : X -> X -> Real;
- the only coupling assumption defect x y = 0 iff rel x y.

Lean then proves:

1. rescale_preserves_exact_relation: every positive rescaling defect' = c * defect preserves the exact relation;
2. rescale_zero_iff: it preserves exactly the zero-defect predicate;
3. rescale_budget_iff: finite thresholds transform as c*d <= epsilon iff d <= epsilon/c;
4. rescale_changes_nonzero_defect: if c != 1, every nonzero defect changes;
5. same_relation_arbitrary_positive_scale: on a two-point equality relation, arbitrary positive defect scales have the same exact relation;
6. no_relation_only_quantitative_recovery: no functional of the binary exact relation alone can recover the numerical defect for every admissible presentation;
7. exists_same_relation_different_defect: an explicit two-point witness;
8. relationDefectPresentation_does_not_force_triangle: a three-point equality-relation presentation satisfies nonnegativity and the exact zero-set law but violates the triangle inequality.

The last three give the decisive counterexample/no-go package.

### Mathematical consequence

The candidate common structure has a genuine gauge freedom: d and c*d, for any c > 0, encode the same exact relation.

Therefore exact relation/zero-set information can support exact descent or exact-limit closure, but it cannot by itself identify the numerical scale required by a finite quantitative transport certificate. Even after adding an arbitrary nonnegative zero-compatible defect field, triangle/finite-composition regularity is not forced. To recover an M-TC-style bound one must additionally supply both a normalization/calibration/gauge convention (or physical/statistical unit) and the relevant transport regularity.

This is not a proof that no higher common structure exists. It proves that the remaining proposed relation-plus-uncalibrated-defect packaging does not discharge the independent quantitative premises needed for M-TC and therefore does not justify a 4-to-3 generator reduction.

### Red-team checks

- the target conclusion is not stored as a structure field;
- the no-go uses two explicit admissible presentations;
- no frozen Core theorem is invoked as the desired terminal conclusion;
- no sorry, admit, unsafe proof escape or new axiom is introduced;
- the counterexample works on Bool, so no hidden measure/topology assumption causes the failure;
- the result is invariant under changing UEOT physical interpretation: it is a mathematical identifiability/calibration boundary.

## E. Minimality and complexity judgment

This round does not change the counted generator set.

The best justified statement remains: {M-QD-01, M-TC-01, M-PE-01, M-OI-01} is nonredundant under the declared registered theorem-surface derivation system.

The new no-go strengthens one reason not to conflate M-QD/M-OI with M-TC: exact zero-relation information does not determine quantitative defect scale. It is still not an absolute logical-independence proof.

No original mathematical assumption is removed from a frozen P-ID. No new stronger assumption is smuggled into a source-facing theorem. No generated mapping or independent generator witness is deleted.

Complexity change in this branch is architectural, not LOC compression: one small negative theorem family closes a previously open 4-to-3 candidate route and prevents a larger but invalid abstraction from being promoted.

## F. Scientific claim boundary and C1–C7 impact

| Port | New status from this result |
|---|---|
| C1 measurable existence/general state | no new evidence |
| C2 finite-data object/protocol discovery | no new evidence |
| C3 carrier/destruction algorithms | no new evidence |
| C4 nonstationary identity/transport | boundary only: quantitative transport requires calibrated defect scale |
| C5 Pi/Phi identifiability | conceptual analogy only; this theorem is not a Pi/Phi mechanism result |
| C6 purpose bridge | no new evidence |
| C7 formal-to-real falsification chain | adds a formal claim-boundary/no-go, but no empirical validation |

Scientific interpretation: this is a mathematical unification boundary, not evidence that several physical mechanisms are one mechanism. It supports a typed network architecture in which exact relation/descent, quantitative transport, positive spectral construction and asymptotic closure retain distinct premises.

The result does not prove universal Objecthood, Omega-loop physics, Pi/Phi uniqueness, GOD/GOA universality, or any new empirical prediction.

## G. Engineering evidence and closure gates

Local evidence already obtained at first write:

- current main recovery and clean tracked baseline;
- FKRG reuse status fresh against its pinned source census;
- FKRG reuse regressions: 13/13 PASS;
- E1 focused direct-reuse suite: 14/14 PASS in seven temporary whole modules;
- E2 PMF-TV bridge: PASS;
- fresh 40-pair type-equivalence Lean run: exit 0;
- new MinCore module focused Lean compile: PASS.

The scientific theorem/evidence additions are Track-TC L1 surfaces, but the final branch is **not purely L1**. Three fail-closed existing receipts/tools required explicit temporary L2 authorization rather than bypasses:

- PR #319 / merge `eb87bb38f05ae82546518bd2d6ca3ab7558c29f5` authorizes the existing `UMC_GLOBAL_MODULE_DAG_V4.json` receipt on this research branch.
- PR #320 / merge `c7989419029a562c409ead38cc8c7ff146b8a621` authorizes exactly four live FKRG proof-reuse navigator surfaces (`fkrg_reuse.py`, its regression test, README, and clone rebuild helper). The immutable 2026-10-10 633-module audit remains byte-preserved; a pinned MINCORE overlay extends the live navigator.
- PR #321 / merge `99f4759c9e798109d761789fd1212141875a7a5b` authorizes the existing UMC DAG builder and its CI-executed regression entry point after review found that attribute-prefixed declarations such as `@[simp] theorem` were omitted from metadata counts.

The live proof-reuse state after remediation is 634 modules (623 UEOT-maintained + 11 adapted upstream), 3,803 public authored theorem proof nodes, 37 historical strict equal-type groups, and 10 overlay theorem nodes. The overlay Lean verifier checks 37,930 new-vs-base and 45 new-vs-new `Meta.isDefEq` pairs with zero matches and independently checks the compiled theorem proof terms. Under FKRG's kernel measure (`.thmInfo.value.getUsedConstants` restricted to registered theorem nodes), the MINCORE overlay has 0 theorem-to-theorem edges: the source tactic in `rescale_changes_nonzero_defect` mentions `rescale_defect`, but that theorem constant does not survive in the elaborated proof term. The 634-module clone regeneration remains 68 candidates. `test_fkrg_reuse.py` is 15/15 PASS and the lexical FKRG suite is 17/17 PASS.

Codex review on PR #318 first raised the stale-live-FKRG and omitted-L2-report findings; both were remediated. A later review correctly found that the UMC DAG generator undercounted attribute-prefixed declarations. The parser and the CI-owned regression entry point are now repaired: the live DAG reports 634 modules, 3,977 theorem/lemma tokens globally, and exactly 10 theorem/lemma plus 14 total declarations in the MINCORE module. The same later review proposed one FKRG theorem edge from a source-level tactic reference; an independent Lean kernel audit falsified that proposed edge, so the proof graph retains the kernel-correct empty edge set rather than a textual approximation. A temporary public helper that had produced an unrelated closed-type collision was also removed; the remaining 10 new theorem types have zero definitional-equality collisions.

Independent re-review, new exact-head CI, merge, resulting-main validation and retirement of all three temporary L2 exceptions remain separate evidence gates. No local success is represented here as final remote closure.

## H. Highest-priority next mathematical task

Only one follow-up is recommended if this package closes: Calibrated defect comparison theorem.

Target: given two defect presentations of the same exact relation plus an independently specified calibration bridge, for example constants a*d <= d' <= b*d, prove exact transport of finite certificates and identify which M-TC conclusions are gauge-covariant versus gauge-dependent.

Known inputs:
- RelationDefectPresentation and the present rescaling no-go;
- M-TC weighted_chain_bound;
- M-OI residual-limit closure;
- M-QD exact fibre descent.

Minimum missing bridge: a non-circular calibration relation between two defect presentations.

Success: one Lean theorem transports finite M-TC budgets under explicit calibration and one counterexample shows failure without it.

Failure exit: an explicit calibrated pair satisfying the proposed assumptions but violating the transported certificate, or a Lean proof obligation showing an additional assumption is necessary.

Do not reopen the four-generator count merely because this follow-up produces a useful bridge.
