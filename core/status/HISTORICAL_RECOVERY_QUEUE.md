# UEOT Core — Historical Derivation Recovery Queue

Date: 2026-09-10
Baseline: UEOT Core Mathematics v3.0
Purpose: preserve useful derivations from earlier/later evolutionary versions without silently mutating the v3 source.

## Classification

- **IN-V3** — already represented in the v3 architecture or a v3 P-ID; preserve provenance, do not duplicate.
- **LEAN-GUARD** — valuable no-go/counterexample that should be machine-checked as a regression guard.
- **V3.1-CANDIDATE** — domain-neutral result not cleanly present in v3; independently re-prove and audit before proposing a new Core release.
- **SECTOR-ONLY** — useful in a physical/quantum/etc. sector but not justified as generic Core mathematics.
- **REJECT** — historical claim contradicted by later audit or requiring unsupported universality.

## Recovery matrix

| ID | Historical result | Origin | Class | Action |
|---|---|---|---|---|
| HR-001 | Persistent identity need not be a contraction | Mathematical Foundations III | LEAN-GUARD / IN-V3 | Preserve neutral-recurrence/quasiperiodic counterexample; prevent recovery contraction from becoming a universal objecthood axiom. |
| HR-002 | Predictive sufficiency alone does not imply objecthood | Mathematical Foundations III | LEAN-GUARD / IN-V3 | Add a trivial-i.i.d. predictive-state countermodel to regression tests if absent. |
| HR-003 | Strong instantaneous coupling alone does not imply persistent individuality | Mathematical Foundations III | LEAN-GUARD | Preserve temporal-resampling counterexample; useful for composition/objecthood audits. |
| HR-004 | Canonical predictive state does not imply unique physical boundary | Mathematical Foundations III | IN-V3 / LEAN-GUARD | Maintain redundant-encoding boundary counterexample alongside any uniqueness theorem requiring intersection/intervention assumptions. |
| HR-005 | Bimeasurable representation invariance of predictive core | Mathematical Foundations III / unified v1.1 | IN-V3 | Continue P-FAC-01 exact path-law covariance proof; prohibit invariance claims under lossy preprocessing. |
| HR-006 | Exact controlled quotient preserves value/policy/GOD | Mathematical Foundations III / unified v1.1 | IN-V3 | Ensure the control quotient block proves fiber-constant value and policy lift under reward + controlled transition closure. |
| HR-007 | Approximate quotient gives explicit discounted value-loss bound | unified v1.1 | IN-V3 / proof priority | Preserve constants and TV convention exactly; useful for Object-RG/learned macrostate certification. |
| HR-008 | Parent predictive emergence lower bound / XOR witness | Mathematical Foundations III / unified v1.1 | IN-V3 / LEAN-GUARD | Keep as composition irreducibility witness; never treat positive parent information alone as full parent objecthood. |
| HR-009 | Passive object discovery can be statistically non-identifiable | Mathematical Foundations III | IN-V3 / LEAN-GUARD | Preserve Le Cam/TV no-free-lunch boundary and the need for interventions or model restrictions. |
| HR-010 | Finite mean recovery generates a Poisson/Lyapunov potential | Mathematical Foundations III / unified v1.1 | IN-V3 | Tie to P-REC-03 and generator-domain caveats; do not overgeneralize PDE regularity. |
| HR-011 | Teleological gauge: different Pi/Phi decompositions can induce the same objective | Core v1.0 / unified v1.1 | IN-V3 | Preserve as protection against identifying numerical Pi/Phi sectors from behavior without anchors. |
| HR-012 | Exact object quotient need not uniquely identify micro-attractors | Mathematical Foundations III / unified v1.1 | IN-V3 / LEAN-GUARD | Keep distinction between object-level GOA and unresolved micro recurrent structure. |
| HR-013 | Resolution descendant theorem: every coarse minimal carrier has a fine minimal descendant | later carrier-flow work | V3.1-CANDIDATE | Recast in domain-neutral closure-system language, independently prove, map to existing P-RES assumptions, and check prior art. |
| HR-014 | Resolution monotonicity: number of minimal carriers cannot decrease under refinement | later carrier-flow work | V3.1-CANDIDATE | Depends on HR-013 plus precise finite Boolean carrier semantics; machine-check before promotion. |
| HR-015 | Resolution monotonicity: maximum pairwise-disjoint redundancy cannot decrease | later carrier-flow work | V3.1-CANDIDATE | Define matching/redundancy invariant generically; verify assumptions and edge cases. |
| HR-016 | Resolution monotonicity: minimal hitting/destruction complexity cannot decrease | later carrier-flow work | V3.1-CANDIDATE | Connect to blocker/hitting-set layer already in Core; prove projection argument without quantum assumptions. |
| HR-017 | Resolution monotonicity: minimum monotone physical carrier measure cannot increase | later carrier-flow work | V3.1-CANDIDATE | Requires an explicitly monotone measure/cost on physical regions; keep as an assumption-indexed theorem. |
| HR-018 | Carrier-structural object plateau across resolution/time/protocol windows | later carrier-flow work | V3.1-CANDIDATE | Treat as a candidate certificate/definition, not a theorem, until generic realizability and robustness conditions are fixed. |
| HR-019 | Literal nonzero H1/topological loop is necessary and sufficient for every object | original manifesto | REJECT as generic theorem | Preserve historical motivation only. Core uses an Omega certificate family; topology may be one sector implementation. |
| HR-020 | All dynamics universally obey a unique numerical Pi/Phi decomposition | original manifesto | REJECT as generic theorem | Preserve dual-drive motivation; Core requires independently anchored resource/information coordinates and records gauge/non-identifiability. |
| HR-021 | GOA is always a unique fixed point | original manifesto | REJECT as generic theorem | Preserve GOA as a family of long-run structures; unique fixed point is a special model class. |
| HR-022 | Quantum/GR-specific reconstruction claims define generic Core axioms | original/sector versions | SECTOR-ONLY | Keep outside domain-neutral Core unless independently reclassified and proved without sector assumptions. |

## Immediate formalization recovery work

The highest-value historical guards that can be proved independently of the six current HOT source lanes are:

1. HR-001 contraction-not-necessary counterexample;
2. HR-002 predictive-sufficiency-not-objecthood counterexample;
3. HR-003 coupling-not-persistence counterexample;
4. HR-004 redundant-boundary nonuniqueness counterexample;
5. HR-012 object-level quotient does not imply unique micro-attractor realization.

These should live as regression/countermodel modules and **must not consume a v3 P-ID proved status** unless an exact source P-ID explicitly contains that result.

## Candidate next-version theorem package

HR-013..HR-017 form one coherent candidate package:

`resolution refinement -> descendant minimal carrier -> monotonic realization/redundancy/blocker invariants`.

Before any v3.1 proposal, require:

- a domain-neutral statement using the Core's existing closure/up-set/clutter vocabulary;
- independent proof rather than copy-forward from the later derivation;
- edge-case audit (empty carrier family, singleton universe, non-surjective coarse maps, infinite carrier universes);
- comparison with P-RES-01..06 to avoid duplicate claims;
- prior-art check for hypergraph refinement monotonicity;
- Lean verification on the pinned Core toolchain.

## Preservation rule

Historical versions remain immutable archives. Recovery means importing a result **with provenance and revalidation**, not rewriting history. If a recovered result changes the canonical theorem dependency graph, it enters a new versioned Core proposal; if it only supplies a helper lemma or counterexample, it may enter the formal library without changing v3 semantics.
