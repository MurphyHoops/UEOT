# Track X — X7/X8 Architecture Audit and Final Synthesis

Status: **X0-X8 LOCALLY COMPLETE / VALIDATION PASS / INDEPENDENT AUDIT CLEAR / READY FOR PUSH**

Authority:
- durable parent mission: GitHub Issue #146;
- Track-X tracker: GitHub Issue #225;
- recovery base: main@d0ac01ed45c1515541bf811ba7c5e67b2d81e7c5;
- counted-core impact: **NONE**.

This document closes the local X0-X8 scientific sequence. It does not record a
remote PR, CI result, or cloud review; those lifecycle facts may be added only
after the required local validation and independent audit have completed.

## 1. X0 — interface audit

The frozen interface audit is
docs/compression/cross_track/X0_INTERFACE_AUDIT.md.

Result: **READY / NO H-S MUTATION REQUIRED**.

The audit found that M-QD supplies exact fibre descent, while Track S supplies
the finite-state invariant-law uniqueness/isolation and quantitative
stationary-tracking machinery. P-COMP is a family of heterogeneous supplied
domain certificates rather than a universal parent constructor.

## 2. X1 — cross-track no-go

Public theorem:

- x1_uniquePerCompletion_not_childDetermined.

Witness:

- parent completion type: Bool;
- child evidence: one Unit value for both completions;
- false completion: deterministic reset to false;
- true completion: deterministic reset to true;
- each kernel has l1ResidualConorm = 1;
- each kernel has a unique invariant probability law;
- the final theorem itself packages both explicit point masses as invariant laws
  of their respective kernels;
- those two explicit stationary point masses have lawTV = 1.

Conclusion:

> Same child evidence plus unique long-run semantics for every completion does
> **not** imply child-determined parent long-run semantics.

Architecture role: **G3 boundary**.

This preserves H2 assembly ambiguity instead of silently deleting it with
Track-S uniqueness.

## 3. X2 — exact parent-semantic descent

Public theorems:

- x2_exactParentKernelDescent;
- x2_descendedKernel_rowStochastic;
- x2_descendedKernel_uniqueSemantics.

If pi : P -> C is surjective and QuotientDescent.FiberCompatible pi K holds,
M-QD gives the unique Kbar : C -> Matrix S S Real with Kbar ∘ pi = K.

Surjectivity is explicit because uniqueness away from the image of pi is
otherwise false. A caller that begins with a nonsurjective projection can use
the image subtype as its child codomain.

Once the descended child kernel is stochastic, positive Track-S canonical
residual isolation gives a unique invariant law.

Architecture role: **G2 over existing M-QD + Track-S bridges**.

No new descent primitive is introduced.

## 4. X3 — quantitative parent-semantic stability

Public theorems:

- suppliedInvariant_tracking;
- x3_parentSemanticTracking.

For source completion p0 and target completion p, assume:

- both kernels are finite stochastic kernels;
- both invariant laws are **explicitly supplied**;
- pi p = pi p0;
- source l1ResidualConorm (K p0) > 0;
- every corresponding row differs by at most epsilonBind in total variation.

Then:

lawTV (mu p0) (mu p) <= epsilonBind / l1ResidualConorm (K p0).

This uses the merged Track-S L1 residual inverse and
FiniteDobrushin.tv_step_cross_le.

Architecture role: **G2 bridge**.

Crucial quantifier discipline: target invariant-law existence is not inferred
from source isolation.

The same-fibre equality is intentionally retained as the Track-X semantic
scope condition even though the numerical estimate itself follows from the
explicit pairwise row-defect hypothesis and is therefore slightly stronger.

## 5. X4 — fibre-wide semantic diameter

Public theorems:

- x4_fiber_pairwiseSemanticBound;
- x4_fiberSemanticDiameter.

Definitions:

- fiberSemanticDistances;
- fiberSemanticDiameter.

If one child fibre is nonempty, every pair of kernels in it has row defect at
most epsilon, and every source completion in the fibre satisfies
kappaMin <= l1ResidualConorm (K p) with kappaMin > 0, then:

fiberSemanticDiameter pi mu c <= epsilon / kappaMin.

The preferred constant is therefore achieved exactly. No factor two and no
asymmetric reference-completion relaxation are needed.

Architecture role: **G2 synthesis**.

## 6. X5 — robust parent semantic certificate

Public structure:

- RobustParentSemanticCertificate.

Public consequences:

- RobustParentSemanticCertificate.pairwise_bound;
- RobustParentSemanticCertificate.diameter_bound.

The structure packages only:

- one child-evidence fibre;
- finite stochastic parent kernels;
- explicit invariant-law witnesses;
- within-fibre row defect;
- a positive canonical residual-isolation floor.

It does not encode:

- universal Objecthood;
- teleology;
- objective/maximizer semantics;
- fitness/selection semantics;
- a new G0 primitive.

Architecture role: **G2 / MERGED_UNCOUNTED candidate**.

## 7. X6 — P-COMP out-of-sample generativity test

The X0 audit inspected the actual P-COMP-01..07 contracts. They do not form a
universal parent constructor. In particular:

- P-COMP-01 assumes the common joint child-path/interface law;
- P-COMP-02 assumes declared cut laws;
- P-COMP-04 assumes the parent representation/core map;
- P-COMP-06 assumes physical minimal-carrier semantics;
- P-COMP-07 assumes the diagnostic/window hypotheses.

Track X therefore does not reverse these arrows.

The out-of-sample test uses the most literal parent-assembly surface,
P-COMP-06.

Public structure:

- PCompCarrierAssemblyCertificate.

Public theorem exposing actual P-COMP-06 generation:

- PCompCarrierAssemblyCertificate.admissible_iff_lifted.

This theorem invokes CompositionCarrierLift.p_comp_06, converting the declared
child-minimal validity condition into the canonical two-stage lifted
physical-cover condition.

Public robust-semantic consequences:

- x6_pcomp_pairwiseRobustParentSemantics;
- x6_pcompSemanticDiameter.

Thus the exact out-of-sample result is:

> valid P-COMP-06 parent carrier assembly
> + bounded assembly-induced row-dynamics defect
> + explicit invariant-law witnesses
> + positive parent residual-isolation floor
> implies robust long-run parent semantics.

This is a genuine composition of an existing domain adapter with the new H × S
bridge. X1-X5 were not defined by copying this P-COMP-06 statement.

Architecture role: **G2 conditional synthesis over a retained adapter**.

## 8. H3 separation preservation

Nothing in Track X derives any of the following:

- parent object/carrier -> parent objective;
- carrier -> maximizers;
- behavioral response -> fitness;
- child evidence -> unique parent completion;
- value alignment -> Objecthood.

The existing H3 theorem surfaces carrier_does_not_determine_maximizers and
response_does_not_determine_fitness therefore remain untouched and fully
compatible with every positive X theorem.

## 9. X7 — architecture / deletion audit

| Stage | Result | Role |
|---|---|---|
| X1 | unique-per-completion does not imply child-determined semantics | G3 |
| X2 | exact parent-kernel descent + isolated unique child semantics | G2 |
| X3 | explicit-target epsilon/kappa_1 tracking | G2 |
| X4 | fibre-wide epsilon/kappaMin diameter | G2 |
| X5 | typed robust parent-semantic certificate | G2 / uncounted |
| X6 | P-COMP-06 conditional robust parent semantics | G2 / retained-adapter synthesis |

All positive results are generated from:

- M-QD quotient descent where exact fibre compatibility holds;
- existing Track-S finite-Markov residual isolation/tracking;
- ordinary finite TV order/algebra;
- the retained P-COMP-06 domain adapter at the out-of-sample stage.

No theorem supplies evidence for a fifth counted generator.

### H2 residual status

The H2 parent-binding residual remains real but is now more sharply localized:

> it is a **domain assembly obligation** that supplies or justifies which richer
> parent completions are admissible and how they bind to child evidence.

Once that obligation is supplied, no further independent primitive is needed
to obtain exact semantic descent under fibre compatibility or quantitative
semantic stability under row-defect/isolation hypotheses.

Track X does **not** establish that the H2 residual is a reusable irreducible
G0 mathematical obligation.

Deletion/promotion verdict:

- no 4 -> 5;
- no 4 -> 3;
- no new universal hierarchy/assembly operator;
- frozen counted core remains {M-QD-01, M-TC-01, M-PE-01, M-OI-01};
- counted-core impact: **NONE**.

## 10. X8 — final synthesis

Evidence-backed outcome:

**Outcome 2 — only a narrower conditional synthesis is justified.**

What is established:

1. assembly ambiguity can coexist with individually unique parent semantics;
2. exact fibre-compatible dynamics descend uniquely through child evidence;
3. small within-fibre dynamics diameter relative to residual isolation gives
   small long-run semantic diameter;
4. the exact quantitative finite-state radius is epsilon / kappaMin;
5. an actual P-COMP-06 assembly certificate composes with these bridges to
   produce robust parent long-run semantics.

What is not established:

1. child evidence by itself constructs or uniquely selects a parent completion;
2. P-COMP-01..07 collectively define a universal parent constructor;
3. positive residual isolation creates invariant-law existence for a different
   target completion;
4. parent semantics determine objective/fitness/value semantics;
5. the H2 assembly residual deserves counted primitive promotion.

### Four-generator architecture verdict

The four-generator architecture **survives the Track-X cross-track test for
long-run semantic synthesis**, conditional on explicit domain assembly and
dynamics-defect data.

It does not make the stronger parent-formation residual disappear. That
residual remains an uncounted domain obligation rather than a demonstrated
fifth generator.

## 11. Local validation evidence

The complete X0-X8 implementation has passed the local repository gates that
can be evaluated before an exact candidate commit:

- every CrossTrack source module was focused type-checked during development;
- public `UEOT.V3.Compression.CrossTrack` build: **PASS**;
- `UEOT.V3.Compression` build: **PASS**;
- full `lake build UEOT`: **PASS (9078 jobs)**;
- compression FINAL validator: **PASS**;
- compression-validator regression suite: **PASS**;
- research-governance validator regression suite: **PASS**;
- emitted 106-theorem ledger witness Lean audit: **PASS**;
- compression proof-escape scan: **PASS**;
- Track-X public theorem axiom audit: only standard
  `propext / Classical.choice / Quot.sound`;
- `git diff --check`: **PASS**;
- ownership/frozen-file audit: **PASS** — mutations are confined to
  `Compression/CrossTrack/`, `Compression/CrossTrack.lean`,
  `docs/compression/cross_track/`, and the one allowed root import in
  `Compression.lean`; no ledger, coverage, mission, ablation, H/S theorem,
  validator, governance, or workflow file is changed.

The frozen compression state remains 106 source theorems, 11 generated,
89 retained adapters, 6 retained boundaries, 4 counted generators, and
0 unresolved.

The exact implementation candidate
`688b00f7b47b5b3e66fef1ba4eb49fcbcd0c0917` subsequently passed both
remaining pre-push gates:

1. `validate_compression_research.py` against canonical `origin/main`:
   **PASS (changed_paths=10)**;
2. separate independent read-only semantic/proof audit:
   **RESULT: CLEAR / BLOCKERS: none**.

The independent audit is recorded in
`docs/compression/cross_track/TRACK_X_INDEPENDENT_AUDIT.md`.

Therefore the local Track-X scientific and verification lifecycle is closed.
The next authorized step is cloud branch push followed by the Issue #225
PR/CI/review lifecycle.
