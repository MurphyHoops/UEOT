# Track X — X0 Interface Audit

Status: **X0 COMPLETE / INTERFACE FROZEN / LOCAL WIP**

Authority:
- parent mission: GitHub Issue #146;
- detailed Track-X tracker: GitHub Issue #225;
- canonical recovery base: `main@d0ac01ed45c1515541bf811ba7c5e67b2d81e7c5`;
- counted-core impact: **NONE**.

## 1. Scope

Track X asks whether multiple richer parent completions compatible with the same
child evidence can nevertheless possess exact or quantitatively stable
long-run semantics.  It keeps two ambiguities distinct:

1. **assembly ambiguity**: several parent completions lie over the same child
   evidence;
2. **dynamical semantic ambiguity**: one fixed parent kernel may admit several
   invariant laws.

Uniqueness of the second may not be used to remove the first.

## 2. Exact imported H interfaces

From `UEOT.V3.Compression.Hierarchy.ParentAssemblyResidual`:

- `commonWitness_not_hierarchyLift`;
- `childConsistency_does_not_determine_unique_parent`;
- `same_child_marginals_different_joint`.

These establish only negative parent-formation boundaries.  Track X does not
re-prove them.

From `UEOT.V3.Compression.Hierarchy.Separations`:

- `carrier_does_not_determine_maximizers`;
- `response_does_not_determine_fitness`.

These remain hard separation guards.  Parent/carrier semantics do not determine
objective/maximizer semantics, and behavioral response does not determine
fitness/selection semantics.

## 3. Exact M-QD interface

From `UEOT.V3.Compression.QuotientDescent`:

- `FiberCompatible q g`;
- `descend`;
- `descend_comp`;
- `eq_descend_of_comp_eq`;
- `existsUnique_descend`;
- `fiberCompatible_of_comp_eq`;
- `fiberCompatible_iff_existsUnique_descend`.

Track-X correspondence:

- parent-completion type: `P`;
- child-evidence type: `C`;
- child projection: `pi : P -> C`;
- parent dynamics family:
  `K : P -> Matrix S S Real`.

Exact fibre compatibility is

`pi p = pi q -> K p = K q`.

For a child codomain `C` larger than the image of `pi`, M-QD cannot give a
unique value away from the image.  Therefore the exact X2 descent theorem
explicitly requires `Function.Surjective pi` (or, equivalently, a caller may
replace `C` by the image subtype).  This is not an extra physical assumption;
it is the exact set-level universal-property requirement already present in
M-QD.

M-QD descent here is sufficient because the descended object is a finite
transition matrix.  No new measurable-kernel descent theorem is claimed.

## 4. Exact Track-S interface

Finite state assumptions used by X1-X5:

- `[Fintype S]`;
- `[Nonempty S]`;
- nontriviality `1 < Fintype.card S` whenever positivity of the canonical
  residual conorm is invoked.

From `UEOT.V3.FiniteDobrushin`:

- `lawTV`: total variation between finite simplex laws;
- `crossRowTV`: same-input row-TV defect between two finite stochastic
  kernels;
- `tv_step_cross_le`;
- `pureSimplex`.

From `UEOT.V3.Compression.InvariantSetGaugeInvariance`:

- `invariantLawSet P hP`;
- `mem_invariantLawSet`.

From
`UEOT.V3.Compression.TopologyChangingGoaL1ResidualConorm`:

- `l1ResidualConorm`;
- `l1ResidualConorm_isolation`;
- `l1ResidualConorm_pos_iff_restricted_injective`;
- `canonical_l1_stationary_tracking`.

From
`UEOT.V3.Compression.TopologyChangingGoaInvariantUniquenessIsolation`:

- `invariantLawSet_nonempty`;
- `restricted_injective_iff_invariantLawSet_subsingleton`;
- `l1ResidualConorm_pos_iff_invariantLawSet_subsingleton`;
- `l1ResidualConorm_pos_iff_unique_invariant_law`.

From `UEOT.V3.Compression.TopologyChangingGoaTrackSClosure`:

- `finite_markov_isolation_iff_unique_semantics`;
- `canonical_l1_stationary_tracking_of_unique_invariant_law`;
- the deterministic and recurrent-class closure interfaces.

From
`UEOT.V3.Compression.TopologyChangingGoaSpectralIsolation` and
`TopologyChangingGoaResidualInverseStability`:

- `residualInverse_of_l1Isolation`;
- the branch-residual inverse bound.

This last route lets Track X prove the stronger X3 statement required by the
tracker: **for an explicitly supplied target invariant law**, rather than only
for an existentially selected target invariant law,

`lawTV muSource muTarget <= epsilon / l1ResidualConorm P`.

Thus target invariant-law existence is never inferred from source isolation.

## 5. H -> X and S -> X type correspondence

H's forgetful-map picture becomes:

`P --pi--> C`,

where a fibre `{p | pi p = c}` is the set of admissible richer parent
completions compatible with child evidence `c`.

Track S attaches to each completion:

`p |-> K p : Matrix S S Real`,

together with:

- a proof that `K p` is row stochastic;
- an explicitly supplied invariant law when quantitative pairwise semantics are
  compared;
- the canonical source isolation margin
  `l1ResidualConorm (K p)`;
- the row defect
  `crossRowTV (K p) ... (K q) ... x`.

The long-run semantic distance is exactly `lawTV (mu p) (mu q)`.

## 6. X1-X4 proof readiness

**X1** can be proved without changing H or S.  The finite witness uses two
parent completions with the same child projection and two constant deterministic
reset kernels, one resetting to `false` and one to `true`.  Each has
canonical residual conorm one and a unique invariant law, while the two
stationary point masses have TV distance one.

**X2** can be proved directly by `QuotientDescent.existsUnique_descend`.
Positive residual isolation of a descended stochastic kernel then gives unique
invariant semantics through Track S.

**X3** can be proved by the existing Track-S L1 residual inverse plus
`tv_step_cross_le`.  It needs an explicit source invariant law, an explicit
target invariant law, positive source residual conorm, and a row-TV defect
bound.  It does not require target isolation or target uniqueness.

**X4** follows pairwise from X3.  Under a uniform lower bound
`kappaMin <= l1ResidualConorm (K p)` on the fibre and a pairwise row-TV bound
`epsilon`, the honest pairwise constant is exactly
`epsilon / kappaMin`.  No factor two is required.  The fibre-wide diameter is
the supremum of these pairwise `lawTV` distances.

No X1-X4 theorem requires mutation of Track-H or Track-S owned files.

## 7. P-COMP audit for later X6

The frozen P-COMP family is heterogeneous and does **not** expose a universal
parent constructor:

- P-COMP-01 assumes one common joint child-path/interface law;
- P-COMP-02 assumes observational and declared cut laws;
- P-COMP-03 transports an already supplied cut-distance diagnostic;
- P-COMP-04 assumes a parent representation and measurable parent-core map;
- P-COMP-05 canonicalizes the Boolean overlap geometry of supplied regions;
- P-COMP-06 lifts a supplied physical minimal-carrier family to minimal child
  coalitions;
- P-COMP-07 assumes integration/fidelity diagnostics and proves the exact
  feasible coupling window.

Therefore X6 must consume an explicit parent-assembly certificate.  It may not
pretend that child evidence alone constructs the missing richer parent data.
The cleanest out-of-sample binding surface is P-COMP-06: a supplied physical
minimal-carrier semantics produces a canonical child-coalition family, after
which Track-X dynamics/isolation hypotheses may certify robust long-run
semantics across admissible completions.

## 8. Assumptions and nonclaims

Assumptions are exactly those exposed above: finite nonempty state carrier,
nontriviality where conorm positivity is used, stochastic kernels, explicit
invariant-law witnesses for quantitative comparisons, M-QD fibre compatibility
for exact descent, and explicit row-TV defect bounds for approximate stability.

X0 makes no claim that:

- child data determine a unique parent completion;
- unique invariant semantics for every completion make the parent semantics
  child-determined;
- positive source isolation proves target invariant-law existence;
- parent carrier determines objective/maximizer semantics;
- behavior determines fitness/selection semantics;
- P-COMP-01..07 form a universal parent constructor;
- Track X changes the frozen four-generator counted core.

Conclusion: **X1-X4 are interface-ready on canonical main with no H/S
modification.**
