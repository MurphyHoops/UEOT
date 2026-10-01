# Track S — recurrent-class uniqueness / residual isolation

Status: **MERGED UNCOUNTED / PR #220 / RESULTING-MAIN FULL-GREEN / AUDIT HARDENED LOCALLY**

Counted-core impact: **NONE**.

## Question

The general finite-Markov Track-S theorem already proves

    l1ResidualConorm(P) > 0
      iff
    P has unique invariant probability semantics.

The remaining structural question is how that semantic uniqueness appears in
the repository's certified recurrent-decomposition language.

This lane works with an existing `FiniteRecurrentDecomposition`.  It does not
claim or require a new theorem constructing such a decomposition for every
finite stochastic kernel.

## Class laws are genuinely different

For two distinct recurrent-class indices `c != d`, the decomposition already
provides class laws with exact class support.

Using `classLaw_positive` on class `c` and `classLaw_other_zero` for class `d`,
Lean proves

    classLaw(c) != classLaw(d).

Thus multiple certified recurrent classes immediately produce multiple
invariant probability vectors.

## One recurrent class gives uniqueness

Assume the recurrent-class index type is subsingleton.

For any invariant probability law:

- `invariant_transient_zero` removes all transient mass;
- `stationary_class_formula` expresses every recurrent coordinate as class
  mass times the unique class law;
- because there is only one class and the law has total mass one, that class
  mass is exactly one.

Hence every invariant probability law equals the same class law.

The module packages the raw structural equivalence as

    InvariantProbabilityVectorUnique(M)
      iff
    Subsingleton(C).

## Canonical residual conorm

The decomposition stores stochasticity using the standard `Sum` decidable
equality, while `invariantLawSet` uses a local classical decidable equality.
The module explicitly transfers the row-stochastic certificate through the
instance-independent characterization

    entries nonnegative + every row sums to one.

This lets the already merged finite-Markov uniqueness theorem be reused rather
than duplicated.

On a nontrivial full state space Lean then proves

    l1ResidualConorm(M.P) > 0
      iff
    card(C) = 1.

The audit-hardening theorem `recurrentClass_nonempty_of_nontrivial_full_state`
also proves that a valid decomposition on a nontrivial full state space cannot
have zero recurrent classes.  Therefore the earlier `Subsingleton C` statement
is sharpened literally to `Fintype.card C = 1`: the chain has exactly one
recurrent class.

## Interpretation

This closes the main structural triangle for finite stochastic dynamics:

    positive residual isolation
      <=> unique invariant probability semantics
      <=> exactly one recurrent class

where the last equivalence is stated relative to an existing certified
recurrent decomposition.

Strict Dobrushin mixing remains only a sufficient mechanism for this condition,
not its definition.

## Boundaries / nonclaims

- No generic recurrent-decomposition existence theorem is added.
- No aperiodicity or convergence of raw trajectories is inferred.
- No quantitative lower bound on the conorm follows merely from one class.
- No claim is made that recurrent-class labels are stable under arbitrary
  topology-changing perturbations.
- No frozen P-ID, counted generator, ledger row, or Track-H theorem changes.

## Local validation

This checkpoint was accepted through the batched Track-S closure PR #220.
The accepted branch passed:

- focused Lean compilation of all three new Track-S modules: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS (9051 jobs)**;
- full `lake build UEOT`: **PASS (9070 jobs)**;
- `git diff --check`: **PASS**;
- proof-escape scan: **PASS**;
- public-theorem axiom audit: only `propext`, `Classical.choice`, and
  `Quot.sound`;
- Track-S research governance: **PASS (7 changed paths)**;
- research-governance regression suite: **PASS**;
- frozen Compression governance validator: **PASS**;
- frozen Compression validator regression suite: **PASS**.

PR #220 merged to `main@5fa6b69ad6a166c120a15f89a77f52962ad83607`;
resulting-main Core Lean `36880543971` and Compression Guard `36880543961`
both succeeded.  The exact-cardinality `card(C)=1` strengthening described
above is a post-merge local audit hardening of the same scientific result.
