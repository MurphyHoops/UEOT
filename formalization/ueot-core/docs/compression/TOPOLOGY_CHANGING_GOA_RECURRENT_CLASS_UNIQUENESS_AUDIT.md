# Track S — recurrent-class uniqueness / residual isolation

Status: **LOCAL INTEGRATION CANDIDATE / TRACK S / UNCOUNTED / DO NOT PUSH**

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
    Subsingleton(C).

So, whenever a certified recurrent decomposition is available, the canonical
Track-S isolation constant is positive exactly when the chain has at most one
recurrent class.

## Interpretation

This closes the main structural triangle for finite stochastic dynamics:

    positive residual isolation
      <=> unique invariant probability semantics
      <=> one recurrent class

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

Pending full integration and exact-head validation together with the remaining
Track-S closure commits.  This lane stays local until Track S as a whole is
closed and the complete local validation stack passes.
