# Track S — scientific closure audit

Status: **LOCAL SCIENTIFIC CLOSURE CANDIDATE / UNCOUNTED / DO NOT PUSH YET**

Counted-core impact: **NONE**.

## 1. Closure question

Track S began from a topology-changing GOA problem:

> when the finite closed-loop kernel changes, what actually controls whether
> long-run invariant semantics remains identifiable and quantitatively
> trackable?

The lane is considered scientifically closed only if it answers all of the
following without conflating them:

1. why unconditional long-run semantic continuity can fail;
2. which canonical source-side quantity restores stability;
3. what positivity of that quantity means semantically;
4. what it means structurally in recurrent topology;
5. how it relates to classical mixing conditions; and
6. how it yields an actual perturbation/tracking theorem.

The current local branch now has machine-checked answers to all six.

## 2. Negative boundary: topology change is real

Earlier merged Track-S checkpoints established that arbitrarily small kernel
changes can alter recurrent topology and produce an order-one change in
stationary/GOA semantics.  Therefore there is no unconditional theorem of the
form

    small kernel defect => small long-run semantic defect.

Old recurrent labels also cannot simply be transported across a genuine
topology change; target long-run semantics must be regenerated from the target
carrier/kernel.

This no-go boundary is retained.  The later positive theorems do not weaken it.

## 3. Canonical positive certificate

The positive lane progressively weakened source assumptions from strict
Dobrushin contraction through anchored and multi-step contraction to residual
inverse stability.

The resulting canonical finite-dimensional quantity is the direct-L1
zero-mass residual conorm

    kappa1*(P) = l1ResidualConorm(P).

It is the greatest direct-L1 lower-gain/isolation constant already formalized
for the zero-total-mass residual operator.

When positive, it supplies the canonical stationary perturbation radius

    lawTV(mu*, muhat) <= epsilon / kappa1*(P).

## 4. Semantic meaning

The merged finite-Markov uniqueness theorem proves, on a nontrivial finite
carrier,

    kappa1*(P) > 0
      iff
    P has exactly one invariant probability law.

This is the qualitative center of Track S.

Residual isolation is therefore not merely a convenient proof technique.  Its
positivity means exactly that the long-run invariant probability semantics is
unique.

The closure interface re-exports this as
`finite_markov_isolation_iff_unique_semantics`.

## 5. Recurrent-topology meaning

Two complementary structural classifications are now local-machine-checked.

### Certified stochastic recurrent decomposition

For any existing `FiniteRecurrentDecomposition` on a nontrivial full state
space,

    kappa1*(P) > 0
      iff
    the recurrent-class index is subsingleton.

The proof uses actual class invariant laws, exact support, positivity,
transient-mass extinction, and the stationary class formula.  It does not
assume a new generic decomposition-construction theorem.

### Deterministic functional graphs

For an arbitrary finite deterministic map `f`, residual-null signed mass is
proved to vanish on transient states and to be constant on each recurrent
periodic orbit.  Consequently

    kappa1*(P_f) > 0
      iff
    the functional graph has exactly one recurrent periodic orbit.

The same condition is equivalent to a unique invariant probability law.

Thus the operator quantity has a concrete recurrent-topology interpretation.

## 6. Relation to Dobrushin mixing

The merged bridge proves

    1 - alpha(P) <= kappa1*(P)

under strict Dobrushin contraction.  Therefore

    alpha(P) < 1 => kappa1*(P) > 0 => unique invariant semantics.

The implication is strict, not an equivalence:

- the merged two-state flip has `alpha(P)=1` but positive residual conorm;
- the merged permutation classification extends this to all single-cycle
  permutation kernels;
- the new deterministic functional-graph theorem proves a sharper dichotomy:
  a deterministic kernel has Dobrushin coefficient `0` only for a constant
  map, and otherwise coefficient `1`.

Hence one-step mixing is a sufficient mechanism for long-run semantic
isolation, but not its defining property.

## 7. Final tracking interface

The closure module proves that unique invariant semantics alone is enough to
unlock the canonical Track-S perturbation theorem.

Given a source invariant law `muStar`, unique source invariant semantics, a
target stochastic kernel, and row-TV defect envelope `epsilon`, Lean returns a
target invariant law `muhat` satisfying

    lawTV(muStar, muhat) <= epsilon / kappa1*(P).

This closes the loop from qualitative uniqueness back to a quantitative
stability statement.

## 8. Final machine-facing synthesis

The intended Track-S finite-state summary is now:

    strict Dobrushin mixing
        => positive canonical residual isolation
        <=> unique invariant probability semantics.

When a certified recurrent decomposition is available:

    positive canonical residual isolation
        <=> one recurrent class.

For deterministic finite dynamics:

    positive canonical residual isolation
        <=> one recurrent periodic orbit
        <=> unique invariant probability semantics.

This is the point at which further qualitative certificate hunting should
stop unless a genuinely uncovered counterexample appears.

## 9. What is deliberately not required for Track-S closure

The following remain legitimate future research, but are **not** blockers for
the finite-state Track-S scientific question:

- an exact closed formula for the conorm of an `n`-cycle;
- sharp quantitative lower bounds from detailed cycle/recurrent geometry;
- a new generic constructor proving existence of
  `FiniteRecurrentDecomposition` for every finite stochastic matrix;
- infinite-state, continuous-state, or operator-theoretic extensions;
- time-dependent/nonautonomous analogues beyond the present finite stationary
  setting;
- cross-track Track-S/Track-H synthesis while the governance integration gate
  remains closed.

These are extensions, not missing pieces of the present finite-state answer.

## 10. Governance boundary

- Post-FINAL and uncounted.
- No fifth generator is proposed.
- No frozen P-ID is reopened.
- No counted ledger row changes.
- No Track-H theorem changes.
- The frozen four-generator Core remains unchanged.
- Machine-readable research-architecture registry maintenance, if desired,
  belongs in a separate `ops/compression-*` governance change and must not be
  smuggled into the Track-S theorem branch.

## 11. Local batching discipline

Per current user direction, Track S is being closed locally across multiple
commits before any new remote push.  The local sequence contains:

1. deterministic functional-graph classification;
2. certified recurrent-class uniqueness/conorm classification;
3. final Track-S synthesis interface and closure audit.

The whole sequence will be pushed only after the final exact local head passes
focused Lean checks, Compression/root builds, proof-escape and axiom audits,
research-governance validation/regressions, frozen Compression validation and
regressions, and diff checks.

## 12. Current disposition

**Scientific status: LOCAL CLOSURE CANDIDATE.**

Promotion to remote closure evidence is forbidden until the final local
validation stack is completely green.
