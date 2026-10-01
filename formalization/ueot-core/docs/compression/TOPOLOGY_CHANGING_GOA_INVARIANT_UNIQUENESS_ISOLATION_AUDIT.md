# Track S — invariant uniqueness / residual-isolation equivalence

Status: **MERGED UNCOUNTED / PR #219 / RESULTING-MAIN FULL-GREEN**

Counted-core impact: **NONE**.

## 1. Question

Track S has progressively weakened source-side stability certificates from
strict Dobrushin contraction to a canonical direct-L1 residual conorm
`kappa1*(P)`.

The permutation classification showed that this conorm detects recurrent-orbit
multiplicity even when one-step mixing fails completely.  The next structural
question is whether the qualitative condition

    kappa1*(P) > 0

has a direct semantic meaning for an arbitrary finite stochastic kernel, without
assuming a recurrent decomposition or a mixing hypothesis.

## 2. First direction: residual isolation implies uniqueness

For two invariant probability laws `mu` and `nu`, their signed difference

    v = nu - mu

has total mass zero and satisfies

    R_P(v) = vP - v = 0.

Therefore injectivity of the residual operator on the zero-total-mass signed
space forces `v=0`, hence `mu=nu`.

Lean formalizes this as:

- `invariantLaw_unique_of_restricted_injective`;
- `invariantLawSet_subsingleton_of_restricted_injective`.

No contraction or recurrent-class label is used.

## 3. Reverse direction is constructive, not assumed

The converse is not inserted as finite-Markov folklore.

Assume a nonzero zero-total-mass signed vector `v` satisfies

    R_P(v)=0.

Split `v` into positive and negative parts.  Their total masses are equal and
strictly positive, so after normalization they define two probability laws
`nu0` and `mu0` with

    v = c (nu0 - mu0),   c > 0.

Residual zero implies `vP^n=v` for every `n`.  Hence the scaled difference
between the two orbit laws, and therefore between their Cesaro averages, is
exactly `v` at every horizon.

Use frozen P-GOA-01 / finite-simplex compactness:

1. extract a convergent Cesaro subsequence for `nu0`;
2. extract a sub-subsequence for `mu0`;
3. use the common index map so both limits are seen along the same subsequence;
4. P-GOA-01 proves both limits invariant;
5. continuity preserves the exact nonzero scaled difference.

Thus a nonzero zero-mass residual-null direction produces **two distinct
invariant probability laws**.

Consequently:

    restricted residual injective
      iff
    invariantLawSet(P) is subsingleton.

The public theorem is
`restricted_injective_iff_invariantLawSet_subsingleton`.

## 4. Existence closes the semantic equivalence

Frozen P-GOA-01 already proves that every finite stochastic kernel has at least
one invariant probability law via Cesaro compactness.  The module packages this
as `invariantLawSet_nonempty`.

Therefore subsingleton is equivalent here to **existence of a unique invariant
law**:

    invariantLawSet(P).Subsingleton
      iff
    exists! mu, mu in invariantLawSet(P).

## 5. Canonical conorm interpretation

The previously merged finite-dimensional Track-S theorem gives, on a
nontrivial carrier,

    kappa1*(P) > 0
      iff
    restricted residual injective.

Combining the two equivalences yields the main theorem:

    kappa1*(P) > 0
      iff
    there exists a unique invariant probability law.

The Lean theorem is
`l1ResidualConorm_pos_iff_unique_invariant_law`.

An intermediate public surface also states:

    kappa1*(P) > 0
      iff
    invariantLawSet(P) is subsingleton.

## 6. Scientific interpretation

This identifies the qualitative meaning of the canonical Track-S residual
certificate:

- Dobrushin contraction is one sufficient mechanism for uniqueness/isolation;
- periodic dynamics may have no strict mixing and still have positive conorm;
- positive conorm means exactly that the finite kernel has one invariant
  probability law, not merely that a particular contraction proof is
  available;
- zero conorm means there is a nontrivial zero-mass invariant signed direction,
  and the constructive proof turns it into multiple invariant probability laws.

Thus the current Track-S hierarchy contracts to

    strict mixing
      => positive residual isolation
      <=> unique finite long-run invariant semantics.

The first implication is strict by the merged permutation/flip witnesses.

## 7. Boundary

The canonical greatest-finite-conorm theorem requires

    1 < card(S).

On a one-state carrier the zero-mass subspace is trivial, so every positive
lower-gain constant is vacuously admissible and there is no corresponding
greatest finite isolation constant in the same sense.  The uniqueness theorem
for invariant laws itself does not require this nontrivial-cardinality
assumption; only the final conorm equivalence does.

## 8. Governance and nonclaims

- Track S only.
- Post-FINAL / uncounted.
- No frozen P-ID change.
- No ledger/count/generator change.
- No Track-H mutation.
- No claim that the conorm value is computable from uniqueness alone.
- No claim of a uniform quantitative lower bound over all uniquely invariant
  kernels.
- No generic recurrent-class decomposition theorem is added here.
- No fifth counted primitive or generator is proposed.

## 9. Next structural interpretation

Once this equivalence is merged and audited, the already compiled local
functional-graph prototype can specialize it structurally:

    deterministic finite kernel has unique invariant semantics
      iff
    its functional graph has exactly one recurrent periodic orbit.

That lane should remain separate so the present PR contains one general
finite-Markov claim rather than mixing it with deterministic graph theory.

## 10. Local validation before commit

The integrated working tree was validated locally before any remote push:

- focused Lean compilation of
  `TopologyChangingGoaInvariantUniquenessIsolation.lean`: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS (9048 jobs)**;
- full `lake build UEOT`: **PASS (9067 jobs)**;
- `git diff --check`: **PASS**;
- proof-escape scan of the new module: **PASS**;
- axiom audit of the five public theorem surfaces: only
  `propext`, `Classical.choice`, and `Quot.sound`.

The committed exact head also passed locally before any remote push:

- Track-S research-governance validator: **PASS (3 changed paths)**;
- research-governance regression suite: **PASS**;
- frozen Compression governance validator: **PASS**;
- frozen Compression validator regression suite: **PASS**.
