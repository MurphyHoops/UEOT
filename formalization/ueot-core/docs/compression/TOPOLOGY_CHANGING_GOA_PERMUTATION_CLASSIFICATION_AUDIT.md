# Track S — deterministic permutation residual classification

Status: **MERGED UNCOUNTED / TRACK S / CANONICAL MAIN / INCLUDED IN PR #220 CLOSURE**

Counted-core impact: NONE.

## Question

The merged Dobrushin-to-conorm bridge proves strict one-step mixing is a
sufficient source of residual isolation.  The deterministic flip then proves
that it is not necessary.  The next question is whether this separation can be
explained structurally rather than by one witness.

For a finite permutation sigma, form the deterministic stochastic kernel

    P_sigma(i,j) = 1[j = sigma(i)].

The target is a complete classification inside this family.

## Global Dobrushin geometry

On every nontrivial finite state space, distinct source states are sent to
distinct point masses.  Their row total-variation distance is one.  Since no
probability-law TV distance exceeds one,

    alpha(P_sigma) = 1.

Thus global one-step Dobrushin contraction cannot distinguish any nontrivial
finite permutation dynamics.

## Residual kernel

For signed v,

    (v P_sigma)(y) = v(sigma^{-1}(y)).

Hence residual zero means exactly that v is invariant under sigma.  Such
vectors are constant on every permutation orbit.

### Single orbit

If sigma is a single cycle on the full carrier, residual-zero v is globally
constant.  Intersecting with the zero-total-mass signed subspace leaves only
v=0.  Therefore the restricted residual is injective.

### Multiple orbits

If sigma is not a single cycle, choose an orbit A and its nonempty complement
B.  Define

    v = card(B) on A,
        -card(A) on B.

Both A and B are sigma-invariant, so v P_sigma = v.  The two weights make the
total mass exactly zero, and both sets are nonempty, so v is nonzero.  This is
an explicit nontrivial zero-mass residual-kernel direction.  Restricted
injectivity therefore fails.

## Exact classification

The merged Lean theorem establishes

    restricted residual injective
      iff
    sigma.IsCycleOn univ.

Using the already merged finite-dimensional Track-S equivalence on a
nontrivial carrier,

    kappa1*(P_sigma) > 0
      iff
    sigma.IsCycleOn univ.

Together with alpha(P_sigma)=1, this gives the family-level classification:
Dobrushin sees the entire family as maximally noncontractive, while the
residual conorm detects exactly whether recurrent topology has one orbit or
multiple independent recurrent components.

## Significance

This is stronger than the flip witness:

- it classifies an infinite family of finite dynamical systems;
- it identifies the obstruction to residual isolation as a concrete
  recurrent-topology multiplicity;
- it supplies an explicit null direction when isolation fails;
- it links the operator residual language directly to orbit/recurrent-class
  structure;
- it motivates the next extension from bijective deterministic dynamics to
  general deterministic functional graphs.

## Boundaries

- No exact n-cycle conorm value is claimed in this checkpoint.
- No explicit optimal lower bound as a function of card(S) is claimed.
- No classification for non-bijective deterministic maps is claimed.
- No classification for arbitrary stochastic kernels is claimed.
- No frozen P-ID, counted generator, ledger row, or Track-H theorem changes.

## Optional quantitative extension (not required for closure)

Numerical LP checks for n=2,...,10 support

    kappa1*(C_n) = n / floor(n^2/4).

The exploratory lower-bound route uses the zero-mean identity, pairwise
differences, and shortest-path edge counting on a cycle; balanced two-level
step profiles appear to attain equality.  This remains a separate pressure
test and must not be stated as a theorem before Lean proof.

## Local validation before commit

The integrated working tree was validated locally before any remote push:

- focused Lean compilation of
  `TopologyChangingGoaPermutationClassification.lean`: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS (9047 jobs)**;
- full `lake build UEOT`: **PASS (9066 jobs)**;
- `git diff --check`: **PASS**;
- proof-escape scan of the new module: **PASS**;
- axiom audit of the five public classification surfaces: only
  `propext`, `Classical.choice`, and `Quot.sound`.

The committed exact head was also checked locally before any remote push:

- Track-S research-governance validator: **PASS (3 changed paths)**;
- research-governance regression suite: **PASS**;
- frozen Compression governance validator: **PASS**;
- frozen Compression validator regression suite: **PASS**.
