# Track S — deterministic functional-graph classification

Status: **MERGED UNCOUNTED / PR #220 / RESULTING-MAIN FULL-GREEN**

Counted-core impact: **NONE**.

## Question

The merged finite-Markov theorem now identifies positive canonical residual
isolation with existence of a unique invariant probability law.  This lane
asks for the deterministic structural meaning of that condition for a finite
map `f : S -> S`.

The target classification is:

    positive residual isolation
      iff
    the functional graph has exactly one recurrent periodic orbit.

No generic graph-decomposition theorem is assumed.

## Deterministic kernel and recurrent core

For `f : S -> S`, define the deterministic stochastic kernel

    P_f(i,j) = 1[j = f(i)].

Lean proves the row-action identity

    (v P_f)(y) = sum_{x : f(x)=y} v(x).

Finite pigeonhole plus Mathlib periodic-point APIs then give the uniform
finite-time identity

    range(f^[card(S)]) = periodicPts(f).

Thus every state reaches the periodic recurrent core after at most `card(S)`
steps, while every periodic state has a predecessor under the same iterate.

## Residual-null structure

If `R_f(v)=vP_f-v=0`, induction on the iterate range proves

    y notin range(f^[n])  =>  v(y)=0.

At `n = card(S)`, every residual-null signed vector therefore vanishes on all
transient states.

On the periodic core, each periodic state has exactly one periodic
predecessor; all other predecessors are transient and carry zero residual-null
mass.  Hence

    v(f(x)) = v(x)

for periodic `x`, so a residual-null vector is constant on each recurrent
periodic orbit.

## Exact qualitative classification

Define `HasUniquePeriodicOrbit f` by the existence of a periodic state whose
periodic orbit contains every periodic point.

If that condition holds, any zero-total-mass residual-null vector vanishes on
transient states and is constant on the unique recurrent cycle.  Zero total
mass forces that constant to vanish, so the restricted residual is injective.

If the condition fails, Lean extracts two distinct recurrent periodic orbits
and constructs an explicit nonzero signed vector which is:

- zero on transient states;
- constant on one recurrent orbit;
- oppositely weighted on the remaining periodic states;
- exactly zero in total mass; and
- fixed by the deterministic kernel.

Therefore the local candidate proves

    restricted residual injective
      iff
    HasUniquePeriodicOrbit f.

For `1 < card(S)`, the merged canonical-conorm theorem yields

    l1ResidualConorm(P_f) > 0
      iff
    HasUniquePeriodicOrbit f.

Combining with the merged invariant-uniqueness theorem also yields

    P_f has a unique invariant probability law
      iff
    HasUniquePeriodicOrbit f.

## Deterministic Dobrushin dichotomy

The candidate additionally proves the sharp one-step dichotomy:

- if `f` is constant, `dobrushinAlpha(P_f)=0`;
- if `f` has two distinct images, `dobrushinAlpha(P_f)=1`.

Thus one-step Dobrushin contraction sees only the constant/nonconstant split
for deterministic dynamics.  It cannot distinguish one recurrent cycle from
many, while the residual conorm does exactly that.

## Interpretation

This lane aligns three Track-S languages:

1. one-step mixing — a strong dynamical mechanism;
2. residual isolation — uniqueness/isolation of stationary semantics;
3. recurrent topology — multiplicity of deterministic periodic attractors.

For finite deterministic systems, permanent periodic motion can fail strict
mixing completely and still possess unique isolated long-run semantics.

## Boundaries / nonclaims

- Finite deterministic maps only.
- No claim that arbitrary stochastic kernels possess a literal functional
  graph.
- No claim of trajectory convergence to a fixed state, aperiodicity, or
  mixing from a unique periodic orbit.
- No exact closed formula for the numerical conorm of an `n`-cycle.
- No uniform quantitative lower bound over all one-orbit deterministic maps.
- No new generic recurrent-class decomposition theorem.
- No frozen P-ID, counted generator, ledger, or Track-H change.

## Next Track-S decision

If this classification passes full local and remote audit, Track S reaches a
natural synthesis point:

    strict mixing
      => positive residual isolation
      <=> unique finite invariant semantics,

with deterministic specialization

    positive residual isolation
      <=> exactly one recurrent periodic orbit.

The next research should then be chosen deliberately between a quantitative
cycle-geometry lane (for example an exact/sharp `n`-cycle conorm) and a Track-S
synthesis/closure lane.  A new broad qualitative certificate family should not
be opened without a clear uncovered gap.

## Local validation before commit

The integrated working tree passed locally before any commit or remote push:

- focused Lean compilation: **PASS**;
- `lake build UEOT.V3.Compression`: **PASS (9049 jobs)**;
- full `lake build UEOT`: **PASS (9068 jobs)**;
- `git diff --check`: **PASS**;
- proof-escape scan of the new module: **PASS**;
- axiom audit of the six key public theorem surfaces: only `propext`,
  `Classical.choice`, and `Quot.sound`.

The committed exact head also passed locally before any remote push:

- Track-S research-governance validator: **PASS (3 changed paths)**;
- research-governance regression suite: **PASS**;
- frozen Compression governance validator: **PASS**;
- frozen Compression validator regression suite: **PASS**.

This checkpoint was accepted through the batched Track-S closure PR #220 and
is now canonical on `main@5fa6b69ad6a166c120a15f89a77f52962ad83607`.
Resulting-main Core Lean `36880543971` and Compression Guard `36880543961`
both succeeded.
