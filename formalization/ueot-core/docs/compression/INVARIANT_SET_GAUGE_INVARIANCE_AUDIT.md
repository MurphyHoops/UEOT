# Invariant-Set GOA Gauge Invariance Audit

Status: **LOCAL LEAN PASS / NONUNIQUE GOA SET FORMALIZED / UNCOUNTED**

Module:

`UEOT/V3/Compression/InvariantSetGaugeInvariance.lean`

This lane begins the promised extension beyond the unique Dobrushin GOA regime.

The previous quantitative GOA gauge results use a source contraction margin to
single out one invariant law and to obtain an attraction/perturbation bound.
That is useful but not universal: finite closed loops may have multiple
recurrent classes and therefore an entire family of invariant laws.

## 1. Set-valued GOA

For any finite stochastic kernel `P`, define

\[
\mathcal I(P)
=
\{\mu:\mu P=\mu\}.
\]

This is the full invariant-law set.  It remains meaningful with no
irreducibility, aperiodicity, contraction, uniqueness, or global mixing.

## 2. Exact conjugacy transports every invariant law in both directions

If

\[
P(s,t)=Q(e(s),e(t))
\]

for a state equivalence `e`, then

\[
\mu\in\mathcal I(P)
\iff
e_\#\mu\in\mathcal I(Q).
\]

`relabel_mem_invariantLawSet_iff` proves this equivalence by using the existing
closed-loop relabel theorem in both directions.

## 3. The entire invariant set is gauge invariant

`invariantLawSet_relabel_eq` strengthens pointwise transport to the set identity

\[
\boxed{
\mathcal I(Q)=e_\#\mathcal I(P).
}
\]

Thus, in the nonunique regime, the correct GOA object is not one arbitrarily
chosen stationary distribution.  The full stationary family is preserved
modulo state relabeling.

## 4. Control / GOD adapter

`selectorInvariantGoaSet_gaugeInvariant` applies the generic theorem to two
exact control quotients related by `SemanticRelabel` and one transported
deterministic selector.

`greedyInvariantGoaSet_gaugeInvariant` specializes it to the source greedy
selector.

Therefore the exact finite chain now has two compatible GOA layers:

1. **singleton quantitative GOA** when a Dobrushin margin proves uniqueness and
   geometric attraction;
2. **set-valued invariant GOA** for arbitrary finite closed loops.

The second strictly weakens the long-run assumptions and includes chains with
multiple recurrent classes.

## 5. Boundaries

- This is an exact gauge theorem, not an approximate perturbation theorem.
- It identifies invariant-law sets, not individual recurrent classes yet.
- It does not claim every invariant law is reached from every initial state.
- It does not replace P-GOA-03's quantitative recurrent-decomposition
  perturbation theory.
- No counted generator or frozen P-ID changes.

## 6. Next step

The next layer is **Cesaro occupation gauge**:

\[
\mu_0P^t
\quad\text{and}\quad
\bar\mu_N
\]

should commute exactly with state relabeling under kernel conjugacy.  This will
connect set-valued invariant GOA to the actual long-run occupation structures
produced from initial conditions, before moving to recurrent-class transport.
