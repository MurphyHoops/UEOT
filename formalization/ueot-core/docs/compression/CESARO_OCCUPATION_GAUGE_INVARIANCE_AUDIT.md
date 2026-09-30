# Cesaro Occupation Gauge Invariance Audit

Status: **LOCAL LEAN PASS / TRAJECTORY-LEVEL OCCUPATION GAUGE FORMALIZED / UNCOUNTED**

Module:

`UEOT/V3/Compression/CesaroOccupationGaugeInvariance.lean`

This lane upgrades exact GOA gauge invariance from stationary objects to the
actual long-run occupation sequence generated from an initial law.

## 1. Finite-time orbit covariance

For conjugate stochastic kernels

\[
P(s,t)=Q(e(s),e(t)),
\]

`orbit_relabel_of_conjugate` proves for every time `n`

\[
\boxed{
e_\#(\mu P^n)=(e_\#\mu)Q^n.
}
\]

The proof is by induction using the already formalized one-step conjugacy
theorem.  No long-run assumption is needed.

## 2. Cesaro occupation covariance

For the frozen `FiniteCesaroInvariant.cesaroRow`, the theorem
`cesaroRow_relabel_of_conjugate` proves for every finite horizon `n`

\[
\boxed{
e_\#\bar\mu_n^P=\bar\mu_n^Q(e_\#\mu).
}
\]

Thus occupation averaging itself is coordinate/gauge invariant, not merely its
eventual stationary limit.

## 3. Subsequence-limit covariance

`cesaro_subseq_limit_relabel_of_conjugate` proves:

if a source Cesaro subsequence converges,

\[
\bar\mu_{\phi(n)}^P\to\nu,
\]

then the corresponding target subsequence converges to exactly the relabeled
law

\[
\boxed{
\bar\mu_{\phi(n)}^Q(e_\#\mu)\to e_\#\nu.
}
\]

This matches the P-GOA-01 / M-OI philosophy directly: long-run occupation
cluster points are meaningful modulo representation gauge even when there is
no unique globally attracting invariant law.

## 4. Control adapter

`selectorCesaroRow_gaugeInvariant` applies the generic theorem to exact control
quotients related by `SemanticRelabel`, with the same deterministic selector
transported through the quotient-state equivalence.

The resulting chain is now:

\[
\boxed{
\text{semantic quotient gauge}
\to
\text{closed-loop kernel conjugacy}
\to
\text{finite orbit gauge}
\to
\text{Cesaro occupation gauge}
\to
\text{occupation-limit gauge}.
}
\]

## 5. Relation to set-valued GOA

Together with `InvariantSetGaugeInvariance.lean`, the non-Dobrushin exact lane
now has two levels:

1. **all stationary possibilities** — the complete invariant-law set is
   gauge-invariant;
2. **initial-condition-resolved long-run behavior** — the occupation sequence
   and every convergent Cesaro subsequence are gauge-covariant.

This is strictly broader than the earlier unique-GOA lane.

## 6. Boundaries

- Exact kernel conjugacy is required; no approximate occupation perturbation is
  claimed here.
- The theorem transports a given convergent subsequence but does not prove the
  full Cesaro sequence converges.
- It does not yet identify individual recurrent classes under gauge.
- No counted generator, ledger mapping, or frozen P-ID changes.

## 7. Next step

The natural next exact theorem is **recurrent-class gauge invariance**:
transport a `FiniteRecurrentDecomposition` through a state equivalence and show
that recurrent classes, class stationary laws, hitting-weight vectors, and the
resulting recurrent-mixture GOA are all preserved modulo the same gauge.

Only after that exact structure is closed should approximate P-GOA-03-style
perturbation bounds be lifted to gauge-equivalent recurrent decompositions.
