# TV / Dobrushin Metric Gauge Invariance Audit

Status: **LOCAL LEAN PASS / MIXING-CERTIFICATE GAUGE INVARIANCE ESTABLISHED / UNCOUNTED**

Module:

`UEOT/V3/Compression/MetricGaugeInvariance.lean`

This lane upgrades the preceding unique-GOA gauge theorem from qualitative
identity/uniqueness to quantitative stability-certificate invariance.

## 1. Question

The previous lane proved that conjugate optimal closed loops have invariant
laws related by the quotient-state relabeling.

That did not yet prove that the numerical metric certificate used by M-CF is
itself representation independent.

The present lane asks:

> under a finite state equivalence, do the canonical TV distance, row TV,
> Dobrushin coefficient, and geometric mixing bound remain numerically exact?

The answer is yes.

## 2. Canonical TV is preserved

The proof does not introduce an L1 proxy.  It stays with the event-supremum TV
already used throughout P-GOA-02 and the exact-control code.

For one finite state equivalence `e`, `simplexPMF_relabel` proves

\[
\operatorname{PMF}(e_\#\mu)
=
\operatorname{PMF}(\mu).\operatorname{map}(e).
\]

UEOT's existing theorem `TotalVariation.tvDist_map_measurableEquiv` then gives

\[
D_{TV}(e_\#\mu,e_\#\nu)=D_{TV}(\mu,\nu).
\]

This is `lawTV_relabel`.

No factor of two or normalization convention changes appear.

## 3. Row laws of conjugate kernels

For stochastic matrices satisfying

\[
P(s,t)=Q(e(s),e(t)),
\]

`rowPMF_relabel_of_conjugate` proves that the target row at `e(s)` is exactly
the PMF pushforward of the source row at `s`.

Therefore

\[
\operatorname{rowTV}_Q(e(s),e(t))
=
\operatorname{rowTV}_P(s,t).
\]

This is `rowTV_relabel_of_conjugate`.

## 4. Dobrushin coefficient

The finite coefficient is the maximum pairwise row TV:

\[
\alpha(P)=\max_{s,t}D_{TV}(P_s,P_t).
\]

Because `e` is bijective and every row-TV pair is preserved,

`dobrushinAlpha_relabel_of_conjugate` proves the exact numerical identity

\[
\boxed{\alpha(Q)=\alpha(P)}.
\]

Hence the condition `alpha < 1` is itself quotient-gauge invariant.

## 5. Geometric mixing certificate

Assume

\[
\alpha(P)<1
\]

and let `mu*` be invariant for `P`.

Using the previous closed-loop step conjugacy plus M-CF,

`geometricMixing_relabel_of_conjugate` proves

\[
D_{TV}
\left(
Q^n(e_\#\mu),e_\#\mu^*
\right)
\le
\alpha(P)^nD_{TV}(\mu,\mu^*).
\]

The right-hand side is exactly the source certificate:

- same contraction coefficient;
- same initial TV distance;
- no relabeling penalty;
- no extra approximation term.

## 6. Exact-control adapter

For two exact control quotients related by `SemanticRelabel`, the previous lane
already proved that the source greedy selector and its transported target
selector induce conjugate policy matrices.

`greedyDobrushinAlpha_gaugeInvariant` therefore proves exact equality of their
Dobrushin coefficients.

`greedyGeometricMixing_gaugeInvariant` then constructs a source invariant law
through M-CF and proves, for every initial source law and every time `n`, both:

\[
D_{TV}(P_Q^n\mu,\mu_Q^*)
\le
\alpha^n D_{TV}(\mu,\mu_Q^*),
\]

and

\[
D_{TV}
\left(
P_R^n(e_\#\mu),e_\#\mu_Q^*
\right)
\le
\alpha^nD_{TV}(\mu,\mu_Q^*).
\]

Thus the complete finite M-CF mixing certificate is state-label gauge
invariant.

## 7. What this establishes

The verified exact chain is now:

\[
\boxed{
\text{SameFibers}
\to
\text{control-semantic gauge}
\to
\text{optimal closed-loop conjugacy}
\to
\text{unique GOA gauge invariance}
\to
\text{TV / Dobrushin mixing-certificate gauge invariance}
}.
\]

This is stronger than saying that two quotient models are "the same up to
renaming" informally.  The numerical long-run stability rate used in the formal
GOA theorem is also unchanged.

## 8. Boundaries

### Exact finite conjugacy

All metric equalities are exact and finite.  Approximate conjugacy requires
perturbation bounds rather than equality and remains a separate problem.

### Transported optimal selector

As before, target dynamics use the transported source greedy selector.  It is
Bellman-optimal, but canonical greedy implementations may differ on ties.

### Dobrushin remains a sufficient route

Gauge invariance of the Dobrushin coefficient does not make strict Dobrushin
contraction necessary for meaningful long-run structure.

### No new generator

The result composes:

- quotient/semantic gauge from M-QD-derived structure;
- P-CORE policy-induced kernels;
- canonical TV;
- the existing uncounted M-CF bridge.

It does not reduce the counted four-generator core.

## 9. Scientific disposition

Recommended classification:

**GOA STABILITY-CERTIFICATE GAUGE INVARIANCE: PASS.**

**COUNTED GENERATORS: unchanged at four.**

The significance is structural: both the long-run object and the quantitative
certificate of attraction to that object are invariant under exact quotient
state gauge.

## 10. Next pressure test

The exact gauge program is now close to saturation.  The next scientifically
stronger direction is **approximate semantic gauge stability**:

1. replace exact `SameFibers` / semantic conjugacy by a small representation
   mismatch plus explicit reward/transition defect envelopes;
2. transport those defects into control value/policy error;
3. combine M-TC and M-CF perturbation bounds;
4. obtain a quantitative near-GOA comparison between approximately aligned
   representations.

Representation mismatch alone must not be treated as semantic closeness; the
additional reward/transition hypotheses are essential.
