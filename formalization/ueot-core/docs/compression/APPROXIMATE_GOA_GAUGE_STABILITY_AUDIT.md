# Approximate GOA Gauge Stability Audit

Status: **LOCAL LEAN PASS / FIXED-POLICY NEAR-GOA GAUGE STABILITY ESTABLISHED / UNCOUNTED**

Module:

`UEOT/V3/Compression/ApproximateGoaGaugeStability.lean`

This lane closes the immediate gap left by `ApproximateSemanticGauge.lean`.
Two approximate quotients of the same micro control model are assumed to have
an exact quotient-state relabeling and their own certified transition-TV
defects.  A deterministic source selector is transported through that exact
state gauge.  The theorem then compares the induced closed-loop dynamics and
their stationary laws.

## 1. Coordinate discipline

The source and target quotient states use different labels.  Therefore the
source policy kernel is first reindexed into target coordinates.  Only after
this exact relabeling is it compared rowwise with the target policy kernel.

This avoids the invalid shortcut of feeding two differently labelled kernels
directly to `crossRowTV`.

`fixedPolicy_closedLoop_relabel_tv_le` proves

\[
\sup_y D_{TV}(\bar P_Q(y,\cdot),P_R(y,\cdot))
\le
\epsilon_p^Q+\epsilon_p^R,
\]

where `bar P_Q` is the source closed loop expressed in target coordinates and
the target uses the transported source selector.

## 2. Stationary near-GOA theorem

Assume the source fixed-policy closed loop has Dobrushin coefficient

\[
\alpha_Q<1.
\]

M-CF supplies a unique source invariant law `mu*_Q`.  Exact gauge relabeling
transports that law to an invariant law of the relabeled source kernel.

For **any** invariant law `mu_R` of the target closed loop under the transported
same policy, `fixedPolicy_near_goa_gauge_stability` proves

\[
\boxed{
D_{TV}(e_\#\mu_Q^*,\mu_R)
\le
\frac{\epsilon_p^Q+\epsilon_p^R}{1-\alpha_Q}
}.
\]

The target is not required to have a unique invariant law.  The perturbation
tube is therefore stronger than a theorem that assumes both sides contract.

## 3. Dependency route

The proof composes already audited infrastructure:

1. `ApproximateSemanticGauge.macroTransition_relabel_tv_le` for actionwise
   cross-quotient transition error;
2. `GoaGaugeInvariance.transportSelector` for the fixed policy;
3. exact matrix reindexing for state-label gauge;
4. `MetricGaugeInvariance` for exact TV/Dobrushin preservation under relabeling;
5. `ContractiveFixedPoint.stationary_perturbation_via_mcf` for the final
   invariant-law perturbation radius.

No counted generator is added or removed.

## 4. Critical boundary

This is deliberately a **fixed-policy** theorem.

It does not claim that small reward/transition/value errors preserve the
target's own canonical greedy selector.  A separate optimal-Q perturbation and
strict action-gap condition is required before policy identity can be promoted
from transported-policy semantics to target-greedy semantics.

Thus the valid chain is currently

\[
\boxed{
\text{approximate semantic gauge}
\to
\text{fixed-policy closed-loop row bound}
\to
\text{stationary near-GOA gauge tube}
}.
\]

The stronger chain

\[
\text{approximate semantic gauge}
\to
\text{same optimal policy}
\to
\text{optimal GOA stability}
\]

remains pending the action-gap lane.

## 5. Scientific disposition

Recommended classification:

**APPROXIMATE GOA GAUGE STABILITY: PASS.**

**COUNTED GENERATORS: unchanged at four.**

This is an out-of-sample quantitative bridge from representation/control
semantics to long-run structure.  It strengthens the bridge network without
providing evidence for a 4 -> 3 generator reduction.

## 6. Next pressure test

The next theorem should prove an optimal-Q perturbation bound under the same
exact state gauge and semantic defect assumptions.  With a strictly positive
source action gap `gamma_min`, a uniform Q-error radius `eta` satisfying

\[
2\eta<\gamma_{\min}
\]

should certify that the transported source greedy action remains the unique
target greedy action.  Only then should the present fixed-policy near-GOA tube
be upgraded to an **optimal-policy / GOA** gauge-stability theorem.
