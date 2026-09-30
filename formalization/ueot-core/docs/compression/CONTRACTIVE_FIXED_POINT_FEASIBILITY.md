# Contractive Fixed-Point Compression — Feasibility Audit

Status: **LOCAL LEAN PASS / CROSS-DOMAIN CERTIFICATE CORE / UNCOUNTED**

This audit tests the proposed M-CF compression between finite discounted
Bellman contraction and finite Dobrushin contraction.

## 1. Why a second Banach wrapper would be cosmetic

The Bellman side already uses Mathlib `ContractingWith`, which supplies:

- fixed-point existence on complete spaces;
- uniqueness;
- convergence of iterates;
- a-posteriori residual bounds;
- fixed-point perturbation bounds.

Therefore defining another metric-space contraction generator would merely
rename existing infrastructure.

The nontrivial question is whether the same certificate logic can also serve
the Dobrushin/TV side **without** first rebuilding total variation as an ambient
`MetricSpace` instance.

## 2. Minimal distance-like core

`UEOT/V3/Compression/ContractiveFixedPoint.lean` introduces a deliberately weak
interface:

`DistanceLike X` records only

- nonnegativity;
- triangle inequality;
- separation at zero.

`ContractiveWith D alpha F` adds

\[
0\le\alpha<1,
\qquad
d(Fx,Fy)\le\alpha d(x,y).
\]

No topology, symmetry, completeness, probability structure, or linear
structure is assumed.

From this alone Lean proves:

1. fixed-point uniqueness;
2. equal-time geometric iterate contraction
   \[
   d(F^n x,F^n y)\le\alpha^n d(x,y);
   \]
3. residual certificate
   \[
   d(x,x^*)\le \frac{d(x,Fx)}{1-\alpha};
   \]
4. two-map fixed-point perturbation
   \[
   d(x^*,\hat x^*)\le
   \frac{d(F\hat x^*,G\hat x^*)}{1-\alpha}.
   \]

## 3. Bellman adapter

For finite discounted control:

- `d` is the ordinary sup metric on value functions;
- `F` is the Bellman operator;
- `alpha = discount`.

The existing Bellman `ContractingWith` certificate supplies the one-step
contraction adapter.  M-CF then rederives:

- `bellman_fixedPoint_unique_via_mcf`;
- `bellman_valueError_le_residual_via_mcf`;
- `bellman_iterate_le_via_mcf`.

The residual theorem has the exact statement of the frozen Bellman stopping
certificate.

### Boundary

M-CF does not construct the Bellman operator, prove it is a contraction, prove
fixed-point existence, construct a greedy selector, or prove causal-policy
optimality.  Those remain P-CTL obligations.

## 4. Dobrushin adapter

For P-GOA-02:

- `d = lawTV` on the finite probability simplex;
- `F = step P`;
- `alpha = dobrushinAlpha P`.

The existing finite-TV results supply the `DistanceLike` laws and exact
Dobrushin one-step contraction.

M-CF then rederives:

- invariant-law uniqueness;
- the frozen stationary perturbation bound;
- the exact source-signature theorem `p_goa_02_via_mcf`, retaining P-GOA-01
  only for existence.

Thus the repeated algebra in the original uniqueness/perturbation proofs is
genuinely factored through one cross-domain certificate theorem.

## 5. Out-of-sample consequence

The new theorem

`dobrushin_iterate_to_invariant_le_via_mcf`

gives, for any supplied invariant law `mu*`,

\[
D_{TV}(P^n\mu,\mu^*)
\le
\alpha(P)^n D_{TV}(\mu,\mu^*).
\]

This theorem was not one of the frozen P-GOA-02 endpoints used to motivate the
candidate.  It is a direct generative consequence of the shared M-CF core.

## 6. Does this justify a new counted generator?

Not yet.

### Positive evidence

- two mathematically distinct domains instantiate the same weak certificate;
- the common theorem owns nontrivial proof steps, not only naming;
- P-GOA-02's uniqueness and perturbation halves become thin adapters;
- an out-of-sample geometric mixing theorem is generated.

### Blocking evidence

P-CTL-01 as a frozen source theorem is not merely fixed-point calculus.  Its
core scientific obligations include Bellman construction, finite maximization,
greedy policy realization, and optimality against the full causal randomized
policy class.

P-GOA-02 likewise still needs domain-specific proof of Dobrushin contraction,
same-input kernel perturbation, and an invariant-law existence route.

Consequently M-CF does not currently replace two frozen P-ID families in the
same way that the four counted generators do.

## 7. Relation to Mathlib

On genuine metric spaces, most M-CF conclusions are already standard
consequences of Mathlib `ContractingWith`.  The UEOT-specific value of this
experiment is therefore **not** novelty of contraction mathematics.

Its useful contribution is the typed weak interface that lets TV/simplex and
Bellman/sup-metric certificates share one proof route without forcing the
probability side into an artificial metric-space implementation.

## 8. Classification

Recommended classification:

**M-CF = VALID CROSS-DOMAIN CONTRACTIVE CERTIFICATE BRIDGE, GENERATIVE,
UNCOUNTED.**

No compression-ledger promotion is justified at this stage.  The canonical
four-generator core remains unchanged.

## 9. Architectural consequence for UEOT

The result strengthens the Control -> GOA bridge without identifying the two:

\[
\text{domain-specific evolution operator}
\to
\text{strict contraction certificate}
\to
\begin{cases}
\text{unique stable fixed structure},\\
\text{geometric error decay},\\
\text{residual/perturbation robustness}.
\end{cases}
\]

In control the fixed structure is an optimal value object; in GOA it is an
invariant law.  Their semantics remain distinct while the stability calculus
is shared.

## 10. Next candidate

The remaining high-value compression target is hierarchical alignment:

- P-ALI-02 parent directional value change;
- P-ALI-03 coordination/interpolation threshold;
- P-ALI-01 retained separately as the global integrability/no-go boundary.

The next experiment should test whether P-ALI-02 and P-ALI-03 are exact
instances of one directional-improvement calculus without weakening either
source theorem.
