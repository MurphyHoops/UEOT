# Total conditioned kernels and homogeneous memory survival

This packet completes the existing layer-12 candidate and the R0 publication work
identified in the [2026-10-26 closure audit](../../../../../../../mathematics/review/MATHEMATICAL_CLOSURE_AUDIT_2026-10-26.md).
The Lean source fingerprint is
`2a0482a9717cc776b76383755a42b327ba132a04fbb6dfaea5c3ddb45da47b24`:
694 modules, including the original 691 modules and three additions. The frozen
106 P-IDs, four counted generators and 11/89/6 classification are unchanged.
Strong unified mathematical closure remains **NOT_ESTABLISHED**; external
scientific evidence remains **UNVERIFIED**.

## 1. Independently generated finite-window laws

For a finite safe alphabet, let $Q\ge0$, let $\eta\ge0$ be the original initial
law restricted to the safe set without renormalization, and write

$$
g_r=Q^r\mathbf1,\qquad Z_T=\eta g_T>0.
$$

The construction in `TotalFiniteWindow.lean` has initial PMF

$$
\eta_T(i)=\frac{\eta(i)g_T(i)}{Z_T}
$$

and total next-state rows

$$
R_r(i,j)=
\begin{cases}
Q(i,j)g_r(j)/g_{r+1}(i),&g_{r+1}(i)>0,\\
F_r(i,j),&g_{r+1}(i)=0,
\end{cases}
$$

where each $F_r(i,\cdot)$ is any PMF. At step $k<T$ the generated process
uses $R_{T-k-1}$. Its law is defined by PMF recursion, independently of the
conditional law that it is later proved to equal.

For every $n\le T$ and every state prefix $x_{0:n}$,

$$
P_T(x_{0:n})=
\frac{\eta(x_0)\prod_{k<n}Q(x_k,x_{k+1})g_{T-n}(x_n)}{Z_T}.
$$

The induction includes zero-mass prefixes. When $g_{r+1}(i)=0$, nonnegativity
and the recursion $g_{r+1}(i)=\sum_jQ(i,j)g_r(j)$ imply that every summand is
zero. Thus an arbitrary fallback cannot alter a positive-mass prefix.

The public endpoints in namespace
`UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.TotalFiniteWindowCheck`
are:

- `windowPathLaw_prefix_atom`: the formula for every prefix;
- `windowPathLaw_fallback_independent`: equality of generated laws through $T$
  for any two safe-row fallbacks;
- `generated_prefix_eq_actual`: the safe-alphabet generated law, embedded in
  the original alphabet, equals the original action/state experiment's
  conditional **state** prefix law;
- `generated_ambient_eq_actual` and `generated_ambient_fallback_independent`:
  total original-alphabet rows, including unsafe states, have the same result.

The conditioning event is survival through the declared horizon, and the
normalizer is that original event's mass. This is not an independently supplied
conditional-source identity. It does not reconstruct the full action history.

## 2. A real null row with positive conditioning mass

`TotalFiniteWindowWitness.lean` uses the original source
$f\to t\to\bot\to\bot$, uniform initial law and safe set $\{f,t\}$.
Consequently

$$
Q=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
\eta=(1/3,1/3),\quad g_1=(1,0),\quad Z_1=1/3.
$$

The initial unsafe mass is $1/3$ and the $t$ row has zero remaining one-step
survival. Two different null-row fallbacks nevertheless generate exactly the
same complete conditional path, $\delta_{(f,t)}$. The public endpoint
`TotalFiniteWindowWitnessCheck.null_row_actual_source_witness` consumes its
private computations; no fictitious public direct proof edges are added.

Here $Q^2=0$ and $Z_2=0$. A positive one-step window does not imply a positive
two-step window or an infinite conditioned survival process.

## 3. The actual numerical kernel of the same finite-memory controller

For a fixed original controlled numerical source $P$, the controller's action
law $\sigma(m,\cdot)$ and action/next-observation update $U$, define

$$
\bar P((x,m),(z,m'))=
\sum_a\sigma(m,a)P(x,a,z)
\mathbf1\{m'=U(m,a,q(z))\}.
$$

`HomogeneousMemorySurvival.lean` retains the original actions, reward and
discount. The survival conclusions do not use reward or discount optimality.
`augmentedModel_transitionPMF`, `closed_loop_eq_augmentedRow` and
`actual_augmentedTrajMeasure_eq_homogeneous` identify the action-conditioned
PMF, closed-loop row and full infinite trajectory measure with the already
defined actual controller experiment.

With $\bar K=\{(x,m):x\in K\}$, the original unnormalized safe initial row
$\bar\eta$ and the actual augmented killed matrix $\bar Q$,

$$
\Pr_{\rm actual}(X_0,\ldots,X_n\in K)
=\bar\eta\bar Q^n\mathbf1,
$$

and

$$
\lim_n\bar\eta\bar Q^n\mathbf1
=\Pr_{\rm actual}(\forall n, X_n\in K).
$$

The public endpoints are `actual_finite_survival_eq_killed_mass` and
`killed_mass_tendsto_actual_infinite_survival`. The latter uses the existing
same-source killed tail theorem and decreasing-event continuity. Initial
unsafe mass is retained, and the limit is permitted to be zero.

## 4. Explicit mathematical limits

- Finite-window conditioning requires $Z_T>0$ and only proves prefix identities
  for $n\le T$, including $T=0$. It does not assign a conditional probability
  when the event has zero mass.
- No cross-horizon consistency, infinite Q-process, spectral convergence or
  equality to a fixed Doob process follows from total PMF rows.
- The finite-memory survival bridge requires one fixed numerical source.
  Fixed transition support with changing numerical weights is insufficient.
- Markovity of $(X,M)$ does not imply Markovity of $X$ alone.
- No positive survival, QSD, executable exact-real sampler, executable controller
  synthesis, physical-safety premise or global-purpose claim is supplied by
  these identities. The existing physical-safety theorems retain their inputs.

## 5. Actual evidence and archive recovery

The original native/full-build records are preserved under `actual-execution`.
They include focused failed and successful compilation attempts, the original
46.555-second full build, the 86.647-second native export and 57.175-second
fixed-certificate execution, and the canonical UMC audit. Their pending status
labels remain unchanged as historical observations.

The native records contain 80 owned theorem constants: 12 public source
candidates, 27 private constants and 41 other generated public constants.
There are 27 registered direct proof edges. The 52,140 cross-layer and 66
internal stored-type comparisons have no collisions; they do not establish
general logical independence or scientific novelty.

The R0 recovery corrected one counting detail in the earlier audit: the pinned
manifest has **39 input references but 38 distinct target files**. The
registration driver has two distinct roles pointing to the same file.
Every referenced byte hash has been verified. Existing evidence, repository
bytes and a base Git blob were copied exactly; four input records were recovered
from the deterministic documented protocol adapter and checked against their
already pinned SHA values.

The pinned registered overlay is byte-for-byte unchanged. Its archived copy is
`actual-execution/native-01/REGISTERED_OVERLAY.json`. The original historical
registration receipt could not be recovered. The file now at
`actual-execution/native-01/REGISTRATION_RECEIPT.json` is explicitly a **new
2026-10-26 archive-recovery verification receipt**. It records
`registration_reexecuted=false` and
`historical_registration_receipt_recovered=false`; it is not evidence of a
new native execution or of a recovered historical review. The detailed record
is `actual-execution/recovery-20261026/RECOVERY_RECEIPT.json`.

The restored consumer checks now pass: the targeted four tests and the complete
58-test reuse suite. Source/runtime and local build acceptance for this release
are recorded separately in `RELEASE_ACCEPTANCE.json`; any failed current build
attempts remain retained alongside the successful run. Current independent
source/semantic review is recorded under `review-20261026/`; it does not rewrite
the pending states of the original execution records.

## 6. Publication and next mathematical step

The immutable Git-object preflight, candidate review and resulting-main identity
have separate receipts/PR records. GitHub's three Core workflows are disabled at
the user's request; all Lean and relevant evidence checks are local.

The next mathematical work is R1: from explicit finite support/certification
tables and initial support, compute a controller's winning actions and updates,
then prove its own actual trace support, zero uncertified occupancy and physical
safety under the existing physical premises. The current existence theorem's
`Classical.choose` action and PMF-derived initial support are still the concrete
computational gaps. This packet's survival identities do not close R1.
