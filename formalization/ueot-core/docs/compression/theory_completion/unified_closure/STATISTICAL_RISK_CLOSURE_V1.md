# Statistical Risk Closure: Same Source, Same Experiment, Same Deployment Contract

Research increment from canonical Core `0c093e9fae990d6ef8d670163b84ec93bd6fb025`,
locally integrated against canonical main `78852812650eff0a4803596bf3379d4d792122d0`
after governance PR #339.
The predecessor finite-horizon path construction is documented in
[Finite-Horizon Risk Audit](FINITE_HORIZON_RISK_AUDIT.md).
This increment connects its deterministic calibration premises to actual
finite-sample experiments and makes the microscopic failure semantics explicit.

**Verification stage:** all five production modules have passed local Lean
compilation and independent mathematical source review. The complete public
`lake build UEOT` passed with 9,352 jobs. Native export and the fixed dependency
certificate both executed successfully, with exact equality of their complete
JSON outputs. The final source matches every recorded module and root-import
hash. All 19 local integration gates passed: the first 14 passed in the original
run; an external GitHub 503 interrupted historical receipt verification, and
the remaining five passed after retrying with the same Core inputs and
historical receipts. The original failure record is preserved. The immutable
baseline's existing 89 preflight regression tests also passed. Git candidate
checks, remote research review, CI and merging are tracked in the associated
Git/PR records rather than inferred from this local result.

The [full local audit receipt](STATISTICAL_RISK_LOCAL_AUDIT_V1.json), SHA256
`399f7c4fbe084c4ebd78510a3c772b1de8535ae803b299184d2664fb0a038bb4`,
covers 47 UMC modules and 471 compiler theorem constants: 266 confirmed public
source candidates, 22 private constants and 183 other native public constants.
All 471 axiom closures contain only standard axioms. The broader Compression
audit separately passed for 3,655 native theorem constants, including 265
private constants, and all 192 ledger witnesses. These different scopes must
not be conflated with the five-module evidence census in §6. The 646-module
import graph is acyclic, complete and reachable; this does not establish
empirical applicability or global scientific closure.

## 1. The precise implication being added

Fix finite microscopic states `X`, actions `A`, an actual time-indexed source
model `M`, sample count `N > 0`, horizon `T`, tests `f(t,i)` valued in `[0,1]`,
and nonnegative radii `rho(t)`. A probability space `(Omega, mu)` supplies samples
`Z(t,a,x,k)` whose law is the actual source row `P_t(x,a)`. Samples within each
row are mutually independent; different rows may be dependent. The tests,
source, horizon, count and radii are fixed before the data.

The pointwise identity `finiteKernelRowPMF_trueRisk` derives the population test
mean from the same source mass table used by the dynamic proof. This is a proved
identity, not an extra model-matching assumption. The simultaneous event is

$$
G=\left\{\omega:\ \forall t<T,a,x,i,\quad
\left|\mathbb E_{P_t(x,a)} f_{t,i}
-\frac1N\sum_{k=1}^{N}f_{t,i}(Z_{t,a,x,k}(\omega))\right|\le\rho_t\right\}.
$$

Finite measurable sums and intersections prove that `G` is measurable. The
existing bounded-loss two-sided Hoeffding theorem and a finite row union bound
then give

$$
\mu(G^c)\le\alpha_N
:=\sum_{t<T,a,x}2|I|\exp(-2N\rho_t^2).
$$

A value of `alpha_N` above one is a valid but uninformative upper bound. This is
confidence over the training experiment, not a deployment-path failure rate.

On this **one event**, every subsequent representation, prototype, initial law
and common causal policy satisfying the chosen deterministic checks has the
stated path/risk guarantee. Pointwise universal quantification over choices on
an explicit measurable `G` does not assume the space of all choices, or an
arbitrary data-dependent selector, is measurable.

## 2. Two reference models and their different costs

### 2.1 Sparse tests and a true representative row

Choose a setoid partition, its reachable classes, and an actual section `r`.
Reconstruct every class indicator from the fixed tests with uniform residual
`delta(t)` and coefficient `l1` norm at most `kappa(t)`. Check that empirical test
means in each selected fibre differ by at most `eta(t)`. If there are `m` classes,

$$
\epsilon_t=\min\left\{1,\frac m2
\left[2\delta_t+(\eta_t+2\rho_t)\kappa_t\right]\right\}.
$$

The comparison row is `Q_t(c,a) = q# P_t(r(c),a)`. Two statistical errors occur
because two true rows are compared. The construction reuses the existing SISC
indicator-reconstruction and calibrated finite-PMF TV results. The reference
still contains true unknown rows; its event probability requires calculation or
additional certification in an empirical application.

### 2.2 Full microscopic event tests and an empirical reference row

`empiricalResponsePMF` pushes the uniform PMF on the `N` sample indices through
the observed outcomes, counting repeated samples correctly. Its measure equals
the existing P-STAT-01 empirical measure. The fixed library is now `Finset X`,
with cardinality `2^|X|`, so the same calibration construction proves

$$
\operatorname{TV}(P_t(x,a),\widehat P_{t,x,a})\le\rho_t
\quad\text{on }G.
$$

After observing the data, select finite `Y`, `q : X -> Y`, and prototypes
`r : Y -> X`, and form the **data-built** reference

$$
\widehat Q_t(y,a)=q_\#\widehat P_{t,r(y),a}.
$$

The deterministic check is

$$
\operatorname{TV}(q_\#\widehat P_{t,x,a},\widehat Q_t(qx,a))\le\eta_t.
$$

TV contraction and the triangle inequality then give
`epsilon(t) = min(1, rho(t) + eta(t))`. Only one statistical error occurs because
the comparison endpoint itself is empirical. The direct check makes a section
identity unnecessary for this bound; a stronger quotient interpretation can
require it separately. The full-event confidence cost must not be replaced by
the sparse-test count. No additional union over later choices of `q`, `r` or the
common policy is used.

## 3. Actual paths and microscopic failure

Both routes use the actual microscopic `causalLaw`, its state/action history
projection, and the comparison `causalLaw` from exactly the projected initial
law. Both controllers read the same coarse history and use the same randomized
action law. Hidden-state information is not supplied to only one controller.
The actual projected process may be history-dependent; it is not assumed to be
an exact state-only Markov quotient.

Existing P-DYN-03, through the predecessor finite-prefix adapter, gives

$$
\operatorname{TV}(q_{\mathrm{hist}\#}\mathbb P_{P,\pi},
                   \mathbb P_{Q,\pi})
\le B_T:=1-\prod_{t<T}(1-\epsilon_t)
\le\sum_{t<T}\epsilon_t.
$$

For microscopic event `E` and coarse event `F` with
`E` contained in the history preimage of `F`, the new failure bridge gives

$$
\mathbb P_{P,\pi}(E)
\le\min\{1,\mathbb P_{Q,\pi}(F)+B_T\}.
$$

For state failure `badX`, `riskEverFailure` includes the initial state and every
state reached by the `T` transitions. The constructed conservative label

$$
\operatorname{badY}(y)\iff\exists x,\ q(x)=y\ \land\operatorname{badX}(x)
$$

is proved to cover all microscopic failures and to be minimal among labels
with this pointwise coverage property. This is not a probability-optimal label
for a specified initial law. If every fibre contains a bad state, the canonical
coarse envelope is the whole alphabet and can give a vacuous risk bound.

At `T = 0`, the comparison has the same projected initial law and path budget
zero. Initial failure remains part of the event; the theorem does not infer
initial safety. Statistical certificates exclude `N = 0` through `hN`.

## 4. A concrete selection failure

[StatisticalRiskBoundary.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskBoundary.lean)
constructs two actual Bernoulli action rows with failure probability `3/4`, and
one training sample from each row under their genuine product PMF. For either
fixed action, empirical calibration error greater than `1/4` has probability
`1/4`. Select an empirically safer action using those same observations. The
probability of calibration error becomes **`7/16`**, and on precisely that event
the empirical-plus-`1/4` upper bound understates the actual selected row's risk.

This is an exact PMF calculation. It is not an assertion that the one-sample
Hoeffding bound is useful at this radius, and it is not an online adaptive-sampling
counterexample. It shows why separate pointwise coverage cannot replace the
simultaneous event used by the positive certificates.

## 5. Constructed nontrivial experiment

The witness uses one four-state model `X = Bool x Bool`, visible bit first and
persistent hidden bit second, with Boolean actions. The next visible failure
probability is

$$
p(z,a)=\frac1{16}+\frac{\mathbf1_z}{8}+\frac{\mathbf1_a}{8}.
$$

The coarse map drops the hidden bit. Its within-fibre test gap and its action
response are both genuinely nonzero (`1/8`); the chosen partition is proved
not stable. The example therefore does not assume exact lumpability to obtain
an approximate result.

The sampling probability space is the finite product of actual source-row PMF
measures, with sample variables given by coordinates. Marginal source laws,
measurability and row independence are derived from this construction using
the existing P-STAT-06 coordinate-independence interface. This demonstrates
mathematical realizability of the sampling hypotheses; physical access to
arbitrary source rows remains an experimental requirement.

There are 16 rows at `T = 2`, two fixed class-indicator tests, and `N = 4096`
samples per row. Set `rho = 1/32`, `delta = 0`, `kappa = 1`. The confidence
budget is exactly `64 * exp(-8)`, proved at most `1/4`. Thus the measurable
simultaneous event has probability at least `3/4` and is nonempty. On that
same event, the empirical fibre fit is derived to be at most `3/16`, giving
row budget `1/4` and two-step budget `7/16`.

Choose the shared constant action `false`, prototypes with hidden bit `false`,
and an initial source law with visible bit `false` and a uniformly distributed
hidden bit. Each reference transition has visible failure probability `1/16`.
The action is not called safe: failure remains possible. The reference also
allows recovery; the ever-failed event is not replaced by an absorbing process.

The exact two-step reference event probability is derived from the actual
`causalLaw`, its pointwise history mass and a finite sum:

$$
\mathbb P_{Q,\pi}(\text{ever failed by step }2)
=1-\left(\frac{15}{16}\right)^2=\frac{31}{256}.
$$

The existing P-FAC-01 `causalLaw_transport_equiv` identifies this Boolean
reference calculation with the reference law on the reachable quotient classes.
It changes coordinates within the reference model; it does not assert that the
non-stable microscopic partition admits exact dynamic descent. The generic
microscopic failure bridge then gives, on the same measurable `G`,

$$
\mathbb P_{P,\pi}(\text{ever failed by step }2)
\le\frac{31}{256}+\frac7{16}
=\frac{143}{256}<1.
$$

`joint_statistical_microscopic_risk_witness` combines non-stability, the strict
numerical bound, `mu(G) >= 3/4` and the pointwise deployment-risk guarantee in
one theorem. This is a nonvacuous fixed-policy instance of the uniform
certificate. It does not claim that the data-selected policy is optimal, or
integrate training and deployment into an unspecified joint probability law.

## 6. Source map and genuine reuse

| Added source | Main new responsibility | Existing interface consumed |
|---|---|---|
| [StatisticalRiskCalibration.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskCalibration.lean) | Actual sample means, measurable simultaneous event and uniform sparse-reference risk certificate | `BoundedLossTwoSided.measure_exists_candidate_bad_le`, SISC source expectation, calibrated representative path risk |
| [EmpiricalReferenceRisk.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/EmpiricalReferenceRisk.lean) | Normalized empirical rows, full-event TV and data-built reference risk | P-STAT-01 empirical measure, finite-event TV characterization, TV contraction and triangle |
| [MicroscopicFailureRisk.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/MicroscopicFailureRisk.lean) | Conservative failure envelopes, least state label and actual microscopic risk | Same-policy projected-path error and measurable event transfer |
| [StatisticalRiskBoundary.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskBoundary.lean) | Actual optimistic-selection counterexample | Existing normalized PMF and causal extension constructors |
| [StatisticalRiskWitness.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/StatisticalRiskWitness.lean) | Constructed product experiment, exact reference event and nonvacuous microscopic risk | P-STAT-06 product independence, P-FAC-01 causal-law coordinate transport, new calibrated representative certificate |

This table explains source-level composition. The separately executed native
verifier confirms 91 direct registered proof edges from 73 public source theorem
candidates. For example, the row confidence bound directly consumes
`BoundedLossTwoSided.measure_exists_candidate_bad_le`, the product experiment
directly consumes `coordinate_iIndep`, and reference path transport directly
consumes `causalLaw_transport_equiv`. The final joint theorem reaches these
interfaces through intermediate results; they are not all its direct edges.

The verifier also independently enumerates all 126 theorem constants owned by
the five source modules: 73 public source candidates, 11 private constants and
42 other nonprivate constants. The last group contains three named probability
instances and 39 generated helpers/equations; it is not a count of additional
handwritten theorems. Each of the 126 constants passes transitive axiom checking
against `propext`, `Classical.choice` and `Quot.sound`. Compiled type displays, stored universe
parameters, direct constants and source ownership are retained for all of them,
so private helper chains remain visible even when a public registered edge
list is empty.

There are 282,145 cross-snapshot and 2,628 internal raw-type comparisons, with
zero matches. This uses the established `Meta.isDefEq` protocol on stored types
and their original universe parameter names. It is not a mathematical novelty
claim or a test of all possible logical equivalences. The 646-source duplicate
scan reproduces the historical 68 entries exactly.

The new [native result](../knowledge/reuse/STATISTICAL_RISK_NATIVE_V1.json),
[fixed certificate](../knowledge/reuse/VERIFY_STATISTICAL_RISK_OVERLAY_TYPES.lean)
and [source-bound overlay](../knowledge/reuse/STATISTICAL_RISK_REUSE_OVERLAY_V1.json)
record these scopes separately. Existing immutable evidence is preserved.

## 7. Philosophical feedback and remaining scientific obligations

The original philosophical paper and mathematical manuscript were read directly,
with source hashes, PDF page/line locations and exact theorem endpoints recorded
in [Philosophy–Mathematics Feedback V1](PHILOSOPHY_MATHEMATICS_FEEDBACK_V1.md).
The [revised continuous Core manuscript](UEOT_CORE_PHILOSOPHY_REVISED_V1.md)
incorporates these mathematical constraints into the original argument.

The supported unity is a chain of compatible descriptions of one specified
process, not the unrestricted truth of a topology, two-drive or unique-attractor
postulate. Precise all-times viability results already exist under their own
safe-initial-support and preserving-controller conditions; finite calibrated
risk does not supply these conditions automatically. The real absorbing-leakage
counterexample remains relevant even for arbitrarily small fixed row error.

Remaining application obligations are source-law matching, a valid row-sampling
protocol, calculation or certification of the reference event probability, and
an appropriate failure label/envelope. Online dependent trajectories, postselected
tests/radii/time, deployment drift, and a measurable data-dependent joint
training/deployment law require additional results. Reproduction, physical
self-manufacture, subjective experience and normative value do not follow from
this finite-risk chain.

No counted generator, 106-P-ID status, frozen proof surface, historical receipt
or global scientific-closure status is promoted by this increment.
