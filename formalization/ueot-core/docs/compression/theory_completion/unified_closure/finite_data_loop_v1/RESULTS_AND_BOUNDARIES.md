# Finite data, allowed actions, and the same source's conditional path

Status: same-source mathematics and the complete registered batch verified.
Current publication/continuation status is maintained in Core issues #146/#302
and the original GI CONTINUE entry; this scientific record is immutable.

The known-exact-source certificate is extended to an unknown real four-parameter
family. The actual returned preparation/action table has a finite-data conditional
path certificate. Its target is the TRUE source's own original risk-baseline
experiment conditioned on the original safety event, not an arbitrary fitted law.

## One experiment throughout

States are 0, 1 and absorbing cemetery 2; safe states are 0/1. Initially the two
safe states have probability 1/2 each. The allowed actions are exactly risk, a0,
a1. Risk from i has row `(ri/2,ri/2,1-ri)`; a0/a1 from either safe state have rows
`(1-e0,0,e0)` / `(0,1-e1,e1)`. The registered box is
`r0∈[2/3,5/6], r1∈[1/6,1/3], e0,e1∈[0,1/20]`. Deployment observation is constant.
Training alone has the declared reset/readout rights for four Bernoulli probes.
The source structure and training-source match remain model assumptions.

`FiniteDataConditioned.target_eq_actual` derives the conditioned target from this
same original source. With `m=(r0+r1)/2`, its survival mass is `m^T`; at positive
T the complete target has T factors of `nu=(r0,r1)/(r0+r1)` and a final fair factor.
At T=0 the original initial law is retained. Positivity is structural and does
not depend on a rare-event empirical mass gap.

The data-only selector uses the four raw means. It prepares once with a0/a1
weights `nu_hat`, then uses `nu_hat` for T-1 steps and fair weights on the final
step. Risk has zero weight. Preparation is one actual allowed operation; no
retry or selection of successful preparations occurs. Actual operations number
T+1. The comparison window is `(X1,...,X(T+1))` after preparation; failures remain.
`FiniteDataLiteral.full_experiment_window_eq_literal` proves this projection
from the full original-state/preparation/future-action record.

## Guarantees and the information they require

Every literal preparation row and action table is checked against its own
computed estimate; `FiniteDataCertifiedConsumer.full_record_statistical_certificate`
then proves the guarantee for that SAME table. No choice-based replacement policy
is used. The true prepared distribution is constructed from the true source and
literal action, rather than passed as a known initial PMF.

On the simultaneous four-probe event Good, coordinate errors are at most
`delta=1/250`. The main certified path bound is

```
beta_prep,T(D) = min(1, (T+1) max(ehat0,ehat1)
                      + (T+1) delta + T delta/(rhat0+rhat1)).
```

Initial/row TV error propagates through the existing finite causal path
interfaces. Only genuinely positive target histories require a residual;
empirical zero counts are never interpreted as true unreachable states. The
zero-noise limit recovers equality of the same complete path.

The general same-event route is also proved in `FiniteDataGeneralRoute`: its
baseline error is at most `T delta`, and conditional error pays the reference
survival mass `mhat^T`. Structural rank-one stability replaces this rare-event
factor by `T delta/(rhat0+rhat1)` in the main consumer. The previous general
conditional-stability result and its sharp rare-event boundaries are unchanged.

`FiniteDataCalibration` constructs the actual four transition-derived probe
laws, raw estimator and fixed product experiment. Each record has four probes
with n=262144 each. The scalar budget `8 exp(-8.388608)<1/300` is proved without a
state-subset or selected-candidate factor. The three-record calibration union
is at most 1/100; the same Good event controls both registered horizons.

At the fixed gate `beta≤1/5`, `FiniteDataJoint.registered_joint_failure_le` proves
`P(Accept AND complete-path Fail)≤76/375`. This is a joint training/selection/
deployment event, not `P(Fail|Accept)≤1/5`. It is an individual deployment bound,
not a bound on the union of all registered deployment failures. Good is quantified
in the proof and never supplied as an observed Boolean to the selector.

## Boundaries in this same family

- All risk parameters in the box with `e0,e1≤1/200`, including positive noise,
  pass the T2/T10 ideal gate on Good. Both gates jointly have acceptance probability
  at least 299/300 under the declared sampling model; machine failure is excluded
  from that ideal probability and retained separately by the executable.
- At `e0=e1=1/20`, every allowed action has a failure floor. T10 failure is at least
  `1-(19/20)^10>1/5`. Data provide a Good-conditional statistical no-go using
  `min(1/6,max(0,ehat0-delta),max(0,ehat1-delta))`; no solver failure is a no-go.
- Without preparation, the main risk point `(3/4,1/4)` has initial full-path TV
  floor 1/4 for every future causal state kernel. The entire risk box has floor
  1/6; that weaker floor does not reject the entire box at threshold 1/5.
- At the same low-noise source `e0=e1=1/200`, T45 failure is at least
  `1-(199/200)^45>1/5`. This is a known-parameter mathematical boundary; the
  registered short-horizon data are not represented as having certified it.
- A uniform positive action-failure floor forces survival to zero as T grows.
  Separate finite-horizon controllers do not imply an infinitely safe controller.

These are conditional mathematics for a declared finite model. Packed-bit parsing
and the simulator/PRNG connection to the mathematical iid product law are explicit
host/experiment boundaries. No physical source calibration, ontic identity,
empirical mechanism discovery, or unique purpose has thereby been established.
Strong global closure remains NOT_ESTABLISHED and external science UNVERIFIED.
C5 noisy independent anchors, general source drift and other open ports retain
their separate activation conditions; this program does not activate them.


## Actual registered result

The complete batch was frozen before sampling under FREEZE SHA256
`c36184c21e195ba17500d82d511f84430cd3ec929020d2d43387ffb39ce9f69e`.
Exactly 3,145,728 Bernoulli results were saved and independently recounted.
There was one registered draw, no replacement seed, retry, added sample, or
threshold change. All three records and all five decisions are retained.

| Record | Window | Actual Lean status | Certified budget / lower bound | Independent true path TV |
|---|---:|---|---:|---:|
| A | 2 | CONDITIONAL_STATISTICAL_APPROX | upper 0.0355211 | 0.0149251 |
| A | 10 | CONDITIONAL_STATISTICAL_APPROX | upper 0.1409145 | 0.0536454 |
| B | 2 | CONDITIONAL_STATISTICAL_APPROX | upper 0.0313916 | 0.0105630 |
| B | 10 | CONDITIONAL_STATISTICAL_APPROX | upper 0.1257601 | 0.0376745 |
| C | 10 | STATISTICAL_NO_GO | lower 0.3735897 > 0.2 | rejected, no deployment |

Displayed decimals are for reading only; saved candidates, emitted Lean and the
independent evaluation retain exact rational values. Every positive proof binds
its literal preparation/table, reference prepared distribution and computed
initial/row residuals, and proves their fine reference path bound as well as the
main true-source statistical bound. The saved decision, actual complete trace,
sampling receipt, all raw data, actual Lean file and Core/driver identities are
checked before and after actual build/proof. All five actual build/proof runs
succeeded with every binding checkpoint true.

A uses true `(3/4,1/4,1/200,1/200)`; B independently uses
`(4/5,1/5,1/300,1/250)` and a separate record; C uses
`(3/4,1/4,1/20,1/20)`. Truth is read only by generation/evaluation, never selection.
The matrix-recursion evaluator and the independently written product-factor
checker agree exactly on all safe/dead complete-path masses. The four accepted
single realizations happened not to fail; this is not evidence of zero risk.
Preparation failures remain possible and are included in the computed laws.
The retrospective simulation Good diagnostics are not selector inputs and do
not replace the theorem's sampling/source assumptions.

Exact normal/failure provenance and the five bound proofs are in
`actual-execution/registered-batch-01`, `certified-registered-01`, and the two
actual evaluation receipts. The frozen private simulation seeds/true parameters
are retained for reproducibility and never opened by the data-only selector.

## Execution and release evidence

The source package contains `selector.py`, separate truth-owning `batch.py`,
`emit_data.py`, `certify_data.py`, deterministic checks and the pinned reused
native/integration protocol. `batch.py --freeze` precedes `--sample`; exclusive
markers prohibit a replacement registered draw. All records and rejections are
retained. A lawful implementation repair may replay saved bits without a new draw.

The old exact runner binding repair is documented in [A_BINDING_REPAIR.md](A_BINDING_REPAIR.md),
merged separately in PR389 after authorization PR388. Normal exact mathematical
results remain valid. Bound artifact changes, missing files or unsuccessful
actual Lean checks remain UNKNOWN. Hash checkpoints state their actual endpoint
detection scope and do not claim protection against arbitrary same-permission
change-and-restore attacks.
