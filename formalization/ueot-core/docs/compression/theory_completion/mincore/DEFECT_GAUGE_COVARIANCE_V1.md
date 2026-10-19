# UEOT MINCORE — Defect Gauge Covariance V1

Status: **active additive / uncounted Track-TC research**  
Counted-core impact: **NONE**  
Frozen Core impact: **NONE**

## 1. Motivation

The calibrated-defect comparison established that a positive two-sided
quantitative bridge

```text
a * d <= d' <= b * d
```

is enough to transport zero structure, exact relatedness, finite numerical
budgets, fixed-calibration asymptotic vanishing, and an already-proved M-TC
finite-horizon conclusion.

The remaining structural question is sharper:

> Which local M-TC premises themselves are covariant under a change of defect
> presentation?

The answer splits general calibration from true scalar gauge.

## 2. General two-sided calibration

For two presentations `P,Q` with `DefectCalibration P Q a b`, the new
module proves

`DefectCalibration.triangle_quasi`:

```text
P(x,z) <= P(x,y) + P(y,z)
    =>
Q(x,z) <= (b/a) * (Q(x,y) + Q(y,z)).
```

Thus a generic two-sided calibration transports triangle control, but only
with an explicit condition factor.  It does not justify silently reusing the
exact coefficient-1 triangle premise.

For adjacent stages with calibrations `(a0,b0)` and `(a1,b1)`,
`calibrated_cross_stage_contraction` proves

```text
P1(u,v) <= L * P0(x,y)
    =>
Q1(u,v) <= (b1/a0) * L * Q0(x,y).
```

This gives the guaranteed target-upper/source-lower bound factor for the
cross-stage contraction coefficient. It does not assert that this factor is
optimal for a particular pair of presentations.

## 3. Positive scalar gauge

A narrower transformation,

```text
Q_n = c_n * P_n,   c_n > 0,
```

has stronger structure.  The module proves:

- `rescale_triangle_preserved`: the coefficient-1 triangle inequality is
  preserved exactly at every stage;
- `rescale_contraction_transformed`: the contraction coefficient transforms
  as
  `L'_n = (c_{n+1}/c_n) L_n`;
- `rescale_local_budget_transformed`: the local budget transforms as
  `epsilon'_n = c_{n+1} epsilon_n`.

Therefore positive scalar rescaling is a genuine gauge class for the full
registered M-TC premise family.

## 4. Full weighted-chain covariance

`rescaled_weighted_chain_bound` transports every local premise and then
invokes the registered
`UEOT.V3.Compression.TransportCertificate.weighted_chain_bound` directly.

Its transformed finite-horizon certificate uses

```text
L'_t = (c_{t+1}/c_t) L_t
epsilon'_t = c_{t+1} epsilon_t.
```

No weighted recurrence is reproved in the MINCORE layer.

## 5. Structural conclusion

The current mathematical picture now separates two notions that must not be
conflated.

| Change of presentation | Exact zero/relation | finite budgets | exact triangle | M-TC premise class |
|---|---:|---:|---:|---:|
| general positive two-sided calibration | yes | yes, rescaled | only quasi-triangle bound established | exact registered form not guaranteed by calibration alone |
| positive stagewise scalar rescaling | yes | yes, rescaled | yes | yes, with covariant coefficients |

This strengthens the sufficient covariance results for quantitative defect
presentations: positive scalar gauges preserve the exact M-TC local calculus,
while a general two-sided calibration alone gives the displayed weaker bound.
The scalar result is a sufficient subclass, not a necessary condition or an
exhaustive classification of transformations preserving the local premises.

## 6. Non-claims

This work does not establish:

- reduction or deletion of `M-TC-01`;
- that every bi-Lipschitz-equivalent defect preserves exact triangle structure;
- that the displayed quasi-triangle factor is optimal for a particular pair;
- universal physical Ω;
- unique physical Π/Φ dynamics;
- universal GOD/GOA;
- objecthood uniqueness;
- full C1-C7 closure;
- full Unified Mathematical Closure.

The four counted generators remain
`{M-QD-01, M-TC-01, M-PE-01, M-OI-01}`.

## 7. Validation and evidence refresh

The source was rechecked in an isolated Lean 4.33.1 / pinned-Mathlib worktree:

- focused/public `TheoryCompletion` build: PASS, 9,102 jobs;
- official `lake build UEOT`: PASS, 9,342 jobs;
- exact source remains pinned by the additive
  `DEFECT_GAUGE_REUSE_OVERLAY_V1.json` and its Lean certificate;
- the native certificate checks the six new types against 3,811 prior
  registered theorem types (22,866 comparisons), plus 15 internal pairs:
  zero definitional type matches;
- compiled proof terms certify six registered direct edges, including the
  terminal call to the existing M-TC weighted-chain theorem;
- the live DAG and source-hash census cover 636 bundled modules:
  625 UEOT-maintained plus 11 adapted upstream;
- FKRG source/index regressions: 17/17 PASS; reuse regressions: 17/17 PASS;
- the immutable 68-row source-clone snapshot reproduces unchanged;
- `git diff --check`: PASS.

The refresh consumes the exact existing-path authorization merged in #328.
The two prior overlays and the original source snapshot remain byte-identical;
this round adds a third pinned overlay and certificate. Kernel type identity,
registered proof dependence, source text similarity and scientific adequacy
remain separate judgments. The source-level independent review corrected
sufficiency/necessity and optimal-constant wording without changing any Lean
statement. PR and resulting-main checks are recorded on #327; this source
checkpoint does not predict their outcome.
