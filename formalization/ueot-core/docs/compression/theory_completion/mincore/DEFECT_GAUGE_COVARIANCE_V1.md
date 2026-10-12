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

This identifies the exact target-upper/source-lower distortion of the
cross-stage contraction coefficient.

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
| general positive two-sided calibration | yes | yes, rescaled | only quasi-triangle bound established | not preserved in the exact registered form |
| positive stagewise scalar rescaling | yes | yes, rescaled | yes | yes, with covariant coefficients |

This is a genuine strengthening of the MINCORE classification: the universal
object is not an untyped defect value.  Quantitative presentations have a
gauge structure, and only a restricted gauge subgroup preserves the exact
M-TC local calculus.

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

## 7. Current validation

Before evidence-surface refresh:

- focused Lean compile of `DefectGaugeCovariance.lean`: PASS;
- public `TheoryCompletion` root build: PASS, 9,102 jobs;
- `git diff --check`: PASS.

Because the new Lean module changes the live first-party module set, the
fail-closed UMC DAG and FKRG proof-reuse evidence must be refreshed through
temporary L2 authorization before this round can close.  Historical FKRG
snapshots/overlays must remain immutable; the new evidence must be an additive
layer.

