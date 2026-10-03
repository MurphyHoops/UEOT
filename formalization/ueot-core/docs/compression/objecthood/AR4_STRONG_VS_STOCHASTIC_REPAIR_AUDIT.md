# Track O / AR4 — Strong vs Stochastic Repair Audit

Status: **LOCAL AR4 CLEAR — stage gate passed before commit**

Tracker: #238. Counted-core impact: **NONE**.

## Inclusion

Every `StrongRepairable` state is finite-expected-hitting repairable under the
existing descending repair policy. This follows from the previously proved
rank bound on canonical expected hitting time, so AR4 obtains a direct
inclusion from strong support-safe finite-rank repairability into deterministic
stationary stochastic repairability.

## Strict separation witness

AR4 also formalizes a two-state geometric-retry system. `true` is the target;
from `false`, the only action samples the uniform distribution on `Bool`, so a
failed repair attempt can remain at `false` and another attempt is possible.

A concrete physical repair certificate with potential `2` at `false`, `0` at
`true`, and drift `1` proves finite expected hitting time from `false`. However,
the strong repair iteration never admits `false`, because the unique action's
support contains `false` itself at every finite rank. Hence the inclusion is
strict in general.

## Second-pass review / reflection

- the witness is genuinely stochastic rather than an artificial extra action;
- finite expected hitting is certified independently of `StrongRepairable`, so
  the separation is not circular;
- failure self-loops have positive mass, which is exactly what defeats the
  support-safe finite-rank predecessor operator while still allowing geometric
  retry to hit the target in finite expectation;
- the result distinguishes two semantics rather than weakening the old strong
  notion: strong repair remains valid and sufficient, but is not complete for
  stochastic repairability;
- the separation is within deterministic stationary control; randomized or
  history-dependent policy completeness remains an AR6 question.

Disposition: **CLEAR**.

## Validation

- focused compile and module build: **PASS**;
- Objecthood / Compression / full UEOT builds: **PASS**;
- proof-escape scan: **CLEAR**;
- selected axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression and 3-path governance simulation: **PASS**;
- `git diff --check`: **PASS**.

AR4 disposition: **CLEAR / eligible for its own local commit**.
