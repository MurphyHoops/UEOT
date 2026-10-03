# Track O / AR1 — Fixed-Policy Stochastic Repair Basin Audit

Status: **LOCAL AR1 CLEAR — stage gate passed before commit**

Tracker: #238. Counted-core impact: **NONE**.

## Result

AR1 defines `StationaryRepairBasin P K pi` as finite canonical expected hitting
time under the stationary kernel induced by `pi`. It proves:

- target states have hitting time zero and therefore lie in every fixed-policy basin;
- outside the target, finiteness of the first-step expectation forces every
  positive-mass successor to have finite hitting time;
- hence the basin is support-closed under the fixed policy outside `K`.

The positive-mass argument is measure-theoretic: `ae_lt_top` from a finite
lintegral is combined with the strictly positive singleton mass supplied by PMF
support. No support-closure assumption is added by hand.

## Second-pass review / reflection

- the target-zero lemma is derived from the pathwise survival-set definition;
- the support theorem uses the same stationary kernel on both sides;
- no almost-sure statement is substituted for finite expectation;
- the closure claim is restricted to positive PMF support and to states outside
  the target, exactly where the first-step identity applies;
- no policy synthesis or maximality is claimed in AR1.

Disposition: **CLEAR**.

## Validation

- focused compile and module build: **PASS**;
- Objecthood / Compression / full UEOT builds: **PASS**;
- proof-escape scan: **CLEAR**;
- selected axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression and 3-path governance simulation: **PASS**;
- `git diff --check`: **PASS**.

AR1 disposition: **CLEAR / eligible for its own local commit**.
