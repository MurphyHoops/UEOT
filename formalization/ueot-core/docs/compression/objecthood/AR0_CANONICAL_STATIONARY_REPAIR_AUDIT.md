# Track O / AR0 — Canonical Stationary-Policy Repair Audit

Status: **LOCAL AR0 CLEAR — stage gate passed before commit**

Tracker: #238. Counted-core impact: **NONE**.

## Construction

AR0 defines `policyCanonicalRepairCertificate P K pi` for a fixed
deterministic stationary policy. Its potential is exactly
`expectedHittingTime (stationaryKernel P pi) x K`, its drift is exactly one,
and the drift condition is the existing canonical ENNReal first-step identity
rewritten in the orientation required by `PhysicalRepairCertificate`.

The certificate basin therefore reduces definitionally to finite canonical
expected hitting time under that same fixed stationary policy.

## Scientific advance

The O4 physical-recovery interface no longer requires an externally supplied
Lyapunov potential once a deterministic stationary policy is fixed. The
repository's canonical hitting-time semantics generate the potential and unit
drift certificate directly.

## Boundaries

AR0 does not yet prove closure of the finite-hitting basin, policy patching,
maximal stationary repairability, equivalence with strong repairability, or
completeness relative to randomized/history-dependent strategies. It does not
enter recurrent homeostasis, repair-law self-reconstruction, reopen S/H, alter
the frozen counted ledger, or assert a fifth generator.

## Independent second-pass review / reflection

- kernel identity: the potential, first-step theorem, and certificate all use
  the identical induced kernel `stationaryKernel P pi`; no path-law swap occurs;
- no hidden finite-expectation premise is introduced: the reused first-step
  ENNReal theorem explicitly requires no finiteness assumption;
- measurability does not strengthen the scientific target: finite `X` plus
  `MeasurableSingletonClass X` makes the arbitrary target set measurable, as
  already used throughout the Objecthood lane;
- the drift inequality is actually an equality after commutativity of ENNReal
  addition, so there is no slack or weakened surrogate theorem;
- basin equivalence is definitional through `PhysicalRepairCertificate.basin`,
  not a separately assumed reachability predicate;
- API surface remains fixed-policy only, preventing AR0 from silently claiming
  AR1--AR6 results early.

Disposition: **CLEAR**.

## Exact validation result

- focused `CanonicalStationaryRepair` compile: **PASS**;
- Objecthood root build: **PASS**;
- Compression build: **PASS**;
- full `lake build UEOT`: **PASS — 9114 jobs**;
- AR0 proof-escape scan (`sorry/admit/axiom/opaque/unsafe/native_decide`): **CLEAR**;
- selected axiom audit (`policyCanonicalRepairCertificate_mem_basin_iff`,
  `policyCanonicalRepairCertificate_potential`): only standard `propext`,
  `Classical.choice`, `Quot.sound`;
- research-governance regression: **PASS**;
- working-tree path governance simulation: **PASS — 3 changed paths**;
- `git diff --check`: **PASS**.

AR0 disposition: **CLEAR / eligible for its own local commit**.
