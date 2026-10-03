# Track O / AR3 — Maximal Deterministic-Stationary Repair Audit

Status: **LOCAL AR3 CLEAR — stage gate passed before commit**

Tracker: #238. Counted-core impact: **NONE**.

## Construction

For finite state and action spaces with a nonempty action type, AR3 minimizes
the canonical expected target-hitting time over the finite type of all
deterministic stationary policies, separately at each state. A minimizing whole
policy is selected at each state, and its current-state action defines
`maximalStationaryRepairPolicy`.

The pointwise minimum is itself a unit-drift physical repair potential: at each
state the chosen action agrees with an attaining policy, the global minimum
potential is pointwise below that policy's canonical potential, and the AR0
first-step identity closes the drift inequality.

## Main result

`maximalStationaryRepairBasin_eq_exists_policy` proves

`StationaryRepairBasin P K piMax = {x | ∃ pi, x ∈ StationaryRepairBasin P K pi}`.

Thus one deterministic stationary policy simultaneously realizes the union of
all deterministic-stationary finite-expected-hitting repair basins.

## Second-pass review / reflection

- finiteness is used exactly where intended: the policy type is finite because
  both `X` and `A` are finite; `Nonempty A` is explicit so at least one policy
  exists;
- the construction does not assume a globally minimizing whole policy. It only
  uses a policy attaining the value at the current state, then takes that
  policy's action there; this is precisely what the Bellman-style one-step
  argument requires;
- the pointwise infimum is attained because the policy set is finite; no
  compactness, continuity, or measurable-selection hypothesis is smuggled in;
- the maximality statement is scoped strictly to deterministic stationary
  policies and finite expected hitting time. It makes no AR6 claim about
  randomized or history-dependent policies;
- no counted-core, S/H, RH, RLSR, or fifth-generator surface is touched.

Disposition: **CLEAR**.

## Validation

- focused compile and module build: **PASS**;
- Objecthood / Compression / full UEOT builds: **PASS**;
- proof-escape scan: **CLEAR**;
- selected axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression and 3-path governance simulation: **PASS**;
- `git diff --check`: **PASS**.

AR3 disposition: **CLEAR / eligible for its own local commit**.
