# Track O / AR2 — Stationary Repair Policy Patching Audit

Status: **LOCAL AR2 CLEAR — stage gate passed before commit**

Tracker: #238. Counted-core impact: **NONE**.

## Construction

AR2 patches two deterministic stationary repair policies statewise by comparing
their canonical expected hitting-time potentials and selecting the action from
the policy with the smaller value at the current state. The patched certificate
uses the pointwise minimum of the two canonical potentials and unit drift.

The drift proof is exact: at a state selecting policy `pi1` (respectively
`pi2`), the integral of the pointwise minimum is bounded by the integral of that
policy's canonical potential, and AR0's first-step identity closes the unit
drift inequality.

## Result

- the patched certificate basin is exactly the union of the two source
  stationary repair basins;
- the canonical finite-hitting basin of the patched policy contains that union.

The second statement is deliberately only an inclusion. Patching can create
additional finite-hitting states, so equality with the canonical patched-policy
basin is neither needed nor claimed.

## Second-pass review / reflection

- no history dependence or randomized control is introduced: the result stays
  inside deterministic stationary policies;
- the chosen action and the kernel used in each branch agree definitionally;
- the `min` potential is used only as a valid PhysicalRepairCertificate; its
  basin equality follows from `min_eq_top` and does not assume reachability;
- `lintegral_mono` is applied pointwise to nonnegative ENNReal potentials, so
  no integrability or subtraction premise is hidden;
- the construction strengthens basin union without asserting maximality; AR3
  remains a separate finite-policy synthesis step.

Disposition: **CLEAR**.

## Validation

- focused compile and module build: **PASS**;
- Objecthood / Compression / full UEOT builds: **PASS**;
- proof-escape scan: **CLEAR**;
- selected axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- research-governance regression and 3-path governance simulation: **PASS**;
- `git diff --check`: **PASS**.

AR2 disposition: **CLEAR / eligible for its own local commit**.
