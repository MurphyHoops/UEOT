# Interaction-Generated Parent Identifiability — Local Closure Record

Status: **CLOSED LOCALLY / NEW REMOTE BRANCH ABSENT**

## 1. Remote predecessor closure

The previously completed Dual-Isolation/P-MET branch was pushed before this
mission started:

`origin/compression/cross-track-dual-isolation-local`

at

`5968e93bc90e941af27828a89396e76b302b768a`.

No PR was created as part of that push.

## 2. Current local mission

Branch:

`compression/cross-track-interaction-identifiability-local`.

Exact audited implementation:

`7ca7e67803f84d5e703ef12bf6df7479a2b66dac`.

This branch has not been pushed.

## 3. Mathematical closure

For finite candidate assemblies and a finite nonempty probe family, define the
interaction fingerprint distance

`d_E(a,b) = max_e TV(R(a,e), R(b,e))`

and canonical lower gain

`beta_E = min_{a != b} d_E(a,b) / dist(a,b)`.

Lean proves

`beta_E > 0`

iff every distinct candidate pair is separated by at least one selected
interaction/probe.

If two candidates both fit one observed fingerprint to radius `eta`, then

`dist(a,b) <= 2 eta / beta_E`.

With the already audited common-Markov P-MET realization and Track-S semantic
isolation,

`semantic diameter <= 2 eta / (beta_E * kappaMin)`.

If `eta_n -> 0`, the corresponding invariant-law TV discrepancy tends to zero.

## 4. Source-facing closure

Frozen P-COMP-02 JS zero-set semantics is reused to prove:

pairwise strict JS intervention separation

-> pairwise response-law separation

-> `beta_E > 0`.

Thus the binding-identification margin can now be generated from an actual
finite interaction-response family rather than an arbitrary diagnostic map.

## 5. Probe closure

The mission proves:

- probe augmentation cannot decrease `beta_E`;
- every finite separating probe family contains an inclusion-minimal
  separating subfamily;
- such a family still has positive `beta_E`.

No stronger experiment-optimality claim is made.

## 6. Boundary closure

Machine-checked finite witnesses establish:

- interaction identifiability does not imply one-step viability;
- viability does not imply interaction identifiability.

Accordingly, the next Objecthood phase must not identify `beta_E > 0` with
persistence or identify a viability kernel with an endogenous Omega-loop.

## 7. Remaining residual

The current theory now begins one level closer to lower-level interaction, but
still assumes the candidate assembly type.

The next research residual is:

`lower-level children + environment + interaction law`

-> `admissible candidate assembly family`

plus a parallel persistence branch:

`identified parent dynamics`

-> `endogenous preserving controller / constitutive closure`

-> `Omega-loop persistence candidate`.

Finite-sample `eta_N` concentration and cost-optimal active probe design also
remain future work.

## 8. Frozen architecture

- source/final theorem accounting remains 106/106;
- counted generators remain 4;
- unresolved remains 0;
- no frozen ledger/disposition mutation;
- no Track-S/H source mutation;
- no fifth-generator claim.

## 9. Validation closure

On exact implementation `7ca7e678...`:

- `lake build UEOT.V3.Compression.CrossTrack`: **PASS**;
- full `lake build UEOT`: **PASS (9098 jobs)**;
- research governance: **PASS**;
- research-governance regression suite: **PASS**;
- frozen Compression validator: **PASS**;
- Compression validator regressions: **PASS**;
- proof-escape scan: **PASS**;
- public theorem axiom audit: **standard axioms only**;
- exact diff-check: **PASS**;
- detached exact-hash second-pass audit: **CLEAR**.

The worker interface was unavailable after two attempts with
`WORKER_IDENTITY_LOST`; therefore no independent-worker review is claimed.

## 10. Remote state

For this new local mission:

- no push;
- no remote branch;
- no PR;
- no Issue mutation;
- no merge.

Any remote lifecycle for the Interaction-Identifiability branch requires a
later explicit decision.
