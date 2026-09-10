# UEOT Core Lean — Live Formalization State

> **Recovery entry point.** Read this file first when resuming formalization
> work. Source-level truth is `V3_COVERAGE_STATUS.md`; execution order is
> `PARALLEL_FORMALIZATION_ROADMAP.md`.

Last synchronized: **2026-09-10 (Asia/Taipei)**

## 1. Canonical source and environment

- canonical source: `UEOT_Core_Mathematics_v3.0_Complete.md`
- source P-IDs: **106**
- canonical source SHA-256: `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`
- Lean: **4.33.1**
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- official target: `lake build UEOT`
- integration branch: `main`

Promotion requires exact source matching, official-target branch/PR CI, merge
to `main`, green post-merge CI, and ledger synchronization.

## 2. Current integrated checkpoint

| status | count |
|---|---:|
| proved | **34** |
| partial | **0** |
| pending | **72** |
| total | **106** |

Current integrated main checkpoint:

- main proof head: `8ac668253c4d8bc62ab22f250701bc0a190b6049`
- P-DYN-02 post-merge main CI #506 (`34497930427`): **success**
- immediately preceding P-FAC-01 merge: `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0`
- P-FAC-01 post-merge main CI #502 (`34493839447`): **success**

The two newest completed promotions are therefore **P-FAC-01** and
**P-DYN-02**. The authoritative ledger records **34 / 0 / 72**.

## 3. HOT proof lanes

### A. P-INFO-01 — information retention identity and entropy lower bound

- branch: `formal/pinfo01-04-chain`
- pre-discrete-bridge green head: `a62f5d44d0a1af4b592a750877a2580b1ee3be8b`
- prior official-target CI #483: **success**
- current discrete-bridge import head: `4077cd42c8c46941019802e61034d2ebc0231858`
- CI #508 (`34498908550`): running at this synchronization point

Already machine-checked on the branch:

- deterministic-statistic data processing;
- reversible measurable statistic lift;
- standard-Borel disintegration;
- exact chain identity
  `I(H;Y) = I(M;Y) + I(H;Y|M)`;
- epsilon-retention consequence;
- channel/data-processing reduction from arbitrary output `Y` to the copied
  state KL divergence.

Current mathematical target:

`D_KL(P_(M,M) || P_M × P_M) = H(M)`

for finite/discrete `M`, with Mathlib's `ENNReal` KL reconciled with the
project's real `pmfShannonEntropy`.

The new module `InformationDiscreteEntropy.lean` begins the exact measure-level
bridge. It defines the diagonal density

`copyDensity(m,n) = if m=n then (μ {m})⁻¹ else 0`

and aims to prove:

1. `(μ.prod μ).withDensity copyDensity = copyJoint μ`;
2. `copyJoint μ ≪ μ.prod μ`;
3. the abstract RN derivative agrees a.e. with this explicit density;
4. the KL integral reduces to the finite Shannon sum;
5. combining with the existing channel bound gives `I(M;Y) ≤ H(M)`;
6. combining with the statistic chain gives the literal P-INFO-01 lower bound.

No new UEOT information axiom is permitted.

### B. P-REC-02 — continuous stochastic recovery

- branch: `formal/prec02-continuous-recovery`
- last observed head: `fc4ad64059c2f84324fc7c66312198c0151f3381`
- source contains the Dynkin/localization/integrability regularity required for
  the intended a.e./absolutely-continuous argument
- classification: **F0 proof engineering**, not an identified source defect
- next: instantiate the process-level certificate without strengthening the
  manuscript to pointwise differentiability

### C. P-PER-01 — omega-limit strong invariance audit

- branch: `formal/pper01-omega-limit`
- last observed head: `94ddd8d0bbf231982c772968a985c4347cd46901`
- classification: unresolved **F2 source/statement issue** if a one-sided
  semiflow is required to satisfy exact image equality
  `φ_s '' ω(x) = ω(x)` without enough reverse-time structure
- forward invariance alone is insufficient
- next: derive reverse inclusion from the literal v3.0 assumptions or record a
  v3.1 wording correction; do not silently replace semiflow by flow

## 4. Newly integrated / archive lanes

### P-FAC-01 — integrated

- final feature head: `8c5e451c10f58fa032af73c66b1bd52f2fee7620`
- branch + PR official-target CI: green
- source blocker closed: finite causal feedback path-law transport is derived
  from transported primitive kernels rather than assumed
- squash merge: `29bb6b3fb55cde2d7a87577f4d0ff15c14e29aa0`
- post-merge main CI #502: green

### P-DYN-02 — integrated

- old development branch: `formal/pdyn02-ctmc`; retained as audit history
- old PR #22 closed because the branch was heavily diverged from `main`
- clean branch: `formal/pdyn02-ctmc-clean`
- clean proof head: `8c0212f4bfbd0e7bf9ed0c445e4662eb02cf04ef`
- branch CI #504: green
- clean PR #23 CI #505: green
- squash merge: `8ac668253c4d8bc62ab22f250701bc0a190b6049`
- post-merge main CI #506: green

The source-facing CTMC converse uses the right derivative at zero on `Ici 0`;
no negative-time CTMC assumption is introduced.

Other already integrated lanes include P-PER-03, P-INT-02, P-PRED-03,
P-DYN-04, P-DYN-03, P-PROC-01, P-QSD-02, P-INFO-05, P-REC-01,
P-DYN-01, P-MET-01/02 and the earlier recovered proof set. Do not resume from
stale feature heads unless deliberately recovering an unmerged theorem.

## 5. Theory-maintenance feedback

Canonical v3.0 remains frozen during verification. Theory-facing findings go
under `core/v3-maintenance`, especially
`core/status/FORMALIZATION_FEEDBACK_2026-09-10.md`.

Current high-value findings:

1. CTMC time is one-sided; the source-facing proof should explicitly use the
   right derivative at `t = 0`.
2. Marginal persistence and pathwise persistence are distinct; P-PER-03 now has
   an explicit Ionescu--Tulcea path-law bridge.
3. Representation covariance must be derived from transported primitive
   dynamics, not assumed as final path/value equality.
4. One-sided semiflow forward invariance must not be silently strengthened to
   exact image equality.
5. Import-graph inclusion is part of verification: an unimported green module
   is not proof evidence for the official target.
6. Lean can hide norm-instance mismatches behind identical pretty-printed
   types; eliminate auxiliary bundled analytic structures before the final
   source-facing algebraic equality when possible.
7. P-INFO-01 currently exposes a useful boundary between abstract measure KL
   and finite discrete Shannon entropy; keep that bridge modular rather than
   baking discreteness into the general mutual-information layer.

No active lane has produced an F3 counterexample to the UEOT Core architecture.

## 6. Mandatory recovery procedure

1. Read this file.
2. Read `V3_COVERAGE_STATUS.md`.
3. Fetch current `main` SHA and latest main Action.
4. Inspect every main commit newer than the checkpoint recorded here.
5. Compare every HOT branch to current `main` and inspect its latest CI.
6. Never overwrite a newer branch head with an older remembered version.
7. Feature-green is not `proved` until semantic audit + integration + green
   post-merge CI + ledger sync.
8. New modules must be reachable from `UEOT` / `UEOT.V3`.
9. After material branch-state changes or promotions, update this snapshot in
   the same work session.

## 7. Immediate parallel order

1. **P-INFO-01** — finish copy-KL = Shannon entropy; close the source entropy
   lower bound and then audit whether adjacent P-INFO-02/03/04 can reuse the
   same KL infrastructure.
2. **P-REC-02** — instantiate the literal continuous Dynkin/AC certificate.
3. **P-PER-01** — resolve the one-sided semiflow reverse-inclusion issue without
   source strengthening.
4. Refill free lanes from pending P-IDs only after these near-closure lanes are
   not left half-finished.

## 8. Repository truth hierarchy

- live operational snapshot: `docs/FORMALIZATION_STATE.md`
- source-level P-ID ledger: `docs/V3_COVERAGE_STATUS.md`
- execution plan: `docs/PARALLEL_FORMALIZATION_ROADMAP.md`
- official import graph: `UEOT/V3.lean`
- canonical source identity: `../../core/specifications/manifest.yaml`

If documentation disagrees, the frozen source manuscript + merged Lean
statements + green main CI + promotion gate take precedence; repair
documentation drift before further integration.
