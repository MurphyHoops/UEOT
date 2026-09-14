# UEOT Core 3 Governance Review — 2026-09-14

## Executive finding

The UEOT Core 3 formalization process is mathematically disciplined but accumulated severe repository-state debt. At audit start the remote repository had **221 branches** even though only a small number represented unresolved work.

The central conclusion is:

> **The proof architecture is sound; the governance failure was branch/state lifecycle entropy.**

The formal proof ledger remained conservative: feature green did not directly increment coverage, clean integration was rebuilt from full-green `main`, prohibited-proof audits were enforced, and proof-main/ledger gates prevented premature counting. The failures were operational: branches were retained as archives, live state was duplicated across comments/files, and each proof iteration could create another remote branch.

A second safety review found an important flaw in the first cleanup implementation: a repository-wide “delete everything not on the Core 3 keep-list” rule could eventually delete legitimate UEOT-GI / UEOT-QM / physics branches. That rule was corrected **before merge**. Cleanup is now explicitly scoped to the audited Core 3 legacy namespaces only.

---

## Snapshot at audit start

- Remote branches: **221** (later branch enumeration showed 222 including the new governance branch).
- Integration branch: `main`.
- Counted checkpoint: **76/106 FULL-GREEN**.
- Full-green `main`: `32af6fcc8033b28cb4922f70109a8902c9ac3f36`.
- Legacy `master`: **0 commits ahead, 351 behind** `main`; no unique work.
- Issue #56 had accumulated a long sequence of recovery/checkpoint comments; the body is now the live state.
- Current governance branch: `ops/core3-branch-governance-v1`.
- PR #77 is the governance integration PR.

---

## What the Issue / branch history shows

The Issue #56 history demonstrates a repeated but understandable pattern:

1. source theorem selected;
2. feature branch opened;
3. API/Lean failure produced helper/scratch variants;
4. clean integration branch opened;
5. PR merged;
6. post-main CI run;
7. separate ledger branch/PR opened;
8. milestone comment appended;
9. old branches remained remote.

The proof gates were valuable, but the implementation surfaces were never retired. Over many P-IDs this converted a rigorous promotion pipeline into hundreds of persistent branch names.

Several specific anti-patterns recur in the branch inventory:

- `scratch`, `fresh`, `clean`, `clean-v2` variants;
- repeated `main-integration-vN` branches;
- separate ledger branches left after promotion;
- documentation-only branches left indefinitely;
- branches for P-IDs already counted in the authoritative ledger;
- helper/API experiments promoted to long-lived remote branches instead of commits/modules on one feature branch.

This is why branch count grew much faster than unresolved mathematical work.

---

## What worked well and should remain

### 1. Source-first theorem discipline

Frozen source semantics controlled the proof target. Incorrect shortcuts that narrowed signal spaces, policies, observation spaces, or quantifier structure were rejected.

### 2. Separation of feature proof and counted coverage

The lifecycle

`feature -> clean integration -> proof main -> post-main CI -> ledger PR -> ledger main CI`

correctly prevented feature-green or wrapper-only work from being counted prematurely.

### 3. Clean integration from known full-green `main`

Replaying only final validated files into clean integration branches prevented exploratory proof history from contaminating `main`.

### 4. Prohibited-proof audit

Repeated checks for `sorry`, `admit`, proof-bypass `native_decide`, and unsourced axioms materially protect proof integrity.

### 5. Durable recovery evidence

Commit SHAs, CI run IDs, PRs, source contracts, ledgers, and milestone records make cross-chat recovery possible.

These mechanisms should be retained; the optimization is to reduce repository entropy around them.

---

## Main governance failures and remediation

### Failure A — branches became permanent memory

Completed branches were retained indefinitely. Correct durable memory is `main` + merged PRs + CI + ledgers + milestone records.

**Remediation:** branch retirement is now mandatory after lifecycle completion.

### Failure B — no hard branch-creation preflight

A new branch could be created without proving that the work was uncounted, unique, and not already represented by another branch/PR.

**Remediation:** creation is blocked until coverage, live Issue state, branches, PRs, and `main` are reconciled.

### Failure C — multiple live-state authorities

Issue comments, `HANDOFF_LATEST.md`, `PID_STATUS.yaml`, `FORMALIZATION_STATE.md`, and coverage files could describe different moments.

**Remediation:** authority order is explicit. `V3_COVERAGE_STATUS.md` owns counted coverage; Issue #56 **body** owns high-frequency construction state; comments are history.

### Failure D — branch-per-iteration debugging

Proof debugging generated `scratch/fresh/vN` branches and repeated full CI.

**Remediation:** one P-ID normally has one feature branch; iterations are commits/modules on that branch. Remote `hold/*` is exceptional and short-lived.

### Failure E — initial cleanup automation was too broad

The first cleanup draft used a global keep-list and considered all other branches disposable. That would be unsafe once UEOT-GI, UEOT-QM, physics, or other subprojects begin using distinct branches.

**Remediation:** cleanup now has an explicit destructive scope:

- `master`;
- historical `docs/*` branches;
- historical `formal/*` Core 3 branches;
- the completed governance branch itself.

Unknown/new namespaces are retained by default. Repository-wide policy is now documented in `docs/REPOSITORY_BRANCH_GOVERNANCE.md`.

---

## Audit of the retained legacy branches

The mass cleanup intentionally preserves six non-main historical branches because they contain commits not trivially represented by current `main`. They are **quarantine/audit branches, not active lanes**.

| branch | relation to current main | unique surface | current disposition |
|---|---:|---|---|
| `core/v3-maintenance` | +6 / -187 | Core status/maintenance docs | retain temporarily; audit whether status knowledge belongs on main/archive |
| `formal/persistence-qsd` | +2 / -194 | `QSDPerron.lean` | retain temporarily; theorem/source relevance audit |
| `formal/pqsd03-duration-window-v1` | +3 / -2 | `QSDDurationWindow.lean` | retain temporarily; near-main pending-content audit |
| `formal/v3-coverage-wave2` | +4 / -209 | history Markovization modules | retain temporarily; determine whether superseded |
| `formal/v3-metrics` | +4 / -228 | `TVKernel.lean` | retain temporarily; determine reuse/integration status |
| `formal/v3-process-dynamics` | +7 / -228 | `DynamicsKernel.lean` changes | retain temporarily; source-semantic audit |

The correct target is not to keep these forever. Each must be resolved into one of three states:

1. **integrate useful unique work** through a current clean branch/PR;
2. **archive/document the insight** if code is historically useful but no longer source-relevant;
3. **delete** if superseded or invalid.

After that audit, ordinary operation should use roughly **1–4 remote branches**, not seven permanent survivors.

---

## New repository-level governance model

The new `docs/REPOSITORY_BRANCH_GOVERNANCE.md` makes branch ownership explicit across the whole UEOT repository.

Key invariants:

- `main` is the only integration branch;
- repository target <=8 branches, hard cap 12;
- one durable work item normally maps to one active branch;
- `formal/*` belongs to UEOT Core 3 formalization;
- future projects use explicit namespaces (`gi/*`, `qm/*`, `physics/*`, etc.);
- `docs/*` branch namespace is deprecated;
- cleanup automation must have an explicit scope;
- unknown namespaces are protected by default;
- the tool/platform changing (ChatGPT, Codex, local AI, human terminal) never justifies creating a parallel branch for the same objective.

---

## Issue governance improvements

The history suggests Issues should be modeled as durable objectives, not event streams.

For Core 3:

- Issue #56 body = current live state;
- comments = durable milestones/audit manifests only;
- CI polling and micro-fix logs stay transient;
- branch/head/PR/blocker/exact-next-action must be updated in the body at real state transitions.

Future long-running UEOT subprojects should use the same pattern: one live-state Issue per major ongoing project, with separate Issues only for independently trackable objectives.

---

## Recommended operating loop

`RECOVER -> RECONCILE -> BRANCH PREFLIGHT -> WORK ON ONE ACTIVE BRANCH -> VERIFY -> PR -> MAIN -> RETIRE BRANCH -> UPDATE LIVE STATE -> CONTINUE`

For Core 3 proof promotion, the stricter proof-main/ledger gates remain intact inside this outer repository loop.

---

## Immediate cleanup plan

1. Merge PR #77 only after its updated CI is green.
2. When the reviewed workflow file lands on `main`, its path-scoped push trigger performs the one-time audited Core 3 legacy cleanup.
3. Before deletion it records exact branch names/head SHAs in Issue #56.
4. It deletes only branches inside the explicit legacy scope and preserves the six unique audit branches plus `main`.
5. Verify remote branch count <=12 (expected approximately 7 after cleanup if no new out-of-scope branches appear).
6. Verify resulting `main` CI.
7. Audit the six retained branches one by one and shrink toward the normal 1–4-branch state.
8. Only then resume a genuinely uncounted P-ID.

---

## Final assessment

The project does **not** need a simpler proof standard. It needs a lower-entropy operating system around the proofs.

The strongest governance principle is now:

> **Issue = objective/state; branch = temporary implementation; PR = integration candidate; main = truth.**

A chat may end at any time and a branch may be deleted after its lifecycle. Neither is allowed to be the only place where project truth exists.
