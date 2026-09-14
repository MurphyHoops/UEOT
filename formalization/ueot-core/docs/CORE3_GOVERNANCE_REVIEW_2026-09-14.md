# UEOT Core 3 Governance Review — 2026-09-14

## Executive finding

The formalization process is mathematically disciplined but repository governance accumulated substantial operational debt.

At the start of this audit the remote repository contained **221 branches**, while the operations manual itself recommended fewer than 20 active branches. The main causes were not theorem complexity alone; they were lifecycle failures:

- completed feature/integration/ledger branches were rarely deleted;
- one P-ID sometimes generated multiple `scratch`, `fresh`, `clean`, `v2/v3/v7` branches;
- Issue #56 comments became the de facto live state while the Issue body remained stale;
- low-frequency state documents periodically drifted behind the actual main/coverage state;
- already-counted P-IDs were occasionally reconsidered as if they were new work before reconciliation corrected the mistake;
- full remote CI was used repeatedly during proof debugging because branch/CI checkpoints were cheaper to create than to clean up.

The mathematical proof ledger itself remained conservative: feature green did not directly increment source coverage, clean integration was rebuilt from full-green main, prohibited-proof audits were enforced, and separate proof-main/ledger gates prevented premature counting. The governance problem is therefore primarily **state/branch entropy**, not proof-integrity failure.

---

## Snapshot at audit start

- Remote branch count: **221**.
- Integration branch: `main`.
- Legacy `master`: **351 commits behind `main`, 0 ahead**; no unique work.
- Issue #56 body still described an old **67/106** state even though milestone comments and live main had advanced far beyond it.
- P-REF-04 and P-REF-05 had later wrapper branches even though they were already counted in the authoritative baseline.
- P-BRG-02 likewise had historical branch work despite already being counted.
- The current active promotion was P-BRG-01, with proof lifecycle green and 76/106 ledger promotion in progress.

---

## What worked well

### 1. Source-first theorem discipline

The strongest part of the process is the insistence that the frozen source controls theorem semantics. Several potentially incorrect shortcuts were rejected because they would have narrowed signal spaces, policies, observation spaces, or theorem quantifiers.

### 2. Separation of feature proof and counted coverage

The sequence

`feature -> clean integration -> proof main -> post-main CI -> ledger PR -> ledger main CI`

successfully prevented feature-green or wrapper-only work from being counted prematurely.

### 3. Clean integration from a known full-green main

Replaying only final validated files into a fresh integration branch prevented long exploratory feature history from contaminating main.

### 4. Prohibited-proof audit

The repeated checks for `sorry`, `admit`, proof-bypass `native_decide`, and unsourced axioms materially protect formal proof quality.

### 5. Durable recovery evidence

Commit SHAs, CI run IDs, PRs, source contracts and milestone issue comments make cross-chat recovery possible even when a chat ends abruptly.

---

## What needs improvement

### 1. Branches were treated as permanent memory

This was the largest failure. Branches became an archive of every experiment instead of temporary construction surfaces. The correct archive is:

- final code on `main`;
- merged PR history;
- CI runs;
- coverage/PID ledgers;
- Issue #56 milestone records.

A completed feature branch does not need to exist forever.

### 2. Multiple live-state authorities existed in practice

The intended hierarchy was clear, but daily work often appended Issue comments instead of updating the Issue body. As a result, recovery sometimes required reading later corrections that invalidated earlier comments.

Remediation: Issue #56 **body** is now the one editable live state. Comments are historical milestones only.

### 3. Branch creation lacked a hard preflight gate

The previous manual recommended one branch per P-ID but did not prevent a new branch from being created before checking:

- whether the P-ID was already counted;
- whether a feature branch already existed;
- whether an open PR already represented the work;
- whether a previous branch was merely stale rather than inadequate.

Remediation: branch creation is now blocked until coverage, Issue body, branch search, open PRs and live main have been reconciled.

### 4. Scratch/version branch proliferation

Names such as `scratch`, `fresh`, `clean-v2`, `integration-v7` captured proof iterations that should have remained commits/modules on one feature branch.

Remediation: permanent scratch/version families are prohibited. Emergency remote WIP uses `hold/*` with one-session TTL.

### 5. State-document drift

`PID_STATUS.yaml`, `FORMALIZATION_STATE.md`, `HANDOFF_LATEST.md` and Issue comments sometimes described different points in time.

Remediation: authority order is explicit. Only `V3_COVERAGE_STATUS.md` determines counted coverage; Issue body determines live construction state; other documents are lower-frequency metadata.

### 6. Too much high-frequency CI/state logging

Many micro-fixes generated full branch CI and new comments. This increased noise and made the recovery log harder to read.

Remediation: batch coherent fixes before full CI where possible; comments only for durable milestones; CI polling belongs in transient chat state, not the permanent Issue log.

---

## New governance rules implemented

The updated `UEOT_CORE3_LEAN_OPERATIONS.md` now requires:

1. **Branch creation hard gate** before every new remote branch.
2. **One P-ID / one feature branch** as the default invariant.
3. **Remote branch target <= 8; hard cap 12**.
4. **No new theorem branch while above hard cap**.
5. Standard branch classes only: `formal/<pid>-<topic>`, clean integration, ledger, `ops/*`, emergency `hold/*`.
6. Explicit branch deletion points after merge/full-green lifecycle completion.
7. Issue #56 body as the live state; comments only as milestone history.
8. Automatic branch-hygiene logging and deletion through `.github/workflows/core3-branch-hygiene.yml`.
9. Deletion manifest records exact branch head SHAs in Issue #56 before destructive cleanup.
10. Open-PR branches, `main`, explicit unresolved branches and `hold/*` are protected from automated cleanup.

---

## Initial conservative keep-set for cleanup

The first automated cleanup intentionally keeps a small set of branches whose unique content still merits separate audit:

- `main`
- `core/v3-maintenance`
- `formal/persistence-qsd`
- `formal/pqsd03-duration-window-v1`
- `formal/v3-coverage-wave2`
- `formal/v3-metrics`
- `formal/v3-process-dynamics`

Any branch backing an open PR is also retained automatically. `hold/*` is retained until its explicit short-lived quarantine is resolved.

Everything else is treated as historical completed/superseded work under the current 76-P-ID ledger audit and is eligible for deletion after the governance PR lands.

---

## Recommended next governance improvements

### A. Audit the seven retained legacy branches

Each should be classified as:

- unique pending theorem work -> rename/rebase into one canonical feature branch when activated;
- already represented on main -> delete;
- obsolete experiment -> delete.

The target after this audit is **1–4 remote branches during ordinary proof work**.

### B. Keep promotion branches ephemeral

A normal completed P-ID should leave no permanent feature/integration/ledger branches after full-green counting.

### C. Prefer branchless source audit

Future P-IDs should be audited against the frozen source and current main before a branch is created. A branch begins only when code must change.

### D. Make governance repair blocking

If branch count >12, Issue body stale, or a counted P-ID has an unexplained active branch, repository hygiene takes priority over new theorem development.

### E. Periodic cleanup

Run the branch-hygiene workflow after major promotions or whenever branch count approaches the hard cap. The workflow should remain conservative: preserve open PRs and explicitly unresolved work, delete completed lifecycle branches, and log exact pre-delete SHAs.

---

## Conclusion

The existing proof/promotion architecture is fundamentally sound and should be retained. The main optimization is to make repository state **low-entropy**:

- one live state;
- one feature branch per theorem;
- few simultaneous lanes;
- deterministic promotion gates;
- automatic branch retirement;
- no branch as permanent memory.

This reduces cross-chat recovery cost without weakening any mathematical or formal-verification standard.
