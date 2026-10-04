# UEOT Repository Branch Governance Protocol v2

> Scope: the entire `MurphyHoops/UEOT` repository across UEOT Core, UEOT-QM,
> UEOT-GI, physics, publications and future subprojects.

## 1. Core model

- **Issue** = durable objective / compact live recovery state.
- **Branch** = temporary implementation surface.
- **Pull request** = reviewed integration candidate.
- **`main`** = integrated source of truth.

Branches are not archives. Historical evidence lives in `main`, merged PRs, commits, CI,
releases, ledgers and milestone records.

## 2. Governance principle

Governance cost must scale with semantic blast radius.

- ordinary additive work inside an owned namespace should be cheap;
- changes to shared interfaces should receive stronger review;
- frozen/counting/release truth should receive the strongest gates.

Subproject protocols may define the exact risk tiers, but they must preserve this ordering.

## 3. Branch budget

Normal target:

- remote branches: **<= 8**;
- hard cap: **12**;
- open PRs: normally **<= 4** when they are path/track independent;
- one active branch per durable work item;
- merged governance/integration branches are deleted promptly.

If the hard cap is exceeded, first retire merged/stale branches. Do not stop an unrelated
scientific L0 read-only task merely because cleanup is pending.

## 4. Namespace ownership

Stable prefixes communicate ownership:

- `formal/*` — Core Lean formalization legacy/current source work;
- `compression/*` — post-106 compression/meta-formalization research;
- `gi/*` — UEOT-GI;
- `qm/*` — UEOT-QM;
- `physics/*` — broader physics/experiment work;
- `pub/*` — publication-only preparation where a branch is needed;
- `ops/*` — governance/maintenance;
- `hold/*` — short-lived quarantine only.

A new **task** inside an existing namespace should not require a repository-governance
rewrite. A genuinely new top-level namespace is registered once and then reused.

Unknown namespaces are protected from automated cleanup by default.

## 5. Minimal branch preflight

Before a new mutating branch:

1. fetch/prune;
2. identify the durable objective;
3. confirm it is not already integrated;
4. check for an existing branch/PR for the same objective;
5. reuse that branch if it exists.

Do not create branch families such as `scratch`, `fresh`, `clean-v2`, `final-v7` for
ordinary iteration. Use commits.

Additional project-specific preflight is required only when the change touches a higher
risk tier.

## 6. Branch naming

Recommended:

`<namespace>/<kind-or-id>-<short-purpose>`

Names describe durable objectives, not implementation attempts.

## 7. Lifecycle / retirement

Delete a remote branch after its purpose is integrated and required resulting-main checks
are green. Also retire superseded/abandoned branches after useful commits are integrated
or explicitly rejected.

Before destructive deletion confirm:

- it is not `main`;
- no open PR uses it as head;
- it is not an active task branch;
- its work is integrated/obsolete/archived;
- any unique evidence worth keeping has a durable commit/PR/audit record.

Mass cleanup must use an explicit reviewed scope; never delete everything outside a
repository-wide keep-list.

## 8. Issue governance

A live-state Issue is a **recovery index**, not a CI log or historical database. Keep only:

- canonical checkpoint;
- active objective;
- branch/PR;
- blocker;
- exact next action;
- essential do-not-repeat/protected-boundary notes.

Put long historical evidence in merged PRs, audit files and commits. Comments are for
milestones, not every CI poll.

## 9. PR governance

One coherent objective per PR. Base is `main` unless a documented higher-risk lifecycle
requires otherwise.

Required checks should be proportional to the change:

- docs-only / policy-only: schema/governance validation;
- source change: relevant build/tests;
- shared/frozen/counting change: full regression and stronger review.

Do not run the same full regression in multiple workflows solely to obtain duplicate green
badges.

## 10. Cross-chat / cross-platform recovery

At a new session:

1. fetch current `main`;
2. read the relevant compact live-state record;
3. inspect active branches/PRs;
4. continue the existing objective/branch;
5. read deeper historical documents only when they are dependencies.

At handoff, checkpoint meaningful WIP on the same branch and update live state only when
something materially changed. Never create a branch solely for handoff.

No platform may force-push `main` or create duplicate remote branches for the same
objective without an explicit exception.

## 11. CI efficiency rules

- Prefer one canonical owner for each expensive regression.
- PR workflows should cancel superseded runs when safe.
- Feature-branch push + PR synchronize should not both perform the same expensive build.
- Path filters should prevent documentation-only changes from compiling unrelated proof
  libraries.
- Resulting-main validation remains authoritative for integrated source changes.

## 12. Health check

Periodically verify:

- `main` is the only integration truth;
- remote branch count is within target/cap;
- merged branches are retired;
- no duplicate branches represent one objective;
- live-state Issues match repository reality;
- cleanup automation is explicitly scoped;
- CI does not duplicate expensive checks without a distinct safety purpose;
- ordinary tasks can start inside existing namespaces without governance edits.

## 13. Design principle

`ONE MAIN + STABLE NAMESPACES + FEW TEMPORARY BRANCHES + COMPACT LIVE STATE + RISK-PROPORTIONAL CI`.

The goal is the **minimum sufficient governance** that preserves scientific auditability
without turning governance into a second research project.
