# UEOT Repository Branch Governance Protocol

> Scope: the entire `MurphyHoops/UEOT` repository across UEOT Core, UEOT-QM, UEOT-GI, physics, publications, and future subprojects. This document defines repository-level branch/Issue/PR governance. Subproject manuals may add stricter rules but may not weaken these invariants.

## 1. Core model

Repository state has four different roles:

1. **Issue** = durable work objective / current live state.
2. **Branch** = temporary implementation surface.
3. **Pull request** = reviewed integration candidate.
4. **`main`** = integrated source of truth.

A branch is never permanent memory. Historical evidence belongs in `main`, merged PRs, commits, CI runs, releases, ledgers, and milestone Issue records.

`main` is the only integration branch. Legacy `master` must not be used as an integration target.

---

## 2. Repository-wide branch budget

Normal operating target:

- total remote branches: **<= 8**;
- hard cap: **12**;
- open PRs: normally **<= 2**;
- active implementation branch per durable work item: **1**;
- governance/integration/promotion branches: ephemeral.

If the repository has more than 12 remote branches, branch hygiene takes priority over opening new work branches.

The budget is intentionally small because UEOT development is cross-chat and cross-platform: lower branch entropy directly reduces recovery errors.

---

## 3. Namespace ownership

Branch prefixes communicate ownership and prevent one subproject's cleanup automation from affecting another.

- `formal/*` — reserved for UEOT Core 3 Lean formalization legacy/current proof work governed by `formalization/ueot-core/docs/UEOT_CORE3_LEAN_OPERATIONS.md`.
- `compression/*` — reserved for post-106 UEOT Core compression/meta-formalization work governed by `formalization/ueot-core/docs/compression/COMPRESSION_OPERATIONS.md`.
- `gi/*` — UEOT-GI theory/engineering work.
- `qm/*` — UEOT-QM work.
- `physics/*` — broader physics derivations/experiments.
- `pub/*` — publication-only preparation when a branch is genuinely required.
- `ops/*` — repository or subproject governance/maintenance.
- `hold/*` — explicit short-lived quarantine/WIP only.

`docs/*` as a branch namespace is deprecated. Documentation should normally travel with the branch that owns the underlying change, or use `ops/*` for governance-only changes.

Unknown future namespaces are **protected by default** from cleanup automation until explicitly governed.

---

## 4. Branch creation preflight — mandatory

Before creating any remote branch, the agent/developer must:

1. fetch/prune remote state;
2. identify the durable work item (Issue, theorem ID, experiment ID, or roadmap item);
3. verify the work is not already integrated on `main`;
4. search existing branches for the same work item;
5. search open PRs for the same work item;
6. read the relevant live-state Issue/body for an existing active lane;
7. reuse an existing branch whenever it already represents the work;
8. if replacing a superseded branch, first preserve any needed commits and retire the old branch.

**Default invariant: one work item -> one active branch.**

Do not create `scratch`, `tmp`, `fresh`, `clean-v2`, `v3`, `v7`, or similar branch families merely to checkpoint an iteration. Use commits on the same branch.

---

## 5. Branch naming

Recommended form:

`<namespace>/<kind-or-id>-<short-purpose>`

Examples:

- `formal/pddh02-source-contract`
- `gi/feat-v0-runtime-loop`
- `qm/exp-qdrr-analysis`
- `ops/repository-branch-governance`
- `hold/gi-v0-risky-refactor`

Names should describe a durable objective, not a transient implementation attempt.

---

## 6. Lifecycle and mandatory retirement

Delete a branch when its durable purpose is complete:

- merged feature: after merge and resulting `main` CI is green;
- integration/promotion branch: immediately after its gate closes;
- governance branch: after merge and validation;
- superseded/abandoned branch: after useful commits are folded or explicitly rejected;
- `hold/*`: within one working session after resolution;
- branch for already-completed work: unless a formally recorded reopen exists;
- legacy default branch with no commits unique from `main`.

A merged PR is sufficient historical evidence; keeping its source branch indefinitely is not required.

---

## 7. Safe deletion protocol

Destructive cleanup must be conservative.

Before deleting a branch:

1. confirm it is not `main`;
2. confirm no open PR uses it as head;
3. confirm it is not the active branch named in the relevant live-state Issue;
4. confirm its work is integrated, obsolete, superseded, or explicitly archived;
5. if unique historical commits exist, record the branch head SHA and disposition before deletion;
6. unknown namespaces are retained unless explicitly included in the reviewed cleanup scope.

For mass cleanup:

- produce a dry-run/audit manifest first;
- record exact branch names + head SHAs before deletion;
- cleanup automation must use an **explicit deletion scope**, never “delete everything not on a keep-list” across the whole repository;
- preserve open-PR branches and `hold/*`;
- validate branch count and `main` CI afterward.

---

## 8. Issue governance

Use Issues for durable objectives and live state, not as a CI polling log.

For a long-running subproject, maintain one authoritative **LIVE STATE Issue body** containing:

- current integrated checkpoint;
- active objective;
- active branch/head;
- open PR;
- latest relevant CI;
- blocker/root cause;
- exact next action;
- do-not-repeat guards.

Issue comments are milestone/audit history only. Do not append one comment per micro-fix or CI poll.

For UEOT Core 3, Issue #56 is the current live-state authority below source/main/coverage truth.

A new Issue should represent a durable independently trackable objective, not every implementation step.

---

## 9. PR governance

A PR should correspond to one coherent integration objective.

Required properties:

- base is `main` unless a subproject protocol explicitly defines a staged integration gate;
- title/body identifies the durable work item IDs;
- unrelated changes are excluded;
- required CI is green before merge;
- after merge, resulting `main` must be validated;
- source branch is then retired according to §6.

Do not use a PR as a substitute for a second branch representing the same work item.

---

## 10. Cross-chat protocol

At every new chat or AI-agent session:

1. read the relevant project operations/protocol document from `main`;
2. read the relevant LIVE STATE Issue body;
3. fetch current `main`, branches, PRs, and CI;
4. reconcile live GitHub before creating any branch;
5. continue the existing branch if one is active;
6. only create a new branch after the preflight in §4 passes.

At a handoff boundary:

- checkpoint meaningful unfinished work on the existing branch;
- update the LIVE STATE Issue body;
- persist architectural decisions not already represented in code/docs;
- do not create a handoff-only branch.

A new chat must never require the user to reconstruct branch state manually.

---

## 11. Cross-platform / local-AI protocol

When development moves between ChatGPT, Codex, local AI, or a human terminal:

### Before work

```bash
git fetch --prune origin
git switch main
git pull --ff-only origin main
git branch -r
```

Then read the relevant LIVE STATE Issue and project protocol.

### If an active branch exists

Use it:

```bash
git switch <active-branch>
git pull --ff-only origin <active-branch>
```

Do not create a parallel branch merely because the development tool changed.

### If no active branch exists

Create one only after repository preflight confirms the work is not already represented elsewhere.

### Before handoff

```bash
git status
git add <coherent-files>
git commit -m "wip(<work-id>): <meaningful checkpoint>"
git push origin <active-branch>
```

Then update the relevant LIVE STATE Issue with branch/head/blocker/next action.

### After merge

```bash
git fetch --prune origin
git switch main
git pull --ff-only origin main
```

Delete stale local branches after confirming remote integration.

No platform may force-push `main` or create duplicate remote branches for the same objective without an explicit recorded exception.

---

## 12. Governance health check

At recovery and after major merges, verify:

- `main` is the only integration branch;
- total branch count <= 8 target / <= 12 hard cap;
- no stale open PRs;
- no duplicate branches for one objective;
- no merged integration/ledger/governance branches remain;
- live-state Issue bodies match GitHub reality;
- no cleanup automation has an unbounded repository-wide delete rule;
- new branch namespaces are explicitly owned before automated cleanup includes them.

If any check fails, governance repair precedes new parallel work.

---

## 13. Design principle

The repository should remain recoverable with low cognitive load:

`ONE MAIN + FEW TEMPORARY BRANCHES + ONE LIVE STATE PER LONG-RUNNING PROJECT + AUDITABLE PR/CI HISTORY`.

The objective is not the fewest possible branches at every instant; it is the minimum number necessary to represent genuinely concurrent unresolved work without losing auditability.
