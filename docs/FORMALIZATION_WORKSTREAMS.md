# UEOT Formalization Parallel Workstream Policy

Established: 2026-09-09
Current-policy refresh: 2026-11-11
Status: active engineering policy
Branch of record: `main`

## Purpose

The project uses **parallel research with serialized integration**. Independent
workers can inspect source semantics, design proofs and review consumers while
one coordinator owns shared entrypoints, final verification and publication.

Recover the actual state from [Current Core state](../core/status/CURRENT.md)
and the [formalization entry](../formalization/ueot-core/README.md). The frozen
106-P-ID baseline, the Core definitive edition, PR #446 hardening and PR #447
growth classification are completed within their respective contracts. A new
workstream needs a specific remaining question or correction; this policy does
not reopen those units or authorize automatic expansion of their scope.

## What runs in parallel

Independent workstreams may simultaneously perform:

- source-statement semantic audit;
- theorem decomposition and dependency analysis;
- Mathlib API lookup;
- proof design;
- creation of candidate Lean modules/blobs;
- documentation and bridge-contract updates;
- restoration research for historical verified modules.

Example task divisions, not a current queue:

- actual source semantics and implementation;
- the new mathematical claim and its failure boundaries;
- an independent consumer or proof review;
- documentation and final integration.

Assign nonoverlapping files or read-only snapshots. Workers report the exact
source they used and the work they actually verified; parallel authorship alone
does not establish independent review or external academic peer review.

## What stays serialized

The coordinator serializes shared edits and adoption:

1. refresh actual `main`, applicable instructions, current ownership and the
   relevant contract before integrating candidates;
2. complete a coherent change on its assigned branch or isolated worktree,
   preserving unrelated work and existing release history;
3. check source semantics, the actual consumer and affected public imports,
   then perform pinned local verification proportionate to the change;
4. record status only from the matching proof, execution or review evidence;
5. publish and merge the reviewed change, then reconcile the actual merged
   source with the accepted candidate.

Use coherent commits that reviewers can assess. There is no requirement to
create a separate commit for every theorem or every failed local attempt.
Preserve relevant failures and corrections in their evidence records, and do
not let two writers race on the same integration branch or shared entrypoint.

The [current branch-governance policy](REPOSITORY_BRANCH_GOVERNANCE.md#11-ci-efficiency-rules)
requires local-only Core validation and keeps the Core Lean, Compression Guard
and Compression Research Base Policy GitHub workflows disabled. Use the
[operations guidance](../formalization/ueot-core/docs/compression/COMPRESSION_OPERATIONS.md)
for applicable local checks. Reuse unchanged, source-matching evidence; do not
restart historical full builds or enable cloud CI merely to update
documentation. An absent cloud run is not a successful check, and a
governance-only CI result is not evidence of a Lean run. Required checks on an
actual PR retain their own meaning.

## Prepared-but-not-integrated work

A workstream may prepare and locally check a source module before adoption on
`main`. A blob by itself supplies no proof evidence; a successful check supports
the exact checked bytes, but does not establish that the candidate is merged.

Its state is:

```text
prepared → source-matched and locally checked → integrated and reviewed → merged and reconciled
```

Report only completed stages. Source-semantic matching, machine verification,
native execution, exact independent calculations and merged adoption are
separate facts. Where a new mathematical supplement has a written proof but no
dedicated Lean endpoint, disclose that state rather than borrowing a neighbouring
module's verification label.

## Failure discipline

A failed check in one lane does not stop independent theorem design elsewhere.

However:

- no dependent theorem is promoted on top of an unresolved failure;
- a later successful run does not erase the failed run;
- repairs do not silently weaken theorem statements;
- if semantic audit discovers that a green theorem is narrower than the source,
  the P-ID remains partial until source strength is restored.

## Source-strength discipline

Parallelism must never become a reason to accept weaker surrogates.

Historical source-audit examples, retained as methodological lessons:

- P-PRED-01 was not promoted after the common-codomain proof because the source
  permits protocol-dependent future spaces;
- P-PRED-02 required the same dependent-space audit before promotion;
- P-DYN-01 distinguishes finite-step transition consistency from the stronger
  conditional-history Markov/path-law statement.

These examples do not change the current 106/106 baseline or recreate a pending
P-ID task. For post-106 work, preserve the source's permissions, resource limits,
failure events and comparison class; a false strong claim requires an explicit
counterexample or narrowing rather than a hidden change of source.

## Scheduling heuristic

Prefer simultaneous lanes with low file overlap:

- probability/prediction;
- dynamics;
- control/teleology;
- restoration/docs.

Avoid concurrent writes to the same module or entrypoint. Integrate reviewed
changes one at a time using the current branch policy, checking intervening
main changes rather than resetting to an old audit SHA.

## Completion metric

Parallel throughput does not change the completion metric.

The source-level completion count for frozen v3.0 is the fixed 106-P-ID ledger.
Later contracts have their own declared exits and evidence; their completion
does not increase or rewrite that inventory. Theorem count, Lake job count,
prepared blobs and number of parallel lanes are not completion percentages.

Stop when the assigned contract is satisfied, or report a precise unresolved
research obstruction. Preserve `CLASSIFIED_CORE_CLOSED` for the completed Core
content and `UNVERIFIED` for its natural empirical support. New questions and
external scientific assessment remain distinct from the completed local units.
