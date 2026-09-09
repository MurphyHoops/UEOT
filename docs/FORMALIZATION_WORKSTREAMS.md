# UEOT Formalization Parallel Workstream Policy

Date: 2026-09-09
Status: active engineering policy
Branch of record: `main`

## Purpose

UEOT Core formalization is large enough that a strictly single-threaded workflow
wastes time on dependency downloads, CI, API lookup, and source semantic audits.
The project therefore uses **parallel research with serialized integration**.

## What runs in parallel

Independent workstreams may simultaneously perform:

- source-statement semantic audit;
- theorem decomposition and dependency analysis;
- Mathlib API lookup;
- proof design;
- creation of candidate Lean modules/blobs;
- documentation and bridge-contract updates;
- restoration research for historical verified modules.

Example active lanes:

- A — predictive canonicality / P-PRED;
- B — stochastic dynamics / P-DYN;
- C — infinite-horizon teleology / P-TEL;
- D — historical restoration, documentation, and claim-registry maintenance.

## What stays serialized

The following remain serialized on `main`:

1. each independent theorem/module advance receives one commit;
2. each repair receives its own commit;
3. a source P-ID is promoted only after the final source-matched statement is in
   an official target and pinned CI succeeds;
4. coverage/status documentation is committed only after proof evidence exists.

This prevents two concurrent workers from racing on the same branch tip and
keeps failed CI attributable to one logical change.

## Prepared-but-not-integrated work

A workstream may prepare a Git blob or complete source module without attaching
it to `main`. Such a blob is **not proof evidence**.

Its state is:

```text
prepared → integrated → official-target CI → semantic audit → promoted
```

Only the last four stages are repository-visible proof progress.

## Failure discipline

A red CI in one lane does not stop theorem design in other lanes.

However:

- no dependent theorem is promoted on top of an unresolved failure;
- a later green run does not erase the failed run;
- repair commits do not silently weaken theorem statements;
- if semantic audit discovers that a green theorem is narrower than the source,
  the P-ID remains partial until source strength is restored.

## Source-strength discipline

Parallelism must never become a reason to accept weaker surrogates.

Recent examples:

- P-PRED-01 was not promoted after the common-codomain proof because the source
  permits protocol-dependent future spaces;
- P-PRED-02 uses the same dependent-space audit before promotion;
- P-DYN-01 distinguishes finite-step transition consistency from the stronger
  conditional-history Markov/path-law statement.

## Scheduling heuristic

Prefer simultaneous lanes with low file overlap:

- probability/prediction;
- dynamics;
- control/teleology;
- restoration/docs.

Avoid two live integration commits that edit the same module or entrypoint at
the same time. Prepare them independently, then fast-forward one at a time.

## Completion metric

Parallel throughput does not change the completion metric.

The only source-level completion count is the fixed 106-P-ID ledger.
Theorem count, Lake job count, prepared blobs, and number of parallel lanes are
not completion percentages.
