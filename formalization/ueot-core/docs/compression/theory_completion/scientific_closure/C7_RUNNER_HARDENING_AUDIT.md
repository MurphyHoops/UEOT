# C7 — Evidence Runner Hardening Audit

Status: **P1 REMEDIATED FOR FUTURE COLLECTION / V1 RETENTION PROVENANCE UNVERIFIABLE**

## 1. Reachable preregistration provenance

The Scientific Closure branch was rebased before remote promotion, so the
pre-rebase preregistration identifier embedded in the generated v1 summaries
(`4e014cb589ca713d3a6af34523a23af5bfe038e9`) is no longer a reachable object on
the promoted branch.  The preregistration ordering itself is still directly
verifiable in the current reachable history:

- preregistration commit:
  `1b3e01d236f65e42ceff83a0c2bc152fca293bbb`;
- evidence-package commit:
  `8b3a9b1b7df5cfd64699f6d78f698cdb77804ff4`;
- `1b3e01d2` adds only `C7_PREREGISTRATION.md`;
- its parent contains neither the preregistration file nor C7 raw evidence;
- `8b3a9b1b` is a descendant of `1b3e01d2` and is the commit that adds the v1
  raw/summary/recomputed evidence files.

The preregistration commit author time is `2026-10-07T23:26:23+08:00`.  The
first v1 certification raw timestamp is `2026-10-07T15:27:23.138131+00:00`
(`2026-10-07T23:27:23.138131+08:00`).  Rebase changed the reachable commit hash
and committer time, not this author-time ordering or the parent/child ordering.

The old identifier remains inside the frozen v1 summary JSON because rewriting a
generated evidence object merely to substitute a post-rebase hash would destroy
its original content hash.  Audits must use the reachable commit above for Git
provenance and treat the old summary field as a historical pre-rebase identifier.
Likewise the frozen preregistration document records its pre-rebase parent
`dc55c292123191a60b13c6335ecd09d015919317`; the reachable rebased parent of the
preregistration commit is `4c905f1e23a47eb462604d22f1b2265194e0335e`.

## 2. P1 runner defect found during remote review

The v1 `run_pilot.py` accumulated all 45 records in memory and created
`raw_<label>.jsonl` only after all registered calls returned.  Therefore an
exception during worker launch, pipe I/O, JSON parsing, or query execution could
terminate the process before any raw file existed.  The same label could then be
reused, so an earlier unsuccessful collection attempt could have been censored.

This violated the frozen preregistration rule:

> execute the complete registered run count or record `EXECUTION_ERROR`; missing
> runs are failures, not silently dropped observations.

The committed v1 raw files each contain a complete 45-row run and are internally
recomputable, but the old runner design means the stronger statement “no earlier
failed attempt was ever silently dropped before these files were created” cannot
be established retrospectively.  That no-censoring provenance is therefore
classified **UNVERIFIABLE for v1**.

For audit preservation, the exact data-generating v1 scripts are retained as:

- `c7_pilot/run_pilot_v1.py`;
- `c7_pilot/verify_evidence_v1.py`.

Their SHA-256 values are identical to the corresponding scripts in the original
v1 evidence manifest.  The original manifest itself is also preserved byte for
byte as `c7_pilot/EVIDENCE_MANIFEST_v1.sha256`; the current
`EVIDENCE_MANIFEST.sha256` verifies that historical manifest together with the
current hardened tooling.

## 3. Hardened collection contract

The current `run_pilot.py` now:

1. reserves the raw evidence path with exclusive create **before** any worker is
   launched;
2. appends every completed registered attempt immediately;
3. flushes and `fsync`s each row before the next attempt can start;
4. converts Python-level execution failures to a durable `EXECUTION_ERROR` row
   and re-raises;
5. preserves the partial raw file if the process terminates;
6. refuses any later invocation that reuses the same label/path;
7. cleans up partially constructed worker sets when worker creation itself fails.

A hard process kill can occur before an explicit `EXECUTION_ERROR` row is
written, but it still leaves the already-created raw file and all prior fsynced
rows.  The hardened verifier detects the resulting missing registered run IDs and
returns `UNRESOLVED`; the same label cannot be silently rerun.

## 4. Hardened verifier contract

The current `verify_evidence.py` now checks all of the following before any local
claim can be `SUPPORTED_LOCAL` or `REJECTED_LOCAL`:

- exactly the 45 preregistered run IDs are present;
- run IDs are unique;
- no `EXECUTION_ERROR` record exists;
- every row carries the durable-attempt marker (`OBSERVED` or
  `EXECUTION_ERROR`);
- all expected timestamps, protocol-specific fields and logical outcomes are
  present.

If collection integrity is incomplete, all three C7 local claim verdicts become
`UNRESOLVED`.  Successful prefixes are never promoted to a claim verdict.

This intentionally means the hardened verifier does **not** certify the legacy
v1 files as satisfying the new durable-attempt provenance check, because those
rows predate the `record_status` marker.  The frozen `verify_evidence_v1.py`
remains available only to reproduce the historical v1 recomputation exactly.

## 5. Fault-injection regression

`c7_pilot/test_evidence_durability.py` covers both the low-level writer and the
actual runner main loop.  It forces the second registered attempt to fail and
checks that:

- the first `OBSERVED` row is already durable;
- the failing attempt is recorded as `EXECUTION_ERROR`;
- no summary is produced;
- the hardened verifier returns non-zero and all C7 claims are `UNRESOLVED`;
- a second invocation using the same label is refused before new collection.

Local result: **PASS**.

A separate temporary-directory full collection also executes all 45 hardened
attempts.  Every row carries `record_status = OBSERVED`, the summary is produced,
and the hardened verifier returns `all_checks_pass = true` with the three
registered local logical verdicts supported.  This is an implementation
validation after review, not a new independent or blind certification dataset.

## 6. Scientific consequence

The v1 logical observations remain useful completed-run evidence and retain their
original hashes.  However the package no longer uses them to claim strict
no-censoring preregistration compliance.  The correct classification is:

- preregistration design/order: **VERIFIED**;
- v1 completed-run logical recomputation: **PASS**;
- v1 no-censoring execution provenance: **UNVERIFIABLE**;
- current runner/verifier durability contract: **HARDENED / FAULT-INJECTION AND
  FULL-45 TEMP COLLECTION PASS**;
- independent/external validation: **OPEN**.

No Core theorem, counted generator, FBT theorem, C1-C6 result, or external-validity
claim is changed by this remediation.
