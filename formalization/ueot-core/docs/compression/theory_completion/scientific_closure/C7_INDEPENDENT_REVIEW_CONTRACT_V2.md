# C7 — independent evidence review contract v2

Status: **REVIEW-READY PROTOCOL / NOT YET AN INDEPENDENT REVIEW**.
The existing `independent_review = REVIEW_PENDING` remains authoritative.

## Separation of roles and frozen objects

- **Producer:** generated the v1 45-row certification/reproduction files and
  the current hardened runner/verifier. Producer self-reproduction is not
  independent review.
- **Independent auditor:** an executor who did not produce the frozen pilot
  records or co-develop this validation. Auditor identity, environment,
  independent implementation/procedure and signed timestamped report must be
  traceable. Codex code review is useful but is not a substitute for executing
  an independent replication.
- **Evidence authority:** `C7_PREREGISTRATION.md`, the reachable prereg commit
  `1b3e01d236f65e42ceff83a0c2bc152fca293bbb`, the reachable evidence
  commit `8b3a9b1b7df5cfd64699f6d78f698cdb77804ff4`, and the exact frozen
  raw/runner/verifier hashes in `c7_pilot/EVIDENCE_MANIFEST_v1.sha256`.
  The archival v1 data must never be silently reissued from a revised runner.

## Gate I — independent historical evidence audit

Before reading producer conclusions, an independent reviewer must record:

1. canonical commit, working tree status, OS/architecture, Python version,
   audit date, source hashes and v1 manifest check result;
2. full expected run-ID inventory and the 45-row cardinality of *both* v1 files;
3. own recomputation of nested first-good, holdout replacement, double-fault
   negative control and single-worker baseline **directly from frozen raw JSONL**,
   without using producer summary as an oracle;
4. cross-check of the independent results against the frozen summary and
   the archived v1 verifier, reporting all discrepancies and failure classes;
5. a distinct finding on v1 collection-retention provenance: because the v1
   runner wrote at the end, earlier dropped attempts cannot be excluded.
   This must remain `UNVERIFIABLE`, even if all observed rows match.

Success of Gate I may certify **independent historical artifact recomputation**.
It cannot certify independent generation or clean no-censoring of v1.

### Frozen-archive integrity helper (not independent adjudication)

Run from the repository root after a clean checkout:

```sh
python3 formalization/ueot-core/docs/compression/theory_completion/scientific_closure/c7_pilot/audit_archived_v1_integrity.py
```

The helper verifies the 10 historical manifest digests and both exact 45-row
run-ID inventories. It intentionally maps historical `run_pilot.py` and
`verify_evidence.py` manifest names to archived `run_pilot_v1.py` and
`verify_evidence_v1.py` paths; checking the present-day hardened scripts against
old hashes would be invalid.  A deliberate raw-file tamper must produce nonzero
exit status.  This is a convenience *producer-authored artifact-integrity*
check: an independent auditor must still inspect and recompute the claims
without trusting the helper's result. It cannot reconstruct pre-write failed
collection attempts or award an independence certificate.

## Gate II — genuinely independent new collection

A new preregistration/commit and independent executor are required **before**
collecting new data. Pin runner/verifier/worker hashes, candidate universe,
interventions, sample count, stop rule, fresh unguessable evidence label,
missingness handling, and a non-overwriteable raw destination.

- Execute the frozen hardened workflow under the independent auditor's
  separately provisioned process environment; retain all attempted runs,
  including `EXECUTION_ERROR` and interrupted/partial raw files.
- Before looking at aggregate summaries, perform blinded raw recomputation
  from run IDs, worker IDs/PIDs, intervention return codes, query tokens and
  results, and verify the complete registered run set.
- Include preregistered negative controls and mutation/adversarial checks:
  wrong terminated worker, replayed token, duplicate surviving PID, missing
  run ID and a coherent `DEAD` outcome. Check that integrity corruption gives
  `UNRESOLVED`, whereas a coherent contradictory outcome gives the correct
  `REJECTED_LOCAL` verdict.
- Record a full checksum manifest of both raw data and the independently
  produced recomputation; require a second reviewer to sign the report when
  independence of personnel is claimed.

Gate II establishes *independent local digital-process replication* at most.
It does not establish validity outside the constructed majority-service model.

## Decision fields and failure attribution

Report separately, never as one generic PASS:

- `historical_v1_independent_recomputation`: PASS / FAIL / NOT_RUN;
- `historical_v1_no_censoring`: UNVERIFIABLE (fixed historical limitation);
- `independent_new_collection`: PASS / FAIL / NOT_RUN;
- `independent_protocol_adherence`: PASS / FAIL / UNRESOLVED;
- `independent_review`: REVIEW_PENDING / REVIEWED_WITH_LIMITS / REVIEW_REJECTED;
- `external_domain_support`: UNVERIFIED / REJECTED / DOMAIN_CONDITIONAL;
- all discrepant rows, checksums, and one of the C7 four failure classes.

A same-executor rerun, an unsigned summary, a clean PR review, or a summary
computed from producer flags **must not** set `independent_review` to complete.
No status mutation is authorized by this document; status requires separate
review, governance authorization and exact-head integration gates.
