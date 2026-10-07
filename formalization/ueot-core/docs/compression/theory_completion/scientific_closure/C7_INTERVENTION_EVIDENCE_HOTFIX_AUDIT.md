# C7 — Intervention Evidence Hotfix Audit

Status: **POST-MERGE REVIEW REMEDIATION / FUTURE TOOLING ONLY**

Claim class: **EVIDENCE-INTEGRITY TOOLING**, not a new scientific theorem or
external empirical result.

## 1. Trigger

The final overlapping Codex review of Scientific Closure PR #293 identified two
evidence-integrity gaps after that PR had already merged:

1. fault-protocol rows were accepted from registered service outputs without
   independently requiring the recorded intervention itself to match the
   preregistered terminated worker(s);
2. the durability regression generated a complete hardened 45-row collection
   but did not first verify that pristine collection as a positive control.

The first direct hotfix attempt was correctly rejected by post-FINAL governance
because the verifier and regression are existing Track-TC surfaces.  PR #295
therefore added the missing L2 machinery and a temporary baseline-only exception
scoped to exactly the classified hotfix branch and these two existing files.

## 2. Intervention-evidence contract

The hardened verifier now treats a fault protocol as evidence only when the raw
record contains the registered intervention and an internally consistent
post-intervention query.  In addition to run-ID/protocol/split/candidate binding,
it checks:

- the exact registered terminated worker identity or identities;
- positive process IDs and nonzero integer termination return codes;
- distinct terminated PIDs for double-fault records;
- the survivor reply identities are exactly the registered non-terminated
  candidates;
- terminated worker identities and terminated PIDs do not reappear in the
  subsequent replies;
- candidate size, quorum, successful-reply count and aggregate service output
  are recomputed from the registered candidate/intervention state;
- held-out replacement records bind `W3 -> W4`, require distinct old/new PIDs,
  require the `W4` read reply PID to equal the recorded replacement PID, exclude
  the old/replaced process from subsequent replies, and preserve `W1/W2` process
  identity across the read and held-out-fault queries.

Missing or inconsistent intervention evidence is a collection-integrity defect,
so all C7 claims remain `UNRESOLVED`; it is not converted into a scientific
negative result.  By contrast, an internally coherent observation that genuinely
contradicts a preregistered expected output remains eligible for a local
`REJECTED_LOCAL` verdict.

## 3. Positive and adversarial regression contract

`test_evidence_durability.py` now verifies the pristine hardened 45-row
collection **before** mutating copies.  The positive control requires:

- verifier exit code zero;
- `all_checks_pass = true`;
- `registered_intervention_match = true`;
- all three registered local C7 verdicts equal `SUPPORTED_LOCAL`;
- a runner summary exists and agrees with the verifier verdicts.

Adversarial copies then test, among the earlier metadata/integrity cases:

- missing single-fault action;
- wrong terminated worker;
- terminated worker reappearing in survivor replies;
- incomplete double-fault action list;
- a zero termination return code;
- a held-out replacement PID that disagrees with the observed `W4` process;
- protocol/split/candidate substitution;
- a coherent contradictory observation paired with a lying producer
  `matches_expected = true` flag;
- missing/non-string run IDs.

Intervention or metadata corruption must produce nonzero verification with all
claims `UNRESOLVED`.  The coherent contradictory-observation case must be
recomputed from raw data rather than trusting the producer flag.

## 4. Historical boundary

This hotfix does **not** rewrite or strengthen the frozen v1 evidence:

- v1 completed-run logical recomputation remains usable;
- v1 strict no-censoring execution provenance remains **UNVERIFIABLE**;
- the archived v1 runner/verifier and manifests remain historical evidence;
- no new independent collection is claimed by this tooling patch.

Likewise this remediation does not alter C1-C6, any Lean theorem, the frozen
106/106 Core, the four counted generators, or counted compression mappings.

## 5. Scientific status after the hotfix

- current future-collection runner/verifier: **HARDENED**;
- intervention evidence binding: **REQUIRED**;
- pristine positive-control regression: **REQUIRED**;
- local constructed-process interpretation: **UNCHANGED**;
- independent empirical review/reproduction: **REVIEW_PENDING**;
- real-world support: **UNVERIFIED**.

The hotfix therefore closes an evidence-integrity defect without promoting the
C7 pilot beyond the scientific status justified by its data.
