# C7 — Evidence / Reproducibility Audit

Package status: **LOCAL COMPLETE / REVIEW_PENDING / REAL_WORLD_UNVERIFIED**
Conclusion classes: **LOCAL DIGITAL PILOT + NO-GO-PRESERVING METHOD + GOVERNANCE THEOREM**
Preregistration commit: `4e014cb589ca713d3a6af34523a23af5bfe038e9`

## 1. Preregistration ordering

`C7_PREREGISTRATION.md` was committed before any certification evidence was
collected. It fixed claim IDs, candidate family, two protocols, held-out
replacement, negative control, naive baseline, repetition count, stopping rule,
logical pass/fail thresholds, failure taxonomy and independent-review status.

The executable implementation was written after the preregistration and is
content-hashed in the evidence package. Therefore the local pilot is valid as a
registered method execution, but the implementation itself was not separately
committed before data collection. This limitation is retained in the final
classification rather than hidden.

## 2. Actual local digital process

The pilot uses real OS subprocesses, not an in-memory stochastic simulation.
Each worker has an actual PID and line-oriented request/response channel. The
runner performs actual process termination and fresh-process replacement.

Registered nested candidates and strict-majority quorum:

- 1 worker: healthy read succeeds; loss of the only worker fails;
- 2 workers: healthy read succeeds; loss of one fails because quorum is 2;
- 3 workers: healthy read succeeds; loss of one succeeds because quorum is 2.

Across 5 registered repetitions, the first single-fault-tolerant candidate in
the nested family is therefore size 3.

## 3. Held-out structural replacement

The held-out protocol terminates `W3`, starts a fresh `W4` process and then
runs healthy-read plus single-fault tests on `{W1,W2,W4}`.

All 5 registered repetitions passed. Raw records preserve different old/new PIDs,
so the evidence is genuinely structural replacement at the process level.

This does **not** identify `W3` and `W4` as the same component. It certifies
only continuity of the preregistered majority-service behavior under the tested
replacement/transport.

## 4. Positive, negative and baseline evidence

Certification record count: **45**.

- C7-LOCAL-FORM-01: `SUPPORTED_LOCAL`;
- C7-LOCAL-FBT-01: `SUPPORTED_LOCAL`;
- C7-LOCAL-NEG-01: `SUPPORTED_LOCAL`;
- double-fault negative control: 5/5 service unavailable as registered;
- one-worker naive baseline after its sole worker loss: 5/5 unavailable as registered.

No failed or unresolved run was dropped from the raw evidence.

## 5. Raw recomputation and self-reproduction

`verify_evidence.py` does not read or trust the generated summary. It recomputes
all registered counts, first-good candidate, held-out replacement checks,
negative control and baseline directly from raw JSONL.

It passes for both certification and a second local reproduction run.
`reproduction_comparison.json` verifies the two runs have identical logical
signatures and claim verdicts while allowing PID/timestamp/latency to differ.

This is **self-reproduction by the same execution lane**, not independent review.
Independent review remains `REVIEW_PENDING`.

## 6. Machine-checkable failure attribution

`C7EvidenceGovernance.lean` formalizes the four registered failure classes and
proves that only `mathematicsOrSourceSemanticsMismatch` satisfies
`RequiresCoreTheoremReview`. Measurement/estimation failure, concrete domain
bridge rejection and insufficient coverage do not logically refute the generic
Core theorem by themselves.

## 7. Evidence hashes

- certification raw JSONL: `8ed8a15816f93f927de7ef53ed3c126e5c81929d4a78a5e196aec90e93baddb5`;
- certification recomputation: `b327a0ba330eb3ea4fcbe25d44c3a57975a28906a89998c3bd8514b76b0db705`;
- reproduction raw JSONL: `1950781bcc5dd8540bf24a6d2b1f40b1b27a5487a3d47c68350c7dbb3a5952c6`;
- reproduction comparison: `09d462eb87422b5b03dccc990cf7a69f55738f83e22d5503c89b01d156725ff3`;
- complete manifest: `c7_pilot/EVIDENCE_MANIFEST.sha256`.

## 8. Scientific classification

The strongest valid statement from C7 is:

> The preregistered C2/C3/C4 method stack works end-to-end on one constructed,
> resettable, locally executed digital majority-service process with real process
> failure and replacement, including registered negative controls and raw-data
> recomputation.

It does **not** establish external/natural-system UEOT validity, universal carrier
minimality, universal structural identity, Π/Φ mechanism identification, or a
purpose mechanism.

Therefore:

- C7 local package: **PACKAGE_CLOSED**;
- independent review: **REVIEW_PENDING**;
- real-world/external support: **UNVERIFIED**;
- Core §31.2 C7 stronger port: **OPEN**.
