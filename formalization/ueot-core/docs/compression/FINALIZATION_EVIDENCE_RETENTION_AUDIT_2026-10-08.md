# UEOT Core Compression — FINAL evidence retention audit

Date: 2026-10-08
Scope: governance/provenance only; no Core theorem, counted mapping, generator, or scientific claim change.

## 1. Trigger

The local Scientific Closure G4 audit reported that legacy FINAL Compression Guard run
`36578717533` could no longer be returned by GitHub. Because the live compression
validator requires `--verify-finalization-refs`, that observation was treated as a future
cloud-CI blocker. The recorded FINAL event is:

- candidate main: `bf1d01a0f7bf658f8c205ddcc1a2832a4bb3638b`;
- Core Lean run: `36578717005`;
- Compression Guard run: `36578717533`;
- closure PR: `#175`.

The audit correctly refused to replace either run ID with a newer green run. Such a
substitution would falsify event provenance.

## 2. Read-only root-cause recheck

On 2026-10-08 both historical Actions runs were again returned by the GitHub REST API and
matched the ledger exactly:

- workflow names: `UEOT Core Lean` and `UEOT Core Compression Guard`;
- event: `push`;
- state: `completed/success`;
- head SHA: `bf1d01a0f7bf658f8c205ddcc1a2832a4bb3638b`;
- creation time: `2026-09-29T13:55:19Z`.

PR `#175` also remained available and preserved the same candidate SHA, the two run IDs,
the exact-head review record, merge commit
`4eade136cf5b289756148ff48ea939e57181f082`, and the four-generator accounting.

During the same recheck, requests for these still-live resources intermittently failed with
`net/http: TLS handshake timeout` and then succeeded on retry. An older local closure audit
already recorded the same class of GitHub GraphQL/TLS failure for PR `#175`.

Therefore the evidence does **not** support the stronger diagnosis that run
`36578717533` had already expired or been deleted. The observed immediate root cause was a
transient external access failure. The long-term architectural risk is nevertheless real:
the validator currently requires an external Actions provider to retain old run metadata
forever.

## 3. Invariant

The fix must preserve all of the following:

1. a new FINAL event is verified online against its exact candidate SHA, both named push
   runs, and its closure PR;
2. historical run IDs are never rewritten to newer unrelated runs;
3. timeout, TLS, authentication, rate-limit, server, malformed-response, and unknown
   failures do not become PASS;
4. only an explicit HTTP 404 for an Actions run may enter historical-receipt fallback;
5. fallback requires a receipt already present in the immutable PR baseline and byte-for-byte
   unchanged in the candidate;
6. closure PR identity and Git merge ancestry remain live-verified even when an old Actions
   run is served from the receipt;
7. existing receipts are immutable history; a current candidate cannot create a receipt to
   self-authorize a run that is already missing.

## 4. Chosen minimal repair

The counted ledger schema and its four FINAL evidence fields remain unchanged.

`validate_compression.py` now uses the GitHub REST API for live reference checks. For
Actions runs it follows **online first** semantics. If and only if a recorded run returns
HTTP 404, the validator may load
`docs/compression/finalization_receipts/<candidate_main_sha>.json` from the supplied
baseline ref. The candidate copy must be identical to that baseline blob, and the receipt
must reproduce the ledger candidate SHA, closure PR number, run IDs, workflow names,
`push/completed/success` status, head SHA, and a canonical event digest.

The PR remains an online requirement; the receipt is deliberately not a general
"GitHub unavailable => pass" mechanism.

For future re-finalizations, the receipt is captured while both Actions runs are still
online and committed through the closure PR. The current M-OI FINAL event predates this
mechanism, so its first receipt is explicitly marked
`retrospective_live_reverification`. That label means exactly what it says: the external
records were live and reverified at capture time; it does **not** claim that this receipt
existed on 2026-09-29.

## 5. Rejected alternatives

- **Replace the old run ID with a recent green run:** rejected as false provenance.
- **Ignore any unavailable run:** rejected because it turns evidence loss into automatic
  success.
- **Fallback on timeout/TLS/auth errors:** rejected because transient inability to verify is
  not evidence of historical validity.
- **Store only a human note:** rejected because it is not machine-bound to the exact event.
- **Make every GitHub object offline-verifiable:** rejected as unnecessary scope expansion;
  Actions retention is the identified durability problem, while the PR remains part of the
  live identity/ancestry gate.

## 6. Scientific impact

None. This is provenance transport hardening only. It does not alter frozen Core v3
106/106 status, the four counted generators, compression accounting, any C1-C7 theorem or
no-go, real-world support, or independent-review classification.
