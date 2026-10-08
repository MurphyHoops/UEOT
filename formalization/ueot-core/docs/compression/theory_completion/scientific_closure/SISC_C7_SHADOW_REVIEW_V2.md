# SISC C7 shadow review v2 — self-hash is not provenance

Status: **LOCAL POST-COLLECTION CONSISTENCY REVIEW**. No independent executor,
new external trial, author-separated implementation or historical no-censoring
certificate. The original preregistered runner, v1 verifier, raw evidence and
manifest are **byte-for-byte unchanged**. Original positive local result still
reads `PASS_METHOD`; scientific C7/SI-5 remains OPEN.

## Added checks

`evidence/sisc_c7_sqlite_review_v2.py` verifies the *specific archived* SHA
`7484c8212c5aba6ad076d4359aa6c467ea3063f339400405211a5739052ff9d5`
against the original raw bytes. It also checks the exact run/phase inventory,
event sequence, monotone logged timestamps, carrier names, device/inode types,
all embedded response hashes, consistent original snapshots, and preservation
of each clone/moved inode **across the UPDATE event**.

Its adversarial tests exercise timestamp rollback, a replaced carrier during
UPDATE, coherent experimental contradiction, and a fully coordinated
post-hoc alteration of carrier inodes accompanied by a recomputed manifest.

## A falsifiable audit-counterexample

A mutated copy of the complete five-event archive with every recorded inode
increased by one million, all intra-record and inter-record equalities
preserved, and the manifest digest recomputed still yields:

- v1 self-authored `verify()` → `PASS_METHOD`;
- v2 *unanchored* internal structural checker → `PASS_METHOD`;
- v2 *pinned archive* checker → `UNRESOLVED` (the byte digest changed).

This proves an **integrity/authenticity distinction**: an internally consistent
self-hashed record can be fabricated by an actor controlling both data and
manifest. The pinned digest only verifies identity to **this archived
artifact**, committed after the v1 collection; it does not authenticate the
truth of recorded SQLite executions or retroactively prove unbiased retention.

## Scientific governance result

Only `v1_raw_recomputation = PASS_METHOD` and
`v2_archived_consistency = PASS` can be recorded. Preserve separately:

- `independent_collection = NOT_RUN`;
- `independent_review = REVIEW_PENDING`;
- `historical_attempt_censoring = UNVERIFIABLE`;
- `external_domain_support = UNVERIFIED`;
- `SISC_SI5 = OPEN`;
- `CLOUD_PUSH = HOLD`.

Next external run must freeze independent custody, attempt inventory,
authenticating audit/receipt controls, precommitted source code and protocol,
and second-party blinded evaluation **before** any outcomes are visible.
