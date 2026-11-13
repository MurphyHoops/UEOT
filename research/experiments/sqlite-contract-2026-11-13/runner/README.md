# SQLite ACK / process-fault study runner

Status: final implementation for preregistration; **certification has not run**.
The coordinator must create the real preregistration commit and issue the matching
authorization before certification or independent replication.

This is newly authored research instrumentation. No Apache/MIT or other software
license is added here; follow the repository LICENSE_SCOPE. SQLite is called through
the installed Python module; no SQLite implementation is copied or modified.

## Scope and actual target

The target is Apple vendor SQLite 3.51.0, source ID:

    2025-06-12 13:14:41 f0ca7bba1c5e232e5d279fad6338121ab55af0c8c68c84cdfb18ba5114dcaapl

The measured interpreter is Python 3.9.6 at
/Library/Developer/CommandLineTools/usr/bin/python3 on macOS 26.6.2 arm64.
The protocol pins the SQLite version/source ID, compile-options digest, interpreter
binary digest and _sqlite3 module digest. Every worker READY is checked against the
pin. The raw environment and effective PRAGMA values remain in every trial.

Fixed connection settings are DELETE rollback journal, synchronous FULL (query
value 2), foreign_keys ON, cache_size 5, cache_spill ON and busy_timeout 1000 ms.
Worker readback is repeated after initialization. All policy connections set and
read back the same settings. FULL/DELETE here is a process-crash configuration,
not a power-loss durability certificate. The Apple vendor identity is not called
an unmodified upstream SQLite release.

There was an earlier 20261008 SQLite copy/rename/inode/update method pilot.
This study adds transaction confirmation, process interruption, history checking,
equal-information baselines, explicit budget limits and a held-out workload.

## Entry points

Use the exact frozen files and the recorded Mac interpreter. The output directory
must be new. Existing runs are never overwritten.

    python3 sqlite_study.py run --split calibration --protocol protocol.json --out NEW_CALIBRATION_DIRECTORY
    python3 sqlite_study.py run --split certification --protocol protocol.json --out NEW_CERTIFICATION_DIRECTORY --authorization REAL_AUTHORIZATION_JSON
    python3 sqlite_study.py run --split replication --protocol protocol.json --out NEW_C_REPLICATION_DIRECTORY --authorization REAL_AUTHORIZATION_JSON

The final protocol's calibration allocation is only the two targeted v2 cases.
The original seven-case calibration v1 has a separately preserved source/protocol
and is not silently replaced. It is not necessary to rerun either calibration.

Certification is exactly W1/W2 × seven scenarios × two repetitions = 28 reset
trials. Replication is exactly W2 × seven scenarios × one repetition = seven new
reset trials. C runs replication separately, using a separate output directory,
after the same preregistration authorization. B does not run the C allocation.

The authorization JSON must have approved=true, the actual 40-character
preregistration_commit, runner_sha256, protocol_sha256 and allowed_splits containing
the requested phase. These are not arbitrary placeholders: the script verifies
the source/protocol hashes and the protocol's frozen status. The coordinator
records the actual remote commit before creating this file. The local JSON gate
prevents accidental early execution; it is not a remote cryptographic verification
service or an OS security boundary.

## Finite workload and raw parameter reconstruction

Each trial has one fresh worker process and a fresh database. The business table
has integer primary keys, integer values and text payloads. A transaction updates
every registered business row and atomically inserts a unique transaction ID,
sequence and request hash into the transactions table.

The initial row i is [i, 10000+i, repeat("initial-%04d|" % i) truncated to L].
For transaction sequence s, each prior value v becomes v + ((i+s) mod 7) - 3.
Its payload token is SHA256(UTF8(txn-ID + ":" + decimal(i))). The actual payload
is repetitions of that hexadecimal token truncated to L characters. Thus each
compact request contains all values needed to recover every actual bound SQL
parameter exactly. The worker records the SHA256 of the expanded parameter list.
The controller preserves the original request and the received binding witness.

Transaction IDs are UUID5 of the full run identity and transaction ordinal.
Run identity includes study ID, protocol revision, phase, workload, scenario and
repetition; independent replication has different IDs. Policies receive opaque
IDs only through a shared completion certificate, not a scenario name. No verdict
branches on IDs or paths.

Canonical state is JSON with keys business and transactions, sorted JSON keys,
UTF-8, no added spaces, ensure_ascii=False; business rows are ordered by id and
transaction rows by seq. The parent reference model derives expected states from
initial state and recorded requests, not from faulted target output. Policies
compare SHA256 summaries; the digest is not a proof of mathematical injectivity.
Raw actual rows and complete allowed reference states are retained for C to
compare values directly with separately authored code.

There is no separate database-domain metadata table. Source binding is through
the nonempty unique transaction sequence, the request contents, the complete
business state and recorded file/process provenance. Do not claim a nonexistent
domain-field check. The initialized state is constructed and committed by the
worker; it is not separately closed and independently fully queried before every
fault. Pre-fault requests/ACKs and final raw comparisons are available to audit
this explicit initialization assumption.

## ACK knowledge and shared policy inputs

The parent logs a successful ACK only after receiving and parsing its complete
message. Worker ACKs occur after successful COMMIT return. A request whose COMMIT
was allowed but ACK was not received remains UNKNOWN.

The public completion certificate is one of:

- ACK_RECEIVED, with matching txn-ID and parent receipt event;
- PRECOMMIT_GATE_WITHHELD, with received precommit barrier, no commit release and
  observed SIGKILL/reap result;
- REQUEST_WITHOUT_ACK.

The withheld-commit certificate is deliberately common information for candidate
and strong baseline. It is not hidden oracle truth given only to the candidate.
The internal COMMIT_RETURNED_NO_ACK event is retained for intervention audit but
is not exposed to policies as proof of a unique final commitment.

The allowed state set is {S1} for ACKED, {S0} for certified NOT_COMMITTED and
{S0,S1} for UNKNOWN. Every member includes all prior acknowledged transactions.
With complete evidence, current membership can be ACCEPT_CURRENT_ALLOWED while
ack_class stays UNKNOWN. Acceptance does not invent a received ACK or uniquely
reconstruct all past events. Absence of an ACK alone never means NOT_COMMITTED.

The policy input object is constructed from a fixed whitelist: allowed-state
digests, completion class/certificate, key count and callback budget. It contains
no scenario label, expected verdict or private COMMIT_RETURNED event. This is
auditable code/interface discipline, not a filesystem sandbox against a malicious
policy. Parent oracle and target share a host and disk; independence is only from
the declared worker kill / target-file replacement intervention set.

## Faults, snapshots and preservation

Seven scenarios are fixed: NORMAL, PRECOMMIT_KILL, COMMIT_NO_ACK_KILL,
POST_ACK_KILL, STALE_BACKUP, BUDGET_ZERO and BUDGET_SMALL.

The two commit-boundary kills occur at explicit protocol barriers. They are not
a stochastic survey of internal disk timing. SIGKILL only terminates a process:
the OS, its caches, filesystem and storage controller continue.

After worker termination and reap, before any SQLite reopen, the full target
database and sidecar set is copied to postfault_raw. Every candidate, strong
baseline, weak diagnostic and ablation receives its own complete clone, retaining
the correct db.sqlite-journal basename. Original hashes are checked after each
policy. A last separate adjudication clone records raw values; its B-authored
observation is not C's independent result check.

For STALE_BACKUP, a clean closed current-state snapshot is additionally preserved
under pre_replacement_current before copying in the older completed backup. That
extra read/write byte cost is recorded. C may later clone and query it to compare
D_new and D_old under the exact same history. The original target and postfault
raw are never queried first for this purpose.

For each journal the runner records file size, first 28 bytes and SHA256. A
nonempty journal alone does not establish hot-journal recovery. A positive hot
header candidate requires length >512 and the SQLite journal magic. Actual
recovery evidence additionally uses the reaped writer, independent-clone before/
after file changes, journal removal and full state comparison. No journal is
manually deleted to make a strategy pass.

Calibration v1's precommit journal had a zero header and unchanged DB/journal
after observation. It did not demonstrate a hot rollback. The bounded v2 larger
calibration produced valid magic, a changed recovered DB, journal disappearance
and prior-state membership; this is calibration evidence, not held-out proof.

## Equal-information comparison

Candidate and strong baseline implement the same finite rule in two separately
spelled functions in this same source: require complete observation, correct
configuration, nonexceeded measured budget, structural integrity and membership
in the same allowed state set. The baseline is the familiar single-writer
reference-model/history-checking method family. The naming of the candidate does
not add information or control power. These functions are not independent
inventions or external human reviews.

The actual observer runs separately on each clone. No extra budget, lookup,
hidden oracle or earlier recovered state is provided to the candidate.
The expected result is decision equivalence; a lack of advantage is a valid
result, not a reason to weaken the baseline.

Weak_structure only checks opening and structural integrity; STRUCTURE_OK is not
a business-history acceptance. Identity_ablation performs the same full scans
and pays the same observation fees but omits external history membership from
its decision. It is an ablation, not the strong comparison baseline.

## Resource units and limits

The finite SQL budget counts actual SQLite progress-handler callbacks at
interval N=1. At the B-th call the handler returns nonzero and no subsequent SQL
is started. Callback count is not an exact count of VM instructions, pages or
hardware I/O: SQLite documents N as approximate and permits prepare callbacks.

The callback handler is installed after sqlite3.connect and before the first
configuration SQL. B=0 returns before connecting to the target. Wall time starts
after loading the common input summary and before the connection attempt; it is
not full-pipeline wall time. Closing/cleanup has the handler disabled.

Initialization, parent reference-model computation, canonicalization/serialization,
shared history-summary generation, source hashing and experimental clones are
common external preprocessing; they are not charged to the callback counter.
Their available sizes/times are recorded separately where instrumented. Opening,
automatic recovery, VFS/OS work and physical I/O are not given a strict hard bound.
In particular BUDGET_ZERO still has experimental preparation and clone costs;
it does not mean zero physical work.

Every SQL stage records callback counts, returned rows, returned canonical bytes
and elapsed time. Incomplete/interrupted scanning never becomes evidence that a
row is absent. Python 3.9 may not expose a numeric SQLite error code; the recorded
exception type/message, exposed code if any and callback interruption flag are
preserved without inventing an observed numeric code.

Calibration established B=32 interrupts the first journal_mode PRAGMA, before
business scanning. It is a real insufficient-observation case, not a partially
completed business-table scan. High budget stays 1,000,000, zero stays 0.

The 1,800-second overall rule stops starting subsequent trials once the threshold
is reached. Remaining planned IDs get NOT_RUN records. It is checked between
trials and is not a hard OS wall-clock deadline; the in-progress trial retains
its per-stage waits and cleanup/file-I/O overhead. Worker waits are 15 seconds
and observers 30 seconds. No failure or timeout is replaced with a new favorable
seed.

Monotonic timestamps are interpreted within their emitting process. In particular,
Python 3.9/macOS clock values must not be assumed directly comparable across
processes. Parent receipt order, sent controls and worker messages provide the
cross-process causal evidence; UTC timestamps are additional provenance.

## Records and interpretation

Each run preserves planned IDs, source/protocol hashes, authorization, raw parent
JSONL, raw worker output/error, original requests, ACK records, allowed reference
states, all policy SQL rows, process exit codes, timing and budgets, database
snapshots, sidecars and SHA manifests. All attempted trials appear in SUMMARY.
Raw originals and each clone remain available; gzip/ZIP may preserve exact bytes
for publication.

The original seven-case calibration and its source are separate from the two-case
v2 calibration; neither is included in 28 certification trials. W1/W2 have not been
run in calibration. A/C and the coordinator review final code before the actual
preregistration commit; certification starts only after explicit go.

The primary finite claim must include non-vacuity: sufficient-budget normal and
commit-boundary cases decide current allowed membership, stale acknowledged
history is rejected, and insufficient observations remain unresolved. An always-
UNRESOLVED checker would fail that claim. Results do not estimate a production
failure probability, prove all SQLite histories, validate power loss, establish
general object identity, or change the frozen Core/global empirical status.

## Method sources

- https://sqlite.org/atomiccommit.html — rollback journal and hardware assumptions.
- https://sqlite.org/pragma.html — integrity_check, DELETE, FULL, cache_size and spill.
- https://sqlite.org/c3ref/progress_handler.html — approximate interval and interrupt.
- https://sqlite.org/testing.html — existing stronger simulated VFS crash testing.
- https://sqlite.org/backup.html — ordinary snapshot backup.
- https://www.cs.columbia.edu/~wing/publications/HerlihyWing90.pdf — sequential
  specification/history correctness as a mature method family.
- https://github.com/jepsen-io/knossos — conventional ok/fail/info distinction.
  Knossos is not run or imported by this study.

