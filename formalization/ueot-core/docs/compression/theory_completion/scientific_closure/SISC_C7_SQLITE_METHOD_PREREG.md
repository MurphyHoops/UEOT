# SISC C7/SQLITE-METHOD-01 — PRECOLLECTION REGISTRATION

Registration status: **DESIGN / CODE FROZEN BEFORE NEW RUN**.
This is a self-administered *method and instrumentation* pilot on the
independently maintained SQLite engine, not an independent-executor test and
not established external-domain UEOT support. No natural-system claims.

## Scope and observable contract

- Run label: `SISC_SQLITE_METHOD_20261008_V1`.
- Engine: installed `/usr/bin/sqlite3`, report its exact version at runtime.
- Experimental sandbox: brand new private temporary directory, never any
  user-owned or production database. All mutations remain inside sandbox.
- Candidate carrier: a SQLite database file holding the same declared query.
- Declared observation: sorted `SELECT id, value FROM items ORDER BY id`.
- Physical provenance signal: same-filesystem `st_dev/st_ino` from `os.stat`,
  **not** a general or metaphysical definition of object identity.
- Causal operations: copy, rename, and subsequent change of moved source.
- One preregistered execution; no rerun can overwrite any raw record.

## Predeclared steps, order and acceptance

1. `INITIAL`: write one row `(1, alpha)` to `original.db`, close database and
   log query fingerprint and file inode.
2. `COPY`: copy the closed original to `clone.db`; query must be equal while
   inode must differ. Demonstrates observational equality with different
   independently observed carrier provenance.
3. `RENAME`: rename original to `moved.db` on same filesystem; both query
   fingerprint and inode must be preserved.
4. `UPDATE`: mutate the moved file's row to `(1, beta)`; clone must remain
   `(1, alpha)`. Demonstrates distinct interventions after cloning.
5. `COMPLETE`: log a terminal record. Collect all intermediate attempts and
   return codes in append-only, fsynced JSONL, not just summary flags.

`PASS_METHOD` iff all registered operations and positive/negative checks pass,
all `INITIAL,COPY,RENAME,UPDATE,COMPLETE` records appear once in order, and
the independent raw-file verifier recomputes their verdict. A coherent
counterexample is `REJECTED_METHOD`; missing raw data, subprocess failure,
partial evidence, unexpected sample count or manifest tampering is
`UNRESOLVED`. No retry, filtering or post hoc thresholds.

This is qualitative proof-of-method; no hypothesis about statistical
confidence, real-world frequency, or general `SameObject` is registered.
External tests must still independently freeze protocols, coverage, priors,
estimated error budgets and instrumented negative controls before collecting
certification observations.

## Audit boundary

Runner and verifier are both researcher-authored even though they interrogate
the external SQLite process: their agreement is **not independent review**.
Do not replace existing `C7_PREREGISTRATION.md` or archive history. Independent
review remains `REVIEW_PENDING`; `real_world_support = UNVERIFIED`; the broader
SISC SI-5 stage remains OPEN pending externally administered experiments.
