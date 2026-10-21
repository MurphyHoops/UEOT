# Tenth-overlay consumer preparation

This directory prepares only the five existing consumer paths authorized by
the canonical operations renewal at
`299a4e3a71914af064ccd7916bb285bac201f62a`:

- `knowledge/reuse/fkrg_reuse.py`
- `knowledge/reuse/test_fkrg_reuse.py`
- `knowledge/reuse/REBUILD_CLONE_CANDIDATES.py`
- `knowledge/README.md`
- `knowledge/reuse/README.md`

Paths above are relative to
`formalization/ueot-core/docs/compression/theory_completion/`.
The current UMC source DAG is owned and updated separately. This preparation
does not edit any of the nine prior overlays, immutable proof snapshots,
historical receipts, counted ledgers, parser, or governance rules.

## Actual consumer result

The independently reviewed proposal 02 was installed exactly. All **50 reuse
tests passed** (exit 0; unittest 1.818 seconds, capture runner 1.928 seconds),
including the existing full-current clone regeneration test. All five
installed hashes stayed unchanged during the test run.

- [Exact installed patch](proposal-02/consumer.patch):
  `088839c289b80b8d17825c6781909de302cb5da59bddbb7ae4f4c3709ddf649a`.
- [Apply receipt](proposal-02/APPLIED_CONSUMER_UPDATE.json):
  `d9bfbcaf92d15d8cd9ec70954de8cd99f78c56806aec63d11d79cf28e043f75b`.
- [Actual test receipt](actual-tests-01/REUSE_TEST_RECEIPT.json):
  `f85203b0b37792e6dd80722f89e7d96b73bca872255492f9faa32731d39fd3b3`.
- [Raw test output](actual-tests-01/reuse-tests.log):
  `8cb123f14916191b451c8c42de673841e35d7d4ea3eb13050c90369d2eb08188`.

Exact original and proposed bytes are retained under `proposal-02/baseline/`
and `proposal-02/proposed/`. The earlier unapplied proposal remains under
`proposal-01/`. Original PREPARED/RUNNING/apply-time PENDING states are not
rewritten; the subsequent test receipt supplies the actual PASS.
Root-owned FKRG, full UMC, Git and release gates remain separate.

## Inputs and scope

`prepare_consumer_update.py` requires the actual metadata-registration
receipt, registered overlay, native export, fixed verifier and their archived
inputs. It checks the registered payload against the raw candidate, verifies
the archived hashes and successful full-build/native records, and derives
the new graph and native counts from those artifacts. It never generates a
PASS result from a source-only preflight or from this document.

The frozen source fingerprint is
`179783b20a817affae721d2f1ad36c4fcb25763cbb91701c120b68351b103ae6`.
The already frozen source scope is 684 modules, six added physical modules,
35 public source candidates and six lexical hint groups. Actual native
owned/private counts, proof-edge counts and all new evidence digests are
read from the successful export and registration when the script runs.

Before registration exists, the script and `.in` files are an unapplied
proposal. Placeholder names in those templates are not execution evidence.
During preparation, the five live files were kept byte-for-byte equal to the
authorized base. After a successful preparation, the resulting `consumer.patch` and proposed
tree make the complete edit reviewable without modifying the live files.

The runtime consumer change appends the tenth overlay and fixed verifier to
the four existing registries. All existing source and evidence checks stay
in place. The script verifies the prior registry prefixes and proof graph
are unchanged, then loads the proposed consumer against the actual current
source inventory. This read-only loading is not a full test-suite run.

All 47 existing regression methods remain present. Only current census
literals change in three existing methods. Three additional tests cover:

1. Complete native ownership, public/private classification, standard axioms,
   raw-type comparison counts, actual proof edges, and native hash drift.
   The generic controller module remains in the native scope despite having
   no explicit public theorem candidate.
2. Concrete prior-theorem reuse in the finite checker, constructed
   controller, and positive/negative witnesses. Public theorem registration
   remains distinct from definitions and module imports.
3. Metadata-only registration, preserved raw execution bytes and historical
   PENDING states, archived provenance hashes, and the separate Git-object
   gate. No future Git or release acceptance is inferred.

The clone-scanner edit changes only its current-census docstring; an AST
comparison requires the scanner implementation to stay identical. Both
READMEs retain all nine historical layer sections and append the finite-memory
results with their actual digests and bounded mathematical scope.

## Exact execution commands

Run from the repository root after actual metadata registration has finished.
The commands below use a fresh output directory; an existing proposal must
have exactly matching bytes.

```bash
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/consumer/prepare_consumer_update.py \
  --repo "$PWD" \
  --native-archive formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/actual-execution/native-01 \
  --output /workspace/scratch/534b0448126c/tmp/core-finite-memory-publication/consumer-proposal-02
```

This writes only `consumer.patch`, `PREPARED_CONSUMER_UPDATE.json`, the five
exact original files under `baseline/`, and the five proposed files under
`proposed/`. The receipt reports the precise patch
hash and marks tests and clone regeneration as unexecuted.

After review of that exact patch and the actual registration notification,
the same command with `--apply` installs only those five files:

```bash
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/consumer/prepare_consumer_update.py \
  --repo "$PWD" \
  --native-archive formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/actual-execution/native-01 \
  --output /workspace/scratch/534b0448126c/tmp/core-finite-memory-publication/consumer-proposal-02 \
  --apply
```

`APPLIED_CONSUMER_UPDATE.json` reports `APPLIED_FIVE_CONSUMERS_TESTS_PENDING`.
The exact proposed patch for this corrected version is
`088839c289b80b8d17825c6781909de302cb5da59bddbb7ae4f4c3709ddf649a`.
The earlier proposal and the preparation-only failed check remain recorded
in `PREPARATION_HISTORY.json`.

After installation, run the full reuse suite once with its raw combined
output and observed 50-test count retained:

```bash
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/consumer/run_reuse_tests.py \
  --repo "$PWD" \
  --proposal /workspace/scratch/534b0448126c/tmp/core-finite-memory-publication/consumer-proposal-02 \
  --output formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/consumer/actual-tests-01
```

The reuse suite includes its existing full-current clone-regeneration test.
The FKRG/parser tests, UMC audit and exact Git/PR/resulting-main gates remain
separately executed and recorded by the root task. These scripts do not call
Mac tools, run Lean, create a commit, push a branch, or change scientific
closure status.
