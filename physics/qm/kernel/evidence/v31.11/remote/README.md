# Observed remote execution evidence

These records preserve GitHub execution identities separately from the local
new-module and seven-command receipts. The scientific PR is
[457](https://github.com/MurphyHoops/UEOT/pull/457); its accepted head is
`366e0bbf0e895d0d3125d7769cb4b4d1d6d17069`. The scientific merge is
`06ca0dce8b03cd34e86785e97fdc3c7aa2c582bd`, with exactly the same tree.

- `pr457-first-head/` retains the original runtime artifact at
  `78aad3c7859084a918c00e655cf198b7b5beecf2`. Computation passed, but the v1
  runner's hard-coded actor label was wrong for CI. That workflow was
  superseded/cancelled when the corrected head was pushed. The old ZIP is
  unaltered and is not the accepted v2 runtime evidence.
- `pr457/` holds the accepted-head runtime and proof archives, their
  independent source/record inspections, and exact tree-overlay checks.
- `main/` holds the scientific-merge execution archives and their independent
  inspections. Only actual existing receipts determine completed states.
- `scientific-main-tree-readback.json` is the earlier exact-tree readback;
  its then-pending CI state is historical. Final CI completion is recorded
  separately in `../integration-verification.json`.

The read-only inspectors are in
`physics/qm/audits/OPERATIONAL_MICRO_ROBUST_v31.11/`:
`verify_remote_runtime_artifact.py` and `verify_remote_lean_artifact.py`.
They require the named Git commit to be available locally and compare the
downloaded ZIP digest with the actual GitHub artifact metadata. The recorded
commands show the temporary download locations actually used; the same ZIP
bytes are retained here for reproducibility.

The CI public source inventory has 130 entries. Its recursive proof-module
witness inventory has 148 module sources; the local targeted closure has 158
proof/configuration inputs. These are different inventories with different
scopes, not interchangeable counts. The public axiom archive contains 1365
requested/report-matched constants, including all 80 new operational
namespace constants. Their accepted dependencies are only `propext`,
`Classical.choice` and `Quot.sound`.

The six positive generated certificates, four rejected false claims with
accepted false-check witnesses, and thirteen retained finite witness scripts
keep their own source and log identities. Logs from deliberately failed
Lean elaborations may show temporary `sorryAx` placeholders. Such failed
candidates are preserved as negative controls and never counted as accepted
proofs; every accepted audit is separately checked against the allowed set.

None of these CI checks proves the paper-only normal trace-class,
infinite-dimensional, robust-calibration or complete OPT statements.
Synthetic records remain synthetic; there is no new hardware evidence.
