# A: bind the actual finite certificate artifacts

The prior runner could return CERTIFIED after actual Lean checked a replacement
comment-only file. This is an artifact identity defect, not a refutation of the
normal mathematical certificates.

`certify.py` now detaches and normalizes its input, hashes intended serialized
bytes, freezes input/candidate/proof/Core identity artifacts before build, and
checks those artifacts and Core/driver sources before and after both actual
commands. Missing or changed evidence returns UNKNOWN. The output directory is
new and has no other intended writer. Endpoint hashes do not claim to defeat an
arbitrary same-permission change-and-restore attacker.

Actual regression evidence at
`/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/longterm-audit-20261029`:

- `A-actual-proof-replacement-fixed-01/REGRESSION.json`: real build exit 0,
  real Lean on the comment replacement exit 0, corrected runner UNKNOWN;
  result SHA256 `3c7646c43363f3580c8d7f9cb28b639715fd1a4eba06136056d259b46b780ded`.
- `A-registered-fixed-01/result.json`: all eight prior statuses preserved,
  all four identity checkpoints pass; SHA256
  `f92514f2e21de8d4c97ff64086c0f9a476bc21d12642d8e8b45f0021a6b89aa2`.
- Focused test runner: actual positive/nonconstant-observation proof and actual
  comment-replacement proof; artifact mutation/deletion cases use explicit
  mocks and are not represented as real Lean experiments.
- `A-full-UEOT.log`: actual full `lake build UEOT`, exit 0.

This completes A's implementation/verification dependency. B–F remain the same
long-term contract, not completed by this repair. No resampling has occurred.
