# Private SourcePolicyPathBridge — actual focused compile receipt

Status: **PRIVATE_FOCUSED_COMPILE_PASS_STANDARD_AXIOMS_ONLY**.

The unchanged source compiled under the authorized Linux Lean runtime with `LEAN_NUM_THREADS=1`. Exactly one additional Lean process was active at a time; no `lake build` was launched. Production, Git, Mac, and remote state were not modified.

- Source SHA256: `108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`.
- Successful attempt: `lean-attempt-002/`.
- Actual Lean exit code: **0**.
- Elapsed time: **35.495 seconds**; no timeout.
- Full stdout/stderr: `lean-attempt-002/lean.log`.
- Compiled private artifact: `lean-attempt-002/SourcePolicyPathBridge.olean`.
- Both public endpoint declarations printed only `propext`, `Classical.choice`, and `Quot.sound`.

## Preserved failure

Attempt 1 failed before elaboration because generating the private `.olean` required its source to lie under the selected package root. Attempt 2 added `--root=<private source directory>` while retaining the production working directory and `lake env` import environment. The original source, failed log, and failed receipt remain unchanged. No theorem statement, hypothesis, or proof body was changed.

## Proven interface and scope

`actual_next_state_eq_stationary_row` identifies the next-state marginal of the actual action/state risk kernel with the stationary transition PMF derived from the same model and action PMFs. `actual_state_path_eq_stationary_path` identifies the action-erased complete microscopic state history with the existing `policyPathKernel` law, for every initial PMF and finite horizon.

The observation policy is time-independent and depends only on the current observation. The observation type need not be finite or Markov. Arbitrary history-dependent policies are outside this stationary reduction. Erasing action records transfers state-history events directly; action-dependent failures require the original record law or an additional factorization theorem.

This is a private focused compile result, not canonical integration or native export. The killed restriction and actual survival-event contract remains a separately reviewed mathematical contract that has not been formalized here.
