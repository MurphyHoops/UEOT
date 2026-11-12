# C review of source reuse, actual execution, and CI fallback

Date: 2026-11-12 (Asia/Shanghai). Reviewer: native research agent C.

## Reviewed current files

- `physics/qm/growing_cutoff/verify_inherited_evidence.py`
  SHA256 `569b399e19faa4f5e662d40762e6b7543f75a339d59dd79245030a436152c2ff`.
- `physics/qm/growing_cutoff/run_verification.py`
  SHA256 `b97d9dfe0c99f3408375a109838d5f48557ebf6c301325354ad3148c11a9c819`.
- `.github/workflows/ueot-qm.yml`
  SHA256 `9ffe79e4d7b58458528ee875742361653194cd71dbe33d8842c99e429bac5fee`.

These hashes identify the actual reviewed versions; later changes need their own targeted review.

## Source reuse

The verifier pins the historical source manifest, Lean verification receipt, main workflow identity, Lean inspection receipt, and now the original v31.11 runtime receipt. C found that the first draft read the old runtime receipt without pinning it, permitting an altered empty input list to masquerade as identical runtime inputs. **Resolved:** the runtime receipt is pinned to `44c4d1a1e06144c1b8f7932fc576cba5e17e0fdf669a0198f480e390c5547523` and checked for PASS, 13 inputs and seven commands.

The 158 recorded proof/configuration inputs are hashed against their actual current bytes. A complete proof/tool inventory comparison also detects newly added or changed files outside the old manifest. Source mismatch selects a fresh full Lean verification; equality permits reuse of the specifically identified v31.11 execution. The output explicitly reports zero new Lean theorems/execution and does not promote the new paper statements to machine proofs.

C's independent publication verifier separately read and hashed all 158 inputs and checked the source-reuse receipt. This repeated identity inspection does not rerun the historical compiler or heavy proof suite.

## New runtime identity

The runner executes exactly the four new commands, records actual UTC times and exit codes, and binds input bytes before/after execution plus actual outputs/logs. It uses `local_python_process` or actual GitHub environment fields, records observed HEAD and a dirty-worktree flag, and explains that hashes identify dirty-worktree source. It does not write a fixed author name as the executor.

The independent publication checker separately inspected all four resulting reports: source integration, A's operational controls, B's microscopic controls, and C's exact certificate. Each is tied to current model/checker bytes. Actual statuses, report check counts, and the explicit small numerical carrier domain are checked. New runtime evidence remains distinct from reused Lean evidence and absent device data.

## Workflow fallback

Both checkout steps fetch full history, so the pinned historical source object is normally available. All original full Lean gates remain present: source capture, dependency lock, official compiler installation, dependency/cache setup, proof-escape check, full module build, axiom audit, generated-certificate negative witnesses and retained finite witnesses.

The first workflow draft failed the job safely if the source-detection step itself errored, but did not actually fall back to the full build because subsequent `if` expressions have implicit success conditions. **Resolved:** the detector now has `continue-on-error: true`, and every full-proof gate uses `proof_scope.outcome != 'success' || proof_scope.outputs.reuse != 'true'` (with the additional cache-miss conjunct for saving the cache). An error or explicit mismatch therefore selects the original full gates; later genuine full-proof failures still block subsequent success. Exact successful reuse skips only those unchanged heavy gates. The archive step is `always()` and includes the actual reuse receipt.

The runtime job executes the new four-command pipeline and independent book-3.9 check. Chinese and English canonical sources both trigger the workflow after the requested English-path addition.

## Verdict and limits

**PASS after the stated corrections.** No historical heavy verification was rerun for this review. This is internal AI source/workflow review and byte-identity verification, not evidence that the remote workflow has already run or that a PR has merged. Final publication metadata/PDF identities remain subject to the independent `--require-complete` gate after the actual final files exist.
