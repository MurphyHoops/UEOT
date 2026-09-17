# Event Protocol v3 — Optional Work Acceleration

GitHub event-triggered Work is optional. v3 does not depend on it for liveness, correctness or recovery.

## Trust boundary

Any event worker must resolve `.ai/TRUST_POLICY.json` from the PR **base SHA**. Candidate HEAD never defines who may approve itself or what evidence authorizes merge.

Structured artifacts are navigation evidence until verified against current `(base_sha, head_sha)`, base-policy reviewer authorization and applicable protected-CI/elevated-review rules.

## Event aggregates

Trusted relay may emit:

- `success` — ordinary protected CI settled green;
- `failure` — protected CI or candidate declaration failed;
- `review-required` — trust/runtime/unmatched/protected-input changes require elevated independent review.

## Optional event worker

If deliberately enabled:
1. re-read GitHub and base trust policy;
2. reject stale `(base, head)`, duplicate or already-completed transitions;
3. route `failure` to one Builder repair;
4. route `success` to independent protected-ci review if no current review exists;
5. route `review-required` to independent elevated review;
6. route authoritative current-pair PASS to an AI merge transition if all policy conditions are met;
7. persist the handoff and exit.

Builder self-approval remains forbidden. Event delivery is never required; a later ordinary Chat `/ueot-resume` can derive the same transition from GitHub.
