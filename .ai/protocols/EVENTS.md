# Event Protocol v3 — Optional Work Acceleration

GitHub event-triggered Work is optional. v3 does not depend on it for liveness, correctness or recovery.

## Trust boundary

Any event worker must resolve `.ai/TRUST_POLICY.json` from the PR **base SHA**. Candidate HEAD must never define reviewer authorization or minimum CI gates for itself.

Structured CI/review text is navigation evidence only until verified against:
- current PR **base SHA + head SHA**;
- base-policy reviewer authorization;
- base-policy `human_only_paths` and path-derived protected gates;
- trusted workflow/job identity and protected base blobs;
- required GitHub platform enforcement.

If base policy is absent, the PR is bootstrap-human-only.

## Structured artifact identity

Trusted CI signal keys bind both revisions:

`ci-settled:<base_sha>:<head_sha>:<success|failure|blocked>`

Reviewer keys bind both revisions:

`review:<base_sha>:<head_sha>:<pass|changes-requested>`

A base change makes old artifacts stale even if head SHA is unchanged.

## Duplicate provenance

Relay idempotency must only treat an existing marker as a duplicate when GitHub metadata proves it was authored by the trusted relay identity (`github-actions[bot]`). An ordinary commenter copying a marker is not a duplicate and cannot suppress signal emission.

## Optional event worker

If deliberately enabled:
1. re-read GitHub and the base trust policy;
2. verify current `(base, head)` and platform enforcement;
3. reject stale pair, untrusted duplicate marker, untrusted review author, weakened candidate declarations or already-completed transitions;
4. perform at most one bounded Builder/Reviewer transition;
5. bootstrap-human-only, trust-critical changes, PASS, ordinary comments, bookkeeping and no-action states are no-op for automation;
6. persist durable handoff and exit.

A later ordinary Chat `/ueot-resume` can derive the same transition without Work.
