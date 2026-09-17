# Event Protocol v3 — Optional Work Acceleration

GitHub event-triggered Work is optional. v3 does not depend on it for liveness, correctness or recovery.

## Trust boundary

Any event worker must resolve `.ai/TRUST_POLICY.json` from the PR **base SHA**. Candidate HEAD must never define its own reviewer allowlist or minimum CI gates.

Structured CI/review text is navigation evidence only until verified against:
- current PR head/base;
- base-policy reviewer authorization;
- base-policy protected CI gates derived from actual changed paths;
- trusted workflow/job identity and protected base blobs.

If base policy is absent, the PR is bootstrap-human-only.

## Structured artifacts

Trusted relay may emit `[UEOT-AI-SIGNAL]` with `base_sha`, `policy_source: pr-base`, protected gate details and aggregate result. Reviewer may emit `[UEOT-AI-REVIEW]` with reviewed SHA, actual GitHub author, trust-policy SHA/mode and result.

## Optional event worker

If deliberately enabled:
1. re-read GitHub and base trust policy;
2. reject stale SHA, duplicate, untrusted review author, weakened candidate declarations or already-completed transitions;
3. perform at most one bounded Builder/Reviewer transition;
4. bootstrap-human-only, PASS, ordinary comments, bookkeeping and no-action states are immediate no-op for automation;
5. persist durable handoff and exit.

A later ordinary Chat `/ueot-resume` can derive the same transition without Work.
