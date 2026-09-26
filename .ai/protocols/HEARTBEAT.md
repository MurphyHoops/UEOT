# Heartbeat Protocol v3 — Optional Scheduled Acceleration

The Heartbeat is optional and disabled for baseline operation. Primary continuation is a fresh ordinary Chat invoking `/ueot-resume`.

## If enabled

Each scheduled run is disposable and must:

1. read governance/System/resource policy;
2. reconcile active Issue/PR/current `(base_sha, head_sha)`/diff/state;
3. fetch `.ai/TRUST_POLICY.json` from the PR base SHA;
4. derive protected-CI or elevated-review requirements from base policy + actual changed paths;
5. authenticate reviews/owner authorization from GitHub metadata;
6. perform at most ONE bounded transition and exit.

## Route

- CI running/pending -> no mutation;
- protected CI failed -> one Builder repair;
- current-pair CHANGES_REQUESTED -> one Builder repair;
- trust/runtime/unmatched/protected-input change -> one independent elevated review;
- protected CI green without valid independent review -> one protected-ci review;
- authoritative current-pair PASS -> merge-capable AI may merge to `main` with expected reviewed head;
- no actionable task -> no-op.

Never poll repeatedly, process multiple tasks in one run, create bookkeeping-only commits, or let Builder self-approve.
