# Heartbeat Protocol v3 — Optional Scheduled Acceleration

The Heartbeat is optional and disabled for baseline operation. Primary continuation is a fresh ordinary Chat invoking `/ueot-resume`.

## If enabled

Each scheduled run is disposable and must:

1. read governance/System/resource policy;
2. reconcile active Issue/PR/current `(base_sha, head_sha)`/diff/state;
3. fetch `.ai/TRUST_POLICY.json` from the PR base SHA;
4. verify required GitHub platform enforcement; unverifiable/missing enforcement => human-only;
5. if base policy is absent, a trust-critical path changed, protected inputs changed, or paths are unmatched, no-op into human-only/BLOCKED handling;
6. derive protected CI gates from base policy + actual changed paths and authenticate current-pair reviews against base-policy allowlist;
7. perform at most ONE bounded transition and exit.

## Route

- protected CI running/pending -> no mutation;
- protected CI failed -> one Builder repair;
- authoritative current-pair CHANGES_REQUESTED -> one Builder repair;
- protected CI green without valid current-pair independent review -> one Reviewer pass;
- authoritative current-pair PASS + protected CI green + platform enforcement -> human merge gate;
- bootstrap / trust-critical / unmatched / protected-input changed / unverified platform / no actionable task -> no autonomous authorization.

Never poll repeatedly, process more than one task, create bookkeeping-only commits, or substitute candidate-defined trust rules for PR-base policy. A base movement invalidates evidence even if head remains unchanged.
