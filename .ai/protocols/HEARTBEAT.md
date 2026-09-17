# Heartbeat Protocol v3 — Optional Scheduled Acceleration

The Heartbeat is optional and disabled for baseline operation. Primary continuation is a fresh ordinary Chat invoking `/ueot-resume`.

## If enabled

Each scheduled run is disposable and must:

1. read governance/System/resource policy;
2. reconcile active Issue/PR/base/head/diff/state;
3. fetch `.ai/TRUST_POLICY.json` from the PR **base SHA**;
4. if base policy is absent, trust infrastructure changed, or changed paths are unmatched, no-op into human-only/BLOCKED handling;
5. derive protected CI gates from base policy + actual changed paths and authenticate reviews against the base-policy allowlist;
6. perform at most ONE bounded transition and exit.

## Route

- protected CI running/pending -> no mutation;
- protected CI failed -> one Builder repair;
- authoritative current-head CHANGES_REQUESTED -> one Builder repair;
- protected CI green without valid independent review -> one Reviewer pass;
- authoritative current-head PASS + protected CI green -> human merge gate;
- bootstrap-human-only / unmatched / protected trust-input changed / no actionable task -> no autonomous authorization.

Never poll repeatedly, process more than one task, create bookkeeping-only commits, or substitute candidate-defined trust rules for the PR-base policy.
