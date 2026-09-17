# Heartbeat Protocol v3 — Optional Scheduled Acceleration

The Heartbeat is no longer the primary liveness mechanism. In v3 it is an optional scheduled Work accelerator that may be enabled temporarily when unattended progression is worth additional agentic usage.

## Default state

Disabled / not configured for baseline operation.

Primary continuation is a fresh ordinary ChatGPT conversation invoking `/ueot-resume` under `.ai/protocols/CHAT.md`.

## If enabled

Each scheduled run is a disposable worker that:

1. reads governance/System/resource policy;
2. reconciles active Issue/PR/head/CI/reviews/state;
3. selects at most ONE actionable task;
4. performs at most ONE bounded transition;
5. persists the handoff and exits.

## Route

- required CI running/pending -> no mutation; exit;
- required CI failed -> one Builder repair;
- current-head `CHANGES_REQUESTED` -> one Builder repair;
- green current-head CI without valid independent review -> one Reviewer pass;
- current-head PASS + green CI -> human merge gate; no mutation;
- no actionable task -> quiet no-op.

## Cost and loop controls

- never poll repeatedly inside one run;
- never process more than one task per heartbeat;
- never create bookkeeping-only commits;
- never repeat an already-completed transition;
- disable the Heartbeat when unattended operation is no longer needed.

Heartbeat failure never damages resumability because GitHub remains authoritative and `/ueot-resume` can recover manually.
