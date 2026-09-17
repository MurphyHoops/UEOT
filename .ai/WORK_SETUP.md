# ChatGPT Work Setup — Persistent Agent v2

v2 uses **Heartbeat-first liveness** and treats GitHub Event Trigger as an optional accelerator.

## Required: UEOT GitOps Heartbeat

Create one recurring ChatGPT scheduled Work task named `UEOT GitOps Heartbeat`, scheduled hourly when supported by the account.

Prompt:

> You are the UEOT persistent GitOps Heartbeat. Treat this invocation as disposable. Read `docs/REPOSITORY_BRANCH_GOVERNANCE.md`, `.ai/SYSTEM.md`, `.ai/protocols/HEARTBEAT.md`, `.ai/protocols/EVENTS.md`, and the selected Builder/Reviewer protocol. Recover active tasks from durable GitHub Issues, open PRs and `.ai/tasks/*/STATE.json`. Reconcile current main, PR head SHA, complete relevant diff/source, required checks, current GitHub Actions results and structured reviews. Select at most ONE actionable task. If CI is pending, do nothing. If required CI failed, perform exactly one bounded Builder repair. If the current head has CHANGES_REQUESTED, perform one bounded Builder repair. If required CI is green and the current head lacks a valid independent review, perform exactly one independent Reviewer pass. If current-head PASS + green CI exists, leave the human merge gate untouched. Ignore DONE, READY_TO_MERGE, unresolved BLOCKED, stale and duplicate work. Never create a replacement branch, write/merge main, force-push, wait for future CI, or rely on previous chat history. Persist the durable handoff and exit. If nothing is actionable, finish quietly.

## Optional: UEOT GitOps Event Accelerator

The existing GitHub event-triggered task may remain paused until desired. If enabled, accept that trigger-side marker filtering and bot-origin wake-ups may be incomplete. Its only purpose is lower latency.

Inside the prompt, no-op unless GitHub evidence shows an actionable current-head transition. Never depend on the accelerator for eventual continuation.

Recommended logical filtering after invocation:
- `[UEOT-AI-SIGNAL]` -> reconcile and route;
- `[UEOT-AI-REVIEW] result: CHANGES_REQUESTED` -> Builder;
- PASS, ordinary comments and bookkeeping -> no-op.

## Manual fallback

A fresh chat can always say: `Recover the active UEOT task from GitHub and execute exactly one bounded next transition using .ai/SYSTEM.md and .ai/protocols/HEARTBEAT.md. Do not rely on previous chat history.`

## Deployment order

1. independently review and human-merge bootstrap PR;
2. verify State Guard / CI Signal on `main`;
3. create and enable the hourly Heartbeat;
4. test Heartbeat recovery on one disposable task;
5. optionally enable Event Accelerator and compare latency/no-op cost;
6. only then use unattended continuation for substantive UEOT work.
