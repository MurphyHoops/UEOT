# Persistent Agent v3 Quickstart

## What v3 solves

A ChatGPT conversation can end, but the UEOT task does not depend on that conversation. Durable task identity is:

`Issue + one branch + one PR + CI + .ai state`

Default execution is:

`ordinary ChatGPT Chat + GitHub connector + GitHub Actions`

Default continuation is:

`new ordinary Chat -> /ueot-resume`

Work/Event/Heartbeat/Codex are optional accelerators or escalations and are disabled by default.

## Bootstrap

1. independently review and human-merge runtime PR #102;
2. confirm state/CI workflows are on `main`;
3. leave `UEOT GitOps Router` paused;
4. do not create an hourly Work Heartbeat for baseline use;
5. prove one disposable task can be resumed from a fresh ordinary Chat using `/ueot-resume`.

## Start a persistent task

Create one durable Issue and one branch. Scaffold `.ai/tasks/issue-N/{GOAL.md,STATE.json}` with `scripts/ai/init_task.py`, list real GitHub job names in `required_checks`, and open one PR.

## Normal loop

1. ordinary Chat recovers/reconciles GitHub;
2. Builder performs one bounded change and checkpoints `WAITING_CI`;
3. GitHub Actions runs build/test/Lean/validation;
4. when convenient, open/resume an ordinary Chat and invoke `/ueot-resume`;
5. green CI routes to independent review; failure/CHANGES_REQUESTED routes to one Builder repair;
6. current-head PASS + green CI reaches the human merge gate.

No previous conversation is required.

## Canonical resume

`/ueot-resume`

Equivalent prompt:

> Recover the active UEOT task from GitHub. Read repository governance, `.ai/SYSTEM.md`, `.ai/RESOURCE_POLICY.md`, `.ai/protocols/CHAT.md`, current Issue/PR/head/CI/reviews and task state. Execute exactly one actionable bounded transition and persist the handoff. Do not rely on previous conversation history.

## Optional automation

Enable Work Event Trigger or scheduled Heartbeat only when lower latency/unattended progression is worth the additional agentic usage. They are not required for correctness or recoverability.
