# Persistent Agent v2 Quickstart

## What changes

Work/chat limits remain, but a task no longer depends on any one conversation or event webhook.

Durable task identity:

`Issue + one branch + one PR + CI + .ai state`

Liveness:

`hourly Heartbeat (primary) + GitHub Event Trigger (optional accelerator) + manual fresh-chat fallback`

## Bootstrap

1. independently review and human-merge runtime PR #102;
2. confirm the AI workflows are on `main`;
3. create `UEOT GitOps Heartbeat` from `.ai/WORK_SETUP.md`;
4. keep the existing Event Trigger paused initially;
5. prove one disposable task can advance after its original chat is gone;
6. optionally enable the Event Accelerator.

## Start a persistent task

Create one durable Issue and one branch. Scaffold `.ai/tasks/issue-N/{GOAL.md,STATE.json}` with `scripts/ai/init_task.py`, list real GitHub job names in `required_checks`, and open one PR.

## Normal loop

Builder -> commit/WAITING_CI -> GitHub Actions -> either Event Accelerator wakes early OR next Heartbeat inspects state -> Builder/Reviewer -> human merge gate.

If CI finishes at 10:07 and no supported event wakes Work, an hourly Heartbeat may pick it up at the next scheduled run. This is latency, not loss of state.

## Manual recovery

Open any fresh ChatGPT/Work conversation and say:

> Recover the active UEOT task from GitHub. Read repository governance, `.ai/SYSTEM.md`, `.ai/protocols/HEARTBEAT.md`, current Issue/PR/head/CI/reviews and task state. Execute exactly one actionable bounded transition and persist the handoff. Do not rely on previous conversation history.
