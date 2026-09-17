# Persistent Agent Quickstart

## What this solves

A ChatGPT Work run can end after a limited runtime and a conversation can eventually hit
its turn/context limits. This runtime does not remove those product limits. It removes the
requirement that the *same conversation* stay alive.

The durable task lives in GitHub:

`Issue + one branch + one PR + CI + .ai task state`

A fresh Work invocation can recover and continue from those facts.

## One-time repository bootstrap

1. Merge the reviewed runtime bootstrap PR to `main`.
2. Confirm both workflows exist on `main`:
   - `UEOT AI Agent State Guard`
   - `UEOT AI CI Signal`
3. Configure the ChatGPT Work GitHub-event trigger described in `.ai/WORK_SETUP.md`.
4. Test it with a small disposable task before relying on automatic continuation.

## Start a new persistent task

Create one durable GitHub Issue, then one branch for that Issue. Do not create a new branch
when a ChatGPT conversation changes.

If using a local shell, scaffold state with:

```bash
python scripts/ai/init_task.py \
  --issue 123 \
  --objective "Formalize theorem X without strengthening the frozen source assumptions" \
  --branch formal/theorem-x \
  --base-sha <40-char-main-sha> \
  --required-check build
```

Then edit `.ai/tasks/issue-123/GOAL.md` with exact success criteria, commit the task state
on the same branch, and open one PR to `main`.

If working entirely through ChatGPT/GitHub, ask the worker to create the same two files by
following `.ai/schema/task-state.schema.json` and the existing Issue task as an example.

## Normal automatic loop

1. Builder performs one bounded implementation iteration.
2. Builder checkpoints `STATE.json` as `WAITING_CI`, pushes, and exits.
3. GitHub Actions executes real checks.
4. `UEOT AI CI Signal` posts one deduplicated `[UEOT-AI-SIGNAL]` comment after required checks settle.
5. ChatGPT Work wakes a new invocation.
6. Green CI routes to independent review; failed CI routes to Builder repair.
7. Review changes route back to Builder; review pass + green CI produces `READY_TO_MERGE`.
8. Human merges to `main`.

At no point is the previous chat required to remain alive.

## Manual fallback

If the external Work event trigger does not fire, start any fresh ChatGPT conversation in
the UEOT Project and say:

> Recover the active UEOT task from GitHub. Read repository governance, the durable live
> Issue, `.ai/SYSTEM.md`, current PR/head/CI, and the task `STATE.json`. Reconcile GitHub
> reality, execute exactly the recorded next bounded action, checkpoint, and stop. Do not
> rely on previous conversation history.

This fallback is intentionally conversation-independent.
