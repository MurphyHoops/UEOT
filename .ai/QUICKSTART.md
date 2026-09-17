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
2. Confirm `UEOT AI Agent State Guard` succeeds on `main`.
3. Configure the ChatGPT Work GitHub-event trigger described in `.ai/WORK_SETUP.md`.
4. Test it with a small disposable task before relying on unattended continuation.

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
  --required-check validate-state \
  --required-check build
```

Use the actual GitHub **job/check names** required for that task. `validate-state` is the
persistent-state guard; `build` is the existing UEOT Core Lean job. A GI/QM task can name
its own checks without modifying the orchestrator.

Then edit `.ai/tasks/issue-123/GOAL.md` with exact success criteria, commit the task state
with the implementation on the same branch, and open one PR to `main`.

If working entirely through ChatGPT/GitHub, tell the Builder to create the same two task
files using `.ai/schema/task-state.schema.json` and an existing Issue task as the pattern.

## Normal loop

1. Builder performs one bounded implementation iteration on the existing branch.
2. The same commit checkpoints task state as `WAITING_CI`.
3. PR CI starts. The state guard validates state and waits for every `required_checks` gate.
4. It posts one deduplicated `[UEOT-AI-SIGNAL]` comment with `success`, `failure`, or `blocked`.
5. ChatGPT Work starts a fresh invocation from that GitHub event.
6. Green CI routes to independent review; failure routes to one Builder repair; blocked
   routes to gate/configuration recovery.
7. Review changes route back to Builder. Review pass + green CI reaches the human merge gate.
8. Human merges to `main` and retires the temporary branch under repository governance.

No previous chat needs to remain alive.

## Manual fallback

If the external Work event trigger does not fire, start any fresh ChatGPT conversation in
the UEOT Project and say:

> Recover the active UEOT task from GitHub. Read repository governance, the durable live
> Issue, `.ai/SYSTEM.md`, current PR/head/CI/reviews, and the task `STATE.json`. Reconcile
> GitHub reality, execute exactly the recorded next bounded action, persist the handoff,
> and stop. Do not rely on previous conversation history.

This fallback is intentionally conversation-independent.
