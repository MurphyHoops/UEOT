# Persistent Agent Quickstart

## What this solves

A Work run can end and a conversation can hit its limits. This runtime does not remove
those product limits; it makes the conversation disposable.

The durable task lives in GitHub:

`Issue + one branch + one PR + CI + .ai task state`

A fresh invocation recovers from those facts.

## One-time bootstrap

1. Independently review and human-merge the runtime bootstrap PR to `main`.
2. Confirm `UEOT AI Agent State Guard` and `UEOT AI CI Signal` are present on `main`.
3. Configure the ChatGPT Work GitHub-event task in `.ai/WORK_SETUP.md`.
4. Prove the full loop on one disposable task.

## Start a persistent task

Create one durable GitHub Issue and one branch for that Issue. A conversation change never
creates a replacement branch.

Local scaffold example:

```bash
python scripts/ai/init_task.py \
  --issue 123 \
  --objective "Formalize theorem X without strengthening the frozen source assumptions" \
  --branch formal/theorem-x \
  --base-sha <40-char-main-sha> \
  --required-check validate-state \
  --required-check build
```

`required_checks` are GitHub job/check names. For UEOT Core Lean, the existing job is
`build`. GI/QM tasks can name their own checks without changing the relay.

Edit `GOAL.md` with externally checkable success criteria. Every Builder implementation
checkpoint must also update its task state so the State Guard runs for that PR head.

## Automatic loop

1. Builder performs one bounded implementation iteration on the existing branch.
2. The implementation checkpoint records `WAITING_CI` and is pushed to the same PR.
3. State Guard validates the task; trusted CI Signal waits for all `required_checks`.
4. CI Signal posts one `[UEOT-AI-SIGNAL]` PR comment: `success`, `failure`, or `blocked`.
5. ChatGPT Work starts a fresh invocation from that PR event.
6. Success routes to independent review; failure to one repair iteration; blocked to gate
   recovery/human decision.
7. Review changes route back to Builder. Review pass + green CI reaches the human merge gate.
8. Human merges and the temporary branch is retired under repository governance.

The previous chat is never required.

## Manual fallback

If the event-triggered Work task does not fire, start any fresh ChatGPT conversation in the
UEOT Project and say:

> Recover the active UEOT task from GitHub. Read repository governance, the durable live
> Issue, `.ai/SYSTEM.md`, current PR/head/CI/reviews, and the task state. Reconcile GitHub
> reality, execute exactly the recorded next bounded action, persist the handoff, and stop.
> Do not rely on previous conversation history.
