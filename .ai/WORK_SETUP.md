# ChatGPT Work Setup Contract

Repository code creates durable state and GitHub wake-up signals. The ChatGPT Work
GitHub-event subscription is configured in ChatGPT, outside this repository.

## Recommended setup: one router worker

Create one GitHub-event-triggered Work task scoped to `MurphyHoops/UEOT` PR comments and
reviews. Use a condition so it runs **only** when the event is either:

1. a PR comment containing `[UEOT-AI-SIGNAL]`, or
2. a PR comment containing `[UEOT-AI-REVIEW]` and `result: CHANGES_REQUESTED`.

Do not wake on `[UEOT-AI-REVIEW] ... PASS` or bookkeeping text. PASS exposes the human
merge gate and needs no new model invocation.

Route from current GitHub evidence:

- signal `success` -> independent Reviewer path;
- signal `failure` -> Builder repair path;
- signal `blocked` -> diagnose missing/stuck required checks;
- structured `CHANGES_REQUESTED` -> Builder path;
- duplicate event, stale SHA, `READY_TO_MERGE`, `BLOCKED`, or `DONE` -> no mutation.

### Router prompt

> You are the UEOT persistent GitOps router. Treat each invocation as disposable. First
> read `docs/REPOSITORY_BRANCH_GOVERNANCE.md`, `.ai/SYSTEM.md`, `.ai/protocols/EVENTS.md`,
> and recover the current task from GitHub PR -> durable Issue -> `.ai/tasks/*/STATE.json`.
> Reconcile current PR head SHA, complete diff, relevant source, required checks, prior
> structured reviews and event-consumption markers before doing anything. Reject stale or
> duplicate events. For failed CI, perform exactly one bounded Builder repair using
> `.ai/protocols/BUILDER.md`; for green CI, perform an independent review using
> `.ai/protocols/REVIEWER.md`; for blocked CI, repair the gate/configuration or record a
> precise BLOCKED state; for structured CHANGES_REQUESTED, perform one Builder repair.
> Never create a new branch because the conversation changed. Never merge `main`. Persist
> the role-specific durable handoff and finish instead of waiting for another event.

## Hardened setup: two logical workers

For stronger role separation, create two event-triggered Work tasks with mutually exclusive
conditions:

- **Builder:** failed/blocked signals or structured CHANGES_REQUESTED only.
- **Reviewer:** successful CI signals only.

Both no-op if repository evidence does not match their role.

## Activation sequence

1. Independently review and human-merge the runtime bootstrap PR to `main`.
2. Confirm both `UEOT AI Agent State Guard` and `UEOT AI CI Signal` exist on `main`.
3. In ChatGPT, connect/authorize GitHub for `MurphyHoops/UEOT` if not already connected.
4. Open **Work** and ask it to create an event-triggered GitHub task using the Router prompt
   and filtering condition above.
5. Review the generated Trigger, Condition and Prompt, authorize it, then manage it in
   **Scheduled**.
6. Run a disposable Issue/branch/PR and verify: CI signal -> fresh Work invocation -> one
   structured review/repair artifact -> next state.
7. Only then rely on unattended continuation for substantive UEOT work.

Do not store ChatGPT conversation URLs as task state. Conversations are replaceable compute
instances; GitHub is the handoff substrate.
