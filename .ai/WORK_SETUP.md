# ChatGPT Work Setup Contract

Repository code creates durable state and GitHub wake-up signals. The ChatGPT Work
GitHub-event subscription is configured in ChatGPT, outside this repository.

## Recommended setup: one router worker

Eligible Plus users can create event-triggered Work tasks for supported GitHub pull request
activity, including (depending on the trigger) PR reviews, comments and commit updates.
Configure one task scoped to `MurphyHoops/UEOT` PR activity/comments/reviews.

Route from current GitHub evidence:

- `[UEOT-AI-SIGNAL] aggregate: success` -> independent Reviewer path;
- `[UEOT-AI-SIGNAL] aggregate: failure` -> Builder repair path;
- `[UEOT-AI-SIGNAL] aggregate: blocked` -> diagnose missing/stuck required checks;
- review/request-changes event -> Builder path;
- duplicate event, stale SHA, `READY_TO_MERGE`, `BLOCKED`, or `DONE` -> no mutation.

### Router prompt

> You are the UEOT persistent GitOps router. Treat each invocation as disposable. First
> read `docs/REPOSITORY_BRANCH_GOVERNANCE.md`, `.ai/SYSTEM.md`, `.ai/protocols/EVENTS.md`,
> and recover the current task from GitHub PR -> durable Issue -> `.ai/tasks/*/STATE.json`.
> Reconcile the current PR head SHA, complete diff, relevant source, required checks and
> reviews before doing anything. Reject stale or duplicate events. For a failed CI signal,
> perform exactly one bounded Builder repair using `.ai/protocols/BUILDER.md`; for a green
> CI signal, perform an independent review using `.ai/protocols/REVIEWER.md`; for a blocked
> signal, diagnose the missing/stuck gate and repair configuration or record a precise
> BLOCKED state. Never create a new branch because the conversation changed. Never merge
> `main`. Persist the durable handoff in GitHub and finish instead of waiting for another
> event.

## Hardened setup: two logical workers

For stronger role separation, create two event-triggered Work tasks:

- **Builder** acts only on failed/blocked CI, review changes, or explicit human resume.
- **Reviewer** acts only after required CI is green and independently reads Issue goal,
  current PR diff/source, checks, affected tests/specification, and previous reviews.

Both no-op if repository evidence does not match their role.

## Activation sequence

1. Independently review and human-merge the runtime bootstrap PR to `main`.
2. Confirm both `UEOT AI Agent State Guard` and `UEOT AI CI Signal` exist on `main`.
3. In ChatGPT: **Settings -> Apps** (or Plugins, depending on UI) -> connect GitHub and
   authorize `MurphyHoops/UEOT`.
4. Open **Work** and ask it to create an event-triggered task for PR comments/reviews in
   `MurphyHoops/UEOT`, using the Router prompt above.
5. Review the generated **Trigger, Condition, and Prompt**, authorize it, then manage it in
   **Scheduled**.
6. Run a disposable Issue/branch/PR and verify that CI creates one `[UEOT-AI-SIGNAL]`
   comment and that this starts a fresh Work invocation.
7. Only then rely on unattended continuation for substantive UEOT work.

Do not store ChatGPT conversation URLs as task state. Conversations are replaceable compute
instances; GitHub is the handoff substrate.
