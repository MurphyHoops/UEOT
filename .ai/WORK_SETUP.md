# ChatGPT Work Setup Contract

Repository code creates durable state and GitHub wake-up signals. The ChatGPT Work
GitHub-event subscription is configured in ChatGPT, outside this repository.

## Recommended setup: one router worker

Create one GitHub-event-triggered Work task scoped to the UEOT repository. It should wake
on PR comments/reviews and route itself from current GitHub evidence:

- `[UEOT-AI-SIGNAL] aggregate: success` -> independent Reviewer path;
- `[UEOT-AI-SIGNAL] aggregate: failure` -> Builder repair path;
- `[UEOT-AI-SIGNAL] aggregate: blocked` -> diagnose missing/stuck required checks;
- review/request-changes event -> Builder path;
- duplicate event, stale SHA, `READY_TO_MERGE`, `BLOCKED`, or `DONE` -> no mutation.

### Router startup instruction

Use the following as the Work task instruction:

> You are the UEOT persistent GitOps router. Treat each invocation as disposable. First
> read `docs/REPOSITORY_BRANCH_GOVERNANCE.md`, `.ai/SYSTEM.md`, `.ai/protocols/EVENTS.md`,
> and the current PR/Issue/task state from GitHub. Reconcile the current PR head SHA,
> complete diff, relevant source, required checks, reviews, and durable Issue before doing
> anything. Reject stale or duplicate events. For a failed CI signal run exactly one
> bounded Builder repair using `.ai/protocols/BUILDER.md`; for a green CI signal run an
> independent review using `.ai/protocols/REVIEWER.md`; for a blocked signal diagnose the
> missing/stuck gate and either repair configuration or record a precise BLOCKED state.
> Never create a new branch because the conversation changed. Never merge `main`. Persist
> the durable handoff in GitHub, then finish instead of waiting for the next event.

## Hardened setup: two logical workers

For stronger role separation, create two event-triggered Work tasks:

- **Builder** acts only on failed/blocked CI, review changes, or explicit human resume.
- **Reviewer** acts only after required CI is green and independently reads Issue goal,
  current PR diff/source, checks, and affected tests/specification.

Both workers must no-op if repository evidence does not match their role. This prevents
simultaneous event delivery from producing duplicate mutations.

## Activation sequence

1. Review and merge the runtime bootstrap PR to `main`.
2. Confirm `UEOT AI Agent State Guard` is green on `main`.
3. Create the ChatGPT Work GitHub-event trigger(s) using the instruction above.
4. Scope the trigger to `MurphyHoops/UEOT` PR comments/reviews.
5. Run one disposable Issue/branch/PR test and verify a `[UEOT-AI-SIGNAL]` comment wakes a
   fresh Work invocation.
6. Only then rely on unattended continuation for substantive UEOT work.

The PR orchestrator itself can be exercised on the bootstrap PR before merge, but stable
production use should start after the reviewed runtime exists on `main`.

Do not store ChatGPT conversation URLs as task state. Conversations are replaceable
compute instances; GitHub is the handoff substrate.
