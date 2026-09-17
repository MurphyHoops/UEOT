# ChatGPT Work Setup Contract

Repository code creates durable state and GitHub wake-up signals, but the ChatGPT Work
GitHub-event subscription is configured in ChatGPT, outside this repository.

## Recommended setup: one router worker

The simplest production configuration is one GitHub-event-triggered Work task whose
instruction is to route itself from repository evidence:

- `[UEOT-AI-SIGNAL] aggregate: success` + `WAITING_CI` -> run the independent Reviewer protocol;
- `[UEOT-AI-SIGNAL] aggregate: failure` -> run the Builder repair protocol;
- GitHub review/request-changes event -> run the Builder protocol;
- `READY_TO_MERGE`, `BLOCKED`, `DONE`, duplicate event key, or stale SHA -> no mutation.

Because each invocation starts by re-reading GitHub and processes one bounded event, the
conversation that handled the previous iteration is not required.

### Router startup instruction

1. Read `docs/REPOSITORY_BRANCH_GOVERNANCE.md`.
2. Read `.ai/SYSTEM.md`, `.ai/protocols/EVENTS.md`, and the role protocol selected by the event.
3. Recover task from PR -> `.ai/tasks/*/STATE.json` -> durable Issue.
4. Reconcile PR head, diff, current source, checks, and Issue before acting.
5. Reject duplicate event keys and stale SHAs.
6. Perform exactly one bounded Builder or Reviewer transition.
7. Checkpoint durable state and finish. Never wait in-chat for the next CI/event.
8. Never merge `main`.

## Hardened setup: two logical workers

For stronger role separation, create a Builder-triggered Work task and a Reviewer-triggered
Work task. Both may receive the same event, but each must no-op unless repository state and
event type match its role.

### Builder

Acts only on CI failure, `CHANGES_REQUESTED`, or an explicit human resume event. It may
modify the existing task branch, run/inspect checks, and checkpoint `WAITING_CI`.

### Reviewer

Acts only after required CI is green. It independently reads Issue goal, current PR diff,
source, and checks. It must not rely on Builder completion claims as evidence, and it must
not repair implementation source and approve that same repair.

## Activation/bootstrap sequence

The CI relay uses GitHub `workflow_run`, which becomes effective only after
`.github/workflows/ai-ci-signal.yml` is present on the default branch (`main`). Therefore:

1. merge the one-time bootstrap PR after independent review;
2. verify `UEOT AI CI Signal` exists on `main`;
3. create the ChatGPT Work GitHub-event trigger(s);
4. point trigger scope at `MurphyHoops/UEOT` PR activity/comments/reviews;
5. instruct the task to act only on `[UEOT-AI-SIGNAL]` comments or explicit review-change events;
6. run a small disposable test Issue/branch/PR and verify a CI-settled comment wakes a fresh Work invocation;
7. only then use the runtime for substantive UEOT work.

Do not make a ChatGPT conversation URL part of persistent state. Conversations are
replaceable compute instances; GitHub is the handoff substrate.
