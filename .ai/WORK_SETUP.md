# ChatGPT Work Setup Contract

Repository code can create durable state and GitHub wake-up signals, but the ChatGPT Work
GitHub-event subscription is configured in ChatGPT, outside this repository.

Configure two logical workers for the same UEOT GitHub repository.

## Builder worker

Wake on structured PR comments containing `[UEOT-AI-SIGNAL]` and route only when current
state/evidence calls for Builder work (`CI_FAILED` or `CHANGES_REQUESTED`).

Startup instruction:

1. Read `docs/REPOSITORY_BRANCH_GOVERNANCE.md`.
2. Read `.ai/SYSTEM.md`, `.ai/protocols/EVENTS.md`, and `.ai/protocols/BUILDER.md`.
3. Recover the task from PR -> `.ai/tasks/*/STATE.json` -> Issue.
4. Reconcile PR head and CI before acting.
5. Process one new event key and one bounded iteration only.
6. Push the checkpoint and finish; do not wait for the next event.

## Reviewer worker

Wake on the same structured CI-settled signal, but act only when required CI is green and
the task should enter `REVIEWING`.

Startup instruction:

1. Read governance/system/event/Reviewer protocols.
2. Independently inspect Issue goal, PR diff, current head source, and required CI.
3. Do not trust Builder completion claims as evidence.
4. Emit actionable changes or a review-pass signal; do not modify implementation source
   and then approve the same repair.
5. Never merge `main`.

## Important

Do not make a ChatGPT conversation URL part of persistent state. Conversations are
replaceable compute instances. GitHub is the handoff substrate.
