# Persistent Agent System Protocol v3

## Purpose

Keep UEOT development resumable across ordinary ChatGPT conversation limits while minimizing dependence on agentic Work/Codex execution.

## Mandatory startup

Every Builder, Reviewer or resume invocation must:

1. read `docs/REPOSITORY_BRANCH_GOVERNANCE.md` from integrated `main`;
2. read candidate `.ai/README.md`, `.ai/RESOURCE_POLICY.md`, this file, and the selected role protocol for behavior/navigation;
3. recover durable task candidates from GitHub Issue -> PR -> `.ai/tasks/*/STATE.json`;
4. reconcile current `main`, PR base/head SHA, complete relevant diff/source, current checks and structured reviews;
5. resolve authorization separately from candidate content: fetch `.ai/TRUST_POLICY.json` from the PR **base SHA** (or integrated `main` when no PR exists), never from candidate HEAD;
6. derive protected CI gates from that base policy and the actual changed paths; candidate `STATE.required_checks` is only a declaration mirror and cannot weaken base-derived gates;
7. authenticate structured review artifacts using actual GitHub author metadata against the **base-policy** reviewer allowlist;
8. resolve stale state by the repository truth order; never reconstruct correctness from chat memory.

## Bootstrap rule

If the PR base does not contain `.ai/TRUST_POLICY.json`, the candidate is installing the trust root. It cannot authorize itself. Automated structured review/CI artifacts are advisory only and the merge decision is **human-only** after explicit inspection. Once merged, that policy becomes the trust root for later PRs.

A change to `.ai/TRUST_POLICY.json` is evaluated under the old policy from the PR base and becomes effective only after merge.

## Bounded transaction

One invocation may execute at most one coherent task transition. Do not keep a conversation alive merely to wait for future CI.

Builder checkpoints increment `STATE.json.iteration` once per substantive implementation iteration. Reviewer PASS does not create a state-only code commit.

## Continuation invariant

The runtime must remain recoverable with Work, scheduled tasks and GitHub event-triggered Work completely disabled.

- Primary worker: ordinary ChatGPT Chat with GitHub connector (`protocols/CHAT.md`).
- Primary continuation: fresh ordinary chat + `/ueot-resume`.
- Optional acceleration: Work Heartbeat and GitHub Event Trigger.
- Optional coding escalation: Codex.

## Trust invariants

- candidate HEAD never defines who may approve that same candidate;
- candidate HEAD never defines the minimum CI gates that authorize itself;
- review trust and CI trust resolve from PR base / integrated `main`;
- marker text alone is never authoritative;
- protected CI gates bind to a base-approved workflow path + job name, and protected workflow/runner inputs must match base blobs;
- unmatched changed paths or protected trust-infrastructure changes degrade to human-only rather than silently weakening policy.

## Safety brakes

- one durable work item -> one active branch -> one PR;
- never write directly to `main` and never force-push;
- never create a replacement branch because a chat changed;
- reject stale SHA and duplicate work;
- `iteration <= max_iterations`;
- same root failure and consecutive CI failures obey task retry limits;
- Builder cannot self-approve;
- final merge is human-only unless repository governance is explicitly changed;
- optional automation must obey the same one-transition bound.

## Durable end states

`WAITING_CI`, `REVIEWING`, `CHANGES_REQUESTED`, `READY_TO_MERGE`, `BLOCKED`, or `DONE`.
