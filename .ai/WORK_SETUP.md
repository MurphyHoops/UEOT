# Optional ChatGPT Work Setup — Persistent Agent v3

v3 does **not** require ChatGPT Work, scheduled tasks, event-triggered Work or Codex for normal operation.

The default path is ordinary ChatGPT Chat + GitHub connector + GitHub Actions. See `.ai/protocols/CHAT.md` and `.ai/RESOURCE_POLICY.md`.

## Default recommendation

Keep `UEOT GitOps Router` paused. Do not create or enable an hourly Heartbeat merely for baseline resumability.

After a conversation ends, open a fresh ordinary ChatGPT conversation and use `/ueot-resume`.

## Optional Event Accelerator

If lower latency is worth additional agentic usage, the GitHub event-triggered Work task may be enabled as a best-effort accelerator. It must not be required for correctness because marker filtering and bot-origin trigger behavior may be incomplete.

Inside the Work prompt, no-op unless current GitHub evidence shows exactly one actionable transition. PASS, ordinary comments, stale events and bookkeeping are no-op.

## Optional Scheduled Heartbeat

If unattended progression is temporarily more valuable than conserving agentic usage, a scheduled Work Heartbeat may be enabled using `.ai/protocols/HEARTBEAT.md`.

The Heartbeat must process at most one actionable task and exit immediately on pending CI or no-op state. Disable it when the unattended window is over.

## Manual/default resume

Open a normal ChatGPT conversation with GitHub access and say:

> `/ueot-resume`

or:

> Recover the active UEOT task from GitHub using `.ai/SYSTEM.md` and `.ai/protocols/CHAT.md`. Reconcile current Issue/PR/head/CI/reviews/state, execute exactly one bounded next transition, persist the handoff, and stop. Do not rely on previous chat history.

## Deployment order

1. independently review and human-merge the runtime PR;
2. verify repository CI/state machinery on `main`;
3. use ordinary Chat as the normal UEOT development worker;
4. prove fresh-chat `/ueot-resume` recovery on a disposable task;
5. leave Work automation paused by default;
6. enable Event/Heartbeat only for deliberate temporary automation experiments.
