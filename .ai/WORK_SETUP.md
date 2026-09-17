# Optional ChatGPT Work Setup — Persistent Agent v3

v3 does **not** require ChatGPT Work, scheduled tasks, event-triggered Work or Codex for normal operation.

Default path: ordinary ChatGPT Chat + GitHub connector + GitHub Actions.

## Recommendation

Keep `UEOT GitOps Router` paused by default. Do not create an hourly Heartbeat merely for resumability. A fresh ordinary Chat can resume with `/ueot-resume`.

## Optional Event Accelerator

If lower latency is worth additional agentic usage, an event-triggered Work task may be enabled as a best-effort accelerator. It must re-read GitHub, base trust policy and current `(base, head)` before acting; event text itself is never authority.

## Optional Scheduled Heartbeat

A temporary scheduled Heartbeat may be enabled for unattended windows. It processes at most one actionable transition and exits immediately on pending/no-op states.

## Merge authority

Whether invoked from ordinary Chat or optional Work, a worker may merge to `main` only under `.ai/TRUST_POLICY.json` and `.ai/OPERATIONS.md`. Builder self-approval remains forbidden. Direct-main writes are reserved for explicit recovery/maintenance exceptions.

## Deployment order

1. obtain independent technical PASS for bootstrap PR #102 under the owner-authorization bootstrap rule;
2. AI merges #102 using the exact reviewed head SHA;
3. verify policy/workflows on resulting `main`;
4. prove fresh-chat `/ueot-resume` recovery on a disposable task;
5. keep Work automation paused unless temporary automation is worth its agentic usage.
