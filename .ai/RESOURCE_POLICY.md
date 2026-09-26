# Persistent Agent v3 Resource Policy

The v3 default optimizes for ordinary ChatGPT usage plus GitHub-hosted execution.

## Default path

- reasoning / planning / repository edits: ordinary ChatGPT conversation with GitHub connector;
- durable state: GitHub Issue + branch + PR + `.ai/tasks/*`;
- deterministic execution: GitHub Actions;
- continuation after a chat ends: open a fresh ordinary chat and invoke `/ueot-resume`.

## Optional escalation

Work, scheduled tasks, GitHub event-triggered Work and Codex are optional. Enable them only when their automation or interactive coding value is worth the agentic usage cost.

No task may require those optional services for correctness, recovery, or merge eligibility.

## Design consequence

v3 guarantees resumability, not unattended autonomy. A task may wait after CI until a new ordinary ChatGPT conversation resumes it. That wait is acceptable because state is durable and reconstructable from GitHub.
