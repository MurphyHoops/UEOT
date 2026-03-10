---
name: ueot-techops-openclaw
description: Operate the UEOT Omega system on OpenClaw. Use when managing agent workspaces, local skills, cron, memory indexing, health checks, or deciding whether a built-in skill solves an operational problem before creating a custom UEOT skill.
---

# UEOT TechOps OpenClaw

Use this skill for system operations.

## Decision Policy

1. Check whether OpenClaw already has a built-in skill that solves the task.
2. If yes, use or install it.
3. If no, create or refine a local UEOT-specific skill.

## Core Responsibilities

- agent provisioning
- workspace seeding
- cron registration
- memory indexing
- validation and recovery

## References

- See [references/ops-checklist.md](references/ops-checklist.md)
