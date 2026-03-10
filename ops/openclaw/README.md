# OpenClaw UEOT Operations

This directory contains the operational layer for the UEOT Omega Research
System.

## Key Scripts

- `scripts/provision_ueot_openclaw.sh`
  Creates agent worktrees, installs local workspace files, registers OpenClaw
  agents, configures memory search, installs local skills, and provisions cron.
- `scripts/install_workspace_files.sh`
  Seeds agent-local `SOUL.md`, `IDENTITY.md`, `USER.md`, `HEARTBEAT.md`,
  `MEMORY.md`, and per-worktree git excludes.
- `scripts/install_local_skills.sh`
  Symlinks repo-local UEOT skills into the OpenClaw main workspace.
- `scripts/reindex_ueot_memory.sh`
  Rebuilds OpenClaw memory indexes for all UEOT agents when a remote embedding
  provider is available.
- `scripts/build_shared_memory_registry.py`
  Rebuilds the file-first shared memory registry used when embedding-backed
  memory search is unavailable or quota-limited.
- `scripts/validate_ueot_system.sh`
  Verifies repo structure, OpenClaw agent registration, cron inventory, and
  the shared-memory registry.

## Runtime Notes

- Canonical repo: `/home/ubuntu/ueot`
- Agent worktrees: `/home/ubuntu/ueot-agents/<agent-id>`
- Canonical docs remain in the repo; role files are copied into each worktree
  as local operational files.
- This environment does not rely on local embedding models. Shared memory is
  anchored by `memory/shared/UEOT_MEMORY_REGISTRY.yaml`, and OpenClaw memory
  search is treated as an optional remote enhancement.
- Docker sandboxing is not enabled by default in this environment. Filesystem
  scope is still constrained via workspace-only tool policy and isolated
  worktrees.
