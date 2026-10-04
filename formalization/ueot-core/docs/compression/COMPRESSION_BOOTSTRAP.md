# UEOT Core Compression — New Chat Bootstrap v2

The user should only need to say:

> 继续 UEOT Core Compression Formalization，从当前 main / Issue #146 恢复并直接继续。

The recovery goal is to recover **active state**, not replay project history.

## Fast recovery

1. `git fetch --prune origin` and read canonical `origin/main`;
2. verify Core v3 baseline is still **106/106 FULL-GREEN** and read the live counted
   minimal core from `COMPRESSION_LEDGER.yaml`;
3. read the short current block of Issue #146;
4. read `COMPRESSION_RESEARCH_TRACKS.json` only for the active track's namespace/risk
   policy;
5. read the active task tracker if one is named;
6. list open PRs/live branches and recover the active branch/head/CI;
7. reuse that branch; do not create a replacement because the chat/tool changed;
8. continue the exact scientific next action.

Read `COMPRESSION_MISSION.md` in full only for L3/counting/finalization work. Read historical
track audits only when they are actual mathematical dependencies.

## Expected snapshot

```text
Compression recovery complete.
main: <sha>
Core baseline: 106/106 FULL-GREEN
mission/counting state: <state>
minimal core: <ids>
active task: <tracker/title or none>
risk tier: L0 | L1 | L2 | L3
track: S | H | X | O | none
branch/PR: <branch@sha / PR or none>
latest required CI: <run/status>
blocker: <if any>
exact next action: <action>
```

## Handoff

Checkpoint meaningful WIP on the same branch. Update Issue #146/task tracker only when
state or scientific decisions actually changed. Do not create handoff-only branches and
do not copy historical CI logs into the live-state block.
