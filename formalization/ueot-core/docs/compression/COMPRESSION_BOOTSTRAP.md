# UEOT Core Compression — New Chat Bootstrap

The user should only need to say:

> 继续 UEOT Core Compression Formalization。执行 Compression Recovery
> Protocol，从 GitHub 恢复 Issue #146、active M-ID、branch、CI 和 exact next
> action，直接继续，不要新开重复任务。

The AI must then execute this recovery chain:

`REPOSITORY_BRANCH_GOVERNANCE -> COMPRESSION_OPERATIONS ->
COMPRESSION_MISSION -> V3_COVERAGE_STATUS -> COMPRESSION_LEDGER -> COMPRESSION_COVERAGE ->
COMPRESSION_RESEARCH_TRACKS -> Issue #146 -> active child tracker (if named) ->
live branches/PR/CI -> active track branch -> exact next action`.

Mandatory checks:

1. verify Core v3 still reads **106/106 FULL-GREEN**;
2. fetch current `main` SHA;
3. read `COMPRESSION_MISSION.md`, then counted state from the ledger on `main`;
4. read Issue #146 LIVE STATE;
5. read `COMPRESSION_RESEARCH_TRACKS.json` and recover the independent
   architecture role, lifecycle, track owner, authority/provenance and
   counted-core-impact axes;
6. if Issue #146 names a P0b/Track S/Track H tracker, read that child tracker
   before selecting a branch; when S∞ is active, Issue #223 is the authoritative
   detailed Track-S tracker and must be read before Track-S mutation;
7. list remote branches and open PRs, then classify each governed branch as
   governance / Track S / Track H / unclassified;
8. recover the active branch/head and latest relevant CI for each active lane;
9. reconcile Issue state against GitHub reality and the immutable base-policy
   validator;
10. reuse the active branch if it exists; do not create a replacement merely
    because a chat was compacted or another agent is continuing;
11. keep Track X closed until the registry says the cross-track integration gate
    is open, and consume cross-track dependencies only from canonical `main`;
12. never infer a full compression mapping from a partial theorem;
13. immediately continue the exact next action.

Expected recovery snapshot:

```text
Compression recovery complete.
main: <sha>
Core baseline: 106/106 FULL-GREEN
analyzed: <N>/106
schema-classified: <N>/106
Lean-rederived: <N>/106
counted-compressed: <N>/106
final dispositions: <N>/106
unresolved dispositions: <N>/106
mission state: active | ready_for_finalization | final
minimal core: open | candidate | frozen
counted generators: <list or none>
active M-ID: <id or none>
architecture role/lifecycle: <G0-G3>/<status or none>
Track S: <branch>@<sha / PR / next action or inactive>
Track S mission: <finite-state CLOSED | S∞ stage / tracker #223 | other>
Track H: <branch>@<sha / PR / next action or inactive>
Track X gate: closed | open
latest Core Lean CI: <run/status>
latest Compression Guard CI: <run/status>
state: analysis | proof | audit | integration | ledger | governance
blocker: <if any>
exact next action: <action>
```

If a conversation is near its limit, checkpoint on the same active track branch,
push it, update Issue #146 and the named child tracker when appropriate, and
continue until the conversation can no longer do useful work. Do not create a
handoff-only branch and do not cross-edit another track's owned namespace.
