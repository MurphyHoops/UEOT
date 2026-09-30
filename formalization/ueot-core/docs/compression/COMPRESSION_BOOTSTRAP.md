# UEOT Core Compression — New Chat Bootstrap

The user should only need to say:

> 继续 UEOT Core Compression Formalization。执行 Compression Recovery
> Protocol，从 GitHub 恢复 Issue #146、active M-ID、branch、CI 和 exact next
> action，直接继续，不要新开重复任务。

The AI must then execute this recovery chain:

`REPOSITORY_BRANCH_GOVERNANCE -> COMPRESSION_OPERATIONS ->
COMPRESSION_MISSION -> POST_FINAL_RESEARCH_GOVERNANCE ->
COMPRESSION_RESEARCH_TRACKS -> V3_COVERAGE_STATUS -> COMPRESSION_LEDGER ->
COMPRESSION_COVERAGE -> Issue #146 -> live branches/PR/CI ->
active Track S / Track H branches -> exact next action`.

Mandatory checks:

1. verify Core v3 still reads **106/106 FULL-GREEN**;
2. fetch current `main` SHA;
3. read `COMPRESSION_MISSION.md`, then counted state from the ledger on `main`;
4. read Issue #146 LIVE STATE;
5. list remote branches and open PRs;
6. recover the active branch/head and latest relevant CI;
7. recover Track S / Track H ownership and cross-track gate state;
8. reconcile Issue state against GitHub reality;
9. reuse the active branch if it exists;
10. never infer a full compression mapping from a partial theorem;
11. never create a Track H theorem that duplicates an active Track S stability
    family;
12. immediately continue the exact next action.

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
Track S branch/PR: <branch>@<sha / PR or none>
Track H branch/PR: <branch>@<sha / PR or none>
cross-track gate: closed | open
latest Core Lean CI: <run/status>
latest Compression Guard CI: <run/status>
state: analysis | proof | audit | integration | ledger | governance
blocker: <if any>
exact next action: <action>
```

If a conversation is near its limit, checkpoint on the same active branch,
push it, update Issue #146, and continue until the conversation can no longer
do useful work. Do not create a handoff-only branch.
