# UEOT Core Compression — New Chat Bootstrap

The user should only need to say:

> 继续 UEOT Core Compression Formalization。执行 Compression Recovery
> Protocol，从 GitHub 恢复 Issue #146、active M-ID、branch、CI 和 exact next
> action，直接继续，不要新开重复任务。

The AI must then execute this recovery chain:

`REPOSITORY_BRANCH_GOVERNANCE -> COMPRESSION_OPERATIONS ->
V3_COVERAGE_STATUS -> COMPRESSION_LEDGER -> COMPRESSION_COVERAGE ->
Issue #146 -> live branches/PR/CI -> active branch -> exact next action`.

Mandatory checks:

1. verify Core v3 still reads **106/106 FULL-GREEN**;
2. fetch current `main` SHA;
3. read counted compression state from the ledger on `main`;
4. read Issue #146 LIVE STATE;
5. list remote branches and open PRs;
6. recover the active branch/head and latest relevant CI;
7. reconcile Issue state against GitHub reality;
8. reuse the active branch if it exists;
9. never infer a full compression mapping from a partial theorem;
10. immediately continue the exact next action.

Expected recovery snapshot:

```text
Compression recovery complete.
main: <sha>
Core baseline: 106/106 FULL-GREEN
analyzed: <N>/106
schema-classified: <N>/106
Lean-rederived: <N>/106
counted-compressed: <N>/106
counted generators: <list or none>
active M-ID: <id or none>
active branch: <branch>@<sha or none>
open PR: <number or none>
latest Core Lean CI: <run/status>
latest Compression Guard CI: <run/status>
state: analysis | proof | audit | integration | ledger | governance
blocker: <if any>
exact next action: <action>
```

If a conversation is near its limit, checkpoint on the same active branch,
push it, update Issue #146, and continue until the conversation can no longer
do useful work. Do not create a handoff-only branch.
