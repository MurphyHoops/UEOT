# UEOT Core 3 Lean — New Chat Bootstrap

Copy/paste the following as the first message in every new ChatGPT conversation used for UEOT Core 3 Lean formalization.

```text
继续 UEOT Core 3 Lean 全形式化。

首先执行跨对话 Recovery Protocol：

1. 检索我过去对话中最近一次 UEOT Core 3 Lean formalization 的最新工作状态；
2. 显式从 GitHub MurphyHoops/UEOT 的 main 分支读取：
   formalization/ueot-core/docs/UEOT_CORE3_LEAN_OPERATIONS.md
   formalization/ueot-core/docs/HANDOFF_LATEST.md
   formalization/ueot-core/docs/PID_STATUS.yaml
   formalization/ueot-core/docs/V3_COVERAGE_STATUS.md
   formalization/ueot-core/docs/FORMALIZATION_STATE.md
3. 查询当前 main SHA、active feature branch、最新 CI、branch compare、PR；
4. 对 GitHub 状态、handoff 和上一轮聊天进行 reconciliation；
5. 给我一个简短 Recovery Snapshot；
6. 不要重新证明已经 green / integrated / counted 的内容；
7. 立即从上一轮 exact next action 接着推进；
8. 每个重要 checkpoint 更新 HANDOFF_LATEST.md；
9. feature green 不得直接增加 coverage；
10. 目标始终是冻结版 UEOT Core 3 的 106/106 source-level Lean machine verification；
11. 不要把 GitHub full CI 当 Lean REPL；先模块级检查，再 affected-stack，再 milestone full CI；
12. 恢复完成后立即执行实际 proof / fix / audit / integration，不要只给计划；
13. 如果状态文件中的 active SHA/CI 比 GitHub live state 老，以 live GitHub + HANDOFF_LATEST reconciliation 为准；
14. integration 永远基于最新 main，长 feature history 不直接整支 merge；
15. P-ID promotion 必须经过 source semantic audit、feature green、clean integration green、main、post-main green、prohibited-proof audit 和 ledger synchronization。
```

## Expected first response

The AI should recover state and report a compact snapshot similar to:

```text
Recovery complete.
main: <sha>
coverage: <N>/106
active P-ID: <pid>
feature: <branch>@<sha>
latest CI: <run> <status>
state: proof | integration | promotion | audit
exact next action: <action>
```

Then it should immediately execute the exact next action using GitHub/Lean tooling.

Do not ask the user to manually restate the previous chat unless recovery from GitHub plus cross-chat context is genuinely impossible.
