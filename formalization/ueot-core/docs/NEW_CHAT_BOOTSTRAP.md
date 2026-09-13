# UEOT Core 3 Lean — New Chat Bootstrap

Copy/paste the following as the first message in every new ChatGPT conversation used for UEOT Core 3 Lean formalization.

```text
继续 UEOT Core 3 Lean 全形式化。

执行简化跨对话 Recovery Protocol：

1. 从 GitHub `MurphyHoops/UEOT` 的 `main` 显式读取：
   - `formalization/ueot-core/docs/UEOT_CORE3_LEAN_OPERATIONS.md`
   - `formalization/ueot-core/docs/V3_COVERAGE_STATUS.md`
2. 读取 GitHub Issue #56：
   `[LIVE] UEOT Core 3 Lean Formalization — Current State & Cross-Chat Handoff`
   这是唯一需要高频维护的实时施工状态入口。
3. 检索我过去对话中最近一次 UEOT Core 3 Lean formalization，补回尚未来得及同步到 GitHub 的最后推理或决定。
4. 查询 live GitHub：当前 `main` SHA、Issue #56 指向的 active feature branch/head、最新 CI、branch compare、相关 PR/integration branch。
5. 做 reconciliation：
   - frozen source 决定 theorem semantics；
   - `V3_COVERAGE_STATUS.md` 决定正式 coverage；
   - live branch/Actions 决定实际代码与 CI；
   - Issue #56 决定最新施工意图、blocker 和 exact next action；
   - 旧聊天只作为补充，不能覆盖 live GitHub。
6. 给我一个简短 Recovery Snapshot，然后立即执行 Issue #56 的 `Exact next action`；不要问我“上次做到哪里了”。
7. 不要重新证明已经 green / integrated / counted 的内容。
8. 未完成工作也必须保存：任何非平凡代码修改，在可能跨聊天前都要做 WIP checkpoint commit 并 push 到 active feature branch；WIP 可以红、可以未完成，但不得增加 coverage。
9. 日常只更新 Issue #56 中 materially changed 的字段：active P-ID、branch/head、CI、blocker/root cause、exact next action、do-not-repeat/API notes。不要每轮维护一堆 main 文档。
10. `PID_STATUS.yaml`、`FORMALIZATION_STATE.md`、`HANDOFF_LATEST.md`、`V3_COVERAGE_STATUS.md` 只在真实生命周期变化时同步，例如 feature freeze、integration、promotion 或全局 audit；不是每个聊天回合都更新。
11. feature green 不得直接增加 coverage；promotion 必须经过 source semantic audit、clean integration green、main、post-main green、prohibited-proof audit 和 ledger synchronization。
12. 不要把 GitHub full CI 当 Lean REPL：module check -> affected-stack check -> milestone `lake build UEOT`。
13. integration 永远从 live latest `main` 开始，长 development history 不直接整支 merge。
14. 最终目标始终是冻结版 UEOT Core 3 的 106/106 source-level Lean machine verification。
```

## Expected first response

```text
Recovery complete.
main: <sha>
coverage: <N>/106
active P-ID: <pid>
feature: <branch>@<sha>
latest CI: <run> <status>
state: proof | integration | promotion | audit
blocker: <if any>
exact next action: <one concrete action>
```

Then immediately continue actual Lean / GitHub work.

## Why this is robust

- `main` keeps stable project rules and formal counted state.
- Issue #56 is the single high-frequency live handoff and does not trigger Lean CI.
- The active feature branch stores unfinished code through WIP checkpoint commits.
- Prior-chat recovery is only the emergency supplement for reasoning not yet checkpointed.
- Truly uncommitted edits that existed only in an ephemeral working tree cannot be guaranteed recoverable, so meaningful edits must be checkpointed early rather than waiting for theorem completion.
