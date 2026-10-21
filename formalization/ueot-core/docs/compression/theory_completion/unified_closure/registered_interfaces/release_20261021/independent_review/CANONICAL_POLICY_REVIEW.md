# #355 合并后 canonical 政策独立核验

**结论：实际 canonical main `86dfbec88c20a9da3c98cd222611aac55cc55f2f` 已包含本轮准确的 TC 例外政策；六路径范围及其他冻结规则保持原样。**

状态：`CANONICAL_POLICY_CONTENT_CONFIRMED_EXACT_BRANCH_SIX_PATH_SCOPE`。只读 Git 对象与已保存合并工具收据，没有执行测试或修改 refs。

## 实际对象

- 本地已 fetch 的 `origin/main` 确实指向 `86dfbec88c20a9da3c98cd222611aac55cc55f2f`。
- 其实际父提交为新 main `e9b61ca9c35955028c4bfa425dfa278fd1864029` 与治理候选 `6777a727c1df0618ef7d52800e3528c37e7c48d4`。
- 实际 tree 为 `f3758e41c77fc90ddfa0b243a2f1d7adf5a2d421`，与上一份独审验证的合并树完全相同。
- `OPS_RELEASE.json` 的实际成功合并 SHA、候选 head、前 main 与 Git 对象一致；旧拒绝记录及旧 pending 收据未覆盖。

## 准确授权范围

异常 ID：`TC-REGISTERED-INTERFACES-EVIDENCE-2026-10-21`；track：`TC`；temporary：`true`。

精确分支匹配：`^compression/theory-completion-registered-interfaces$`。六条既有路径为：

- `formalization/ueot-core/docs/compression/theory_completion/unified_closure/UMC_GLOBAL_MODULE_DAG_V4.json`
- `formalization/ueot-core/docs/compression/theory_completion/knowledge/README.md`
- `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/fkrg_reuse.py`
- `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py`
- `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/README.md`
- `formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/REBUILD_CLONE_CANDIDATES.py`

canonical 策略 blob 与已审 `6777a727` 候选字节相同，SHA256 为 `081c224ff4a9ba553297e1615cd1558bc1540524ed8241815f9470e6e98a9f70`。相对合并前只改异常 ID、精确 branch pattern 和 reason；六路径 allowlist 及 JSON 其他所有字段均未变化。

## 保留范围

合并前后全部已跟踪差异只有该政策 JSON。因此原 Lean 全树、UEOT.lean、三份构建环境文件、治理脚本、工作流、账本、post-final 规则、六消费者、两书及 handoff 均未变化。另逐项核对了这些对象；`formalization/ueot-qm/` 与 `physics/` 的完整 tree 也分别与合并前相同，没有读取数学正文。

此收据确认实际 canonical 政策内容和授权范围；未执行 base policy validator、parser tests 或 Git-object preflight。它不声称 Core、native 或 resulting-main 构建 PASS，也不是计数 FINAL 事件收据。合并工具收据中的 proof check 为 skipped，不能将治理成功解释为 Lean 已运行。
