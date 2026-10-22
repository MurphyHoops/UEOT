<!-- 本地草稿，未发送；仅提供新的 current recovery，旧正文完整保留为历史。 -->

## Current UEOT Core recovery — 同源路径实现（2026-10-22）

<!-- UEOT_CORE_CURRENT_PATH_REALIZATION_BEGIN -->
本批接续已验收的 [#363](https://github.com/MurphyHoops/UEOT/pull/363)、[#365](https://github.com/MurphyHoops/UEOT/pull/365)。operations [#366](https://github.com/MurphyHoops/UEOT/pull/366) 已验收，授权基线为 main `d503586107974c56e0773b4ea106b41a7d144b43`；本批科学集成的最终发布身份见下表。

**新增推论：** 七模块构造同一有限记忆控制器的实际增广/无限路径与物理安全桥；从原实验证明完整有限窗条件路径、Doob 末端倾斜及同初始边际下 TV 为 `1/4` 的真实源反例；把 C3 注册族最小下标推进为实际搜索和精确调用 trace。数学细节、原始来源及独审见[完整报告][report]。

**实际验证：** 七个最终模块聚焦 Lean PASS、独立静态审查 CLEAR。当前 `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379` 源的全量构建 **PASS，14.23 秒，691 模块**；native 导出与固定 verifier 均 **PASS**（58.451 / 58.297 秒），实际摘要为 **73 个公开声明、249 个编译器定理常量、114 条注册证明边**。收据仍明确待独立执行审查与注册，后续门不能由这些 PASS 代填。

物理安全公开端点已增强为三份实际来源的前提独立性合取，明确两反例的 `¬hclosed` / `¬hinit`；五项质量事实继续保留。公开比较域由 77 改为 73，私有生成常量继续受审。原 `c344bf66…` 的构建 PASS 与 native01 中断 FAIL 分别保留。

**边界：** 记忆路线的无限安全端点保留有限状态/行动/记忆条件，数值源允许非自治；有限窗矩阵路线要求数值齐次，当前只识别正质量条件行，尚未证明独立 total 条件核的全路径生成。物理安全仍需原初态和认证后继支持条件；C3 仅保证注册族内 exact-oracle 搜索，经验与统计校准责任保留。来源支持一致性不缩减参考检查预算。

冻结 **106 P-ID = 11 generated / 89 adapters / 6 boundaries**、**4 counted generators** 保持；本批为 **uncounted** 扩展，全局 **`NOT_ESTABLISHED`**。下一步完成执行原档独审、消费者注册/canonical 与发布验收；研究任务继续在 #302。

### ROOT_TO_FILL：最终验收位置

| 项目 | 实际结果待填 |
|---|---|
| 本批 PR / candidate / resulting main / 双端树身份 | `ROOT_TO_FILL_RELEASE_IDENTITY` |
| native 完整原档、公理/ownership/raw-type/固定边与对象等同性的独立核对 | `PENDING — ROOT_TO_FILL_NATIVE_REVIEW` |
| 最终注册声明/累计证明边/overlay census | `PENDING — ROOT_TO_FILL_REGISTRATION_CENSUS` |
| 消费者、完整 clone、canonical 与必要回归 | `PENDING — ROOT_TO_FILL_CANONICAL` |
| 执行原档及独立执行审查 | `ROOT_TO_FILL_EXECUTION_EVIDENCE` |

[report]: ROOT_TO_FILL_REPORT_URL
<!-- UEOT_CORE_CURRENT_PATH_REALIZATION_END -->
