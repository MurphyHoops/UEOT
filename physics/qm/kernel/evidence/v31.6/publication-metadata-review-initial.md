# v31.6 发布元数据脚本独立审查

审查者：`/root/q316_classical_core`。审查方式：只读源码、AST 与实际回执核对；**没有导入或执行 `/tmp/qm316_publish_docs.py`，没有运行 Lean，也没有修改发布目标**。

所审脚本 SHA256：`a20727392efd8982d928397779b02c17e10a1ad4aff47ccac4bc87ab74ae0dac`。

**结论：科学范围、实际计数、70 源身份和历史写入边界通过；发布前应修正三项当前元数据问题。** 这些问题不影响已通过的数学证明，但会使当前状态文件的主体或回执指向不准确。

## 需要修正

### PUB-01：继承主张仍含旧版当前回执

脚本更新继承 claim 的 `current_source_identity`、`current_proof_receipt`，但 **14 条 `verification_scope` 仍写 v31.5**。此外 QMK-05、06、07、09、11、15、16、21 的 `runtime_status` 为 `PASS_100_TEST_METHOD_SUITE`，`runtime_receipt` 却仍指 v31.4；实际该旧回执是 **87 方法**。QMK-21 的实例回执、QMK-22 的执行证据同样保留旧版当前字段。

应在新台账中把当前 scope/runtime/instance 回执明确绑定本次 v31.6，原值保留为 prior/history 或通过旧 ledger 访问；不要改写旧 ledger 或旧回执。完整受影响列表在 JSON。

### PUB-02：ACTIVE_RESEARCH 的公开统计字段未更新

该对象被更新为 `LOCAL_VERIFIED_CI_PENDING`，但 `public_source_statistics` 仍是 “Remain v31.5 until actual unified acceptance”。本次统一验收已完成，这个字段应更新为实际 v31.6 数据或指向实际回执。

### PUB-03：QMK-13 状态与主张主体混合

旧 QMK-13 的主体是“从内核导出复量子扇区或新增经验确认”。脚本将 `NOT_CLAIMED` 改成描述经典/实反模型已证的状态，虽然后缀和 limits 保留开放边界，仍把另一件事的正面状态挂到了原主体上。

建议该主体保持 `NOT_CLAIMED`；用独立 `selection_boundary_status` 与 `related_proved_slices` 表达反模型进展。正文的实际科学限制已经准确，不需弱化已证结果。

## 非阻断改进

- QMK-40 包括有限实张成障碍，当前 witnesses 列表只列 `complex_product_distinguishes`。可增加 `UEOTQM.RealLocalTomography.Examples.joint_test_not_finite_real_product_sum`，使机器可读引用直接覆盖该半项主张。
- Kernel README 的链接目标会替换为 v31.6，但字面标签 `[v31.5 主报告]` 仍留下。若顺手整理，可同时把 inherited v31.5 的 `finite_dynamics` 新增 API 叙述注明为上版继承，避免本轮新意归属混淆。

## 已通过的核对

实际回执给出统一构建 **8786 jobs、22 模块、459 显式定理、573 命名审计**；125 新定理、181 新审计与 56 非定理增量一致。四见证 **62/22/84**、79 模块输入绑定；56 Core 导入及新增 43；六正实例/42 审计、四坏数据真证明拒绝及同数据假值证明；100 运行方法、四演示、九依赖均与脚本一致。

70 项受验输入逐项重读，SHA256 与字节数 **零差异**；源集合哈希重新计算为 `8a2cea35e060f5341f5672534d0717c605f5c441d998a08cc7677fb50a113115`。脚本的文档、导航和元数据写入不属于这 70 项输入；不会因本次发布重写已验 Lean、运行 Python、工作流或固定证书。脚本没有写入 OLD 或 v31.5 ledger/evidence，旧 verification/integration 均显式深复制到历史字段。原 v31.6 未来时合同只加完成说明，其历史正文保留。

脚本把当前远端验收保持为 PENDING、提交和运行身份置空，旧 MAIN_VERIFIED 只留在 prior 记录。没有用本地 PASS 推断远端 PASS。v31.7 合同明确审定待执行，不混入本版已证统计。

三路线的科学主张均有正确边界：经典只覆盖公开 B 解释与 H1–H6；实层析量化全部合法实局部乘积效应，但不冒称完整 real OPT 或唯一复量子重构；Doob 需要明确本征度量和正率，任意初态仅给有限条件化，右本征态的额外结论、实质量与复迹、非线性归一过滤、谱存在/唯一性/长时吸引均分开。

## 书稿与执行边界

审查时 B 尚未安装目的地 v3.2 书稿证据；stage 的结构回执已是 57 章、6 附录、272 小节、117 结果。脚本在首次写入前要求已安装 Markdown 等于 stage。根端仍应在 B 安装并检查实际 PDF/书稿回执后执行，本审查不提前代替其 186 页与视觉审阅验收。

本次同时按根端要求刷新 C 的四个 focused 档案，其他 64 档案内容不变，全部重新核对；当前 focused manifest SHA 为 `e5cb2a297e31a8562429552cac4c097a9c2db78cf3a3d0016ea966de8638c5ef`。四模块最终源 SHA 再次一致。

完整输入身份、计数、问题列表和范围见 `/tmp/qm316_publication_metadata_review.json`。脚本修订后应绑定新 SHA 并复核相关字段；本报告不是脚本执行或远端发布回执。
