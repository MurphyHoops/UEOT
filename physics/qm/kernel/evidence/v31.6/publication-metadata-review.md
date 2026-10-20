# v31.6 发布元数据脚本独立审查

**最终结论：PASS。初审的三项当前元数据问题及两项非阻断改进均已解决。**

审查者：`/root/q316_classical_core`。最终所审 `/tmp/qm316_publish_docs.py` SHA256：

`d638c3ca69c73490ce1ef9140c01560c2de0414635f21c50d86a2027fbb7c8af`

本次只读源码、AST、实际验收回执和文件身份；**没有导入或执行发布脚本，没有运行 Lean，没有修改源码、书稿或任何根端证据文件**。根端可执行此已审脚本，再进行发布产物回读与后续远端验收；本审查不提前宣称这些步骤完成。

## 初审问题与复核结果

| 编号 | 初审发现 | 最终复核 |
|---|---|---|
| PUB-01 | 14 条 scope 仍说 v31.5；8 条 PASS_100 运行状态却指向实际只有 87 方法的 v31.4 回执；另有旧实例回执 | 已保存 `prior_verification_scope`、`prior_*` 回执；当前 scope 和 runtime/instance/evidence 统一绑定 v31.6，历史文件不改 |
| PUB-02 | ACTIVE_RESEARCH 已设本地验收完成，但公开统计仍说维持 v31.5 | 已替换为实际 22/459/573、84、42、4、100/4、70 源和源集合哈希 |
| PUB-03 | QMK-13 原主体是复量子导出或新增经验确认，status 却改成别的反模型已证 | 原主体保留 `NOT_CLAIMED`，反模型进展独立放入 `selection_boundary_status` 与 related slices |
| PUB-04 | QMK-40 的 span 否定未列对应 theorem 名 | 已加入 `finite_real_product_span_blind` 和 `joint_test_not_finite_real_product_sum` |
| PUB-05 | kernel README 留下 v31.5 链接标签及旧新增 API 的归属歧义 | 当前报告标签已改 v31.6，finite_dynamics 和 13 方法明确写为 v31.5 继承、本轮重跑 |

初审原报告另存 `/tmp/qm316_publication_metadata_review_initial.md/json`。最终 JSON 保留初审脚本身份、全部发现与解决记录，未擦除曾存在的问题。

## 科学范围与计数

三条科学线的范围准确：经典结论限于公开 B 解释和 H1–H6 有限 Core 接口、任意有限经典辅助系统、同源实际商与路径边际；实层析量化全部合法实局部乘积效应，但不冒称完整 real OPT 或唯一复量子重构；Doob 明确本征度量、正率与有限条件化，右本征态承担额外结论，谱存在、唯一性与长时吸引仍开放。没有新增实验确认、全部 Core 覆盖或最终物理真理的状态提升。

脚本计数与实际回执一致：统一构建 **8786 jobs、22 模块、459 显式定理、573 命名审计**；新增 125 定理、181 审计，其中 56 非定理目标。四见证 **62 定理/22 定义/84 审计**，79 模块绑定；56 Core 导入、43 新导入；六正实例/42 审计，四坏数据真证明拒绝及同数据假值证明；100 运行方法、四演示、九依赖。不同证据类别没有混计。

## 源身份与历史边界

复核时再次逐项回读 **70 个受验源，SHA256 和字节数零差异**。源集合哈希：

`8a2cea35e060f5341f5672534d0717c605f5c441d998a08cc7677fb50a113115`

完整 AST 中的写入目标仍为当前导航、v31.6 文档/状态/集成占位及下一轮合同；不改这 70 项受验输入。没有写入 OLD 或历史 v31.5 ledger/evidence。旧 verification 和 integration 深复制保存；当前远端提交/运行身份为 None/PENDING，旧 MAIN_VERIFIED 只出现在 prior 历史。原 v31.6 未来时任务合同只增完成说明，其原正文保留。v31.7 已审定任务明确尚未形式化，不计为 v31.6 已证成果。

## 书稿安装后回读

B 已安装正式书稿及 v3.2 证据，实际 Markdown 与 stage 字节相同。实际 Markdown/PDF 哈希同时匹配结构、构建和视觉审阅回执：

- Markdown：`6289bebfbd4ae0efe5ac2257f6ac15efb37fb7b95bb78612367818eb5d6e4fd4`
- PDF：`51de239d72d1fb3659fdeb7b7d951c031a5c01913315c88bedb86ec348b5e57a`

绑定回执给 57 章、6 附录、272 编号小节、117 结果、186 页。本人核对文件身份和回执，没有重新排版或冒称增加一次视觉审查。

## Focused 档案更新

仅按要求刷新 C 的四个档案，其他档案逐项核对未变，四个新模块冻结 SHA 一致。当前 focused manifest SHA：

`e5cb2a297e31a8562429552cac4c097a9c2db78cf3a3d0016ea966de8638c5ef`

完整输入身份、计数和逐项解决证据见 `/tmp/qm316_publication_metadata_review.json`。最终无未解决项；根端负责脚本执行后的回读、Git 和远端独立验收。
