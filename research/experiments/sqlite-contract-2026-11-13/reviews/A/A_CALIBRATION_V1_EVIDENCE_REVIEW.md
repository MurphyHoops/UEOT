# A：v1 校准小回执的实际证据与解释边界

日期：2026-11-13。性质：A1 首审后的证据更新。**这是校准阅读，不是认证验收或主张最终通过。** A 没有修改／执行 B 的程序，也未重新运行 Lean。

## 1. 阅读对象与身份

实际读取路径均在 `agents/B/evidence/calibration-v1/retrieved/calibration/`：

| 文件 | SHA-256 |
|---|---|
| v1-controller-receipt.json | `7c404a6aa046d7ae8f8168a25797aff03f57b465865b992a25ddcf781c00112e` |
| v1-compact-readback.json | `8ad66e20695954acd9d21208b7407780bce9f10ab5ff4080e14f712b3895240b` |

A 另读 run-v1 的 RUN_MANIFEST、RUNS_PLANNED、SUMMARY 与 FILE_MANIFEST 的结构，程序抽取7行记录；compact 所绑定的 SUMMARY SHA 与实际文件相符。实现与协议回执分别是已做静态审查的 `e8190f5b…5f5ce`、`cd83b24f…1f63`。

controller 回执记载真实 Local Mac 运行于 2026-11-13 13:25:38—13:25:40 UTC，returncode=0，phase=CALIBRATION_ONLY；RUN_MANIFEST.authorization=null。全部行属于 W0、七种场景各一条，不是 W1/W2 留出或28条认证。

worker 环境报告 SQLite 3.51.0 与完整 Apple source ID；七条 worker 配置均为 journal_mode=delete、synchronous=2、page_size=4096、cache_size=5、cache_spill=5、fullfsync=0。这里报告所读实际值，不按上游版本名替换 vendor 身份。

## 2. 七格读取结果

候选与强基线在这7条记录中的决定、callback数、完整标志、返回行数与规范返回字节逐项相同。

| 场景 | ACK类 | 候选／强基线 | callback | 直接可见的范围 |
|---|---|---|---:|---|
| NORMAL | ACKED | ACCEPT_CURRENT_ALLOWED | 350 | 正常路径给出非空确定判定 |
| PRECOMMIT_KILL | NOT_COMMITTED | ACCEPT_CURRENT_ALLOWED | 330 | 记录未放行证书及returncode −9；允许前态被接受 |
| COMMIT_NO_ACK_KILL | UNKNOWN | ACCEPT_CURRENT_ALLOWED | 350 | 未把UNKNOWN改成ACKED；当前允许集成员可接受 |
| POST_ACK_KILL | ACKED | ACCEPT_CURRENT_ALLOWED | 350 | ACK后进程终止路径仍有确定结果 |
| STALE_BACKUP | ACKED | REJECT_HISTORY | 310 | 弱结构为STRUCTURE_OK，身份消融为ACCEPT_ABLATED |
| BUDGET_SMALL | ACKED | UNRESOLVED_BUDGET | 32 | complete=false、实际OperationalError interrupted |
| BUDGET_ZERO | ACKED | UNRESOLVED_BUDGET | 0 | connect_attempted=false |

全部 trial 的记录状态为 COMPLETE，original_unchanged=true；这与“试验程序没有执行错误”和“原始快照未变”的登记相符。它不能单独代替对全部原始业务行和父事件的独立真值重建。

## 3. 恢复覆盖：v1 没有给 hot-journal 恢复见证

PRECOMMIT 的数据库为114688字节，journal为111320字节。其28字节头为：

`0000000000000000000000009ffb213f0000001c0000020000001000`

首8字节不是有效journal magic；记录的 hot_header_candidate=false。四个策略克隆打开后，其数据库与journal文件集合和哈希均与打开前相同。依据 [SQLite locking v3 §4.1](https://www.sqlite.org/lockingv3.html)，hot-journal恢复需要满足相应前提；journal文件存在和大小较大并不充分。

**可支持：** 提交前门控、kill/reap及随后读取到允许前态的校准路径得到实际记录。

**不能支持：** 本次已经发生并验证了hot-journal回滚；所有恢复阶段已覆盖；这些运行能替代断电／内核崩溃／特殊VFS试验。

主审授权一次仅W0的定向扩写校准以检查该具体机制，未动W1/W2。若后继仍无相应证据，正确处理是降低恢复覆盖，而非再扩场景或把v1改写成成功恢复。

## 4. 资源覆盖：32 回调停在配置阶段

BUDGET_SMALL 的实际记录是首条 `PRAGMA journal_mode=DELETE` 从0到32回调，返回0行即中断。它证实了该小预算在此初始化查询上触发、complete保持false，以及判定器没有把不完整观察当作业务缺失。

它**不是**“读取若干业务行后扫描被截断”的实测。源码已保留那种情况下所需的完整性门，但不能把未发生的分支称为已实验覆盖。本阶段无需仅为增加覆盖数量再加中断试验；最终文字按实际阶段描述即可。

0预算没有connect；足额候选扫描报告350、330或310回调。这些数是本口径的逻辑观测指标，不是磁盘操作总数、能耗或实时保证。少量同机耗时不支持性能优越性。

## 5. 观察别名的严格含义

弱策略的NORMAL与STALE结构结果均为STRUCTURE_OK，但callback分别为279与249，其他运行标识和记录也不同。因此“不足以决定历史”的对象只能是明确登记的结构响应投影，例如 O_structure=(打开成功,完整性结果)。不能说两条试验的全部可访问数据或全部测量相同。

而且两条不同run的H不同，v1没有独立保留STALE替换前的同run D_new供后置核对。后继已经提出保留同H的D_new／D_old完整快照；那项证据实际到齐后，才可把本轮领域见证写成“同一H、同一结构投影、不同业务合同真值”。较低费用本身可以是另一观察，但本次不研究其普遍识别能力。

## 6. A 的独立核查限度与 C 的后继回复

compact 保存策略输出、阶段计数、文件hash及部分证书，未包含所有完整业务行和父原始请求／ACK事件。A 本次没有用它独立重建全部S0／S1，也没有把 B 的 history_membership 布尔值改称独立oracle证明。C 已消息报告，在Mac用自写计算器对318个v1原始文件逐值复算通过；这是**C 的独立工作报告**，不是A亲自执行的验证。最终采用仍须绑定C的实际产物。

本次可确认的是：v1确实执行了七格校准，所读事件与策略输出实现了预期的几项语义区分；没有观察到额外决策增益，也没有hot-journal恢复见证。认证、同H别名对、后继机制校准及最终研究结论各自等待其真实证据，不提前晋升。
