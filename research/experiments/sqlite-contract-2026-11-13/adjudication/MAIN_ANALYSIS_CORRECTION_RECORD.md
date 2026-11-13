# 主审独立分析器的错误及有界修正

日期：2026-11-13。性质：认证完成后的只读分析实现修正；**没有变更预注册、执行源、协议、样本、原始数据库或实验判准，没有重跑或替换认证。**

## 1. 首次执行及保留

主审另写 `verification/main_independent_analysis.py`，不导入 B 的 runner 或 C 的检查器，从预登记初态公式、实际父请求和实际收到的 ACK 重建完整允许状态，并统计原始观察费用。源 SHA-256 为 `be43a8a3c31b8bdc581772f7d73aab879e3509c7dfac78b0982aff89fe62a091`。

该版本在 Mac 的新 main-adjudication 目录以 PID 89165 执行，实际产生四个 `ACK knowledge mismatch`。原始输出保存为 `evidence/CERTIFICATION_MAIN_ANALYSIS_V1_RAW.json`；其24项成本和决策部分统计是失败分析器的输出，**不得作为28项结果使用**。四个被误报的 run-ID 为：

- 1116bb42-ad2c-5eb2-ab50-e53a72e5657d
- 7ca6f088-2f95-5636-ac4a-b8432cbb587b
- 70315ce6-f96d-55d9-9be4-caf3dfa92515
- c1446fc3-cf5a-5432-8b2a-b58a5470315e

## 2. 错误如何定位

首版仅检查 `PRECOMMIT_READY` 消息和未发送 `GO_COMMIT`，遗漏实际请求是否设置 `pause_precommit=true`。冻结的 worker 对**每一笔**事务都会发出进度消息；只有请求启用暂停，worker 才阻塞等待放行。消息名称本身不是未提交证书。

主审回读首个原始事件流，最后一笔 seq=5 的请求明确为 `pause_precommit=false, pause_preack=true`；随后实际收到 `COMMIT_RETURNED_NO_ACK`，再 SIGKILL/reap=-9，没有收到最后事务的 ACK。因此根据原预注册，策略知识仍为 UNKNOWN，允许当前状态集合仍为 {S0,S1}。这不是 B 的四个错误判定，也不改变 UNKNOWN 的定义。

C 独立读码后确认这一归因。C 在认证前已用于 v2 校准的检查器本来就要求实际 `pause_precommit`、对应 txn 的 ready、无放行及终止链。主审没有要求 C 改判准配合结果。

## 3. 修正及再次分析

`verification/main_independent_analysis_v2.py` 仅从实际最后一笔 TRANSACTION 读取 `pause_precommit is True`，再结合对应 ready；源 SHA-256 为 `c15aa7188e84dcbeb55fd8a514eaa8a0c41f98188edba336cbc9302c034ef4cf`。这恢复了已冻结的屏障语义，而非新增实验假设。

v2 在 PID 89371 中只读原28项，完成于 2026-11-13T13:50:55.509385Z。全28项完整值与判定检查通过：ACKED=20、UNKNOWN=4、NOT_COMMITTED=4；候选与强基线均16接受、4历史拒绝、8预算未决。原始 v1 和 v2 输出及两份源码同时保留。未向候选策略添加私有 COMMIT_RETURNED 信息。

## 4. 错误归属和解释限度

归类为主审后处理实现错误。它说明独立验证器也必须接受源码和原始事件校验；本次没有因此发现 Core 定理、冻结运行器或实际数据库的反例。不能把这次纠正本身包装成 UEOT 相对于标准审查方法的已测优势。

本轮 Desktop Commander 的个别初始化连接错误，以及 B 的 compact v1 对 weak 未扫描字段的不当统计，另在执行／失败账本保留。连接错误不自动等于一次 SQLite trial；是否启动以不可覆盖的 start 文件、进程和完整台账判断。
