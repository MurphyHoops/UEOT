# C 首轮交叉质询记录（认证前）

日期：2026-11-13。此文件只记录设计层质询，尚未接受任何认证结果。

独立首审：ADVERSARIAL_METHOD_REVIEW_INITIAL.md，SHA256 971a5c41961ab2930c5a133d1d2f6d3df305dd897af54264632a75c439db077b。首审冻结后才读取 B 的 IMPLEMENTATION_PLAN.md（120 行）和 A 的 EARLY_METHOD_NOTE.md。

## C→B：四项问题与原义答复

1. 未知 ACK：认可主审允许集合方案，但应保留 ack_class=UNKNOWN；完整状态属于 {S0,S1} 只支持 ACCEPT_CURRENT_ALLOWED，不证明真实过去已提交。候选和强基线必须相同。
2. B 提案 §35 称摘要只从请求/ACK 生成，§48 的 NOT_COMMITTED 又依 PRECOMMIT 屏障、未放行和终止。要求明确这项协议证书是双方可见输入还是仅 oracle 私有信息，防止暗含额外真值。
3. callback 预算可限于明确逻辑单位，但墙钟应从 connect 前开始；若实际 journal 不 hot 或没有需回滚的落盘页，不能从最终状态一致倒推 hot-journal rollback 已实测执行。
4. 原提案 42 次建议、UNKNOWN 一律未决是保留的历史方案；正式冻结应同步主审 28 次与集合语义，不追认旧方案已运行。

B 原义回复：

> 接受 C1/C2/C3。实现将把父协议证书作为双方共同可见输入：ACKED需实际完整接收事件；NOT_COMMITTED需公开归一化证书（PRECOMMIT_READY已收到、COMMIT放行未发送、SIGKILL/reap完成）；UNKNOWN用请求已发且无ACK，允许{S0,S1}，内部COMMIT_RETURNED不提供给策略以缩集合。原始阶段留给方法审查，规范证书双方同信息/同费用。墙钟从connect前起；callback只逻辑单位，hot journal额外记录header/原件与恢复前后。主审28样本+ACCEPT_CURRENT_ALLOWED会同步进协议；先写最小runner校准，不扩理论。

C 裁定：设计层冲突消除，仍须在实际代码、输入对象、原始成本和预注册中复核。此回复不是实现验收。没有新增 Core 缺口或要求额外 Lean 证明。

## C→A：解释桥边界

已向 A 提出：当前允许状态证书与过去提交知识分开；进程故障、旧备份替换与 hot-journal/断电机制分开；B 的公开未提交证书与私有 COMMIT_RETURNED 不混用。A 的独立早期稿 §1–4 已独立采用允许集合、非空确定覆盖、完整克隆、SIGKILL 边界。完整数学源映射仍待正式稿，不在此提前接受某个 Lean 端点实例化。

## 主审设计裁决的当前核对

已读 adjudication/PRE_REGISTRATION_DECISIONS.md。D1–D5 与 C 独立最低条件相容：完整克隆、ACK 集合语义、28 个有限运行、callback 的窄资源口径、标准方法无额外增益可结案。该文件明示尚未认证；实际执行仍未发生。

后续问题按真实代码/数据补记；不以三方同意代替程序和原始证据。

