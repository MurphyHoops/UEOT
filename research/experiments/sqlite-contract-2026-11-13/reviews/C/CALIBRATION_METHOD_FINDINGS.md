# C：校准阶段的实际复算与方法差额

日期：2026-11-13。状态：**CALIBRATION_ONLY；不是认证或 C 的七格重现。**

## 1. 实际独立执行

C 通过 Desktop Commander Local Mac，在独占 independent-C/tools 中保存自写计算器并运行。没有 import B 的程序，没有调用 B 的判决函数。计算器源码 SHA256 为 c9c6eefe7e98caf61526347683f68c333370a20c8710f1381aabfd75a8beaf91；Python 3.9 AST 检查通过，Mac 写入后再次读回同 SHA。

实际只读输入目录：/Users/murphyhoops/Documents/ueot-sqlite-study-20261113/calibration/run-v1。
输出：independent-C/calibration-check-v1.json。
实际进程打印 C_CHECK_EXIT 0。
取回共享副本 CALIBRATION_V1_INDEPENDENT_CHECK.json 与 Mac 原件 SHA256 相同：
62ddee0081c08a6d0c78d76a0ea13378e9b5bd6c8bf3ab408246ae7179a643f2。

计算器直接重读并重哈希 318 个实际文件；检查全部 7 个登记运行。它从原始父发送请求、实际接收 ACK、子 stdout 与父接收逐条对应、门控及 SIGKILL/reap 重建提交知识和完整允许业务/txn状态，再逐值比较原始 SQL 行。B 的 allowed_states、hash、history_membership 与 verdict 仅用作被检查对象，没有当作真值来源。

原件、各策略后置实际文件均直接重哈希。各克隆打开前同源关系依赖已有生产者原始哈希记录，C 将其与实际原件比对；C 没有声称在历史打开之前亲自读过那些副本。后续分离执行将独立重复相应过程。

## 2. v1 结果与未覆盖项

7/7 运行通过 C 当前原始证据一致性检查：候选 4 个 ACCEPT_CURRENT_ALLOWED、1 个 REJECT_HISTORY、2 个 UNRESOLVED_BUDGET。候选与强标准基线没有判定分歧；这只验证校准程序可用，不计入最终 28 次认证。

- PRECOMMIT_KILL 的原 journal 实际大小 111,320 字节。C 另行直接读取其原始前 28 字节为 0000000000000000000000009ffb213f0000001c0000020000001000，前 8 字节没有 hot journal magic。原件及四策略后的 DB/journal 哈希一致。**没有 hot-journal rollback 被执行的证据。**
- BUDGET_SMALL 的阈值 32 在第一条 PRAGMA journal_mode=DELETE 中断，实际回调 32、返回 0 行、complete=false。它证明初始查询的回调预算会中断，**未实测业务扫描中途截断**。
- BUDGET_ZERO 没有 connect，没有 SQL，回调 0。
- UNKNOWN 的完整允许集成员被接受而 ACK 标签保持 UNKNOWN；没有由最终数据补造 ACK。
- STALE 的历史矛盾被候选与强基线拒绝，结构弱投影仍正常、消融接受；但 v1 未保存同合同 D_new 字节，故不能在 v1 宣称同一个 H 下的新旧配对见证已完整取得。

C 的直接 hot/budget 补读输出在 Mac independent-C/calibration-v1-hot-budget-readback.json，SHA256 b44318ccbbc08829afdc7b4ba79490b1828087d274592c712c6d4ec92e509671。

## 3. 交叉质询后的精化

A 提出且 C 接受：no-go 应严格相对登记的结构投影 O_weak；仅当行数属于该投影，才要求行数相同。若某函数拿到完整数据但故意不消费它，结论是投影/消融不足，不是所有可访问信息都不可识别。v1 结构相同的不同运行回调数已不同，因此不把成本、时序、公开摘要等全部记录说成相同。

已要求 B 保留 STALE 覆盖前干净当前副本，再与同 trial 的旧副本在同一 H 下配对。此修正只补同源见证，不增加主试验数量。B 另拟一次有理由的较大 W0 校准，只覆盖 PRECOMMIT 与 STALE；W1/W2 不用于调参。若仍无 hot journal，收窄恢复覆盖，不追加搜到成功为止。

主审预注册草稿中，C 要求足额决定格与预算格有明确分母/行为表；低预算按真实中断判，而不是由场景名强制弃权。C 七格 replication 应与主28格分开登记。已建议维持 28 主格与 W2×7 分离重现，不做旧 pilot 或 Lean 重跑。

## 4. 时钟与连接口径

Mac Python 3.9.6 的单调时钟不应直接作为跨进程共同原点；Python 官方 time 文档记录 macOS 跨进程同基准为 3.10 变更。C 仅核父进程内部事件顺序及各 observer 内部耗时，跨进程因果使用发送/接收/屏障/终止链，未把 child 与 parent monotonic_ns 相减。参考：https://docs.python.org/3/library/time.html#time.monotonic 。

C 的首次传输遇到 Local Mac MCP 初始化409，随后执行只报告文件不存在；重试写入后校验源码 SHA 再运行成功。另一次只读命令遇同类409后重试成功。它们是工具通道事件，没有运行认证、没有更动 B 证据目录，也没有抹掉任何实验失败。

## 5. 当前判定

v1 是可用的初始校准，但恢复覆盖与同合同成对见证需按上述事实收窄或在预注册前有限补齐。C 尚未接受最终预注册、尚未运行认证或七格分离重现；这些完成前不得发布本阶段已结案。

