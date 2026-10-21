# 一般 K2：实际私有聚焦编译通过

## 当前结论

**PRIVATE_FOCUSED_LEAN_PASS_NOT_INTEGRATED。** 第 4 轮真实 Lean 执行退出码为 `0`，用时 `7.238` 秒，未超时。源码、原始 stdout/stderr、执行命令、依赖与 `.olean` 身份均已封存；当前没有生产集成或 canonical 发布声明。

源码初建时的 draft banner、原 `STATUS.json`、原数学合同和静态审查都保持原样。它们记录历史状态；本收据与 `COMPILE_PASS.json` 记录随后实际完成的编译结果，不能把旧静态文件误当作编译输出。

| 对象 | SHA256 |
|---|---|
| 实际通过源码 `SameSourceConditionedTerminal.lean` | `8114278dc02e54f681bd576cf62af0dcc83df47a5b4a61bdc506a868750aea3c` |
| 通过产物 `lean-attempt-004/SameSourceConditionedTerminal.olean` | `3882f4be785ccafeb9352042e2c95bc2978570ea0e15d7def2a12e3eaf06fbeb` |
| 汇总执行收据 `COMPILE_PASS.json` | `79327c622f43ff2400278da31961e1dff0300364968c7a19cf1862247cebda7f` |
| 原审稿 `SameSourceConditionedTerminal_v1.lean` | `7ab97381798440497a3a60fac5ee2dd405deb1f7100438e06b1a1b6a2e21d95c` |

## 五个关键端点的实际公理闭包

以下五个 `#print axioms` 都来自第 4 轮实际日志；每个闭包均为 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或新公理。

| 已通过端点 | 结论 |
|---|---|
| `actual_conditioned_terminal_mass` | 同一实际历史先按存活过滤、再取末态，其安全原子质量为 `eta0 Q^n / s_n` |
| `actual_conditioned_terminal_eq_normalized_killed_map` | 实际条件终态 PMF 等于同源归一化 killed 行在安全子类型上的 PMF 的包含映射推前 |
| `actual_zero_survival_no_filter_witness` | 零实际存活事件没有 `PMF.filter` 所需的支撑见证 |
| `actual_conditioned_terminal_mass_at_zero` | 零时刻质量为 `p0(v)/p0(K)`，保留原初始不安全质量的语义 |
| `actual_survival_mass_empty` | 空安全集在所有有限窗口的实际存活质量为零 |

完整命名空间为 `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SameSourceConditionedTerminalCheck`。

实际初始律 `p0` 任意；只要求当前窗口正存活。没有增加 QSD/Perron、初始全安全、`Nonempty K`、全时域正存活或来源身份假设。策略仍是同一个时间齐次当前观察随机 `sigma`；`viableFamilyPolicy` 没有被自动识别为这个策略。

## 四轮真实记录与修订范围

| 轮次 | 实际结果 | 定位与处理 |
|---|---|---|
| 001 | FAIL，退出码 1，`9.762` 秒 | 本地 notation 的 quotation/点号解析；过滤求和非等式分支未同时处理反向等式 |
| 002 | FAIL，退出码 1，`7.697` 秒 | 过滤引理已通过；当前 Mathlib 集合需使用 `Set.ofPred`，局部质量记号改显式函数调用 |
| 003 | FAIL，退出码 1，`6.694` 秒 | 仅剩联合事件中的 `Set.ofPred` 成员化简阻碍调用 K1 |
| 004 | PASS，退出码 0，`7.238` 秒 | 使用 `Set.mem_ofPred_eq` 完成实际同源质量接入 |

前三轮的原源快照、原日志、退出码和状态都保留，没有改写为 PASS。失败日志里的 `sorryAx` 是 Lean 对失败声明的后续恢复输出，不曾作为成功闭包使用。

`PROOF_ELABORATION_DELTA.patch` 记录全部差异。13 个 public 声明中 11 个声明头字节不变；另 2 个仅把 `nu.support` 写成 `(nu).support`。`DECLARATION_COMPARISON.json` 记录逐项原文与哈希；在这项明确括号化后，13 个声明头完全相同。该比较是精确文本比较，不冒称原失败文件曾导出可比较的 kernel type。

局部记号把 set-builder 写为当前 Mathlib 的 `Set.ofPred`，把测度点号链写为 `Measure.real (PMF.toMeasure nu) S`；事件、分布、量词和分母均未改变。其他改动仅为显式指示函数分支、反向非等式与集合成员化简。没有新增全局选项。最后日志保留两组 unused-section-variable 警告，未为消除警告删除继承假设。

## 依赖复用与执行范围

每轮实际执行都重新核对已通过来源桥与 K1 的源码、`.olean` 四项身份。`ENVIRONMENT_REUSE_BINDING.json` 进一步确认：K1 当时的 build identity 与当前完整构建记录在生产源码、工具链、依赖 pin、环境文件、运行工具和 import 环境上相同；当前 666 个生产源文件的路径集合与逐文件哈希也与该记录一致。

生产 source-tree SHA256 为 `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。这是读取和身份核对，没有再次运行全库 build、native 或依赖构建。

实际执行采用绝对 Lake/Lean 路径、`LEAN_NUM_THREADS=1`、私有 `--root`，只复用两个已通过私有 `.olean` 目录及生产缓存。每轮上限 180 秒，均未触发超时；没有停止其他任务。生产文件、消费者、书稿、Git refs 和远端均未由本任务修改。

下一必要门槛是 B 对这个已冻结实际结果的独立增量审查。审查另写新收据，不覆盖先前静态记录；之后由根决定来源研究模块的集成安排。本次没有启动 QSD 或首次退出的后续编译。
