# 一般 K2：实际编译增量独立审查

**结论：COMPILE_DELTA_CLEAR_PRIVATE_FOCUSED_PASS_NOT_INTEGRATED。** 已审原稿的数学内容和来源身份保持不变；实际第 4 轮编译与五个关键端点的标准公理闭包均有真实日志。此次增量审查完成此前静态收据中的 elaboration 待决项，不表示该模块已经进入当前七模块生产发布。

## 绑定对象

| 对象 | SHA256 |
|---|---|
| 原 V1 源码 | `7ab97381798440497a3a60fac5ee2dd405deb1f7100438e06b1a1b6a2e21d95c` |
| 实际通过源码 | `8114278dc02e54f681bd576cf62af0dcc83df47a5b4a61bdc506a868750aea3c` |
| 实际 `.olean` | `3882f4be785ccafeb9352042e2c95bc2978570ea0e15d7def2a12e3eaf06fbeb` |
| attempt004 原始日志 | `161f6596ddf86f93a80886b229ff4a7825edfe33ddae275a05653bd18523504e` |
| attempt004 状态 | `c3c3db0bd45e6858df2af1d2f5aa768f318f61cd72375a4ee05f6c1ba1276521` |
| 作者汇总执行收据 | `79327c622f43ff2400278da31961e1dff0300364968c7a19cf1862247cebda7f` |
| 最终数学合同 | `5f040a5ce6ce27e35f09c83a68a21504975540d9ac56039c6f49208410571920` |

审查者为 `/root/audit_resume`。原 `REVIEW.json`、`REVIEW.md`、作者的历史 draft 状态和数学合同均保持原字节。本次只读取源码、补丁、实际状态、日志及依赖身份，并在独占审查目录新增收据；没有运行 Lean、native、测试或 Git 写操作。

## 证明修复没有改变目标

独立重算原稿到最终稿的完整文本差异，与冻结的 `PROOF_ELABORATION_DELTA.patch` 完全一致。13 个公开声明中，11 个声明头逐字节相同，另 2 个仅将 `nu.support` 显式括号化为 `(nu).support`。这是一项源码比较：原稿未成功 elaboration，因此不声称已对原稿与最终稿执行 kernel type 比较。

过滤后再映射的原子公式仍直接展开 `PMF.filter` 和 `PMF.map` 的实际有限求和。最终稿把指示函数成员关系和正反等式分支写明；它没有引入新的事件概率假设。生存事件改用显式 `Set.ofPred`，质量记号改用 `Measure.real (PMF.toMeasure nu) S`，只是消除本地 notation 的解析问题。最后使用 `Set.mem_ofPred_eq` 将实际联合事件化简，再调用已经通过的 K1 原子恒等式；零时刻证明中的旧成员化简名称也同步替换。

没有把欲证来源等式或归一化等式放入假设，没有弱化量词，也没有增加 QSD、Perron、全时域正存活、初始全安全或 `Nonempty K` 假设。

## 真实执行与失败保留

attempt004 实际退出码为 **0**，耗时 **7.238 秒**，未超时。当前源码与该轮源快照逐字节相同，真实 `.olean`、stdout/stderr 和状态摘要全部匹配。日志只有两组 unused-section-variable 警告，无错误；没有为消除警告删减继承假设。

五个实际 `#print axioms` 输出都只包含 `propext`、`Classical.choice`、`Quot.sound`，分别对应：

- `actual_conditioned_terminal_mass`；
- `actual_conditioned_terminal_eq_normalized_killed_map`；
- `actual_zero_survival_no_filter_witness`；
- `actual_conditioned_terminal_mass_at_zero`；
- `actual_survival_mass_empty`。

这是五个关键端点的实际传递公理闭包，不能描述为该私有模块的全量 native 声明审计。

第 1–3 轮仍分别记录原真实 FAIL、退出码 1、原源快照和原日志。其耗时为 9.762、7.697、6.694 秒；最后一轮失败仅剩实际事件中的集合成员化简。失败恢复输出中的 `sorryAx` 没有被当作成功证据。原始失败与历史未编译 banner 保留，当前实际状态由新执行收据明确说明。

## 同源性和边界继续成立

实际初态 `p0` 任意。原历史 PMF 先按“从零时刻到当前 n 始终安全”的真实事件过滤，再映射到终态；安全原子质量为同一个 `eta0 Q^n` 除以实际存活质量 `s_n`。安全子类型上的 `normalizedKilledTerminal` 从这条行构造，映射回原状态类型后与实际条件终态 PMF 的等式由证明给出。

只在当前 `s_n > 0` 时构造条件 PMF。零质量事件没有所需的支撑见证，也没有任意补出的条件分布。`n = 0` 时的分母是 `p0(K)`，不是自动等于 1；原初始不安全质量没有被预先删去。空安全集在所有有限窗口均有零生存质量，安全集非空由正存活推出。

策略仍是来源桥中的同一个时间齐次、仅依赖当前观察的随机 `sigma`。任意完整因果策略和 `viableFamilyPolicy` 不会自动与它相等。未来若接入这些策略，仍须证明实际策略相等或构造相应扩充状态来源桥。

## 依赖与证据复用范围

实际执行通过绝对 Lean/Lake 路径、私有 root、`LEAN_NUM_THREADS=1` 及两个已通过的私有 `.olean` 目录导入来源桥和 K1。四个私有源码/产物 pin 已独立核对。旧 K1 环境和当前完整构建身份的全部九类组件相同：完整源范围与逐文件列表、模块数、源树摘要、工具链、三个环境文件、运行工具、九个依赖与 import 环境。完整源树摘要仍为 `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。

上述比较复用已有真实构建身份，未再次运行依赖构建或声称新增 Git 干净状态检查。K2 尚未进入生产 import 根、七模块原生审计、图谱或 overlay；生产集成与 canonical/resulting-main 门槛由根后续分别安排。QSD 专化、首次退出和无限路径结论不在本次通过范围。
