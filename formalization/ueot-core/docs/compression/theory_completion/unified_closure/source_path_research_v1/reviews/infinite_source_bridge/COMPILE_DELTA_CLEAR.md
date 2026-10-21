# G1–G3 实际聚焦执行：独立编译增量审查

**结论：COMPILE_DELTA_CLEAR_PRIVATE_FOCUSED_PASS_NOT_INTEGRATED。**

本次复用原始 `REVIEW.md/json` 的完整数学与接口静审，只审从原 v1 到实际 attempt003 的源码差异、声明/定义保真、执行输入及原始输出。没有重跑 Lean、lake、native、测试或 Git；没有编辑作者文件、生产、消费者或书稿。原 v1 的 `NOT_COMPILED` 状态、原静审的 `EXECUTION_PENDING` 和两轮真实失败均保持原样，本页是后续独立完成收据。

## 1. 真实结果与准确身份

| 对象 | SHA256 / 结果 |
|---|---|
| 最终实际源码 | `da7c984a95cfd01d0135787effb7a4d0d06e55b18270b8470585b0b2b9db9b92`；10106 字节 |
| 原 v1 源码 | `7773377037056384b194d09e63623d3a65c127e7d9cd22681430bd89648b54e0`；9988 字节 |
| attempt003 STATUS | `fc223cff8f398868799b4799cf49588eddb85d5407efe3dd2884c459a5fffd87` |
| attempt003 原日志 | `26521b3768620c1c35b1e66d6ce2d55f46e06ee998de1c2abf4e6b194c00d117` |
| attempt003 实际 olean | `9a5d689ba7c866f5597d4b752bd6e9ac05bd3e5e26f7da9be8c28c4659cfff1b`；310712 字节 |
| 作者 COMPILE_PASS.json | `cb165d8c799350061d75543676a42b6ddf0f7732226fccef254e35e76140e7e6` |
| 本次独立比较及绑定明细 | `COMPILE_DELTA_EVIDENCE.json`；`7906fcc522ab7f4a9188a2dfade956bf19f38746ad127fb3872484d0f6bc9fe7` |

逐轮实际结果为：attempt001 **FAIL / exit1 / 8.298 秒**；attempt002 **FAIL / exit1 / 6.395 秒**；attempt003 **PASS / exit0 / 6.305 秒**，均未超时。各轮独立源码快照、日志、STATUS 和实际 Lake 环境与其记录的哈希/字节数一致。最终当前源码与 attempt003 快照、该轮运行前后源码身份完全相同。

原四件 v1 文件仍有字节不变的副本；原 CONTRACT、STATUS 和 API_INPUTS 本身也未改。失败日志中的错误及错误恢复产生的 `sorryAx` 没有改写为成功输出，也不作为任何已完成证明的公理证据。

## 2. 完整声明和定义比较

本审查独立实现了保留偏移的注释/字符串遮蔽与顶层分隔符扫描，识别 `:=`、`where` 和递归方程体的边界。括号、方括号和花括号内的命名参数 `:=` 不会截断声明头；因此包含 `(X := X)` 的完整等式目标也已覆盖。

对比原 v1 与最终源码：

- **13 个完整声明头逐字相同**，包括 10 个定理（其中 3 个私有辅理）、2 个定义和 1 个实例。
- `pmfRowKernel` 与 `stateHistoryEquiv` 的**完整定义正文逐字相同**。
- `pmfRowKernel_isMarkov` 的完整实例正文逐字相同。
- 三项直接 import 逐字相同。
- 作者 `DECLARATION_COMPARISON.json` 中的 13 个完整头文本也与本次独立抽取结果完全相同，没有重现此前首次退出比较器的命名参数截断问题。

原 v1 未通过编译，因此这里是完整源码声明与定义的字节比较，不宣称对未编译原稿做过原生类型比较。最终版本自身由真实 Lean 执行检查通过。

## 3. 全部实质差异均为证明实现修复

完整 source diff 只有四类变化：

1. 源码说明从“尚未编译”改为引用独立执行状态；原说明保留在 v1 副本。
2. `stateHistoryEquiv_last` 的后继分支先显式拆开 `(h,x)`，再加入 `Prod.map` 化简，使末坐标等于新状态。
3. G1 增加仅作用于该定理的 `backward.isDefEq.respectTransparency false` elaboration 设置。
4. G1 的 n=0 分支显式展开递归历史类型、`causalLaw`、相应可测实例和 `stateHistoryEquiv`，随后使用原有 `homTrajMeasure_prefix_zero`。

第 3 项只影响 elaborator 在证明中的定义等价处理，没有引入公理或新的数学前提；实际内核检查和三个端点公理闭包均通过。第 2、4 项解决的正是原静审标出的递归类型/可测实例及末坐标归约风险。没有修改同源构造、历史表示、初态、事件或终端定理的量词。G2 和 G3 的证明体也未改变。

最终日志保留一个 unused-simp 提示和一个 `letI` 风格提示；二者不影响实际退出码、公理输出或命题。没有为了消除这些提示追加一次编译。

## 4. 三个实际端点公理闭包

原日志实际打印：

| 端点 | 实际传递公理闭包 |
|---|---|
| `state_history_eq_homogeneous_prefix` | `propext`、`Classical.choice`、`Quot.sound` |
| `actual_state_prefix_eq_homogeneous_prefix` | `propext`、`Classical.choice`、`Quot.sound` |
| `actual_state_prefix_event_mass` | `propext`、`Classical.choice`、`Quot.sound` |

本次独立解析的名称和集合与作者汇总一致，恰好三个端点，最终日志无错误或 `sorryAx`。这些是该三个端点的真实传递闭包；不是全项目原生声明枚举，也没有新增一轮完整 native 导出。

## 5. 源码、环境与实际导入绑定

实际命令使用已受钉住的绝对 Lake `env` 与绝对 Lean，`LEAN_NUM_THREADS=1`，独立输出目录和 180 秒上限。没有调用 `lake build`。runner 每轮在启动前核对完整生产输入、环境文件、运行时二进制、23 个接口输入和私有来源桥的源码/olean；独立审查又对这些文件身份作只读核对。

完整 **666 个生产源码路径及每个哈希**与已完成 build-attempt9 的 SOURCE_MANIFEST 完全一致，source-tree 身份为：

`29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。

三个环境文件、两个实际运行时工具和 23 个已读 API 输入均匹配。九个依赖的 manifest revision 与既有完整构建记录一致；依赖 Git HEAD/clean-state 使用已有成功构建证据，本轮独审没有执行新的 Git 检查，也不把旧 clean-state 冒充本次重新测得的结果。

三个尝试的 `ENV_AFTER_LAKE.json` 均为合法且相同的真实环境记录。其 `LEAN_PATH` 的 12 个路径准确包含唯一私有来源桥缓存、九个依赖缓存、Core 缓存和指定 Lean 运行时；没有额外空路径或未知搜索根。本次从这些实际搜索路径独立解析到的三项直接导入，与 `RESOLVED_DIRECT_IMPORTS.json` 的首命中结果一致：

- `SourcePolicyPathBridge`：仅命中已通过的 attempt002 olean。
- `UEOT.V3.DynamicsKernel`：命中既有 Core 缓存 olean。
- `Mathlib.MeasureTheory.Integral.Lebesgue.Countable`：命中受钉住 Mathlib 缓存；olean 和存在的 private/server sidecar 均核对。

这些检查支持复用既有构建输入，未扩张为全依赖重新编译或原生目录审计。

## 6. 数学范围与下一条真实义务

原静审的全部量词和范围保留：任意有限 X、原始 p0、固定实际行 J；可测等价保留 0,…,n 全部状态；G2 使用同一 M/q/sigma/p0 的真实动作擦除；Y 不要求有限或可测；G3 仅转移可经状态前缀因子化的事件。一般历史策略不被齐次状态 Markov 化，当前观察过程也未因此被证明 Markov。

因此现在可以准确记录：**G1–G3 已实际私有聚焦 PASS，并完成独立执行增量 CLEAR。** 它们仍未进入生产入口/生产模块计数，也未获得新的生产 native census。

下一条尚未完成的组合是安全前缀事件拉回与 `riskEverFailure` 的逐记录相等，再接同一 p0/Q 的 K1 质量公式并显式处理 ENNReal/real，之后复用既有无限尾极限。这个后续范围没有因 G1–G3 本次通过而自动完成。原始历史状态应继续保留，新增 Stage6 归档可以引用本完成收据和真实 attempt003 产物。
