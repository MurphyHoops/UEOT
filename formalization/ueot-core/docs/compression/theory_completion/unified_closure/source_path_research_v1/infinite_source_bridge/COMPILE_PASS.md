# 同一来源完整有限前缀 → 既有无限轨迹：实际私有 Lean PASS

状态：**PRIVATE_FOCUSED_LEAN_PASS_NOT_INTEGRATED**。执行增量独立审查另写新收据；原数学静审、原 v1 的 NOT_COMPILED/PENDING 字段和两轮真实失败均未改写。

## 结果

- 第 3 轮实际退出码 **0**，耗时 **6.305 s**，未超时；前三轮顺序为 FAIL / FAIL / PASS。
- 最终源码 `SameSourceInfinitePrefix.lean`：`da7c984a95cfd01d0135787effb7a4d0d06e55b18270b8470585b0b2b9db9b92`。
- 实际 olean：`9a5d689ba7c866f5597d4b752bd6e9ac05bd3e5e26f7da9be8c28c4659cfff1b`。
- PASS 原日志：`26521b3768620c1c35b1e66d6ce2d55f46e06ee998de1c2abf4e6b194c00d117`。
- 汇总 JSON：`cb165d8c799350061d75543676a42b6ddf0f7732226fccef254e35e76140e7e6`。
- 三个端点的真实公理输出均仅为 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。失败轮中含 `sorryAx` 的输出保留在原失败日志中，不视为证明。

## 已通过的数学范围

1. `state_history_eq_homogeneous_prefix`：任意有限 X、原始 p0 与固定实际 PMF 行 J 的整个递归状态历史，经已构造可测等价 e_n 后，等于同一 p0 与由 J 直接构造的 kernel 所产生的 `homTrajMeasure` 的完整 `Iic n` 前缀。
2. `actual_state_prefix_eq_homogeneous_prefix`：复用已过 `actual_state_path_eq_stationary_path`，将实际随机当前观察策略的行动—状态实验接到该完整前缀；模型、初态、观察和 sigma 均相同。
3. `actual_state_prefix_event_mass`：原实际记录上任意经完整状态前缀因子化的事件，与同一无限圆柱事件具有相同质量。

时刻 0 与全部旧坐标均保留。Y 无有限性或可测性前提；sigma 为时间齐次当前观察随机反馈。不将一般完整历史策略自动 Markov 化，也不擦除无法经状态路径因子化的行动事件。本轮未追加安全事件/K1、ENNReal→real、尾极限或最大不动点证明。

## 证明修复与声明保真

原始源码完整副本在 `v1-original/`。`DECLARATION_COMPARISON.json` 用顶层分隔符扫描，排除 `(X := X)` 等命名参数中的 `:=`，比较全部 **13 个完整声明头**、**2 个定义正文**和 **1 个实例正文**，均逐字一致。`SOURCE_DELTA.patch` 保存完整差异。

实际修复只有后继积的显式拆分与 `Prod.map` 化简、G1 的局部 definitional-equality elaboration 选项、时刻 0 的递归类型/可测实例归约，以及让源码说明转而引用独立执行状态的注释。没有新增来源相等假设或削弱量词。原稿未编译，故这里不伪称对原稿进行原生类型比较。

## 执行与输入绑定

每轮采用绝对 Lake `env` 和绝对 Lean、`LEAN_NUM_THREADS=1`、独立输出目录、180 秒上限；只允许本轮自己的进程组终止。没有执行 `lake build` 或 native。每轮重核完整 **666 个**生产 Lean 源文件的路径及哈希，完整生产 source-tree 身份为 `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`，并核对工具链、运行时二进制、环境文件、23 个 API 输入及已过来源桥的源/olean。

既有全库构建的依赖版本与 clean-state 证据按原记录复用；本轮不修改依赖，不操作 Git，也不把过去构建重记为本次执行。`ENV_AFTER_LAKE.json` 保存实际导入路径；`RESOLVED_DIRECT_IMPORTS.json` 绑定三项直接导入的实际首命中 olean 及存在的 sidecar。只有 `SourcePolicyPathBridge` 是本轮的私有导入；K1/K2/QSD/first-exit 均非此证明的额外导入。

`lean-attempt-001/`、`002/`、`003/` 各保留对应源、原 stdout/stderr、退出码、环境与身份。原静审在 `tmp/interface-next-review/infinite-source-bridge-v1/REVIEW.json`，SHA `364b5c2c5698b575a10142a77b5277b2d176e72131e88844f09e43150e11fb3d`。本次执行增量已交独立审查，不替代其结论。

两个无害 linter 提示保留，未为消除提示重复编译。生产、消费者、书稿、Git 和远端均未变动。
