# 同一实际受控源的状态路径桥：最小候选

状态：`WRITTEN_NOT_COMPILED`。源码仅在本私有目录，没有生产导入；没有运行 Lean 或共享缓存。主智能体完成当前七模块验证后，可决定对此候选执行一次聚焦编译。

## 精确范围

输入为有限微观状态 X、有限非空共同动作类型 A、既有 `Model X (fun _ => A)`、任意观察类型 Y、观察映射 q，以及 `sigma : Y → PMF A`。Y 不要求有限，也没有引入可测性条件，因为结论是 PMF 相等。

实际完整策略定义为每个时间、每个观察历史 h 上采用 `sigma (last h)`。它必须在所有历史上按同一定义成立，包括概率为零的历史；没有从当前观察纤维推断后验支持。实际微观转移直接使用同一个 `M.transitionPMF`。

诱导的 `StationaryPolicy` 的每个实数行动概率都由这个实际 PMF 的 `toReal` 构造，并用实际 PMF 归一化证明 `prob_sum_one`。模型与策略的来源相等不是外层假设。

## 两个目标

1. 动作—状态实际风险核经 `Prod.snd` 推前，等于 `policyTransitionPMF M (liftedStationaryPolicy q sigma)` 在同一个当前微观状态的行。
2. 对每个 n 和任意初始 PMF p0，实际带动作路径律经过完整 `eraseActionHistory n` 推前，等于 `causalLaw p0 (policyPathKernel M (liftedStationaryPolicy q sigma)) n`。

第一项通过真实行动 bind 的有限质量和及两个既有 `*_apply_toReal` 定理证明。第二项按 n 归纳，复用 `risk_map_extend_right` 与 `coverage_map_extend_reference`，每一步使用第一项已经推导的源身份。没有构造独立比较核后把相等式交给调用者。

## 量词边界

- 这是当前观察决定行动分布的平稳策略。固定时间依赖策略可得到时间非齐次 Markov 核，但不能直接接入当前固定 `policyMatrix` 的长期接口。
- 一般历史依赖策略可能在相同当前微观状态、不同过去历史上选择不同动作，因此不能自动降成同一个 `StationaryPolicy`。若后续研究这类策略，应扩大状态为真实充分记忆，或保留完整历史核；不能只声明一个平稳矩阵代替它。
- 本候选保留完整微观状态历史，仅擦除动作。它不声称观察过程 Y 本身 Markov，也没有因此假设观察 q 强可聚合。
- 未加入 QSD、Cesàro、killed 事件、无限路径或 Bellman 最优性结论。本候选只完成这些后续桥所需的一个来源步骤。
- 对同源四状态实例，取 q(b,u)=b、所有 y 上同一个 Bernoulli 行动 PMF，即可直接实例化；无需新增策略身份假设。

## 已核对的既有接口

- `CoreOperationalAssembly.lean`：`policyTransitionPMF`、`policyTransitionPMF_apply_toReal`、`currentState`、`policyPathKernel`。
- `FiniteDiscountedPolicyResolvent.lean`：`StationaryPolicy` 与 `Model.policyTransition`。
- `FiniteDiscountedApproxQuotient.lean`：`Model.transitionPMF_apply_toReal`。
- `DeploymentCoverage.lean`：`coverage_sum_toReal`、`coverage_map_extend_reference`。
- `FiniteHorizonRisk.lean`：`riskHistoryMap`、`riskLastState`、`risk_last_project`、`riskMicroControlKernel`。
- `FinitePMFProjection.lean`：`risk_map_extend_right`。

新增私有 `pmfExtend_map_snd` 只证明擦除一次行动记录等于真实 bind；没有复制通用条件化或完整历史推前机制。`currentState_eraseActionHistory` 只统一两种既有当前状态表示。
