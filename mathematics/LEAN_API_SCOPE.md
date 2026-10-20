## 阅读说明：数学论证与当前 Lean 接口

下表区分书中数学论证的适用范围与当前可直接调用的 Lean 接口。这三项不是完整前提清单；调用时仍须核对定理的完整类型。

| 接口范围 | 精确阅读口径 |
|---|---|
| 观测类型 `Y` | 当前路径全变差界及微观失效风险接口仍要求 `[Fintype Y]`，包括 `coverage_same_policy_path_error` 及其风险推论。支持追踪与有限时域 `Viable` 双向定理不要求 `Y` 有限；这一较宽范围不自动扩展到现有风险接口。书中对一般观测空间的数学讨论不能据此称为已经提供的 Lean 风险 API。 |
| 每行样本数 `N` | 当前注册校准与联合风险接口使用 `sample : CoverageRegisteredRow certified T → Fin N → Ω → X`，即所有注册行共享同一个正整数 `N`；具体见证取 `N = 256`。书中逐行样本数 `N_j` 的写法属于数学层面的推广，现有联合风险接口尚未提供这一依赖行索引的采样类型。 |
| 事件包络 `henvelope` | 当前通用接口及 `Viable` 组合接口均要求 **所有候选** 满足 `henvelope : ∀ c, E ⊆ (riskHistoryMap …) ⁻¹' F c`。`hfit`、`hcap`、`hchecked`，以及组合接口的 `hinit`，才仅在同一个校准良事件上要求成立；组合接口内部证明零未认证占据，已不再把 `hcap` 作为外部输入。只对良事件中实际选中的候选要求事件包络，是可另行证明的接口弱化，不能直接当作当前签名。 |

对应源码：[DeploymentCoverage](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DeploymentCoverage.lean)、[RegisteredDeploymentRisk](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisteredDeploymentRisk.lean)、[ViableRegisteredJoint](../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViableRegisteredJoint.lean)。这些相对链接按本说明随附于 `mathematics/` 目录设置。
