# 首次退出质量与无限存活：定向复用映射

状态：只读 API 检索；未运行 Lean、未修改生产。以下按实际源码签名整理，不宣称新 flux 端点已经实现。

**结论：Core 已有有限存活尾到真实无限路径事件质量的极限定理。** 本次指定模块及相关符号检索没有找到把当前 `SameSourceKilledPath` 的安全子矩阵 Q、任意初始截断行 η₀ 和原 risk 路径直接接成 first-exit flux 的现成命名端点；这是窄范围检索结论，不是“通用现有引理不能推出”的宣称。真正需要新增的是这一具体来源连接与简短代数后果，不应重建已有 hitting 或全时域理论。

## 1. 精确 API

路径均相对 `formalization/ueot-core/UEOT/V3/`；O 表示 `Compression/Objecthood/`。源码哈希绑定于同目录 `RECEIPT.json`。

| 已有文件与端点 | 可直接复用的内容及边界 |
|---|---|
| `O/AbsorbedRepairHittingSemantics.lean`：`homTrajMeasure_apply_eq_lintegral_initial` | 对同一 Markov 核 R、可测路径事件 E，任意初始测度 μ 的真实路径事件质量等于各 Dirac 初态路径质量的 μ 混合。可用于从点初态推广到 p₀，不允许混合时更换 R。 |
| 同文件：`survivalProb_eq_homTrajMeasure_apply`、`survivalProb_succ_eq_lintegral`、`survivalProb_eq_zero_of_mem` | finite survival 已被识别为真实 `homTrajMeasure` 的有限窗口事件；一步递推明确要求初态不在命中目标中，目标内初态另有质量为零定理。这里参数 A 是**命中目标**，要表达始终处于安全 K，必须传入 A=Kᶜ。 |
| 同文件：`survivalProb_eq_of_eq_outside`、`causalRepairPathLaw_absorbed_survival_eq`、`causalRepairPathLaw_absorbed_eventually_hits_iff` | 核在目标外相等就保持每个首次命中前存活概率；完整历史因果策略下也有原物理无限路径与目标吸收路径的精确关系。吸收只改命中后的行为。不能把这些结果说成完整未条件路径律相等，更不能直接当作 Doob/QSD 关系。 |
| `O/FiniteStationaryHittingExpectation.lean`：`survivalProb_tendsto_neverHitProb` | **现成所需极限接口**：有限 X、可测单点、Markov 核 R、点初态 x、任意目标 A 下，`survivalProb R x A n → neverHitProb R x A`，值域 ENNReal。证明直接使用同一真实无限路径上的连续从上，无不可约性或正存活假设。`neverHitProb_first_step` 还给目标外的调和关系。 |
| 同文件：`expectedHittingTime_ne_top_of_ae_eventually_hits_finite`、`stationary_expectedHittingTime_ne_top_of_ae_eventually_hits` | 已有更强的有限齐次链后果：实际 a.s. 命中推出有限期望命中时间；后一条是确定性平稳控制和点初态的专门接口。本次 flux/极限证明不需要这个更强结论，勿添加 a.s. 命中前提。 |
| `ViabilityTrajectory.lean`：`stationaryKernel`、`stationaryTrajMeasure`、`stationaryTrajMeasure_coordinate`、`exists_stationary_policy_all_times_of_fixed` | 原 PMF 源经确定性平稳反馈生成真实无限路径，坐标边缘身份已证。可行固定点＋初始支撑给所有自然时刻概率一安全。这是成熟生产理论；一般非一的存活概率不能仅从各坐标边缘恢复，必须使用整个前缀事件。 |
| `O/StationaryCausalPathLawBridge.lean`：`fixedPolicyAugmented_current_marginal`、`historyKernel_stationary_strongLumpability`、`stationaryCausal_pathLaw_eq_stationaryTrajMeasure` | 对确定性 π:X→A 和点初态 x，完整历史 causalRepair 路径律等于同源 stationaryTrajMeasure。此处不是任意随机 σ 或任意 p₀ 的现成定理；新 risk PMF 的递归元组历史还须与所用无限路径前缀对齐。 |
| `QSDTVLimit.lean`：`KilledSemigroup.evolved_eq_survival_smul_conditioned`、`eigenmeasure_of_tv_limit`、`qSurvival_add`、`p_qsd_01` | 已有来源明确的连续时间 killed 半群与条件分布关系。`KilledSemigroup` 带 NNReal 时间、半群律、概率初态及所有有限时刻正生存；最终指数存活还需条件 TV 极限、q 后续正生存与零处右连续等条件。它不自动将某个离散安全限制 Q 接到原风险路径，不能把这些正性/收敛前提加到无条件 K1/flux 中。 |

`neverHitSet_eq_iInter_survivalSet`、`antitone_survivalSet` 是 AbsorbedRepairHittingSemantics 的公开端点。其 `neverHit_measure_eq_of_survival_eq` 是 **private**，只能复用其证明路线，不能作为外部公开 API 调用。

## 2. 最小新增连接

令 Q 是 K1 从同一闭环 L 定义得到的安全限制，ηₙ=η₀Qⁿ，sₙ=Σᵤηₙ(u)，并定义

\[
d(u)=1-\sum_v Q(u,v),\qquad
\mathrm{flux}_n=\sum_u\eta_n(u)d(u).
\]

复用 `QSDPerron.rowApply_mul`，展开有限和即可得到

\[
s_n-s_{n+1}=\mathrm{flux}_n=\eta_0Q^n(\mathbf1-Q\mathbf1).
\]

非负性来自实际非负质量与 Q 的行和≤1。若要命名为**实际首次退出质量**，还须把该差识别为同一 n+1 步 risk 路径中的事件“0,…,n 都在 K，而 Xₙ₊₁∉K”，利用实际有限路径的前缀一致性，不能只给代数表达式命名。有限望远镜求和随即给

\[
1-s_T=(1-p_0(K))+\sum_{n<T}\mathrm{flux}_n.
\]

保留时刻零的失败项；无需 p₀ 支撑在 K，无需 K 非空、正存活、QSD 或不可约。空 K 与 T=0 都应由同一命题覆盖。

对无限时间，固定一个由同一闭环 PMF 构造的 Markov 核 R，并令 ν∞=`homTrajMeasure p₀.toMeasure R`。例如 R 的每一行可直接取 `policyTransitionPMF M (liftedStationaryPolicy q sigma)` 的测度；来源不能另行自由指定。先证明

\[
\nu_\infty(\mathrm{survivalSet}\ K^c\ n)=s_n.
\]

可复用 `DynamicsKernel.homTrajMeasure_prefix_zero` / `homTrajMeasure_prefix_succ` 建立有限记录表示的前缀身份，或用现成 survival 一步递推和初始混合对齐相同质量。只比较终端坐标不够。之后直接应用既有 `survivalProb_tendsto_neverHitProb`（Dirac／有限初始混合），或公开 `MeasureTheory.tendsto_measure_iInter_atTop`（同一 ν∞），得到

\[
\nu_\infty(\forall t, X_t\in K)=\lim_n s_n.
\]

ENNReal 到实数使用现有 `ENNReal.tendsto_toReal`，概率质量有限给出所需“不等于 ∞”。不必新增一套无限路径构造或连续从上定理。

## 3. 应保留的解释边界

- 上述极限需要同一个固定源、策略、初始律和一致无限路径；不能取每个 T 各自选择的可行策略，再把各自 s_T 拼成一个无限存活概率。
- QSD 初态下条件终端律可始终等于 r，而 sₙ=ρⁿ 在 0<ρ<1 时趋于零。条件稳定与真实持续不同。ρ=1 的安全结论也仍属于该实际初始律及同源路径，不能扩大到任意初态。
- 已有可行固定点的生产 all-times safety 不受这条私有 flux 桥是否完成的影响。新结果拟补充任意指定平稳策略的退出质量计算，而不是重新证明项目首次获得无限安全。
