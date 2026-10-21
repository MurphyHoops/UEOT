# K2 / QSD 之后：同一源的风险、存活与条件路径任务排序

日期：2026-10-21。范围：只读当前 Core 与已审私有来源桥；本说明没有新增 Lean、构建或发布操作。K1、一般 K2、QSD 特化的私有聚焦 PASS 与独立审查已经分别留有实际收据；它们尚不因本说明而成为生产或 canonical main 的一部分。QSD 最终源码为 `be6c14557d455e8e4c6d752bb9255388a4dc5a561a85bf96112fbfba604f66ed`。

**建议顺序：先完成已有首次退出草稿的真实编译闭环；随后接通当前随机闭环的有限风险路径与既有无限轨迹；有限窗条件路径作为独立的下一条分支推进。** 第三项不依赖无限极限，数学论证可与第二项并行；没有必要等待它才证明无限存活，也不应把它的时变条件核替换成齐次 Doob 核。

## 1. 已有事实与真正的新增内容

以下生产路径均相对 `/workspace/scratch/9a8d58b21e30/ueot-integration/formalization/ueot-core/UEOT/V3/`。

| 层次 | 已有准确端点 | 接下来所补的内容 |
|---|---|---|
| 同源随机闭环 | `CoreOperationalAssembly.lean`：`policyTransitionPMF`、`policyTransitionPMF_apply_toReal`、`policyPathKernel`、`policyMatrix` | 私有 `SourcePolicyPathBridge.actual_state_path_eq_stationary_path` 已将实际含行动记录的风险 PMF 推前为同一状态路径。无需另造状态核。 |
| 实际安全事件 → killed 幂 | 私有 K1：`actual_survival_terminal_mass_eq_killed_pow`、`actual_survival_mass_eq_killed_pow_sum` | 已实际 PASS。初态安全行 `eta0` 不归一化，包含初始失败边界。 |
| killed 行 → 实际条件终态 | 私有一般 K2：`actual_conditioned_terminal_eq_normalized_killed_map`；私有 QSD：`actual_qsd_conditioned_terminal_law_of_survival_pos` | 均已实际 PASS 并独审 CLEAR。条件终态是同一实际历史过滤后所得；不是一份并列的代数证书。完整条件路径仍是另一命题。 |
| QSD / GOA 代数 | `QSDPerron.lean`：`leftPerron_pow`、`qsd_survival_mass_pow`、`qsd_all_steps`；`Compression/TheoryCompletion/GOA.lean`：`KilledQSDGOA` | 私有 QSD 直接构造该原有谓词，固定实际 `p0 = r.map Subtype.val` 和实际 killed 核。无需重证 Perron 代数；QSD 存在性仍不是本批结论。 |
| 真实无限路径与前缀 | `DynamicsKernel.lean`：`homTrajMeasure_prefix_zero`、`homTrajMeasure_prefix_succ`、`pathMeasure_eq_of_prefix_eq`；`ReflexiveStatePathLaw.lean`：`historyPathLaw_prefix` | 现有无限过程和完整前缀递推可复用。需要连接当前递归 `CausalHistory` / 随机状态 PMF 与 `Iic` 索引的同一无限前缀，而不是重建无限过程理论。 |
| 命中 / 永不命中 | `Compression/Objecthood/AbsorbedRepairHittingSemantics.lean`：`survivalProb_eq_homTrajMeasure_apply`、`survivalProb_succ_eq_lintegral`、`homTrajMeasure_apply_eq_lintegral_initial`、`causalRepairPathLaw_absorbed_survival_eq`；`FiniteStationaryHittingExpectation.lean`：`survivalProb_tendsto_neverHitProb`、`neverHitProb_first_step` | 存活尾极限、初态混合及吸收前首次命中的真实语义已经存在。当前待接的是风险 PMF 与其同一来源，不能写成“项目没有首次命中或无限存活”。 |
| 全时域受控安全 | `ViabilityKernel.lean`：`controlledInvariant_subset_iter`、`exists_stationary_policy_of_fixed`；`ViabilityTrajectory.lean`：`exists_stationary_policy_all_times_of_fixed`；`Compression/TheoryCompletion/UnifiedClosure/CoreSourceAllTimesAssembly.lean`：`single_source_terminal_object_viability_all_times` | 已有同一源的真正无限路径、概率一安全。新增目标是固定随机策略的精确存活概率及它与最大闭合集的关系；不是重做已证全时域安全。 |

这条扩展把 H0-DYN 的实际路径、M-PE 的特征结构与 GOA/风险语义连接到同一模型、初态和策略。冻结 106 P-ID 的 `11 generated / 89 adapters / 6 boundaries` 分类不变；新增来源身份不意味着全部适配已由四生成元自动导出。

## 2. 第一优先：实际首次退出通量

### 精确命题

沿用同一个有限模型、任意观察类型、时间齐次当前观察随机策略、实际初态 `p0` 和安全域 `K`。令 `nu_n` 为实际含行动记录的路径 PMF，`S_n` 表示从时刻 0 到 n 均安全，

\[
Q=L|_{K\times K},\quad \eta_0(i)=p_0(i),\quad
s_n=\eta_0Q^n\mathbf1,\quad
\kappa(i)=1-\sum_{j\in K}Q(i,j).
\]

对实际 `n+1` 步记录定义 `F_{n+1}=S_n\cap\{X_{n+1}\notin K\}`，应完成：

\[
\Pr_{\nu_{n+1}}(F_{n+1})
=s_n-s_{n+1}
=\sum_{i\in K}(\eta_0Q^n)(i)\kappa(i),
\]

以及每个 `T : ℕ` 的实际失败分解

\[
\Pr_{\nu_T}(\exists t\le T:X_t\notin K)
=p_0(K^c)+\sum_{n<T}\Pr_{\nu_{n+1}}(F_{n+1})
=1-s_T.
\]

正时间首次退出不包含初始失败；`p0(Kᶜ)` 不可删除。`K=∅`、`T=0`、某时刻 `s_n=0` 均允许，不需 QSD 或正存活。允许退出后返回，故不能把终态在 K 外的概率当成首次退出概率。

### 现有草稿与最小工作

现成私有草稿：`tmp/finite-encoding-20261021/resume-killed-exit-flux/SameSourceKilledExitFlux.lean`，SHA `8f88617f06f793492b04b875d38dbc097b7043bbe9ef12567b8492cb1eaf3c8c`。独审 `tmp/interface-next-review/resume-killed-exit-flux/REVIEW.md` 已给 **STATIC_MATHEMATICAL_SCOPE_CLEAR — NOT_COMPILED**；本轮没有替它运行 Lean。

草稿已经给出实际前缀 `pmfExtend_map_fst` / `causalLaw_map_prefix` 的构造性证明路线、同一 `nu_(n+1)` 下的不交事件分割和有限望远镜。应沿用它完成实际 elaboration，绑定已过 K1，保留旧声明、原失败记录与初始失败项。局部语法、可判定相等实例及集合记号可参照 K2/QSD 已解决的实际问题；不能靠增加来源等式来消除报错。

这项增量最小、风险层收益直接：把累计失败准确分解为初始缺陷和后续流失。完成后，QSD 初态的通量 `rho^n(1-rho)` 与累计风险 `1-rho^T` 只是同一源质量公式的直接推论。`rho=0,n=0` 的首次退出质量为 1，而后续为 0；`rho=1` 时没有退出。不要为这些推论另建一套过滤或路径理论。

## 3. 第二优先：实际有限路径到既有无限轨迹

### 首个明确验收端点

用既有 `policyTransitionPMF` 的同一行定义 Markov 核 `R`，令

\[
\nu_\infty=\operatorname{homTrajMeasure}(p_0.toMeasure,R).
\]

令 `lambda_n := causalLaw p0 (policyPathKernel M pi) n`。构造只改变历史表示的可测等价 `e_n : CausalHistory X X n ≃ᵐ (Iic n → X)`，证明所有 n 的完整前缀身份

\[
(\operatorname{prefix}_n)_*\nu_\infty
=(e_n)_*(\lambda_n.toMeasure).
\]

先复用原 SourcePolicyPathBridge 擦除动作，再用上述身份；来源模型、策略和初始律都不变。`n=0` 使用 `homTrajMeasure_prefix_zero`；后继步骤对齐 PMF 的 bind/map 与 `homTrajMeasure_prefix_succ` 的 compProd/append。`ViabilityTrajectory.stationaryTrajMeasure_coordinate` 只给坐标边缘身份，不能单独替代完整前缀等式。

若实现成本需要缩小，第一个可接受端点可以只证明

\[
\nu_\infty(X_0,\ldots,X_n\in K)=s_n.
\]

这可用同源初值/首步递推证明，足够接无限存活，但应明确它弱于完整前缀身份。完整前缀版本能被未来其他状态路径事件复用，因而优先争取；不需要先构造全新的无限行动记录过程。含行动的任意事件若不可经状态路径因子化，仍需保留其原记录语义。

### 接上即可复用的结论

命中目标应传入 `Kᶜ`。利用已有存活尾极限与实际初态混合，推出

\[
\Pr_{\nu_\infty}(\forall n:X_n\in K)
=\lim_n s_n=\sum_{x\in K}p_0(x)h(x),\qquad
h(x)=\lim_n(Q^n\mathbf1)(x).
\]

随后按已经独审 CLEAR、尚未形式化的 `FINITE_SUPPORT_AND_INFINITE_SURVIVAL.md` 接三个精准结果：`h` 是 `[0,1]^K` 内最大不动点；`D={h=1}` 是原完整 L 的最大支撑闭合安全集；有限状态下 `h(x)>0` 当且仅当存在始终留在 K 的正边路径到 D。零不动点始终存在，不能声称不动点唯一。只在 killed Q 内“闭合”不排除杀死质量；必须对完整 L 的全部原状态检查后继。既有 `Compression/RecurrentClassGaugeInvariance.lean` 的 `ClosedCarrier`、`Reachable` 和 `ViabilityKernel` 的 Unit 行动特化可供复用，不先新增删除算法；把完整 L 的可达性用于本题时还须排除域外绕路。

K1/QSD 的直接收益是：实际 QSD 初态下 `rho<1` 给出无限存活为 0，`rho=1` 给出概率一安全；这不控制初态支撑以外的区域。`rho>0` 的全部有限窗正存活不能代替无限结论。有限性用于可达集最大值取到；可数无限递减退出概率的既有反例阻止无条件推广。

受控连接直接复用既有可行核最大性：固定随机策略的 D 是受控不变集，因此 `D⊆V`。对于完整状态反馈，可用已有全域保持反馈得到某一策略的 `D=V`。观察受限时，准确额外条件是

\[
\forall y\in q(V),\ \exists a\ \forall x\in V,
\quad q(x)=y\Longrightarrow\operatorname{supp}P(x,a)\subseteq V.
\]

需要的是存在共同安全动作，不是要求某次任意选择出来的具体反馈恰好纤维常值；随机化也不能消除共同安全动作要求。

第一、二项完成后还有一个小而有力的联合端点：实际无限期退出概率等于 `p0(Kᶜ)` 加所有非负首次退出通量之和。它由已证有限望远镜和尾极限导出，不依赖 QSD 或 Doob。

## 4. 第三优先：完整有限窗条件路径，保留时变核

本项的详细合同由独立审查者在 `tmp/interface-next-review/finite-window-doob/FINITE_WINDOW_DOOB.md` 维护，当前正在编写，最终身份以其独立收据为准；本说明只列任务边界，不另造第二份推导。它依赖 K1、K2 和实际有限前缀分解，不依赖无限极限，也不需要 QSD 存在性。

给定全窗口 `s_T>0`，令 `H_m=Q^m1`。对时刻 `t≤T` 的实际安全前缀 `h_t`，末态为 i，待证的核心圆柱事件身份为

\[
\Pr_{\nu_T}(\operatorname{prefix}_t=h_t,S_T)
=\nu_t(h_t)\,H_{T-t}(i).
\]

它应从同一 PMF 递推和未来余窗推出，不能作为条件核定理的新增输入。由此得条件初态 `eta0(i)H_T(i)/s_T`，并在正条件前缀上得到时变核

\[
Q^{(T)}_t(i,j)
=\frac{Q(i,j)H_{T-t-1}(j)}{H_{T-t}(i)}\quad(t<T).
\]

`s_T>0` 不保证每个分母正；应限制到实际正条件前缀。若要定义全状态转移函数，零权重行的任意延拓必须明确仅用于补全函数，不能赋予不存在的条件概率意义。`T=0` 只有实际初态在 K 上的条件化，没有转移。

原行动记录也会被未来权重改变。将 `H_m` 在 K 外延拓为零，记为 `bar H_m`。在正条件前缀末态 i，动作和下一状态的联合权重应为

\[
\frac{\sigma(q(i))(a)\,P(i,a,j)\,\bar H_{T-t-1}(j)}
     {H_{T-t}(i)}.
\]

因此条件化后不能无证据保留原行动策略 sigma。左 QSD 只保证 K2 的终态分布稳定；它不保证纯生存条件下的完整路径是齐次 Doob 路径，也不保证条件初态仍为 r。

生产 `QSDPerron` / `PositiveEigenstructure` 的右特征函数和 Doob 代数继续复用。齐次 Doob 的路径权重通常含终点 h 倾斜，和纯生存条件不同。`Q1=rho·1` 且 `rho>0` 时可取 `h=1` 得 `Q/rho`，这是充分条件；在特定初态及可达边上也可能偶然相等，不能把该全局条件写成无条件必要性。

## 5. 开发边界与研究反馈

下一轮首个实际实现候选已经存在，优先把首次退出草稿完成，避免重新起文件。无限源桥随后单独验证；有限窗合同可同时审查，在分配编译窗口后实现。三项不应打包成一个未经分层验证的大证明。

每个里程碑应区分数学合同、私有 Lean PASS、独立审查和生产集成；当前发布候选保持冻结。数学书的新增内容应呈现同一源上的“未条件失败—存活终态—完整条件路径—无限存活”联系及不同假设。哲学反馈可围绕幸存者内部的稳定为何不等于总体持存、概率一保障为何不同于正概率希望展开，不将形式化的明示假设结论扩大为经验世界或目的价值的最终证明。
