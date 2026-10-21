# 固定策略无限存活：独立数学与 API 审查

日期：2026-10-21。审查者：/root/math_resume。

**结论：MATHEMATICAL_REVIEW_CLEAR_NOT_FORMALIZED。** 未发现需要修改命题、增加数学假设或替换反例的实质错误。本文所审的有限矩阵论证成立；现有无限路径 API 的引用准确。该结论不是新增 Lean 编译 PASS，也不证明尚待接入的递归有限历史与真实无限路径前缀身份。

审查源：[FINITE_SUPPORT_AND_INFINITE_SURVIVAL.md](sandbox:/workspace/scratch/9a8d58b21e30/ueot-path-research/formalization/ueot-core/docs/compression/theory_completion/unified_closure/source_path_research_v1/infinite_survival/FINITE_SUPPORT_AND_INFINITE_SURVIVAL.md)。

源 SHA256：8058ebfc61def92b0e679c3cc371f407b6f145097f27f53cd09acea2e00d1ec8。

审查过程中未修改源文件，未运行 Lean、lake build 或 native 导出；未改生产、书稿、Git 或远端。完整源绑定、所读 API 文件身份和精确算术核对写在 REVIEW.json。

## 1. 最大不动点、闭合集与可达性

| 论证 | 结论 | 独立核查要点 |
|---|---|---|
| §3，\(u_n=Q^n\mathbf1\) 逐点递减并收敛 | CLEAR | \(Q\ge0\)、\(Q\mathbf1\le\mathbf1\) 给出 \(0\le u_{n+1}\le u_n\le1\)。有限坐标和交换极限没有额外正性要求。空安全集时全部逐点陈述真空成立。 |
| §3，\(Qh=h\) 且 \(h\) 为 \([0,1]^K\) 中最大不动点 | CLEAR | 对任意 \(0\le g\le1\)、\(Qg=g\)，有 \(g=Q^ng\le Q^n1\)，再取极限。这里是 greatest fixed point，不是唯一不动点；零向量始终是不动点。 |
| §4，\(D=\{h=1\}\) 对原始 \(L\) 支撑闭合 | CLEAR | 对 \(x\in D\)，安全行质量与加权平均同时达到上界 1，既排除域外质量，也排除通向 \(h<1\) 状态的正概率边。必须按原文对全部 \(y\in X\) 量化。 |
| §4，\(D\) 包含每个 \(C\subseteq K\) 的支撑闭合集 | CLEAR | \(1_C\le Q1_C\) 对域内、域外两类坐标都成立。单调归纳给出 \(1_C\le Q^n1\)，故 \(C\subseteq D\)。无需先假设无限路径身份。 |
| §4，初态概率一当且仅当全部支撑位于 \(D\) | CLEAR，概率语义依赖 §2 来源桥 | 将 \(h\) 在 \(K^c\) 上延拓为 0。因为 \(p_0\) 是原始概率律且 \(0\le h\le1\)，有限加权平均等于 1 当且仅当每个正权重点的值为 1。条件化初态会改变此结论的实验。 |
| §5，\(h(x)>0\Rightarrow x\leadsto_K D\) | CLEAR | 安全可达集包含起点，故非空；有限性使正最大值取到。正概率安全后继仍在可达集，不可达安全后继的矩阵项为零。最大值等号迫使最大值层无杀死质量且支撑闭合。 |
| §5，\(x\leadsto_K D\Rightarrow h(x)>0\) | CLEAR | 沿一条有限正边路径反复使用 \(h=Qh\)，终点值为 1，得到 \(h(x)\) 不小于正的路径乘积；长度零也覆盖。 |
| §5，任意初态的严格正判据 | CLEAR，概率语义依赖 §2 来源桥 | 对非负有限和，严格为正当且仅当至少一个 \(p_0(x)h(x)\) 严格为正。没有把某个起点可行换成所有起点可行。 |

§4–5 的两个等号论证可以在实现时写成非负缺陷和。记
\[
\ell(x)=1-\sum_{y\in K}Q(x,y)\ge0.
\]
若 \(h(x)=1\)，则
\[
0=\ell(x)+\sum_{y\in K}Q(x,y)(1-h(y)).
\]
若 \(z\) 属于安全可达集 \(R_x\) 上的正最大值层、最大值为 \(m\)，则
\[
0=m\ell(z)+\sum_{y\in R_x}Q(z,y)(m-h(y)).
\]
两式每项非负。第二式必须使用 \(m>0\) 才能推出 \(\ell(z)=0\)；原稿已经显式保留这一条件。所得最大值层 \(C\) 非空且对原 \(L\) 闭合，命题 A 给出 \(C\subseteq D\)，所以 \(m=1\)。该证明不需要 Perron 存在性、不可约性或常返类分解证书。

## 2. 两个原反例及其准确作用

### 三状态、半概率存活

在 \(K=(x,s)\) 的次序下，
\[
Q=\begin{pmatrix}0&1/2\\0&1\end{pmatrix},\qquad
u_0=(1,1),\quad u_n=(1/2,1)\ (n\ge1).
\]
所以 \(h=(1/2,1)\)、\(D=\{s\}\)。唯一动作意味着受控可行核同样是 \(\{s\}\)，因此 \(x\) 既不是概率一安全起点，也不能通过换控制器成为概率一可行起点，但其无限存活概率严格为正。原稿的每一项结论都正确。

### 可数无限、递减退出概率

对 \(a_k=2^{-k-2}\)，
\[
\sum_{k=n}^{n+T-1}a_k
=2^{-n-1}(1-2^{-T}),
\qquad
\prod_{k=n}^{n+T-1}(1-a_k)
\ge1-\sum_{k=n}^{n+T-1}a_k
\ge1-2^{-n-1}>0.
\]
空乘积 \(T=0\) 也满足下界。对递减的有限存活事件用连续从上，得到正的无限存活质量；它又不超过第一步的 \(1-2^{-n-2}<1\)。每个安全状态都有通向墓地的正边，因而没有非空支撑闭合安全集，且 \(D=\varnothing\)。

这个反例不仅证明有限性不可直接删除，还准确指出了失效步骤：在从 \(n\) 安全可达的无限集合上，\(h(k)\to1\)，但每个 \(h(k)<1\)；上确界为 1 而最大值不取到。失效的是 §5 的有限最大值步骤，不是有限存活尾事件的连续从上。

额外做了少量 Fraction 精确算术核对：三状态安全矩阵的幂 \(n=0,\ldots,8\)，以及可数例的 \(n\in\{0,1,5\}\)、\(T\in\{0,1,2,8\}\)。它们只是对具体数值与索引的独立核对；一般无限结论由上述解析论证支持，未将有限核对标成无限定理验证。

## 3. 受控可行核与观察量词

§6 第一方向成立。固定随机策略的 \(D\) 支撑闭合；对 \(x\in D\)，若某个被正概率选择的动作 \(a\) 有一条通向 \(D^c\) 的正概率转移，则非负混合中的对应乘积为正，原始闭环 \(L\) 也会退出 \(D\)，矛盾。行动 PMF 的支撑非空，因此可选一个安全动作，得到 ControlledInvariant，再由既有最大性得到 \(D\subseteq V\)。

完整状态反馈的反向也成立，而且当前有限、非空行动设定下，相关反馈选择已在生产代码中存在。应一次性复用 exists_stationary_policy_of_fixed 给出的
\[
\exists\pi_V\ \forall x\in V,\quad
\operatorname{supp}P(x,\pi_V(x),\cdot)\subseteq V.
\]
它是一份对整个 \(V\) 有效的完整策略；该 API 已在 \(V\) 外用非空行动类型选 fallback。不要仅凭“对每个初态分别存在一个全时域安全策略”的较弱量词，直接宣称选出了同一份 \(\pi_V\)。原稿的论证使用前一个正确量词。

观察受限方向的边界也正确。可把“纤维上共同实现”精确写为
\[
A_V(y)=\bigcap_{\substack{x\in V\\q(x)=y}}
\{a:\operatorname{supp}P(x,a,\cdot)\subseteq V\},
\qquad
\forall y\in q(V),\quad A_V(y)\ne\varnothing.
\]
在当前有限、非空行动设置下，这等价于存在一份当前观察平稳策略同时保持整个 \(V\)。随机化不能取消共同安全动作要求：其每个正概率动作都必须属于该交集。观察像外可用 fallback。

一个最小边界见证是两个观察相同的安全状态 \(a,b\) 和失败态 \(d\)：动作 0 在 \(a\) 自环、从 \(b\) 去 \(d\)；动作 1 在 \(b\) 自环、从 \(a\) 去 \(d\)。完整状态可行核是 \(\{a,b\}\)。同一观察策略若以 \(p\) 选择动作 0，保持 \(a\) 需要 \(p=1\)，保持 \(b\) 需要 \(p=0\)，不可能同时满足。这里的障碍是 \(\exists\sigma\,\forall x\in V\)，不能用 \(\forall x\in V\,\exists\sigma_x\) 替代。

**非阻断措辞建议：** 共同可实现性应针对“存在一份共同安全反馈”，不必要求某次任意 Classical.choose 产出的具体 \(\pi_V\) 恰好在观察纤维上常值。后者是一个充分证书，但可能比实际需要更强。这不改变原稿命题。

## 4. 已有 API 与实际待接接口

下表路径均相对于审查工作树的 formalization/ueot-core；所读完整文件的 SHA 已记录于 JSON。

| 现有端点与文件 | 可直接复用的事实 | 仍须保持的范围 |
|---|---|---|
| CoreOperationalAssembly.policyTransitionPMF、policyTransitionPMF_apply_toReal、policyPathKernel、policyMatrix | 同一模型、同一随机平稳策略诱导的 PMF、递归路径核与实矩阵已有准确关系 | 不应另给一张独立矩阵再把其等于真实源放入假设。 |
| DynamicsKernel.homTrajMeasure_prefix_zero、homTrajMeasure_prefix_succ、pathMeasure_eq_of_prefix_eq；UEOT/V3/DynamicsKernel.lean | 真实无限路径的完整前缀递推及由所有前缀确定整条路径律已经存在 | 其前缀是 Iic 索引函数；K1 是递归 CausalHistory。当前专门表示桥尚不能标 PASS。 |
| Objecthood.survivalProb_eq_homTrajMeasure_apply、survivalProb_succ_eq_lintegral、survivalProb_eq_zero_of_mem；AbsorbedRepairHittingSemantics.lean | 真实有限存活事件、首步递推和初始已经失败时的零质量已经存在 | 参数 A 是命中目标；本题应传 \(K^c\)，保留时间零。 |
| Objecthood.homTrajMeasure_apply_eq_lintegral_initial；同上 | 任意初态路径事件质量等于点初态质量的真实混合 | 使用 \(p_0.toMeasure\)，而不是重新归一化安全部分。 |
| Objecthood.survivalProb_tendsto_neverHitProb、neverHitProb_first_step；FiniteStationaryHittingExpectation.lean | 存活尾极限和真实 never-hit 概率的调和关系已证 | 当前文件有有限状态与可测单点类前提；不能直接把该有限态封装当作可数反例的已形式化 API。 |
| Objecthood.neverHitProb_zero_support_closed、exists_uniform_half_survival_horizon；同上 | 零存活类的支撑传播和有限态一致尾收缩已有结果 | 不宜把所有支撑/尾行为都描述成新缺口；它们不直接给出本稿的最大正值层结论。 |
| RecurrentClassGaugeInvariance.ClosedCarrier、Reachable；Compression/RecurrentClassGaugeInvariance.lean | 原始支撑闭合谓词与矩阵幂正质量可达谓词已有定义 | ClosedCarrier 应作用于完整 \(L\)。安全可达应作用于 \(Q\) 的安全子类型，不能把允许域外绕路的 Reachable L 当成安全可达。 |
| RecurrentSupportMargin.reachable_trans_of_rowStochastic；Compression/RecurrentSupportMargin.lean | 有限随机矩阵的可达传递性已有证明 | 该端点明示 rowStochastic；killed \(Q\) 只有次随机性，不能直接喂给它。其证明实际只需非负性，若需要可作小范围参数放宽。 |
| ViabilityKernel.controlledInvariant_subset_iter、exists_stationary_policy_of_fixed、finite_viability_kernel_structure；UEOT/V3/ViabilityKernel.lean | 有限删除稳定、最大受控不变集和完整确定性平稳反馈已有 | 固定策略的最大闭合集可通过 Unit 行动特化复用该结构；无需重建删除框架。 |
| ViabilityTrajectory.exists_stationary_policy_all_times_of_fixed；UEOT/V3/ViabilityTrajectory.lean | 支撑在固定可行核内的初态存在真实无限路径全时域安全实现 | 初态支撑、可测性、同一反馈及固定点前提不可省略。 |
| UnifiedClosure.single_source_terminal_object_viability_all_times；CoreSourceAllTimesAssembly.lean | 一份原始源经过既有组织/控制装配得到原微观路径的真实全时域安全 | 保留已注册安全观察和初态支撑等前提；全项目并不缺少全时域同源安全定理。 |
| QSDPerron.leftPerron_pow、qsd_survival_mass_pow、qsd_all_steps；UEOT/V3/QSDPerron.lean | 左特征行的幂传播、生存质量 \(\rho^n\)、正 \(\rho\) 下条件终端行已证 | 新增工作是实际同源初态/路径事件的适配，不是重证矩阵代数。 |

一个实现陷阱需要明确：对 killed 子矩阵使用 ClosedCarrier Q 本身并不排除杀死质量。例如 \(Q=[1/2]\) 的整个一元素载体对 Q 的内部正边闭合，但 \(Q^n1=2^{-n}\to0\)。原稿正确地使用完整 \(L\) 对全部原状态量化，所以没有这个错误。

§2 给出的两条接入路线都合法：

1. 证明完整前缀分布的表示身份，随后任意对应有限事件都可复用。
2. 只证明本题生存事件的同源初值与递推，推出所有有限生存质量相等，再复用尾极限。

第二条足以证明本题无限生存概率，但不会自动得到第一条更强的完整前缀身份。本次审查不对任一路线作已实现或编译通过的声明。

## 5. QSD 推论与状态结论

§7 正确。非负归一化左特征行满足 \(rQ=\rho r\) 时，现有 qsd_survival_mass_pow 已给出全部有限 \(n\) 的 \(\rho^n\)；不要求正右特征向量。非负次随机性使 \(\rho\in[0,1]\)。\(\rho=0\) 仍有 \(s_0=1\)，而 \(n\ge1\) 的生存为零，不能定义这些零分母上的条件律。\(\rho>0\) 时，qsd_all_steps 对应的条件终端行成立；\(\rho=1\) 时归一化初态支撑位于 \(D\)。非全支撑的 \(r\) 不控制其他初态或其他安全区域。

PositiveEigenstructure.BiEigenData 的正右向量及正尺度要求强于本节单纯的左特征行条件；不应为了调用它给本节额外加入严格正右 Perron 数据。尤其 \(\rho=0\) 的生存退化情形不属于它的正尺度接口。

最终审查状态：

- 数学推导、原反例、固定策略/受控策略的量词边界：CLEAR。
- 需要修正的数学命题或补充的假设：无。
- 建议细化的非阻断实施说明：观察纤维共同动作量词、完整 \(L\) 与 killed \(Q\) 的闭合差别、有限/可数 API 范围、\(\rho=0\) 条件化边界。
- 新增无限前缀桥、最大不动点/D/可达性组合 API：本次未实现、未编译、未验证为 PASS。
- 既有全时域安全、存活尾极限、混合与 QSD 幂代数：已确认存在，继续复用。
