# 同源路径实现：数学结果、原始责任与明确边界

日期：2026-10-22。研究起点为已验收 main
`50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04`。

本报告覆盖本批七个新增模块。它说明实际构造、证明所需条件、增加的推论以及
原始任务中仍保留的责任。七个模块的最终源码均已有实际聚焦 Lean 通过结果；
有限窗、Doob 与三状态见证的最终来源链在 compile-09 顺序执行中全部通过。
物理安全见证随后完成实质 API 修订，并在 compile-10 实际通过。

**当前冻结源为 manifest02：691 个模块、73 个源码公开声明、25 条源码提示，
完整指纹为 `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`。**
原源指纹 `c344bf6657ab31a32c46fba9feff6d5c04846b8f061d444aec8accb4994ad41b`
的 full build01 已实际 PASS（30.553 秒）；原 native01 在内部类型比较无进展后
被定点中断，状态为 FAIL，未产生完整验收导出。

**当前新源的 full build02 已实际 PASS（14.23 秒）；native02 的导出与固定
verifier 均实际 PASS（58.451 / 58.297 秒）。** 本报告已读取两份原始工具收据，
native 摘要为 **7 模块、73 个公开声明、249 个编译器审计定理常量、114 条注册
直接证明边**，原状态是 `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`。
完整原档已逐字节导入，独立执行审查 **CLEAR**，第 11 层已实际注册。
54 项复用测试、完整 30 项 FKRG、89 项 parser 及完整 691 模块的 68 行克隆
表核对均通过；原有完整 canonical 审计实际 **PASS，60.702 秒**。[消费者独审][consumer-review]
与 [canonical 执行独审][canonical-review]均已 CLEAR。Git 对象及发布验收由单独记录承担。历史失败、
先前 PENDING 与旧快照继续保留，完整执行记录详见末节。

**本批新增的是实际来源与路径之间的证明连接。** 原有有限记忆控制器现在得到
自己的状态—记忆过程、完整有限前缀以及同源无限状态律；物理初态与认证转移
条件把该控制器的零未认证占据推进为概率一全时安全。另一条路线从原有限实验
构造存活条件路径，证明其有限窗行公式及与同源 Doob 路径的准确差异。C3 路线
把注册嵌套族中的数学选择推进为实际短路搜索和精确查询证书。

物理安全见证的最新公开端点把三份真实来源并列为完整合取，除了保留五个实际
质量结论，还明确证明转移反例的 `¬hclosed` 与初态反例的 `¬hinit`。五个原质量
计算继续作为私有证明成分被全部引用。公开候选域由 77 改为 73；这是有记录的
API 变化，不能称旧的 77 项已完成原全量比较。[修订说明][memory-api-revision]
分别记录新增推论、原失败、公开比较域与包含私有常量的编译器审计域。

这些结果均为 **uncounted same-source path realization**。冻结的 106 个 P-ID
仍是 **11 generated / 89 adapters / 6 boundaries**，counted generators 仍为
**4**，强意义的全局数学闭合仍为 **`NOT_ESTABLISHED`**。本批没有重新分类这些
记录，也没有改变统计校准、物理领域适配或经验验证的责任。

## 一、来源、模块与新增责任

### 1. 五份原始来源的身份

[原始来源绑定记录][original-binding]核对用户提供的五份文件与仓库 canonical
文件逐字节一致。该记录证明本批引用的是同一份原始材料；原路线图中的历史状态
仍是历史状态，不能作为本批执行或发布通过的证据。

| 原始材料 | 仓库中的职责 | SHA-256 |
|---|---|---|
| [UEOT_v3_top.pdf][original-top] | 对象、变化、持续、层级与目的问题的原始动机 | `6c2acdf8d8232377066c3363ce3f0b0a14b3b60608c485ce70f2089c8a2263c3` |
| [UEOT_Core_Mathematics_v3.0_Complete.md][original-core] | 冻结 Core 的定义、命题、假设、证明与开放问题 | `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303` |
| [CORE_V3_OPEN_PORT_MATRIX.md][original-ports] | C1–C7 工作包、适用范围及验收责任 | `f71ba345602ee750116b0481dce7d78cf212a0fb02bccac79d482703ada0b20a` |
| [CORE_V3_POST_CORE_SCIENTIFIC_CLOSURE.md][original-closure] | 原 Core、扩展、领域适配与现实证据的职责划分 | `669ec5667575c9dbe75645fa2c00501e4cfbec68ca8a3420825f4b6d08f41569` |
| [THEORY_COMPLETION_ROADMAP_V2.md][original-roadmap] | 后续研究的依赖、范围与交付门槛 | `64ab8d688f7ddfc7c739dd4af3b7760eba362190cd8897a605644b0fbd95cd07` |

本批没有修订上述原始文件或两部独立著作。后续书稿可以吸收这里的数学联系，
但书稿更新、正式生产验收和经验支持各自需要对应证据。

### 2. 七个模块的作用

| 新模块 | 已有输入 | 本批新增的数学推论 |
|---|---|---|
| [FiniteMemoryRealization][memory-source] | 同一个 `FiniteMemoryController`、原始初态、观察、完整数值转移序列 | 从原微观历史律构造状态—记忆初态与行序列，并证明完整有限及无限前缀身份 |
| [FiniteMemoryPhysicalSafety][physical-source] | 上述实际路径；同一策略的零未认证占据；独立的物理初态与转移条件 | 原微观前缀安全、同源无限状态律上的全时安全，以及现有支持控制器消费者 |
| [FiniteMemorySafetyWitness][safety-witness] | 非空 Boolean 状态与单记忆、单行动真实 PMF 源 | 一个全时安全正例和两个独立必要条件反例，直接计算实际坐标事件质量 |
| [SameSourceFiniteWindow][window-source] | 原齐次模型、原初态、当前观察反馈及其 killed 矩阵 | 原完整前缀与末端存活事件的联合质量、实际条件前缀、初态、全路径及正质量行比 |
| [FiniteWindowDoob][doob-source] | 同一 killed 矩阵的正右特征数据与原安全初始行 | 真正 Doob PMF 路径的端点倾斜公式，以及与实际有限窗条件路径的逐原子相等判据 |
| [FiniteWindowDoobWitness][doob-witness] | 三状态原模型、同源左 QSD 与正右特征数据 | 同初始边际下两条实际二时刻路径的 TV 为 `1/4`，从而路径不相同 |
| [C3ExecutableSearch][c3-source] | 已注册嵌套载体族和实际 Boolean oracle | 首个正响应的可执行搜索、实际输出身份、精确查询次数和注册族内包含极小性 |

这些结论由原始 PMF、递归定义、支持关系和现有定理推出。新的来源身份与安全
结论没有被放进结构字段作为前提。详细接口见[记忆实现合同][memory-contract]、
[有限窗实现端点][window-endpoints]和[C3 合同][c3-contract]。

## 二、同一控制器的状态—记忆过程

### 1. 原实验与更新时序

固定状态类型 $X$、行动类型 $A$、任意观察类型 $Y$、记忆类型 $M$，以及

$$
p_0:\operatorname{PMF}(X),\qquad q:X\to Y,\qquad
P_n:X\times A\to\operatorname{PMF}(X).
$$

固定已有的同一个控制器，记其初始记忆为 $\iota$，行动分布为 $\alpha$，
更新函数为 $u$。原实验按以下顺序运行：

$$
X_0\sim p_0,\quad M_0=\iota(q(X_0)),\quad
A_n\sim\alpha(M_n),\quad X_{n+1}\sim P_n(X_n,A_n),\quad
M_{n+1}=u(M_n,A_n,q(X_{n+1})).
$$

这里 $M_n$ 与现有 `controller.memory n` 对原观察/行动记录的递归重放完全
相同；原历史律始终是 `microLaw p₀ q P controller.policy n`。当前行动先被记录，
随后用这个实际行动和新观察更新记忆。没有把原控制器替换成另一个有限时域
选择器，也没有预先归一化或更换 $p_0$。

### 2. 增广初态与真实非自治行序列

构造 `augmentedInitial`：

$$
\widetilde p_0=
\bigl[x\mapsto(x,\iota(q(x)))\bigr]_*p_0.
$$

构造 `augmentedRow`，记为 $J_n$。它先按 $\alpha(m)$ 采样行动，再按同一个
$P_n(x,a)$ 采样后继 $z$，最后返回 $(z,u(m,a,q(z)))$。在有限类型上，其
原子公式为

$$
J_n\bigl((x,m),(z,m')\bigr)
=\sum_{a\in A}\alpha(m)(a)P_n(x,a)(z)
\mathbf1\{m'=u(m,a,q(z))\}.
$$

因此，状态—记忆过程有实际的数值核序列 $J_0,J_1,\ldots$。一般情况下它
随时间变化。即使所有 $P_n$ 具有同一个支持关系，也不能把数值核序列改写成
一个固定核或一个固定 killed 矩阵。

`augmentHistory` 重放每一个已记录行动，保留从时刻 0 到时刻 $n$ 的所有
状态—记忆对。`augmentHistory_last` 证明最后一对就是原微观末状态和原控制器
的实际记忆；`eraseMemory_augmentHistory` 证明再擦除记忆会得到原完整状态记录。

### 3. 完整有限前缀身份

设 $\mu_n$ 为原 `microLaw`，$\mathsf A_n$ 为上述历史增广映射。
`actual_augmented_history_law` 证明

$$
\boxed{
(\mathsf A_n)_*\mu_n
=\operatorname{causalLaw}_n(\widetilde p_0,J).
}
$$

这是完整历史 PMF 的等式，包含原初态、全部中间状态和全部记忆状态。证明从
真实 PMF 的 `map`/`bind` 和一步扩张递归出发，逐步验证增广与扩张可交换。
`augmented_history_state_projection` 随后证明增广前缀的状态投影就是原行动擦除后
的完整状态前缀。[源码][memory-source]及[独立来源审查][memory-review]核对了
这一时序和来源身份。

状态投影未必具有只依赖当前 $X_n$ 的 Markov 性。记忆已在构造中承担影响行动
的历史信息；擦除记忆后，一般仍需保留历史。另一方面，状态—记忆记录可能无法
恢复全部行动。依赖被擦除行动的事件必须另建保留行动的映射，不能自动当成
增广路径上的事件。

### 4. 同一个无限律及其状态投影

`sequenceTrajMeasure` 将时间 $n$ 的历史末状态送入真实行 $J_n$，使用已有
Ionescu–Tulcea 构造得到无限路径测度。零时刻和一步续接的实际身份给出
`state_history_eq_sequence_prefix`；再代入刚构造的 $\widetilde p_0,J$，得到
`actual_augmented_prefix_eq`。

若 $\widetilde\mu$ 表示 `augmentedTrajMeasure`，$\operatorname{pref}_n$
保留前 $n+1$ 个坐标，那么在相应历史编码等价下，

$$
(\operatorname{pref}_n)_*\widetilde\mu
\quad\text{等于}\quad
\bigl((\mathsf A_n)_*\mu_n\bigr).\operatorname{toMeasure}.
$$

`actual_augmented_prefix_event_mass` 将此身份落实到每个有限前缀事件。

随后定义 `stateTrajMeasure` 为同一个 $\widetilde\mu$ 在逐坐标第一投影
$(x,m)\mapsto x$ 下的像测度 $\mu_X$。`actual_state_prefix_eq` 和
`actual_state_prefix_event_mass` 证明其每一个完整状态前缀来自原实验；特别地，
`stateTrajMeasure_coordinate_mass` 给出

$$
\mu_X\{\omega:\omega_n\in E\}
=\mu_n.\operatorname{toMeasure}
  \{h:\operatorname{lastState}(h)\in E\}.
$$

这一等式包括 $n=0$。原初始失败质量由此保留到无限路径中。

| 层次 | 当前形式化的类型条件 |
|---|---|
| 增广初态、行、重放与完整有限 PMF 等式 | 不要求有限类型或可测结构；观察类型任意 |
| 无限增广律及其 PMF—前缀测度身份 | $X,M$ 有限并具有可测单点；观察与行动类型仍可任意 |
| 原行动历史事件质量及物理支持证明 | 另要求 $A$ 有限并具有可测单点 |
| 现有支持记忆控制器消费者 | 使用其有限支持记忆类型，并显式赋予有限离散可测结构 |

这补上了“这个控制器确实生成这个过程”的责任。它没有额外证明任意历史策略
都能压缩成有限记忆，也没有证明该记忆是规范最小预测商。

## 三、从自身零未认证占据到实际物理安全

### 1. 三项独立输入

给定物理安全集 $K\subseteq X$ 和逐时认证谓词 $C_n(x,a)$。令
$\nu_n^\pi$ 为同一 $p_0,q,P,\pi$ 生成的实际状态/行动占据律。新的安全桥
使用以下三项输入：

$$
\begin{aligned}
&\operatorname{supp}(p_0)\subseteq K,\\
&x\in K\ \land\ C_n(x,a)\ \land\ z\in\operatorname{supp}(P_n(x,a))
  \Longrightarrow z\in K,\\
&U_n^\pi:=\nu_n^\pi\{(x,a):\neg C_n(x,a)\}=0
  \quad\text{对每个 }n.
\end{aligned}
$$

第三项中的占据正是现有 `coverageDeploymentRowLaw` 的实际来源。第一项给出
原初态安全；第二项把“认证”与同一源模型的物理安全后继联系起来。没有这两项，
零未认证占据只说明策略没有使用未认证行。

### 2. 有限支持归纳与无限事件

`supported_micro_history_safe` 先对任意完整因果策略证明：原 `microLaw` 的每个
有支持历史，全部状态都在 $K$ 中。一步归纳从实际扩张的支持中取出原前缀、
所选行动和实际后继；现有零占据/支持认证等价给出这个已选行动在真实状态上
被认证，再使用物理转移条件推进安全。

`actual_finite_safety_one` 因而得到每个原有限实验的全前缀安全概率为 1。对
有限记忆控制器，上一节的实际坐标身份把这些质量转移到同一 $\mu_X$；已有
`ViabilityPath.all_times_safe_eq_one` 对可数个概率一坐标事件取交，得到

$$
\boxed{\mu_X\{\omega:\forall n\ge0,\ \omega_n\in K\}=1.}
$$

公开端点是 `controller_all_times_physical_safe`。这里证明的是同一控制器的
实际无限状态律上永不退出，不只是每个有限时域存在某个好策略，也不是每个
有限时域有正存活概率。[物理安全源码][physical-source]保留上述全部条件。

### 3. 已有支持固定点控制器的直接消费

`supportMemoryController_all_times_physical_safe` 消费已有
`supportMemoryController` 及其 `supportMemoryController_zero_uncovered`。
其原始初态、观察、数值源序列、支持关系、认证谓词、fallback 和初始 winning
条件保持一致；来源支持及认证匹配按原定理要求显式给出。

因此，在原控制器已证明自己的零未认证占据后，新加入物理初态与认证支持保持
条件即可推出它自己的实际无限安全。这里没有把该控制器等同于更早的
`viablePolicy`，也没有用来源支持上的一致性压缩参考过程 $Q$ 的完整历史检查
预算。参考过程在来源零概率历史上的行为仍由其自己的接口负责。

### 4. 两个必要条件的独立反例

[FiniteMemorySafetyWitness][safety-witness] 使用 $X=\{\mathrm{false},\mathrm{true}\}$，
一个记忆、一个行动、恒定观察，以及非空真子集 $K=\{\mathrm{false}\}$。认证
谓词恒真，因此各例的每个实际 $U_n$ 都为零。

| 原初态与真实转移 | 初态安全 | 认证后继保持 $K$ | 实际全时安全质量 |
|---|---|---|---|
| $p_0=\delta_{\mathrm{false}}$，每步返回 `false` | 成立 | 成立 | $1$ |
| $p_0=\delta_{\mathrm{false}}$，每步返回 `true` | 成立 | 不成立 | $0$，时刻 1 的安全质量已为 $0$ |
| $p_0=\delta_{\mathrm{true}}$，每步返回 `false` | 不成立 | 成立 | $0$，时刻 0 的安全质量已为 $0$ |

负例先通过 `stateTrajMeasure_coordinate_mass` 回到原微观 PMF，从支持计算相应
坐标事件质量，再用全时安全事件包含于该坐标事件得到结论。它们没有直接设定
一个目标事件的测度。第三例同时表明：下一步修复不删除“从时刻 0 起从未失败”
这个事件中的原初始失败。

这些例子检验两个物理前提的独立性；有限记忆严格增加控制能力的责任仍由已有
`FiniteMemorySeparation` 的两记忆见证承担。

## 四、从原有限实验得到存活条件路径

### 1. 这一条路线的齐次条件

有限窗路线固定有限状态与有限、非空行动类型、原模型 $M$、观察 $q:X\to Y$、
时间齐次当前观察随机反馈 $\sigma$、原初态 $p_0$ 和安全集 $K$。观察类型
$Y$ 任意。实际反馈产生数值齐次闭环核 $L$，$Q=L|_{K\times K}$ 为同源
killed 子矩阵，$\eta_0(i)=p_0(i)$ 为未重新归一化的安全初始行。

记

$$
S_T=\{X_0,\ldots,X_T\in K\},\qquad
s_T=\Pr_{p_0,L}(S_T),\qquad g_r=Q^r\mathbf1.
$$

`actualSurvivalMass` 的概率来自原行动/状态完整实验；已有同源 killed 路径接口
给出 $s_T=\eta_0Q^T\mathbf1$。本批又在
`actual_survival_mass_eq_initial_remaining_sum` 中写成

$$
s_T=\sum_{i\in K}\eta_0(i)g_T(i).
$$

一般记忆实现中允许的数值非自治性没有被偷偷带入这个固定矩阵公式。若要接入
随时间变化的源，需另证有序核乘积版本，或提供合法的有限相位扩张。

### 2. 完整前缀和未来存活的联合质量

令 $h=(x_0,\ldots,x_t)$ 是安全前缀，末状态为 $i\in K$。从实际路径递归
逐步求和安全后继，本批证明

$$
\boxed{
\Pr(H_t=h,\ S_{t+r})=\Pr(H_t=h)g_r(i).
}
$$

端点是 `actual_prefix_survival_mass`。证明先对任意末端测试函数建立加权后缀
求和归纳，再取常数 1；它由原行动擦除身份接回微观实验。该联合质量身份不要求
前缀或总存活概率为正，包含 $t=0,r=0$，也保留原初态在 $K$ 外的质量。

### 3. 实际条件前缀、初态与完整路径

只有在 $s_{t+r}>0$ 时，`actualConditionedPrefix` 才对原完整行动/状态 PMF
应用 `PMF.filter`，按原存活事件条件化，然后擦除行动并保留状态前缀。
这给出一个实际 PMF；其来源不是另行假定的条件核。

`actual_conditioned_prefix_mass` 得到

$$
\Pr(H_t=h\mid S_{t+r})
=\frac{\Pr(H_t=h)g_r(i)}{s_{t+r}}.
$$

两个重要特化分别是 `actual_conditioned_initial_mass` 和
`actual_conditioned_safe_path_mass`：

$$
\boxed{\Pr(X_0=i\mid S_T)=\frac{\eta_0(i)g_T(i)}{s_T},}
$$

$$
\boxed{
C_T(i_0,\ldots,i_T)
=\frac{\eta_0(i_0)\prod_{k<T}Q(i_k,i_{k+1})}{s_T}.
}
$$

条件化通常改变初态。在 $T=0$ 时，该公式仅把原初态限制在 $K$ 并按其原始
质量归一化；在正时域还额外按未来存活权重 $g_T$ 倾斜。
`actual_conditioned_prefix_support` 证明条件前缀的支持安全，
`actual_conditioned_prefix_eq_zero_of_not_survives` 证明每个不安全前缀原子为零。

本批最后的证明复用重构把通用 filter/map 原子计算改为公有 PMF 外测度与像测度
接口，再在实际来源端点完成 `toMeasure`/`toReal` 转换。它保持上述命题及正性
条件不变；[复用重构记录][window-reuse]保留此前通过快照、未执行中间稿与新候选
的区别。

### 4. 正质量历史上的实际下一行

若从当前前缀到最终时域还剩 $r\ge1$ 步，而且同一个原实验中的父事件
$\Pr(H_t=h,S_{t+r})$ 为正，则

$$
\boxed{
\Pr(X_{t+1}=j\mid H_t=h,S_{t+r})
=Q(i,j)\frac{g_{r-1}(j)}{g_r(i)}.
}
$$

形式化端点 `actual_next_prefix_ratio` 比较同一最终时域下真实 child/parent
联合事件质量；其源码索引 `finiteWindowRow Q r` 表示上述还剩 $r+1$ 步的一行。
`actual_positive_prefix_remaining_pos` 从正父事件质量推出相应 $g_r(i)>0$。

`finiteWindowRowPMF` 只在该行分母严格为正时构造归一化 PMF。全局 $s_T>0$
不足以让每个状态或每个历史都有正条件行；实数表达式的形式总定义也不意味着
零分母处存在概率行。

**当前实现范围是：完整条件路径由原实验过滤直接构造，正质量 child/parent
比值给出有限窗行。** 本批没有另外为所有零质量状态选取 total fallback，构造
独立的时间变化条件核，再证明那个核生成的全路径等于上述过滤 PMF。
这一进一步的生成定理仍有自己的责任。[有限窗端点说明][window-endpoints]与
[独立静态审查][window-review]均按此范围验收。

## 五、同源 Doob 路径及准确相等条件

### 1. 真正构造的初态、转移和路径

给同一个 $Q$ 的正右特征数据

$$
Qh=\rho h,\qquad \rho>0,\qquad h(i)>0,
$$

并保留原未归一化安全初始行 $\eta_0$。记

$$
c=\langle\eta_0,h\rangle>0.
$$

`doobRowPMF` 使用已有正特征结构的非负性和行和证明构造 PMF 行；
`tiltedInitialPMF` 使用实际配对 $c$ 构造自然初始倾斜：

$$
D(i,j)=\frac{Q(i,j)h(j)}{\rho h(i)},\qquad
\eta^h(i)=\frac{\eta_0(i)h(i)}{c}.
$$

`doobPathLaw` 是由这两项生成的真实有限因果 PMF。$c$ 不被默认设为 1；一般
的 $\eta^h$ 也不被默认称为不变初态。这里固定的是 Doob 数值核。

### 2. 原 killed 权重的末端倾斜

沿路径展开实际 PMF 递归，内部的 $h(i_k)$ 逐项消去。
`doob_path_atom` 证明

$$
\boxed{
D_T(i_0,\ldots,i_T)
=\frac{\eta_0(i_0)\prod_{k<T}Q(i_k,i_{k+1})\,h(i_T)}{\rho^Tc}.
}
$$

接入上一节已证明的实际有限窗身份，`actual_doob_path_comparison` 给出

$$
\boxed{
D_T(\gamma)
=C_T(\gamma)\frac{s_T h(\gamma_T)}{\rho^Tc}.
}
$$

对每条 killed 权重严格为正的安全路径，
`actual_doob_atom_eq_iff_terminal_weight` 进一步证明

$$
D_T(\gamma)=C_T(\gamma)
\quad\Longleftrightarrow\quad
h(\gamma_T)=\frac{\rho^Tc}{s_T}.
$$

这个判据约束实际正质量路径的末端，不把不可达状态上的额外条件当成必要条件。
一般有限窗条件路径、QSD 的条件终端分布与固定 Doob 核产生的路径，因此有
明确但不同的对象和量词。[Doob 源码][doob-source]直接证明上述关系。

### 3. 一个充分条件与保留的极限责任

`remainingSurvival_eq_pow_of_constant_row_sum` 证明，若 $Q\mathbf1=\rho\mathbf1$，
则 $g_r=\rho^r\mathbf1$。若再有 $\rho>0$，
`finiteWindowRow_eq_normalized_of_constant_row_sum` 给出每个有限窗行都是 $Q/\rho$。

左 QSD 关系 $\eta Q=\rho\eta$ 本身没有给出常数行和条件。也不能仅由这些
有限时域公式宣布长窗极限或 Q-process 极限成立；正特征数据如何获得、相应
谱条件、支持范围及所需收敛方式仍由各自的命题负责。

## 六、三状态实际源：同初始边际仍有路径 TV 为 $1/4$

### 1. 完整原模型与同源特征数据

令 $X=\{0,1,\dagger\}$，$K=\{0,1\}$，行动类型为单点，观察与反馈恒定。
在顺序 $0,1,\dagger$ 下，完整实际转移矩阵是

$$
L=
\begin{pmatrix}
3/8&3/8&1/4\\
1/8&1/8&3/4\\
0&0&1
\end{pmatrix},\qquad
p_0=(1/2,1/2,0).
$$

墓地吸收是这个见证的实际定义；一般有限窗定理没有要求所有域外状态吸收。
限制原反馈核得到

$$
Q=\begin{pmatrix}3/8&3/8\\1/8&1/8\end{pmatrix},\qquad
\eta=(1/2,1/2),\qquad \rho=1/2.
$$

同一源满足

$$
\eta Q=\tfrac12\eta,\qquad
h=(3/2,1/2),\qquad Qh=\tfrac12h,\qquad \eta h=1.
$$

`source_left_qsd` 和 `actual_survival` 从实际源证明该 QSD 关系及
$s_T=(1/2)^T$。因此这个例子具有真实左 QSD，并且每个有限时域存活质量为正；
这仍不把完整条件路径与 Doob 路径识别为同一个概率对象。

### 2. 两个实际二时刻联合律

在 $T=1$ 时，原存活条件化初始边际是

$$
\frac{\eta(i)g_1(i)}{s_1}=(3/4,1/4).
$$

自然 Doob 初始倾斜也是 $\eta(i)h(i)=(3/4,1/4)$。两者的初始边际相同；
同一 $Q$ 的 Doob 每行均为 $(3/4,1/4)$，而该有限窗条件下一行均为
$(1/2,1/2)$。其完整二时刻联合律为：

| 初态、末态 | 原源条件律 $C_1$ | 自然倾斜 Doob 律 $D_1$ | 绝对差 |
|---|---:|---:|---:|
| $(0,0)$ | $3/8=6/16$ | $9/16$ | $3/16$ |
| $(0,1)$ | $3/8=6/16$ | $3/16$ | $3/16$ |
| $(1,0)$ | $1/8=2/16$ | $3/16$ | $1/16$ |
| $(1,1)$ | $1/8=2/16$ | $1/16$ | $1/16$ |
| 任一坐标为 $\dagger$ 的其余五个原子 | $0$ | $0$ | $0$ |

`conditionedPair` 从原行动/状态实验过滤后取得完整状态对；四个安全原子通过
`actual_conditioned_safe_path_mass` 计算。`doobPair` 是实际 `doobPathLaw`
向同一三状态对空间的像。两侧墓地原子的零质量分别由实际过滤支持和嵌入像
证明。因此对比覆盖同一空间的全部九个原子，而非只比较抽出的子表。

$$
\|C_1-D_1\|_1=\frac{8}{16}=\frac12,
\qquad
\boxed{\operatorname{TV}(C_1,D_1)=\frac14.}
$$

源码使用已有的共同质量公式：

$$
\sum_\gamma\min\{C_1(\gamma),D_1(\gamma)\}=\frac34,
\qquad \operatorname{TV}=1-\frac34.
$$

公开端点是 `actual_conditioned_doob_tv` 和 `actual_conditioned_ne_doob`。
该见证与最终 Window、Doob 源码在 compile-09 顺序执行中全部 PASS，来源和
精确用时见[最终聚焦链记录][window-focused]。此前 compile-08 的上游失败与其
下游消费旧缓存的限制继续保留。数学表格、来源构造与 API 范围的
[独立静态审查][c3-doob-review]及[最终源码独审附记][window-review]与实际执行
分别记录证据。

这个见证排除了“有同源 QSD，且采用自然 Doob 初态，就足以识别有限窗完整路径”
的推广。其差异已经出现在初始边际相同的情况下。它没有否定原 Core 的 QSD
或 Doob 结论，也没有涉及两者在另加谱条件后的长窗渐近关系。

## 七、C3：实际注册载体搜索与精确调用记录

### 1. 程序输入与原数学选择的关系

已有 `C3NestedSearch` 定义注册嵌套族及 `firstGoodIndex`，给出链内最小 good
下标的数学性质。新模块输入真正的

$$
O:\operatorname{Finset}(V)\to\operatorname{Bool},
$$

按注册顺序调用，遇到第一个 `true` 即停止。结果 `SearchRun` 同时包含
`found : Option Nat` 与实际查询索引列表 `queries`。未知真载体、旧的最小下标
或“已有 good 项”的存在证明没有被当作程序输入。

若共有 $N=n+1$ 个注册候选 $F_0,\ldots,F_n$，正确性定理保留明确的模型匹配：

$$
\forall i<N,\quad O(F_i)=\mathrm{true}\ \Longleftrightarrow\ \operatorname{Good}(F_i).
$$

`search_found_iff` 证明实际输出恰为第一个 good 注册下标；`search_none_iff`
证明 `none` 恰表示全部注册项都不 good。`search_eq_firstGoodIndex` 进而证明
程序输出等于原非可计算数学选择，等同性是定理结论。

### 2. 查询语义、数量和范围

通用 `scan O start fuel` 顺序扫描半开区间
$[start,start+fuel)$。它的递归定义记录每次实际调用，相关定理给出

$$
\#\mathrm{queries}=
\begin{cases}
i-start+1,&\mathrm{found}=\mathrm{some}\ i,\\
fuel,&\mathrm{found}=\mathrm{none}.
\end{cases}
$$

注册入口因此在成功下标 $i$ 时恰查询 $i+1$ 次，失败时恰查询 $N$ 次，
统一上界为 $N$。每个查询索引在表内，且没有重复索引。

族中可以出现值相同的多个候选集合；不重复索引没有自动给出集合值去重或
缓存。这里的 oracle 是纯 Boolean 函数，trace 记录该程序定义的函数调用；
它不是外部 I/O、物理操作或样本采集日志。

### 3. 单调性只在实际需要的地方使用

顺序扫描已经查询了输出之前的每个索引，故第一成功/失败定理不需要 oracle
或 Good 的向上单调性。注册集合族的 nested 条件只用于推出

$$
\operatorname{Good}(F_i)\quad\land\quad
\forall j<N,\ F_j\subsetneq F_i\Longrightarrow\neg\operatorname{Good}(F_j).
$$

公开端点 `search_registered_inclusion_minimal` 因而给出注册族内的严格包含
极小性。若将来改用跳过未查询点的二分搜索，所需响应单调性及算法正确性需要
另证。当前结果没有把所有 $V$ 的子集纳入极小性量词。

### 4. 可执行例子与五类成本

源码在 $V=\mathbb N$ 上使用五个注册前缀集合
$\operatorname{range}(0),\ldots,\operatorname{range}(4)$，通过 Lean `decide`
验证精确输出：

| 实际 oracle | 返回值 | 实际查询 trace |
|---|---|---|
| $\lvert S\rvert\ge2$ | `some 2` | `[0, 1, 2]` |
| $\lvert S\rvert\ge5$ | `none` | `[0, 1, 2, 3, 4]` |
| $\lvert S\rvert=1$ 或 $\lvert S\rvert=3$ | `some 1` | `[0, 1]` |

第三例在索引 1 为正、索引 2 为负，直接展示扫描正确性不依赖 upward oracle。

| 成本或责任 | 本批已落实的范围 |
|---|---|
| Query | 实际索引 trace、精确长度、合法范围与无重复索引 |
| Sample | oracle 的统计构造与逐次失败预算仍是外部责任 |
| 时间 | 查询数不包含一次 oracle 内部计算的实际成本，未声明总运行时间定理 |
| 内存 | 实际输出保留查询列表，未建立单独的内存成本语义 |
| 输出量 | 返回至多一个注册极小候选及 trace，未枚举全部极小载体 |

这给 C3-01/02 增加了边界清楚的可执行正向结果。真实结构族、含噪响应区间、
物理删除的 frame 条件、全载体枚举及相同任务下的性能对照仍按原任务负责。
详见[C3 源码][c3-source]、[执行合同][c3-contract]和[独立审查][c3-doob-review]。

## 八、回到原 Core 与 C1–C7：本批补到了哪一步

| 原始职责 | 本批实际增加的联系 | 仍保留的责任 |
|---|---|---|
| Core §2、§7、§8.1、§18.1、§27.1 的过程、历史与可实施策略 | 同一有限记忆策略的增广数值行序列、完整前缀及同源无限状态律 | 一般策略的有限记忆可表示性、最小性、规范预测商的共同可测递归仍需自己的条件 |
| Core §8.5 的概率一可行性与 §28 的接口组合 | 自身零未认证占据加物理初态/支持条件，推出同源实际全时安全 | 认证谓词与物理机制匹配、模型有效性及物理安全集的选择仍不能由类型名称保证 |
| Core §10、§30.6 的 QSD/Doob/条件持续区别 | 原源有限窗完整条件路径、正质量行比、Doob 端点倾斜及 TV 反例 | 谱存在、Q-process 极限、长窗渐近和非自治条件路径生成另列 |
| C3-01/02 与 Core §13–16 的载体发现 | 注册嵌套结构上的实际搜索、旧选择身份、精确 query trace 与链内包含极小性 | 全部载体枚举、结构来源、oracle 内部成本、sample 成本和物理干预 frame 未自动完成 |
| C4-02 的真实非自治过程 | 有限记忆控制器到真实数值 $J_n$ 的来源桥，可供其自己的实际过程消费者使用 | 本批没有新增收缩、参考律变化、跟踪误差界或 GOA 极限；变化载体与分岔亦未覆盖 |
| C7 的可否证与复现链 | 实际源 PMF 见证、精确失败条件、执行日志和来源身份 | 本批数学源是明确定义的形式模型；真实系统数据、操作测量、独立校准与经验认证仍需落实 |

原 [C1–C7 任务矩阵][original-ports]要求局部包的验收只关闭其自身范围。
因此，本批既不把 C3 整体标记完成，也不把非自治实现桥写成 C4 的完整跟踪
或尺度身份结论。已有 C1、C2、C5、C6 和 SISC 局部成果继续复用；本批没有
重做这些源码，也没有扩大其统计或经验适用范围。

对于有限记忆风险接口，还须保留“同一策略、同一实际占据、同一 Good”之间的
匹配；物理安全桥输入的 $U_n=0$ 不会免费产生一个统计失败预算。来源的零概率
历史也不自动约束参考过程的可达历史。原注册风险、候选选择、逐行样本和参考
检查预算的条件保持各自的意义。

## 九、证明复用、独审和执行证据

### 1. 直接复用的既有机制

本批复用 `FiniteMemoryPolicy`、`SupportMemoryController`、原 `microLaw` 与
`coverageDeploymentRowLaw`、`SameSourceInfinitePrefix`、`ViabilityPath`、
`SourcePolicyPathBridge`、同源 killed/QSD 接口、`PositiveEigenstructure`、
`FiniteProbabilityRow`、`C3NestedSearch` 及 Mathlib 原生 PMF/路径构造。

新增内容分别消除了“该核真的是这个控制器的核”“这个条件路径真的是原实验的
条件律”“这个可计算输出真的是原最小下标”等来源缺口。独审核对的是实际定义
和推论，不以命名或模块数代替数学连接。

| 审查材料 | 支持的结论 |
|---|---|
| [MEMORY_SOURCE_REVIEW.md][memory-review] | 记忆更新时间、原初态/策略/行序列、完整前缀与实际物理安全条件的静态来源审查 |
| [物理安全见证修订独审][memory-api-review] | 新三源合取、两个否定前提、五个原质量证明逐字保留与公开可投影性，以及公开比较域变化 |
| [FINITE_WINDOW_SOURCE_REVIEW.md][window-review] | 条件前缀、实际正父事件行比、Doob 路径及其范围的独立静态审查；各次修订分别绑定哈希 |
| [C3_AND_DOOB_WITNESS_REVIEW.md][c3-doob-review] | 实际扫描语义、注册极小性，以及三状态源与全九原子比较的静态数学/API 审查 |
| [NATIVE_PROTOCOL_REVIEW.md][native-review] | 新 native adapter 保留身份、公理、编译器所有权、类型复用、固定边和原始档案绑定检查 |

独审 CLEAR 与实际 Lean PASS 是不同证据。它们均不能替代完整生产导入、全量
构建、native 执行、canonical 或合并后树身份验收。

### 2. 已有聚焦通过快照

下表记录最终聚焦通过源码。后续源码变化须由新的执行收据承接，不能继承旧哈希
的 PASS。compile-09 的最终整链通过由协调者实际执行并报告，
[最终聚焦链记录][window-focused]绑定三项精确来源；原始 tool 收据由协调者
归档，不从本表重构。

本报告随后实际读取了 `FOCUS_09_TOOL_OUTPUT.txt` 的完整原始工具文本，SHA-256 为
`730cd4bbce971acb1eca27e121c7f0015351362f697b38dea70c20ad283c6978`。其三条记录与下表
最终哈希、退出码 `0`、精确用时和空日志一致，原始批次状态为 `FINAL_STATE=PASS`。

物理安全见证修订后，本报告又实际读取 `FOCUS_10_TOOL_OUTPUT.txt` 的完整原始
工具文本，SHA-256 为 `81679829b933f34d132c4b949d143952b2ca8acdbbfec4b25123bbacc0bfbef3`。
它绑定下表新见证哈希，退出码 `0`，用时 `3.559897708` 秒，空日志，
批次状态为 `FINAL_STATE=PASS`。修订只改变该见证模块；其他六个 Lean 模块和
五个协议文件的字节哈希已逐一核对与此前冻结版相同。

| 模块 | 已实际通过的源码 SHA-256 | 用时（秒） | 当前版本说明 |
|---|---|---:|---|
| `FiniteMemoryRealization` | `8306c376acbf26db8ae70a5064460c9e423da527a0c89efe4ec18e0e6150191f` | 5.195 | 通过版本冻结 |
| `FiniteMemoryPhysicalSafety` | `7f231017ef32eb607c0187dc659a139101f92ee4ad2ed434f35d4f0687a46cdd` | 3.703 | 通过版本冻结 |
| `FiniteMemorySafetyWitness` | `08060447a92c3b129351b95615ed2e1b3214e12e9ded21c638d0c6554c400c88` | 3.560 | compile-10，公开三源前提独立性端点；五个质量计算仍保留 |
| `C3ExecutableSearch` | `6a70601f35f12edf0eaf881a39aa36fc8d22d5b42111d0c937fa92948df70abc` | 3.729 | 通过版本冻结 |
| `SameSourceFiniteWindow` | `61feecf09bd38d2b5497a7be33d073b1c04cd20a3e45a6840af19dd1670af363` | 4.276 | compile-09 最终来源链通过，日志为空 |
| `FiniteWindowDoob` | `1bcf2d6baaa55e4ea648d19a78dc490a86b525eaaa109464654184d447544081` | 3.986 | compile-09 消费最终 Window 产物，日志为空 |
| `FiniteWindowDoobWitness` | `e37d32b9f5da631392706e60c68d21fcb26491fea1c67614be57afbf6d4b0455` | 4.083 | compile-09 消费最终完整来源链，日志为空 |

原物理安全见证 `fcc011bd9c7571e9ae95e6df606baaf500e2f7767453be6788af5da470b934e7`
曾以 `3.800526625` 秒实际聚焦通过，并属于原 full build01 通过的源指纹；
这份原源码已逐字归档，原收据继续有效地描述其历史快照。新版本增加了明确的
两个否定前提结论，五个旧质量计算的证明正文保持原字节，仅改为私有声明。
新版本的公开数学内容与验证范围变化见[修订说明][memory-api-revision]。

有限窗重构 `4ce233c0138c17faeb458580c34c7d99985fd3cb0ba9fc3b09884a4d7f655691`
在 compile-08 因未启用的 `ℝ≥0∞` 类型记号解析失败；该批次状态是 `FAIL`。
同批两个下游虽分别通过，消费的是此前 Window 缓存，不能用于验收失败的新来源。
仅改为显式 `ENNReal` 后，上表的最终源码与其下游在 compile-09 整链通过。
此前 Window `eba9136fde3cafdcfd6dc23f1fcba9ff8921665d6ed991171f3f80710d8c78d6`
的 compile-05 通过发生在该复用重构之前；此前 Doob
`5175fed66f44c17f58d965a21c06a60542a22a5edd9dfc22ac146e22cdb61367`
的 compile-06 通过日志含后续清理的两项 unreachable-`ring` 警告，原日志仍保留。
有限窗[复用记录][window-reuse]保留这些阶段的来源和诊断范围。早期语法/证明
失败及其原始日志继续保留，不把整个失败批次改称通过。

### 3. 最终集成与发布指标

这一节区分已完成的实际检查点与后续待完成记录，`PENDING` 不表示默认通过。
上一验收基线为 684 个模块、4,272 个注册公开声明、10 个 overlay。
operations PR #366 的已接受 main 为
`d503586107974c56e0773b4ea106b41a7d144b43`。本批 manifest02 已实际冻结为
691 个模块、73 个源码公开声明和 25 条源码提示，完整源指纹为
`de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379`。
源码提示数量不是编译器实际声明总数。实际 native 与已注册 overlay 确认本批
73 个源码公开定理、249 个模块所属定理常量和 114 条注册直接证明边；完整
生产图为 4,345 个公开定理、5,728 条直接证明边、11 个 overlay。

旧 native01 的定点中断是 native 检查失败，不是已经通过的原 full build01
失败，也不是已发现某个数学命题为假。独立诊断在完成原 328,944 个交叉比较后，
定位到两个闭合轨迹质量等式之间的内部比较无进展。旧正式 native 没有完成最终
输出，因此不能声称已经排除原全部类型碰撞。修订后对新的实际公开集合按原
规则完整执行了 311,856 个交叉比较与 2,628 个内部比较，两轮完整输出一致，
没有定义相等碰撞。七模块实际拥有的全部 249 个定理常量，包括 51 个私有
常量和 125 个非源码候选的其他非私有常量，均进入原编译器审计。公开安全
见证的实际证明常量中直接包含全部五个私有质量计算。[完整执行独审][actual-review]
核对其真实模块归属、类型、证明依赖和标准三公理闭包。

本报告已实际读取以下两份原始工具返回，未从后续文字摘要重造收据：

| 工具原档 | 原字节 SHA-256 | 原档明确记录 |
|---|---|---|
| `FULL_BUILD_02_TOOL_OUTPUT.txt` | `d76116f07b2035b460645c322c1616fd4c2fc95bca634c339082ffbb6b9b54f4` | 状态 `PASS`；691 模块；源码 `de7c7e…`；`lake build UEOT` 退出码 `0`，14.23 秒 |
| `NATIVE_02_TOOL_OUTPUT.json` | `487452fb27ac4e16836eb40724a6a8d823637a680f5ec9bea8318988d854bee9` | 状态 `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`；实际导出与固定 verifier 退出码均为 `0`，分别 58.451 / 58.297 秒 |

full build02 原工具返回绑定实际构建日志哈希
`cee7bac0fd4a65b69427bc2c5d7aa0d042b460bf544295020ff0e6a9755a2669`。
native02 返回的两条原日志哈希相同，均为
`69d1e0ab5717a16608296b4396d3340bccedf8248be8ae270ceee1cd5a7d49f4`；
摘要为本批 7 模块、73 公开声明、249 个编译器审计定理常量和 114 条注册直接证明边。
独立审查随后实际读取了两份完整日志，分别解码完整 JSON，并与首轮及最终
native 导出逐对象、逐文件核对；从精确旧注册表与原 renderer 重建 exporter，
从首轮实际证明依赖重建固定 verifier，所有字节一致。

这些实际执行 PASS 针对新源，未复用旧 full build01 或 native01 的状态。
第一组 149 个 Mac 文件共 9,377,318 字节已逐项导入，171 项归档记录经独立
核对。后续 canonical 与十项消费者同步的 17 个原文件另行逐字节导入归档。
原始 `SOURCE_PREFLIGHT` 和 native 待独审/注册状态继续保留；后来的实际
验收通过追加收据表达。canonical 执行时 Git HEAD 为授权基线 `d503586…`，
工作树源码为 manifest02 的 `de7c7e…`；后续不可变提交必须与这一实际源身份
相等，不能把执行时的基线 HEAD 误读为已含这七模块的发布 main。

| 最终门或指标 | 当前记录 |
|---|---|
| 冻结 operations base 与 source 身份 | operations main `d503586…`；manifest02 源 `de7c7e…`，完整源码 691 模块 |
| 七个最终源码哈希及聚焦通过 | PASS；原始源码、每轮日志、缓存资格与失败均在 [actual-execution][actual-history] |
| 最终源码模块总数、新公开声明数、完整注册声明数 | 691 模块（680 maintained / 11 adapted）；本批 73 公开定理，累计 4,345 公开定理、5,728 直接边、11 层 |
| 当前源实际全量 `lake build` 与前后身份核对 | PASS，14.23 秒；完整身份链独审 CLEAR |
| 当前源首次 native：公理闭包、编译器 ownership、raw-type 比较、直接证明边 | PASS，58.451 秒；独审 CLEAR；旧 native01 中断 FAIL 保留 |
| 当前源第二次 native：固定边与 census 重放、完整 JSON 等同性 | PASS，58.297 秒；完整原始日志与 JSON 独立核对 CLEAR |
| 原始源码/执行档案及 adapter/manifest 字节绑定 | 149 原文件、171 归档记录逐字节核对；受审协议字节保持 |
| 新 overlay 注册与消费者 | 仅新增两项注册元数据，原 native 与 raw overlay 字节保留；独立注册审查 81 项 CLEAR，六消费者/DAG 审查 237 项 CLEAR |
| 必需本地回归 | 54 项 reuse、完整 30 项 FKRG、89 项 parser 全通过，无跳过；parser 保留原实际运行，未无谓重跑 |
| 完整 clone 门 | 对当前全部 691 模块实际扫描，与原 68 行完整表相等；算法与原表未变 |
| canonical 门 | 原 `audit_umc_local.py --full` 实际 PASS，60.702 秒；92 研究模块、672 源码公开候选、1,404 全部原生定理常量（176 private / 556 其他非私有）均只含标准三公理；执行独审 CLEAR |
| 最终 PR、合并树、resulting-main 及双端核对 | Git 对象与发布为后续独立门；不可变候选及最终 main 身份记录在承载本批的 PR、#146 和发布交接中 |

已准备的[native 协议][native-protocol]使用旧 immutable driver 的受检查适配，
保留原身份与证明检查；[准备记录][native-preparation]是当时仅做源码语法和字面
替换锚点检查的历史记录，不能替代之后发生的 freeze、build 或 native 执行。
当前协议字节仍与原受审版一致。本表引用的实际执行由各自原始收据支持，
未把本地科学集成验收提前等同于 GitHub 发布完成。

## 十、后续可直接消费的责任

有限记忆路线可以把实际增广核序列交给已有非自治过程接口，但必须继续使用
同一控制器与来源，并另行证明所消费的收缩或参考过程条件。需要固定 killed
矩阵时，还应核对数值齐次性或真正的相位扩张，不能仅凭支持固定就套用。

有限窗路线下一步可为零质量状态明确选择 total fallback，证明独立构造的
时间变化条件核生成完整过滤路径；随后再按具体谱条件研究长窗与 Doob 的
渐近联系。当前正质量行接口和 TV 反例已给出这些命题不能省略的边界。

C3 路线下一步应选择有真实来源的注册结构族，落实一次 oracle 的成本与语义，
并将不确定响应、样本预算和物理 frame 条件接入实际程序。精确线性查询证书
提供了可复用的执行部分，尚需真实测量或领域 oracle 才能进入现实发现链。

这些后续任务延续 Core 的过程、表示、持续、实现与算法主线。每一步都应说明
它从哪些已有数据构造哪个对象、减少哪项额外假设、得到什么新推论，以及在什么
明确条件下失效。

[original-binding]: ORIGINAL_SOURCE_BINDING.json
[original-top]: ../../../../../../../UEOT_v3_top.pdf
[original-core]: ../../../../../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md
[original-ports]: ../../../../../../../mathematics/source/roadmaps/CORE_V3_OPEN_PORT_MATRIX.md
[original-closure]: ../../../../../../../mathematics/source/roadmaps/CORE_V3_POST_CORE_SCIENTIFIC_CLOSURE.md
[original-roadmap]: ../../../../../../../mathematics/source/roadmaps/THEORY_COMPLETION_ROADMAP_V2.md
[memory-source]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryRealization.lean
[physical-source]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryPhysicalSafety.lean
[safety-witness]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemorySafetyWitness.lean
[window-source]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SameSourceFiniteWindow.lean
[doob-source]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteWindowDoob.lean
[doob-witness]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteWindowDoobWitness.lean
[c3-source]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/C3ExecutableSearch.lean
[memory-contract]: memory-realization/CONTRACT.md
[memory-api-revision]: memory-realization/API_REVISION_02.md
[memory-api-review]: independent/memory-api-revision-02/REVIEW.md
[memory-review]: independent/MEMORY_SOURCE_REVIEW.md
[window-endpoints]: finite-window/IMPLEMENTED_ENDPOINTS.md
[window-reuse]: finite-window/PUBLIC_REUSE_REFACTOR.md
[window-focused]: finite-window/FOCUSED_CHAIN_PASS.md
[window-review]: independent/FINITE_WINDOW_SOURCE_REVIEW.md
[c3-contract]: c3-search/CONTRACT.md
[c3-doob-review]: independent/C3_AND_DOOB_WITNESS_REVIEW.md
[native-protocol]: native_protocol/README.md
[native-review]: independent/NATIVE_PROTOCOL_REVIEW.md
[native-preparation]: native_protocol/SOURCE_PREPARATION_CHECK.json
[actual-review]: independent/ACTUAL_EXECUTION_REVIEW.md
[actual-history]: actual-execution/README.md
[consumer-review]: independent/registration-consumer-review/CONSUMER_DAG_REVIEW.md
[canonical-review]: independent/CANONICAL_UMC_EXECUTION_REVIEW.md
