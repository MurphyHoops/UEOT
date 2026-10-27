# UEOT 当前数学进展、条件稳定性与后续问题

审查日期：2026-10-28（Asia/Shanghai）。本报告接续 [2026-10-26 数学闭环审计][audit]，核对当前生产端点并解释本轮条件稳定性增量。它保存数学结论、使用前提和可继续推进的问题；正式执行与发布身份由文末证据绑定。

## 1. 当前完成到什么程度

**冻结 v3.0 的 106 项源证明合同已经全部完成；最新主线也已从存在性接口推进到实际同源路径、可执行控制器、有限样本风险证书和一个实际信念商。强统一理论仍有明确的识别、可实施性及世界适用边界。** 当前方案有可验证的数学主线，下一步应减少具体消费者所需的外给假设，而不是继续增加阶段编号。

本次读取的真实 Mac 主工作树是：

`/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/total-kernel-memory-20261023`

数学审查基准为 `44e1b7d25272b5ce09acb71ef7b36f9a1c4c001d`。它是 [PR #378](https://github.com/MurphyHoops/UEOT/pull/378) 合并点，继承 #377 的数学源码；#378 只退休完成任务的治理例外。当前增量的正式集成基准已经推进到 [PR #379](https://github.com/MurphyHoops/UEOT/pull/379) 的 `7708a3a1289b1a009c269d81edceef06a4c347dc`：该 PR 只授权本研究分支更新六条既有证据消费者路径，数学源码与 `44e1b7d` 相同。

| 计数或状态 | 已核实内容 | 正确解释 |
|---|---|---|
| 冻结源覆盖 | 106/106；Partial 0；Pending 0 | 指定原文、假设及接口的证明合同已完成 |
| 压缩账本 | 11 generated / 89 adapters / 6 boundaries；未决 0 | 11 项有注册重推路线，89 项继续承担适配前提，6 项保留边界 |
| counted generators | 4 | 在注册推导系统内非冗余；不是全部数学的绝对最小公理组 |
| 当前审查基线 | 701 个 bundled Lean 模块，含 690 个维护模块和 11 个改编模块 | 模块数是源码规模；不能直接换算成理论完成度 |
| P0–P12 | 程序状态 CLOSED；`next_stage = PROGRAM_COMPLETE` | 冻结阶段合同已关闭，P12 的最终裁决仍是 `PARTIAL / EXPLICIT BOUNDARY` |
| 强统一与科学适用 | 尚未建立无条件强闭环；现实源适用仍需独立证据 | 不随模块、定理或阶段数量自动获得 |

以上分别来自 [当前 Core 状态][current]、[冻结覆盖账本][coverage]、[压缩账本][compression]、[理论完成状态][status]和[当前知识索引][knowledge]。这些单位不能混用：源命题、Lean 模块、公共定理和编译器生成常量都不是“世界真理”的等长份额。因此可以给冻结合同的完成率 100%，不能诚实地给“整个 UEOT 理论完成了 80%”之类的总百分比。

## 2. 怎样更新 10 月 7 日附件和 10 月 26 日审计

10 月 7 日的核心规范、开放端口矩阵、后核心方案和路线图提供历史定义与研究合同。读取时应保留原假设、否定结论和完成标准，再用当前源码及后继 PR 更新实施状态。早期的 PLANNED、旧模块数或单执行者日程不能覆盖已经合并的成果。[冻结原文][core-source]、[开放端口矩阵][ports]、[后核心方案][post-core]与[路线图][roadmap-source]仍应保留原版本身份。

10 月 26 日审计 [PR #369](https://github.com/MurphyHoops/UEOT/pull/369) 的问题分析仍有价值，但其中“第 12 层未发布”“R1/R2 待实施”“具体 R3b 待接入”等状态已有后继：

| 后继 | 已增加的实质 | 对旧审计的更新 |
|---|---|---|
| [#371](https://github.com/MurphyHoops/UEOT/pull/371) | R0：全域条件窗生成核、原源条件路径等式、实际记忆过程与生存律 | 第 12 层已发布；不能继续按未发布候选处理 |
| [#373](https://github.com/MurphyHoops/UEOT/pull/373) | R1：有限表真正综合出可执行 Program，并证明它自己的部署过程安全 | “存在 winning selector”已推进为明确算法和返回程序 |
| [#375](https://github.com/MurphyHoops/UEOT/pull/375) | R2：固定样本 exact-support no-go、三值 noisy oracle、同源选后联合风险与实际模型采样 | 噪声选择和实际风险已有具体端点，精确支持仍单独声明 |
| [#377](https://github.com/MurphyHoops/UEOT/pull/377) | R3b：实际 C1 后验核通过二元可观察坐标下降，附唯一性和正反例 | 一个具体可测像上的信念商已经实现 |
| [#378](https://github.com/MurphyHoops/UEOT/pull/378) | 完成 R3b 例外退休 | 治理收尾，没有增加数学命题 |

#371 同时恢复了旧候选引用的 39 个输入引用、38 个不同文件。缺失的历史 registration receipt 没有被伪造为“找回”：后继明确记录新做的恢复核验，`registration_reexecuted=false`、`historical_registration_receipt_recovered=false`。这个历史边界应继续保留。[R0 结果报告][r0-report]

本报告作为后继更新，不改写原审计当时真实的失败记录。数学书、哲学书也各有出版范围；不能仅修改某处旧模块数，就把整部书宣称为最新源码的重新审定版。

## 3. 已完成的四条主线及其保留前提

### 3.1 R0：条件路径已经来自原过程，初态倾斜没有遗漏

令 \(Q\) 为固定策略下的 killed 安全核，\(\eta\) 为原初态限制在安全集合后的质量行，保留其可能小于 1 的总质量。设

\[
g_r=Q^r\mathbf 1,\qquad Z_T=\eta g_T>0.
\]

有限窗条件初态和正分母转移行是

\[
\eta_T(i)=\frac{\eta_i g_T(i)}{Z_T},
\qquad
K^{(T)}_t(i,j)
=\frac{Q_{ij}g_{T-t-1}(j)}{g_{T-t}(i)}
\quad (0\le t<T).
\]

[`TotalFiniteWindow.lean`][total-window] 的 `windowInitial` 独立构造倾斜初态，`windowPathLaw` 从初态与核生成路径。分母为零的行使用全域 PMF fallback；`generated_ambient_eq_actual` 证明生成的完整原状态前缀律等于**原 action/state 实验条件化后再投影**的状态律，`generated_ambient_fallback_independent` 证明实际条件路径不受这些 fallback 影响。它覆盖零质量前缀，也保留原初态不安全部分的影响。

这不是把目标条件分布作为构造输入。初态倾斜、零行和原源连接已经有证明，不能再次列为缺口。[`SameSourceFiniteWindow.lean`][same-window] 也明确给出实际条件初态公式；[`FiniteWindowDoob.lean`][doob] 区分有限窗条件律与带正特征结构的 Doob 路径律，见证给出两者 TV 为 \(1/4\) 的实际模型。

[`HomogeneousMemorySurvival.lean`][memory-survival] 则从同一个固定数值源 \(P\) 与控制器记忆构造

\[
\bar P((x,m),(z,m'))
=\sum_a \sigma(m,a)P(x,a,z)
\,\mathbf 1_{\{m'=U(m,a,q(z))\}}.
\]

它证明实际增广轨迹就是这个齐次链，有限 killed 质量等于实际有限生存概率，其极限等于实际所有时刻生存概率。**极限可以为零**。这里需要数值源固定；仅固定支持不能推出同一个齐次数值核。增广状态 \((X,M)\) 是 Markov，也不意味着原状态 \(X\) 自身 Markov。

仍保留的边界是有限窗正存活质量、明确的固定源及策略、实际安全事件，以及额外谱假设下才可能进一步研究的 Q-process 极限。已有有限窗等式没有宣布正概率永生或任意非自治源的谱结论。

### 3.2 R1：返回了真实程序，结构表的来源仍是前提

[`ExecutableSupportController.lean`][support] 的 `synthesize` 返回 `Option (Program X Y A)`。Program 有可执行的 `initialMemory`、`action`、`update` 三个字段。输入为有限状态和动作枚举、可计算观测、可判定支持关系 \(R\)、认证表 \(C\)、初始支持 \(I\)、覆盖全部动作的有序表和 fallback。

算法维护与观测相容的支持集合，复用截止深度 \(2^{|X|}-1\) 的有限 viability 检查，用 `List.find?` 选第一个合格动作。证明追踪**这个返回程序自己的**实际历史，得到零未认证占据；在初态安全和认证动作安全闭合前提下，得到所有时刻物理安全。`synthesize_some_killed_mass_one` 把数值生存质量接回 R0。[R1 结果报告][r1-report]

仍需给出

\[
I=\operatorname{supp}(p_0),\qquad
R(x,a,z)\iff z\in\operatorname{supp}(P_n(x,a)),
\qquad
C(x,a)\iff\operatorname{Certified}_n(x,a).
\]

这些不是程序从有限数据自动发现的事实。概率可以随时间变化，但支持与认证须符合固定表。现有递归算法终止、确实可运行，也有实际 12 步控制器见证；它可能重复搜索，未证明记忆全局最小或高效 memoization 复杂度。

### 3.3 R2：有限样本给风险证书，不会凭空给精确支持

[`FixedSampleSupportNoGo.lean`][support-no-go] 证明：固定正样本数 \(N\)，允许任意随机化且跨参数固定的 exact-zero 认证规则；若它在 \(p=0\) 时认证概率为 \(\rho\)，则在正 Bernoulli 源 \(p>0\) 的误认证概率至少为

\[
\rho(1-p)^N.
\]

因此要求对任意 \(p>0\) 误认证率至多 \(\alpha\) 的规则，在 \(p=0\) 的认证能力至多 \(\alpha\)。这不是“某条边这次没出现”的单例，而是规则级统计边界。它没有否定已知最小正概率、外给精确支持或不同停止时实验。

[`NoisyFiniteRiskOracle.lean`][noisy] 计算经验行、纤维差异、参考核、有限历史概率和风险预算。PASS / FAIL / AMBIGUOUS 由有理数区间判断；顺序扫描只在 FAIL 后继续，AMBIGUOUS 会停止。对固定样本表的共同 `CalibrationGood`，它从原源行校准推出所选控制器的有限时域风险，没有另把选后拟合正确性作为输入。

在独立固定产品训练、相同未知源部署的明确实验中，若共同校准失败预算为 \(B\)，接受风险上限为 \(\beta\)，已有结论是

\[
\Pr(\text{训练接受且部署失败})
\le \min\{1,B+(1-B)\beta\}.
\]

这是联合概率。得到“给定接受后的失败概率”还需要处理接受概率，不能直接复用同一上界。

三状态模型分别有未知转移概率 \(1/4\) 与 \(1/8\)，两步未到达目标风险为 \(9/16\)、\(49/64\)，后者超过 \(7/10\)。实际保存的一次每行 4096 样本模型实验中，起点行有 1018 次成功，选择细观测候选，计算预算为 \(13939757/20971520<7/10\)。所有原始响应保留，没有为接受而重采样。其意义是代码和模型证书确实运行；OS 随机源与理想独立模型的匹配、现实外部源匹配仍是明确假设。[R2 结果报告][r2-report]

### 3.4 R3b：构造出具体预测商，也证明何时不能使用它

[`ObservableBeliefQuotient.lean`][belief] 从非空标准 Borel 状态空间、实际 Markov 源和二元确定观测 \(q:X\to\mathrm{Bool}\) 出发，用

\[
T(b)=b(q=\mathrm{true})\in[0,1]
\]

作为信念坐标。有两个观测类的代表点时，坐标像严格等于闭区间，二点 Dirac 混合给可测 section。假设同观测微观状态的下一步 true 概率在每个动作下相同，可证明所有有限动作—观测测试通过该坐标因子化。

真正下降的是已有的 `c1BeliefTransitionKernel`，不是任意另外声明的核。定理 `closed_tests_iff_existsUnique_quotient` 给出源测试闭合与唯一可测 Markov 商的等价。后验关于当前观测的 Dirac 性只在观测几乎处处成立；零概率观测没有被强迫满足错误的点态等式。[R3b 结果报告][r3-report]

正例含真实随机隐藏噪声，某个未来 probe 的概率直接等于 \(T(b)\)，因此“所有有限未来测试相同”与“坐标相同”在该例中等价。负例使隐藏位显露，排除任何此坐标上的核因子化。奖励与安全另有独立读出：可观察奖励和可观察安全类可以因子化，隐藏奖励和隐藏安全概率在预测等价信念上仍可能不同。

这个成果支持具体的预测充分性和可测商构造。它没有给任意可测空间、任意后验坐标像、任意目标的控制充分性，也没有给任意实数后验的运行算法或全局最小记忆。

## 4. 核心方案本身是否合理

数学上，方案合理的部分在于它把“对象—观察—行动—存活—目的”拆成可证明的桥，并保留反例。下列区分是其可信度的基础，不能为了统一叙事而删去。[冻结核心规范][core-source]、[开放端口矩阵][ports]、[10 月 26 日审计 §§4、11][audit]

| 核心概念 | 数学上已获得或可接受的解释 | 仍需独立论证的主张 |
|---|---|---|
| 对象与预测商 | 相对于指定未来实验、协议和共同历史律的预测等价、商与充分性 | 这个商就是唯一世界本体，或可恢复真实祖先 |
| 对象生成与循环 | 给定故障、修复和部件语义后的对象证书；有限失败超图的明确循环关系 | 任意几何循环自动生成对象，或已有证书推出无条件自生成 |
| GOD | 独立评价桥给定后，目标的 argmax 对应或相应控制问题 | 从对象状态唯一推出目的；任意 GOD 都是一个梯度 |
| GOA | 具体假设下的占据极限、不变律、QSD、Q-process 或其他分别定义的长期对象 | 唯一不变律即混合；命名“吸引子”即证明路径吸引 |
| 二元驱动 | 共同二维潜变量假设推出联合响应秩至多 2，并可被稳定秩三证据拒绝 | 一个标量目标推出共同二维机制；秩至多 2 唯一识别物理 \(\Pi/\Phi\) |
| 目的机制 | 明确机制观察、评价读出及 faithfulness 下的排序识别 | 同一个对象或同一动力学无信息地决定唯一目的 |

特别是，所有环境必须在**同一预算点**共享同一个二维坐标，才能得到联合响应矩阵的秩约束。每个环境各自存在一个二维表示不够；通过必要秩检验也不等于机制识别。标量分解的规范分类与二维潜在 GL(2) 自由度已经分别有源码，不能混成“二元驱动已经得到唯一验证”。[`DualDriveGaugeCompleteness.lean`][scalar-gauge]、[`DualDriveLinearGauge.lean`][linear-gauge]、[C5 共同二维检验][c5]

数学证明的责任是说明“这些源、实验和桥满足前提时，结论必然成立”，也可以证明更强主张不可能从这些信息得出。哲学解释可以据此修正关于对象、目的和世界的论证，但解释本身不自动成为 Lean 定理；现实过程是否满足这些源与干预假设，也需要单独的适用证据。这项区分允许数学研究持续推进，无需把外部实证虚报为已完成，也无需每次推进都先解决全部世界接口。

## 5. 本次推进：把路径误差传给同一事件下的条件预测

本轮落实旧审计 §10.4 的明确消费者问题，并把其中非最优的 \(2\varepsilon/s\) 充分界强化为尖锐界。新增 [`FiniteConditionalStability.lean`][conditional] 和[三状态见证][conditional-witness]。

### 5.1 真正的条件分布与尖锐界

令 \(P,Q\) 是同一有限字母表上的概率律，\(S\) 是**同一个**事件，

\[
p=P(S)>0,\qquad q=Q(S)>0,\qquad d_{\rm TV}(P,Q)\le\varepsilon.
\]

使用 Mathlib 的实际 `PMF.filter` 构造 \(P_S=P(\cdot\mid S)\)、\(Q_S=Q(\cdot\mid S)\)，而不是把一个任意“条件律”作为输入。`mass_mul_conditioned_atom` 证明其原子质量恰好满足原质量除以事件质量。主要定理 `conditional_tv_le_max_mass` 给出

\[
\boxed{\displaystyle
d_{\rm TV}(P_S,Q_S)
\le \min\left\{1,\frac{\varepsilon}{\max(p,q)}\right\}.}
\]

分母是两者中的较大值，也不要求 \(p=q\)。独立验证可取 \(p\ge q\)：对 \(A\subseteq S\)，

\[
p\left(\frac{P(A)}p-\frac{Q(A)}q\right)
=P(A)-\frac pq Q(A)
\le P(A)-Q(A)\le\varepsilon.
\]

把 \(A\) 换成 \(S\setminus A\) 给反向差值，因此得到绝对值界。Lean 实现采用有限共同质量与 TV 的恒等式证明同一结论。

### 5.2 只知道参考事件质量也能认证

若只有可计算的参考质量 \(q=Q(S)>\varepsilon\)，无条件 TV 同时给

\[
P(S)\ge q-\varepsilon>0,
\qquad
d_{\rm TV}(P_S,Q_S)
\le \min\left\{1,\frac{\varepsilon}{q}\right\}.
\]

`reference_mass_conditional_certificate` 把真实事件正性与误差界一起返回。这里 \(q-\varepsilon\) 用于证明正性；最终误差分母可以保留 \(q\)，无需退到 \(q-\varepsilon\)。若 \(q\le\varepsilon\)，这份证据不足以保证真实事件正质量，不应构造一个虚假的零事件条件律。

### 5.3 直接消费现有 R2，而非要求新的拟合假设

`causal_path_conditional_certificate` 复用既有实际因果路径 TV 定理：相同初态、逐步共同历史行误差 \(\varepsilon_t\in[0,1]\) 给

\[
E_T=1-\prod_{t<T}(1-\varepsilon_t).
\]

当参考路径的事件质量超过 \(E_T\) 时，条件路径 TV 至多 \(E_T/Q(S)\)，并自动证明实际事件有正概率。

更直接的 `noisy_reference_conditional_certificate` 固定一份训练记录和同一个实际 R1 Program，在现有共同 `CalibrationGood` 下调用 R2 的 `calibrated_reference_row`，再调用 `same_policy_projected_path_error`。设

\[
e=\min\{1,u+\widehat{\mathrm{defect}}\},
\qquad
E_T=1-(1-e)^T.
\]

实际律是原受控微观路径投影到共同观测 action/state 记录的律；参考律来自该样本的经验代表核，运行同一个 Program。只要其 \(Q(S)>E_T\)，新端点就返回实际正性和条件 TV 证书。调用者不需要再提供无条件路径拟合或条件拟合结论。

这项结果把已有噪声校准送到有限条件窗的误差分析，减少了一条独立外给误差假设。它**不会**使“看见幸存路径”自动成为原动作集合中可实施的控制策略。

### 5.4 实际 readout 范围

`conditioned_readout_tv_le_reference_mass` 允许在两边条件律上应用**同一个可测函数**，因此前缀、终态或其他相同记录读出继承误差界。它不要求目标空间有限。

R2 直接端点的事件 \(S\) 定义在共同的观测 action/state 历史字母表上。若要把它解释成微观物理存活，需要明确证明微观存活事件正是该观测事件的拉回。隐藏危险若不能由观测记录判定，就不能把“观测存活”直接写成“物理存活”。不同事件的失配也需要单独计入。

该定理固定训练记录后进行条件化。若改为训练与部署的联合实验，条件化存活会按每份记录的存活概率重新加权训练分布；不能保留原训练边缘后直接平均各记录的条件证书。本轮没有声称这个额外联合条件化定理。

### 5.5 三状态正反例把放大因素钉死

三状态是两个事件内状态 \(a,b\) 和事件外状态 \(c\)，\(S=\{a,b\}\)，每个分布及其条件律都由实际 PMF 构造。

| 见证 | 原分布 \(P,Q\)，按 \(a,b,c\) 排列 | 原 TV / 事件质量 | 条件 TV |
|---|---|---|---|
| 稀有事件族，\(0<r\le1\) | \(P=(r,0,1-r)\)，\(Q=(0,r,1-r)\) | \(r\)；两边事件质量均为 \(r\) | \(1\) |
| 未饱和正例 | \(P=(1/4,1/4,1/2)\)，\(Q=(3/8,1/8,1/2)\) | \(1/8\)；两边事件质量均为 \(1/2\) | \(1/4\) |

`rare_event_sharpness` 与 `arbitrarily_small_unconditional_error` 证明：即使固定三状态、固定同一事件，原 TV 可以任意小，条件 TV 仍等于 1。因此没有正事件质量控制就不存在统一的小误差保证。

`positive_reference_certificate_is_sharp` 证明 \(q=1/2>\varepsilon=1/8\) 时，条件 TV 恰为 \(\varepsilon/q=1/4\)。尖锐性不只发生在上界已经饱和为 1 的例子。这些是数学见证，不是外部世界实验。

## 6. 接下来优先做三个有明确消费者的问题

### 6.1 第一优先：条件核能否由允许动作实际实现

现有 R0 已经构造正确的条件核；尚需区分它是否能由原系统允许的行动产生。这直接对应冻结规范 §22.2 的路径重加权与反馈可实现性边界。

有限动作集合下，先证明一个小而完整的判据。固定状态 \(x\)，动作行 \(P(x,a,\cdot)\) 和目标行 \(R(x,\cdot)\)，有

\[
\exists \sigma_x\in\mathrm{PMF}(A),\quad
R(x,\cdot)=\sum_a\sigma_x(a)P(x,a,\cdot)
\quad\Longleftrightarrow\quad
R(x,\cdot)\in
\operatorname{conv}\{P(x,a,\cdot):a\in A\}.
\]

用 PMF 的实数质量向量表述凸包，复用有限 PMF 行构造、`PMF.bind`/`PMF.map` 和 Mathlib 已有有限凸组合 API 即可。随后将行等式接到已有 [源—策略—路径桥][policy-bridge]，证明在相同初态、可观察控制信息及策略可用性前提下的路径实现。逐状态凸包成员资格只直接给全状态反馈；部分观测时，同一可区分信息类还必须有相容的共同动作混合，不能跳过这一约束。

现有[有限窗 Doob 见证][doob-witness]即可提供非实现性消费者：只有一个动作时，从两个安全状态的一步安全质量分别为 \(3/4\)、\(1/4\)，而条件核的下一步安全质量为 1。允许动作的任意混合都不改变该行，因此对目标行的 TV 差至少分别为 \(1/4\)、\(3/4\)。另加两个确定性动作、目标公平混合的正例，可显示随机化何时必要。

还须保留初态限制：即使每个目标转移行都可实现，原固定初态也不自动变成条件倾斜初态 \(\eta_T\)。转移行动不能事后改变已经给定的初态分布。首版应明确“给定同一目标初态的转移实现”，或把允许的初态准备机制单独建模。

这项推进会给出“何时可实施、何时有严格不可实现误差”的判据，比再次证明条件路径公式更有增量。

### 6.2 第二优先：C5 非退化分解的逆向分类与操作锚

已有[标量规范完整分类][scalar-gauge]和[二维 GL(2) 不变性][linear-gauge]不能被重复包装成新成果。真正新的问题是：所有非退化线性分解是否恰好属于同一个规范轨道？

若联合响应矩阵有两个秩 2 分解

\[
J=AB^\mathsf T=\widetilde A\widetilde B^\mathsf T,
\]

且四个因子都具有两列满列秩，目标是证明存在唯一 \(R\in GL(2)\) 满足

\[
\widetilde A=AR,\qquad
\widetilde B=B R^{-\mathsf T}.
\]

证明路线是先由 \(J\) 确定相同的二维列空间，构造唯一换基，再由注入性得到另一因子的逆转置关系。这补全既有“一种换轴保持响应”的正向命题，精确描述线性、非退化情形中的全部等价性。秩退化时不能沿用唯一性结论；局部矩阵分类也不能直接升级成全局非线性潜变量存在。

接着只在有消费者时引入**独立定义的操作锚**：例如选择性资源/信息干预分别确定两条轴、方向约束排除符号反转、量纲校准固定尺度。要证明这些锚如何把 GL(2) 缩小，而非把“\(\Pi\) 已知”“\(\Phi\) 已知”直接作为期望结论的同义输入。秩检验继续承担可否定共同二维假设的角色，轴的物理命名由独立操作信息支持。[C5 检验][c5]、[联合二维拒绝][joint2d]

### 6.3 C4 只随具体消费者推进

若实际消费者需要时变源的条件窗，就从同一 \(P_t\) 推导时变生存函数与实际前缀律；若需要给定边缘的合法身份历史，就证明对应耦合可行条件，并识别原过程的真实推前。[C4 集合值桥][c4]和[旧审计 §11.1][audit]已清楚区分“每点有合法后继”“边缘可以耦合”和“该耦合就是实际历史”。

现有 M-TC 误差传播应继续复用。新增内容应是从实际过程得到它消费的局部误差和一致性条件。没有消费者时，不先做无限维全泛化，也不把相同求和公式换一个阶段名字再证明一遍。

## 7. 当前判断与执行证据

本轮数学选择合理：R2 已有无条件路径误差，R0 已有真实有限窗条件律，两者之间缺少条件稳定性消费者；新定理恰好连接它们，且正反例确定了必要的事件质量条件和最优放大系数。下一条最值得继续的是行动凸包可实施性，因为它能判断“正确的条件模型”能否成为原系统可执行的控制。

独立语义审查已对最终两个源文件给出 CLEAR：

| 文件 | SHA-256 |
|---|---|
| `FiniteConditionalStability.lean` | `ee47efdc109f9670c77f6bb04595c66f56e8475144bb75f2f190e0cdfd730e05` |
| `FiniteConditionalStabilityWitness.lean` | `434556fd1a9433bd3a52741520cba4743cc4747995caa44024869ef9da8e5829` |

最终见证已完整重读，实际运行已绑定上述最终源码。正式源码指纹为 `0e17dd5ef3c4a9e3eaea47c8c0b7e83f6ef097915bed6092ca81e3e6c032abe0`。本轮实际验证结果如下；数字分别标明其统计对象，不相互替代。

| 实际检查 | 结果与范围 |
|---|---|
| 最终 focused 编译 | exit 0；5.549 秒，8,837 jobs（包括缓存）；见证导入主模块 |
| 官方完整 `lake build UEOT` | exit 0；703 个生产模块，9,409 jobs（包括缓存），11.175 秒 |
| 本层编译后导出 / 固定验证器回放 | 两次 exit 0；53.028 / 52.820 秒；完整 JSON 与两个 239,111-byte 日志一致 |
| 本层 native 范围 | 63 个所属证明常量 = 11 个公共源码定理 + 34 个 private + 18 个其他公共生成常量；只有 Lean 标准公理 |
| 类型与证明边 | 49,093 次跨登记类型比较、55 次本层内部比较，零碰撞；19 条实际登记证明边 |
| 当前复用图 | 16 层，4,474 个公共源码定理节点、5,926 条直接边；47 个既有复用资产字节未改 |
| 消费者与治理 | reuse 74 / parser 89 / FKRG 30 / governance 38 全通过；12 个预期拒绝全部拒绝；历史 clone 68 行精确保持 |
| 全局源码图 | 703 个模块均从公共入口可达，无环、无缺失 import |
| UMC 全域本地审计 | 104 个研究模块，801 个公共源码候选；1,879 个编译归属常量均只依赖标准公理；此入口统计另见导入归属比较 |

[逐条定理复用独审](independent/TYPED_REUSE_REVIEW.json) 已核全部 11 个新声明和 15 个最近旧端点的实际编译类型。原子质量恒等式属于接口整理，reference/readout/路径端点属于派生结果或消费者；11 个公共源码定理不等于 11 条彼此独立的新数学原理。零词法候选和零类型碰撞也不被解释成一般数学独立性。

完整记录见 [本地验收](RELEASE_ACCEPTANCE.json)、[真实完整构建](actual-execution/full-build-01/FULL_BUILD_RECEIPT.json)、[native 与回放](actual-execution/native-01/STATUS.json)、[消费者运行](actual-execution/consumer-checks-01/COMMAND_RESULTS.json)、[UMC 全域审计](actual-execution/consumer-checks-01/UMC_FULL_RECEIPT.json)、[独立语义审查](independent/LEAN_SEMANTIC_REVIEW.json)及[实际收据独审](independent/ACTUAL_INTEGRATION_REVIEW.json)。最初五轮 focused 编译失败的真实源码与日志继续保存；第三轮因覆盖传输被拒绝，实际重复运行了第二轮源码，不把它改写成新版本运行。

Core 三个 GitHub workflow 保持用户要求的 `disabled_manually`。上述通过均来自实际本地检查；没有云端 CI 通过的主张。这个内容绑定的验收记录在 Git 提交前生成，精确候选 Git 对象预检、最终 HEAD 独审、PR 合并及合并后源码/环境身份与真实本地构建记录由对应发布 PR 和 resulting-main 收据单独绑定，避免让一个提交声称包含自己的哈希。

UMC 历史 1,808 与本轮 1,879 不应直接相减后宣称本轮有 71 个新定理。新公开源命题确为 11，所属 native 常量确为 63；额外的 8 个计数差在生成常量归属范围，已用旧根原 import 列表和当前根分别做只读重放，原始名单与差集保存在 [导入归属比较](actual-execution/import-ownership/UMC_IMPORT_CENSUS_COMPARISON.json)。旧环境的逐名查询进一步确认，这 8 个名字本来全部存在，先前归属在 ScientificClosure 等 UMC 范围之外，当前因导入次序而首先归属到既有 UMC 模块；两边均仅依赖标准公理。见[八个生成定理的旧归属实查](actual-execution/import-ownership/GENERATED_OWNER_EXPLANATION.json)。这个统计现象不增加新的源码数学命题。

[audit]: ../../../../../../../mathematics/review/MATHEMATICAL_CLOSURE_AUDIT_2026-10-26.md
[current]: ../../../../../../../core/status/CURRENT.md
[coverage]: ../../../../V3_COVERAGE_STATUS.md
[compression]: ../../../COMPRESSION_LEDGER.yaml
[status]: ../../THEORY_COMPLETION_STATUS.json
[knowledge]: ../../knowledge/README.md
[core-source]: ../../../../../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md
[ports]: ../../../../../../../mathematics/source/roadmaps/CORE_V3_OPEN_PORT_MATRIX.md
[post-core]: ../../../../../../../mathematics/source/roadmaps/CORE_V3_POST_CORE_SCIENTIFIC_CLOSURE.md
[roadmap-source]: ../../../../../../../mathematics/source/roadmaps/THEORY_COMPLETION_ROADMAP_V2.md
[r0-report]: ../total_kernel_memory_v1/RESULTS_AND_BOUNDARIES.md
[r1-report]: ../executable_support_v1/RESULTS_AND_BOUNDARIES.md
[r2-report]: ../noisy_oracle_v1/RESULTS_AND_BOUNDARIES.md
[r3-report]: ../observable_belief_v1/RESULTS_AND_BOUNDARIES.md
[total-window]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/TotalFiniteWindow.lean
[same-window]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SameSourceFiniteWindow.lean
[doob]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteWindowDoob.lean
[memory-survival]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/HomogeneousMemorySurvival.lean
[support]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ExecutableSupportController.lean
[support-no-go]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FixedSampleSupportNoGo.lean
[noisy]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/NoisyFiniteRiskOracle.lean
[belief]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ObservableBeliefQuotient.lean
[scalar-gauge]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DualDriveGaugeCompleteness.lean
[linear-gauge]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DualDriveLinearGauge.lean
[c5]: ../../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C5DualDriveTest.lean
[conditional]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteConditionalStability.lean
[conditional-witness]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteConditionalStabilityWitness.lean
[policy-bridge]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SourcePolicyPathBridge.lean
[doob-witness]: ../../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteWindowDoobWitness.lean
[joint2d]: ../../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCJoint2DRejection.lean
[c4]: ../../../../../UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C4SetValuedFBT.lean
