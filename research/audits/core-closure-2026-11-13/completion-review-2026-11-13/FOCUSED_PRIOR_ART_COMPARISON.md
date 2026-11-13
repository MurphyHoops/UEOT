# 五项贡献的精确先行比较与停止扩张决定

日期：2026-11-13（Asia/Shanghai）。审查源：main `ab4862db08bae9333f422f7bdbba490f8c1ce0df`。
范围：原 B 审计 D4 的有限后继；不重写原首审，不增加 Core 公理、生产 Lean 或新的普适主张。

## 1. 本次究竟补足什么

#461 已完成有限来源归因和贡献边界，并未把所有内容宣传为首创。本次进一步完成原建议中的 **3—5 项主贡献与最接近先行成果逐对象、逐假设、逐结论比较**：三个数学单位、两个哲学／机制单位。

主审独立检查了关键源类型、两类型实际请求行、正权重证明及主要一手文献。A、B、C 为真正分离的原生智能体，沿用原三个任务身份，先出独立记录，再交叉质询。它们不是三个外部人类审稿人。完整细节、精确源位置和阅读限度分别见 [A 报告](reviews/A/A_TASK_COMPLETION_AND_PHILOSOPHICAL_COMPARISON.md)、[B 报告](reviews/B/B_TASK_COMPLETION_AND_MATHEMATICAL_COMPARISON.md)、[C 报告](reviews/C/C_COMPLETION_LEDGER_AND_NEXT_STAGE_REVIEW.md)及 [交叉裁决](CROSS_REVIEW_AND_ADJUDICATION.md)。

**结论：有限 D4 目标已经补足；已有原理的归属更明确，具体实现贡献的范围也更明确。没有发现因此必须重开 Core 数学或增加 Lean 的理由。**

| 单位 | 最接近的具体先行成果 | 可以成立的比较 | 不据此声称 |
|---|---|---|---|
| M1 预测充分表示 | Shalizi–Crutchfield 的因果状态、预测充分与最小性 | 在给定条件未来核的明确交叠类，预测分布向量的纤维对应因果状态；可测因子序连接到适当有限熵下的复杂度比较 | 一般核族都是某个平稳过程；首次发现最小预测状态 |
| M2 精确控制商 | Givan–Dean–Greig 的有限 MDP 随机双模拟 | 在共享动作、状态奖励的交叠类，商的定义相互对应；Bellman 和最优策略保持同源 | 任意观察等价都足以控制；原文完整动作类型与 UEOT 逐字相同 |
| M3 再生源与增长分类 | Nesterov–Protasov 非负 product-family 定理；早期受控分枝文献 | 当前均值行族是精确实例；另给达到最优处的正势和完整策略人口桥 | JSR 等式自动给最优底数上的全时常数界；所有历史策略和身体身份都被矩阵投影保留 |
| P4 同源维持、执行与继承 | 组织约束闭包、跨代功能、生物调节理论 | 逐项区分约束相互维持、跨代连续性、调节条件与 UEOT 的具体程序账本 | 首次统一维持与繁殖；付费恢复已解释全部生命组织起源 |
| P5 反例反向限制解释 | 既有功能与组织论证及科学论证的量词责任 | 当前具体反例确实限制哲学解释，并落实到正式合同和采用关系 | “用反例收窄主张”是一种新哲学方法；增长能推出伦理正当性 |

这里的“五项”是五个研究单位，不是五项已证世界首创。比较得出成熟数学实例、工程组织贡献或尚无独立增益，都是有效结论。

## 2. M1：预测充分表示的明确交叠类

### 2.1 当前 UEOT 真正接收与给出什么

`PredictionDependent.lean` 接收历史空间 \(H\)、可数任务集 \(I\)、各自可测输出 \(Y_i\)、给定可测响应核 \(K_i\) 与历史测度。若竞争表示 \(s:H\to Z\) 有可测解码核 \(L_i\)，且逐 \(i\) 满足
\[
K_i(h)=L_i(s(h))\quad\text{a.e.},
\]
则在共同满测集上
\[
C(h)=(K_i(h))_{i\in I}=d(s(h)),\qquad d(z)=(L_i(z))_{i\in I}.
\]

可数性使零集可合并；乘积可测结构使 \(d\) 可测。`canonical_ae_minimal` 处理的是这个因子序。它没有先证明任意现实任务都存在适当条件概率核、所有因果机制可识别，或任意不可数协议都有共同零集。[S1]

### 2.2 与先行因果状态如何对应

Shalizi–Crutchfield 的相关原理见作者版 §V Theorem 1／Corollary 1、Lemma 7、Theorems 2／3。[L1] 在有限字母平稳过程的可测历史空间，先给定同一全未来条件概率核，令 \(I\) 是正整数、\(K_L\) 是长度 \(L\) 未来块的条件分布。其所有有限前缀分布决定全未来分布，所以 \(C\) 的纤维正是预测等价类。

这个对应的数学责任可以直接检查：两个概率测度若在所有有限前缀柱集一致，就在其生成的未来 σ 代数一致。任意 UEOT 核族则未必满足这类前缀相容，因此上述结论只在所选交叠类成立。

对给定历史的可测表示 \(R=s(H)\)，并给定相应条件概率核后，有限输出下条件熵差等于相应条件分布的平均 KL 散度。零差等价于该长度的分布因子化；对可数长度取共同满测集，得到上述 \(C=d(R)\)。若还具适当离散状态和有限熵，才进一步得到状态熵的最小性。**一般可测因子序与任意连续变量的 Shannon 熵最小并不等价。**这些步骤是本次在交叠类中的独立推导，不是声称 L1 原文带有 UEOT 的 Lean 类型。

### 2.3 贡献裁定

最小充分预测状态已有明确先行。UEOT 的贡献候选是依赖输出空间、共同 a.e. 因子接口及其后继消费者的明确组织和形式化。未发现必须新增证明的缺口；也不应为主张首创而重复证明标准充分性。

## 3. M2：精确控制商与随机双模拟

### 3.1 全部必要字段

`ExactControlQuotient` 要求有限状态满射 \(f:X\twoheadrightarrow Y\)，同纤维动作由共同族 \(\bar A(f(x))\) 给定，同一严格折扣 \(0<\beta<1\)，奖励闭合与每个动作的转移推前闭合：
\[
r_X(x,a)=r_Y(f(x),a),\qquad
\sum_{x':f(x')=y}P_X(x,a,x')=P_Y(f(x),a,y).
\]
各状态的动作集合有限且非空，微宏转移行均非负且归一，奖励在所用有限模型上有界。这些是输入义务，不是只凭两状态看起来相同便能推出的结果。[S2]

### 3.2 双向对应及结论

Givan–Dean–Greig 的相关定义和 Theorems 5／7 使用有限 MDP、共享动作和状态奖励；本次准确交叠取其非负状态奖励设置。UEOT 还允许相应有界的动作依赖奖励及依赖动作族，不能把两者完整签名说成同一。[L2]

若 \(E\) 是该交叠类的随机双模拟，令 \(Y=X/E\)。奖励相同和逐动作各块概率相同恰保证宏观奖励、转移与代表无关，得到 UEOT 精确商。反向令 \(xEx'\iff f(x)=f(x')\)，精确商字段给相同奖励和块概率；满射使两个商空间只差重命名。这是定义级的实际双向映射。

对任意宏观值函数 \(v\)，有限分块求和给
\[
T_X(v\circ f)=(T_Yv)\circ f.
\]
折扣压缩的固定点唯一性继而给 \(V_X^\ast=V_Y^\ast\circ f\)，同一动作的 Q 值相等使最优宏观策略可提升。这对应 `expect_pullback`、`bellman_pullback`、`optimalValue_pullback` 及策略端点。[S2]

UEOT 另显式对全声明的随机历史 `CausalPolicy` 比较。其数学桥是标准 Bellman 不等式经策略混合、条件期望和折扣尾项消失；这不是因为策略类型写得更明确就变成全新控制原理。两个观察永远相同而动作奖励相反的自环状态，已足以反驳“预测等价自动保持最优控制”。

### 3.3 贡献裁定

精确控制商属于成熟理论的明确实例／接口表达。UEOT 可以主张真实的动作、资源和共同误差消费者衔接，不能主张首次发现商保持最优值。本次没有完成近似 MDP 全部先行成果的独立检索，不把本段精确对应外推为近似界的全球优先权结论。

## 4. M3：再生源、product family 与最优增长

### 4.1 真实动作表先于矩阵优化

在当前严格正 `ProbabilityValid` 域，
\[
0<\delta<s<1,\quad b,\gamma>0,\quad b+\gamma<1,\quad0<q<1.
\]
令 \(k_c=s+b,\ k_b=s-\delta+b+\gamma,\ u=(1-q,q)\)。从 `realizedMean_eq` 及实际拒绝规则得到：[S3–S5]

| 类型 | care | bloom | stop |
|---|---|---|---|
| 健康 H | \(k_cu\) | \(k_bu\) | \(0\) |
| 损坏 D | \(k_cu\) | \((0,1)\) | \(0\) |

损坏 bloom 的修复、操作及输出预留请求 cap 为 7，超过交易上限 6，所以在实际支付前拒绝并留存原体；这一行不能删除或换成繁殖行。行和可大于 1，故这是人口均值矩阵，不是普通随机转移矩阵。

每个类型独立选一行构成有限非负 product family \(\mathcal M\)。Pliska 1976 与 Rothblum–Whittle 1982 的原刊摘要已足以说明受控分枝及此类增长优化有强先行；本次仍未取得其完整定理条件，不能声称全部 UEOT 策略与机制已被它们逐项包含。[L3,L4]

### 4.2 全文可核的通用先行定理

本次新增核读 Nesterov–Protasov 2011／2012 修订作者稿 §2—§4，正式发表年份为 2013。对其 (3.3) 非负 product family，Theorem 4 给最大谱半径、联合谱半径与共同正势优化下确界的对应。[L5]

按该稿 (3.2) 的 \(F^{\mathsf T}=(F_j)_j\)、\(A=BF\) 及 Theorem 1 的实际行替换证明，取 \(E=\mathbb R^2\)、正锥、\(B=I\)，让 \(F\) 的两行分别在上表有限集合内独立选择，就直接得到当前族。稿中附近文字使用 column 用语；这里以公式和证明确定方向，避免误将右势随意转置。若人口采用列向量 \(z\)，演化是 \(M^{\mathsf T}z\)，相应势仍为 \(r^{\mathsf T}z\)。

当前矩阵含零行及拒绝行，适用的是非负扩展 Theorem 4，不能仅援引严格正的 Theorem 2。本段给出了模型条件的实际代入，不只是相似性判断。

### 4.3 当前特殊类的具体证书

置
\[
k_\ast=\max(k_c,k_b),\quad
\mu=(1-q)k_\ast+qk_c,\quad
R=\max(1,\mu)=\max(1,k_c,(1-q)k_b+qk_c).
\]
当前源给出严格正 \(r\)：
\[
r=
\begin{cases}
(k_\ast,k_c),&\mu\ge1,\\
\left(\dfrac{qk_\ast}{1-(1-q)k_\ast},1\right),&\mu<1.
\end{cases}
\]
第二支分母为正，因为 \(\mu<1\)。

逐行直接乘法验证 \(Mr\le Rr\) 对所有允许 \(M\) 成立，并有按类型固定选行的 \(M_\ast r=Rr\)。第一支选择健康最大行、损坏 care；第二支选择健康最大行、损坏拒绝行。于是最大谱半径与 JSR 都为上述 \(R\)。这个显式公式是特定参数类的计算，不是一个新发现的一般谱半径原理。

这还不是高层策略定理的全部证明。令人口势
\[
W_t=\sum_{v\in N_t}r_{\mathrm{kind}(v)}.
\]
固定真实人口和整个请求词，实际输出的期望按成员相加，再用逐行界。按归一化的联合历史策略混合仍有
\[
\mathbb E[W_{t+1}\mid\text{当前源与历史}]\le RW_t.
\]
不要求请求相互独立；源噪声和可观察类型须满足实际模型规定。迭代得到 \(\mathbb E W_n\le R^nW_0\)，所选允许策略达等号。由于 \(r_{\min},r_{\max}>0\)，非空初态给
\[
\mathbb E_K|N_n|\le (W_0/r_{\min})R^n,\qquad
\mathbb E_{K_\ast}|N_n|\ge (W_0/r_{\max})R^n.
\]
任意较小正底数不可能对达到者给全时共同上界。这正是最小统一底数与双边界的具体人口桥，不是把每条高层历史策略的全部路径律等同于一串确定矩阵。[S4–S6]

### 4.4 不能省略的反例：增长指数不自动给精确底数的全时界

取单矩阵 product family
\[
J=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
J^n=\begin{pmatrix}1&n\\0&1\end{pmatrix}.
\]
其 JSR 与谱半径都是 1，但 \((1,0)J^n(1,1)^{\mathsf T}=n+1\)，不存在有限 \(C\) 给所有 \(n\) 上界 \(C\,1^n\)。同时不存在严格正 \(r\) 满足 \(Jr\le r\)，正势最优值只是下确界。

因此，不能因一般 Theorem 4 给 JSR 等式，便删除当前源中“最优值处达到的正势”和真实人口证明。这个反例反驳的是过度的先行包含推断，**不是当前严格正 UEOT 源的反例**；当前源确有上节的显式正势。

### 4.5 留下哪些可评审贡献

一般非负矩阵增长、分枝控制、正向量方法与条件期望法已有先行。UEOT 可提交的具体贡献是：

- 实际代码、损伤、付费恢复和拒绝语义到计数行的源内证明；
- 当前严格参数类最优基的精确公式与两个内置程序的充要达到区域；
- 全允许联合历史策略、观察权限和实际人口之间的接口；
- 同一受损创始体的修复、内部执行及程序继承条件的贯通。

内部程序的解释仍需 `ProgramPopulation`、可达保持和正概率分支条件；一般 canonical 状态本身不够。[S5,S6] 这些贡献已在源码中存在。本次没有创建新定理，全球优先权和比既有实现更强的外部解释能力仍未证明。

## 5. P4：同源维持与继承，不等同于一般组织闭包

Montévil–Mossio 的组织闭包需要具体约束、过程、时间尺度和相互依赖；它不是一条泛称“存在反馈”的定义。[L6] UEOT 的程序、恢复器、账本和人口记录可以被进一步分析为某个组织实例，但现有源中的字段不自动满足其全部条件。

**外部供给本身不是反驳。** 先行闭包理论允许外部边界和独立约束；因此不能仅因 UEOT 每轮外供资源便判其维持机制无效。真正需检查的是声称属于组织内部的那些约束是否得到所要求的依赖支持。

Saborido–Mossio–Moreno 2011 已直接研究跨代功能、组织自维持与因果／材料连续性。[L7] 继承程序和 parent-ID 可以是 UEOT 的具体模拟记账，却不自动给出这套生物连续性，更不支持“首次统一维持和繁殖”。Bich 等人的调节条件又要求明确的内生形成、动力关系与功能整合；读取内部程序并不能直接替代这些条件。[L8]

**裁定：** 当前同源机制具有具体构造与形式化组织价值。一般生命自生产、无前提自创生和所有调节起源不属于已证范围。没有必要为了“全覆盖”把这些生物概念再塞入冻结 Core。

## 6. P5：反例如何实质限制哲学解释

Mossio–Saborido–Moreno 2009 的功能理论讨论相互维持、功能归属及其规范维度，当前 UEOT 哲学已经引用它；不能把本次更细比较说成首次发现缺失先行文献。[L9] 功能是否有利于某个组织的持续，与某种行为是否道德正当，是不同论证问题。UEOT 把增长目标与伦理理由分开，不等于推翻先行功能理论，也不等于 Lean 已证明某套伦理学。

当前 UEOT 的可核增量是 **把具体数学边界落实为解释限制和正式采用责任**：非空失败结构要有任务与干预前提；共同二维表示要有真正的因子化；最优期望增长不等于逐路径生存、数值同一或规范进步。#461 将这些区别接入宪章、canonical claims、术语、方法与继承入口。[S7]

这种量词与证据分层并非全新哲学方法。本项目的学术价值只能由具体论证、反例和冲突处理是否改善理解来承担；三份 AI 意见或正式发布都不能替代这一责任。

## 7. 主审最终裁决与后续停止条件

1. D1、D2 已采用；D3 定向执行已完成；D4 的五项有限比较现已达到原建议要求的精度。
2. 维持 **A：在当前明确范围内合理闭合**。不据此声称所有哲学立场等价于 Lean、所有现实系统都被解释，或全球原创性已经证明。
3. 不新增 Core 公理、大包装定理、定理计数或重复 Lean。既有定义和证明留在其真实条件下。
4. 先行论文全文尚未取得的地方继续标明限度。精确比较已可由其他合法全文和独立推导完成，不必为消除一切未知而无限检索。
5. 后续有具体审稿异议、实际消费者失败、反例或证据身份冲突时，按现行规则重开精确问题；不因旧 OPEN 或无差额重复阅读重开。
6. 下一阶段转向 [独立系统的合同检验与公平比较](NEXT_STAGE_EXECUTION_PROMPT.zh-CN.md)。该文件仍是任务书，不是已运行实验的报告。

## 8. 文献、源码与阅读限度

### 一手文献

- [L1] Shalizi, C. R.; Crutchfield, J. P. (2001), *Computational Mechanics: Pattern and Prediction, Structure and Simplicity*. [作者全文](https://csc.ucdavis.edu/~cmg/papers/cmppss.pdf)。相关 §V 与条件测度讨论；不是把下载等同于全部逐页审读。
- [L2] Givan, R.; Dean, T.; Greig, M. (2003), *Equivalence Notions and Model Minimization in Markov Decision Processes*. [作者全文](https://cs.brown.edu/people/tdean/publications/archive/GivanetalAIJ-03.pdf)，模型、双模拟、Theorems 5／7 和相应附录证明；[DOI](https://doi.org/10.1016/S0004-3702(02)00376-4)。
- [L3] Pliska, S. R. (1976), *Optimization of Multitype Branching Processes*. [原刊摘要](https://pubsonline.informs.org/doi/abs/10.1287/mnsc.23.2.117)。本轮仍仅摘要。
- [L4] Rothblum, U. G.; Whittle, P. (1982), *Growth Optimality for Branching Markov Decision Chains*. [原刊摘要](https://pubsonline.informs.org/doi/10.1287/moor.7.4.582)。本轮仍仅摘要。
- [L5] Nesterov, Y.; Protasov, V. Y. (2013), *Optimizing the Spectral Radius*, SIAM J. Matrix Anal. Appl. 34(3), 999–1013。[正式书目](https://epubs.siam.org/doi/10.1137/110850967)；实际核读 [2011／2012 修订作者稿](https://optimization-online.org/wp-content/uploads/2011/12/3272.pdf) §2—§4 的相关定义、定理和证明。正式刊年与作者稿年份分别记录。
- [L6] Montévil, M.; Mossio, M. (2015), *Biological organisation as closure of constraints*. [作者全文](https://montevil.org/publications/articles/2015-mm-organisation-closure-constraints/)，主要 §§3–5、定义1–4及§6开头。
- [L7] Saborido, C.; Mossio, M.; Moreno, A. (2011), *Biological Organization and Cross-Generation Functions*. [作者研究组存档](https://www.ias-research.net/wp-content/uploads/2019/02/Saborido_41241903.pdf)，§§3.2–3.3及结论；部分 PDF OCR 截断，未据此声称逐页无损读取。
- [L8] Bich, L.; Mossio, M.; Ruiz-Mirazo, K.; Moreno, A. (2016), *Biological regulation: controlling the system from within*. [作者稿](https://leonardobich.wordpress.com/wp-content/uploads/2015/08/bich-mossio-ruiz-mirazo-moreno-2015-biological_regulation-controlling-the-system-from-within-biology-philosophy.pdf)，主要§§4–5及调节条件。
- [L9] Mossio, M.; Saborido, C.; Moreno, A. (2009), *An Organizational Account of Biological Functions*. [作者研究组存档](https://www.ias-research.net/wp-content/uploads/2019/02/Mossio_25592036.pdf)，§§4.1–5.2、6.1–6.4。

本文为原创比较、独立推导和简要释义。第三方论文仅链接及标注读取范围，不随本包重新分发全文。

### 固定源码

以下相对路径均以 [审查提交](https://github.com/MurphyHoops/UEOT/tree/ab4862db08bae9333f422f7bdbba490f8c1ce0df) 为准；B 报告和来源清单记录实际 Git blob：

- S1：`formalization/ueot-core/UEOT/V3/PredictionDependent.lean` 及 `PredictionAE.lean`。
- S2：`formalization/ueot-core/UEOT/V3/FiniteDiscountedExactQuotient.lean` 及 `FiniteDiscountedControl.lean`。
- S3：`formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeSource.lean`。
- S4：同目录 `CoreRegenerativeGrowthClassification.lean`。
- S5：同目录 `CoreRegenerativeControlPopulation.lean` 及 `CoreRegenerativeGrowthPopulation.lean`。
- S6：同目录 `CoreRegenerativeGrowthAttainment.lean`。
- S7：`council/resolutions/20261113-core-claim-scope-reconciliation.md`、四治理文件及 `philosophy/UEOT_PHILOSOPHY.md`。

证据等级：本轮直接源码、事件和独立推导为 E1-S；所列一手文献在实际读取范围内为 E1-L。历史 D3 执行继续以其原时间和源身份接受，本轮未再运行 Lean。首创、全域适用和外部人类接受保留未确立状态。
