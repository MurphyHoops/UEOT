# UEOT 数学形式化闭环：现场审查、数学缺口与执行方案

审查日期：2026-10-26（Asia/Shanghai）。主干基准：[`41c4b27ef8d993c797b2414311f0934eeb4cb561`](https://github.com/MurphyHoops/UEOT/commit/41c4b27ef8d993c797b2414311f0934eeb4cb561)。本报告是独立研究审查与后续实施合同，不改写冻结 Core、数学书正文、已有证明裁决或历史运行收据。

**核心目标：以数学约束、推导和排除关于世界的主张，逼近“这个世界究竟允许什么、必然什么、不能识别什么”。** 本轮交付是核实现状、辨别真正缺口、给出可执行数学路线并保存接续入口；不是宣布已经完成一切自然理论，也不把未来实证阶段加入本轮文档的验收条件。

## 1. 结论先行

1. **冻结 v3 的源命题形式化已完成：106/106。** 这是对指定原文、假设和形式化接口的完成，不是 106 条无条件自然定律。四个 counted generators、11 generated / 89 adapters / 6 boundaries 保持原义。
2. **同源数学主线已很强。** 现在已有共同源上的预测/控制连接、实际路径与后验、部署占据风险、选择后联合风险、无限策略存在、有限支持记忆、真实记忆过程、killed 生存律与有限窗反例。不能退回“这些桥都还没有”的旧计划。
3. **强统一闭环仍未建立。** 已关闭 P0–P12 的最终裁决包含 `PARTIAL / EXPLICIT BOUNDARY`；C1–C7 的包关闭不消除其开放端口；统一任务 #302 仍 OPEN。实际科学支持仍为 `UNVERIFIED`。
4. **第 12 层是有证明证据的未发布候选。** 它有 694 模块的真实完整构建和匹配源码；但注册清单引用的 39 份归档文件在候选目录中全部缺失。最小相关检查运行 4 项，3 通过，1 因这些文件缺失失败。不能直接把候选写成 main 成果。
5. **下一步应优先消除具体外给输入。** 先完成第 12 层证据发布；数学主线优先把可执行可行性判定变成真正可执行的控制器综合，再把真实有噪声 oracle 的三值结果接到同一个控制/风险实验。规范预测商、机制辨识和目的来源按实际阻塞接入，不能只是继续增加“闭环”命名的总装定理。

最终可争取的严谨结论应写成：

$$
\text{明确的源与实验条件}
\Longrightarrow
\text{可实现表示、可执行策略、可计算证书及有条件保证},
$$

并同时给出：哪些条件可由同一源导出，哪些可从数据检验，哪些只能成为不可辨识边界。`BOUNDARY_CLOSED` 也是数学成果；不能为了得到一个肯定答案而删除 no-go。

## 2. 本轮究竟检查了什么

### 2.1 证据层级与核验范围

审查采用四种不同证据，不能互相替代：

| 层级 | 本轮核验 | 能支持什么 | 不能支持什么 |
|---|---|---|---|
| Git / GitHub | 当前 main、开放 PR、#146/#302、#363/#365/#367/#368、实际 workflow jobs | 是否合并、源码身份、实际执行了哪些检查 | 定理语义自动正确 |
| 源码与数学 | 冻结 ledger、主文、关键总装端点、正负例、最新生产链与候选 | 定理的输入、结论、作用域和接续缺口 | 对 691 模块每行重新独立证明 |
| 可复现运行证据 | 既有 full-build 源文件及环境哈希、原日志、候选 native/UMC 收据 | 既有成功构建与当前受审字节的一致性 | “2026-10-26 又重跑了全量 Lean” |
| 本轮实际检查 | 候选 4 项 consumer 检查；文档链接、来源和 diff 检查 | 当前归档缺失等具体问题 | 新的 Lean 定理或外部科学验证 |

本轮做的是**关键证明链的深入语义审查与全源身份核验**，不声称重新人工证明所有库定理；也没有以无 `sorry` 的文本扫描替代 Lean 内核。

### 2.2 当前基准与近期推进

| 事项 | 核验结果 | 科学意义 |
|---|---|---|
| main | `41c4b27ef8d993c797b2414311f0934eeb4cb561` | #368 合并点；本报告的基准 |
| #363 | 已合并；`a9109004959975b3d2c5a303741e117f1cd8cb9c` | 同源长期律、无限策略、逐探针 SISC |
| #365 | 已合并；`50a91fb9c81e0f5e698ce2cc02ec1a44c9583b04` | 支持齐次下有限记忆与可执行判定 |
| #367 | 已合并；`d794847707c6f66b03901814d584bd432789aa0a` | 真实记忆路径、有限窗条件化、可执行 C3 顺序搜索 |
| #368 | 已合并；只改 `COMPRESSION_RESEARCH_TRACKS.json` | 为后续证据消费者更新提供治理授权，本身不增加定理 |
| 开放 PR | 本轮初始查询为 0 | 没有可被误认为第 12 层已发布的开放 PR |
| #146 | 顶部仍以 #367 的 SHA 作为 current main | 恢复索引落后一个治理合并；不等于数学源码落后 |
| #302 | OPEN | 强统一数学任务没有关闭 |

主干源 census 为 **691 = 根 `UEOT.lean` 1 + `UEOT/` 下 690**；其中 680 维护、11 改编的分类沿用该次审计。UMC 子树有 92 个生产模块。DAG 的 126,169 行、4,606 个 theorem/lemma tokens 是词法元数据，不是自然规律数量或数学闭环百分比。

### 2.3 完整构建证据与当前 CI

主干的既有收据：

`formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1/actual-execution/full-build-02/FULL_BUILD_RECEIPT.json`。

其真实 `lake build UEOT` 记录为 exit 0、14.23 秒，日志末行为 `Build completed successfully (9397 jobs).` 本轮逐一核对其 **691 个源文件**的 SHA/字节数，集合完全相等、0 mismatch；`lean-toolchain`、`lakefile.lean`、`lake-manifest.json` 及原构建日志哈希匹配。#368 相比 #367 只修改治理 registry，证明源码及上述环境文件 Git 对象相同。

因此可以说“**本轮复核了既有完整构建的来源匹配，可以复用这份证据**”。不应说“本轮重新运行全量 Lean 成功”。候选的更完整环境核验见第 7 节。

main 的实际 [Core Guard run 39823612191](https://github.com/MurphyHoops/UEOT/actions/runs/39823612191)：`classify=success`、`governance=success`、`proof=skipped`。`UEOT Core Lean` 是手动 workflow；Guard proof 也只在手动 dispatch 时运行。**绿色治理状态与官方全量证明运行是两个事实。** 文档修改没有理由重跑数千个 Lean jobs。

### 2.4 需要纠正阅读方式的旧文字

- `V3_COVERAGE_STATUS.md` 仍有“canonical source bytes pending synchronization”的历史文字。当前冻结文件已经存在，183,440 bytes，SHA-256 为 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`，与 ledger 一致。这不是当前未完成任务，也不需要重开 106 的证明裁决。
- `SCIENTIFIC_CLOSURE_STATUS.json` 同时保留 `LOCAL_COMPLETE_REVIEW_PENDING` 和 `CANONICAL_MAIN_PR_296_MERGED...` 等历史阶段字段。应连同真实 Git/后继来源解释，不能仅取一个旧字段否定已合并工作。
- 数学书与 `LEAN_API_SCOPE.md` 的 666 模块范围是相应出版版本的范围；后续 #363/#365/#367 已到 691。出版版本不能自动冒充最新源码目录，也不应在本轮审查中静默重写 MD 而不维护其 TeX/PDF。
- 旧 P10 审计所列参数化后验缺口，已有后继 C1 定理解决常用条件下的联合可测更新；旧“无限策略、有限记忆、有限窗尚待实现”等计划也有相应生产后继。每次启动从实际端点核起。

## 3. “数学逼出世界真理”的精确含义

### 3.1 数学证明、模型识别与世界解释

记理论假设为 $A$，结论为 $C$。形式证明提供

$$
A\vdash C,
\qquad\text{在所用逻辑的可靠解释下，}\quad
\forall M\;(M\models A\Rightarrow M\models C).
$$

实际世界过程 $W$、观测 $O$、可实施实验族 $\mathcal E$ 与数学模型 $M$ 的关系是另一项义务：例如

$$
\sup_{e\in\mathcal E}
d_{\rm TV}\!\left(\mathcal L_W(O\mid\operatorname{do}e),
\mathcal L_M(O\mid\operatorname{do}e)\right)\le\varepsilon.
$$

必须明确这里是有限注册实验、所有允许实验，还是仅一段数据上的估计；不能把有限检验写成上述全称式已经成立。数学可以推导误差如何传到结论，却不能仅从逻辑推导出未经声明的现实源身份。

### 3.2 可识别真理与不可辨识边界

对声明的模型类 $\mathcal M$，定义实验等价

$$
M\sim_{\mathcal E}M'
\iff
\forall e\in\mathcal E,
\ \mathcal L_M(O\mid\operatorname{do}e)
=\mathcal L_{M'}(O\mid\operatorname{do}e).
$$

目标属性 $\tau:\mathcal M\to T$ 可由该实验族识别的必要且充分的集合论条件，是它在每个等价类上恒定：

$$
M\sim_{\mathcal E}M'\Rightarrow\tau(M)=\tau(M').
$$

必要性：相同实验响应给任何只消费这些响应的方法相同输入；不同正确答案无法都得到。充分性：可在响应像上定义唯一属性值。**该充分性不额外保证可测、可计算、稳定或有限样本有效**，这些正是后续应补的数学。

这给核心目标一个可执行判据：每项研究要么扩大能识别的 $\tau$，要么减少所需 $\mathcal E$/前提，要么证明更强主张在当前信息下不可能。仅给结构字段换名不增加上述能力。

### 3.3 允许保留的三种终点

- **条件构造闭环**：给定可检查条件，所有对象、算法与证书来自同一源，结论由实际执行路径产生。
- **边界闭环**：给出同实验不可分而目标不同的反例，明确额外信息需求；不再循环尝试被反例否定的无条件目标。
- **现实适用闭环**：另有真实源匹配、预先声明的预测及外部反驳渠道。它是长期目标，本轮提供接口和失败条件，不虚报已完成实证。

所谓 FULL 必须相对于明确列出的模型类、实验族、时间域与目标；“所有可能世界的一切真理”没有在本仓库得到一个可验证的完成合同。

## 4. 现有数学资产与不能越过的边界

### 4.1 冻结 Core 与四个生成器

| 资产 | 数学内容 | 保留前提 |
|---|---|---|
| M-QD | 纤维相容使映射下降到商；$f(x)=f(x')\Rightarrow g(x)=g(x')$ 给 $g=\bar g\circ f$ | 纤维相容、需要时的可测/连续因子化 |
| M-TC | 误差递推 $e_{n+1}\le a_ne_n+b_n$ 的传输与复合 | 非负常数、每条边对同一误差量有效 |
| M-PE | 给定正特征结构的归一化及相关转移构造 | 正性、特征方程、归一化非零；不自动提供任意源的谱结构 |
| M-OI | 在适当极限条件下消失的残差产生不变/相容关系 | 收敛、连续性或实际使用的极限假设 |

四者非冗余的既有结论是**相对于注册推导 DAG**，不能升级成绝对逻辑独立性或全部数学的最小公理系。

106 中的 P-CTL-03 是连续时间 HJB verification：给有界 $C^2$ 候选 $V$、$\rho>0$、HJB 不等式及可测最大化 selector、可行受控扩散和局部化/可积性条件，证明所有 admissible control 的值被 $V$ 支配且 selector 达到它。由于所固定 Mathlib 没有完整受控 SDE Itô 栈，`ItoRun` 仍提供过程特定的有限时域 Itô 期望输出。Lean 完成从该输出到无限时域最优性的论证；**没有因此完成所有 SDE 的构造与 Itô 定理栈**。

### 4.2 P0–P12 的闭合含义

| 包 | 已完成合同 | 仍不能自动推出 |
|---|---|---|
| P0 | 对象、身份、GOD/GOA、目的、尺度的类型区分 | 名称相同即实体相同 |
| P1 | 目的合同、排序与数值表示 | 从无信息物理状态唯一产生目的 |
| P2 | 同一对象的 agency/控制/生存接口 | 最优一定安全，安全一定最优 |
| P3–P4 | 有限数据与变化候选类识别 | 无间隔、任意漂移、任意采样下一致识别 |
| P5 | 同一故障/修复过程的平均稳态 | 每条路径最终永不出错 |
| P6 | 期望资源预算 | 每条随机路径永不破产 |
| P7 | 从携带所需程序信息的种子组装修复组织 | 从不可区分物理部分凭空生成不同正确程序 |
| P8 | 谱系与 Price/Perron 条件桥 | 由当前预测状态识别真实祖先 |
| P9 | 已给性质的尺度运输 | 已推导全部物理 RG 或 Wilson 流相容性 |
| P10 | 一般核/信念的接口及后续 C1 实现 | 任意可测空间都存在良好规范后验 |
| P11 | 随机分析条件接口 | 任意真实过程满足 Itô/Dynkin/Girsanov 前提 |
| P12 | 条件有限状态生命周期终端 | 无条件自生成、自修复、普遍目的或完整自然理论 |

例如 P12 给出的平均非法占据与资源结论具有形式

$$
\limsup_{N\to\infty}\frac1N\sum_{n<N}D_n
\le\frac\lambda\kappa,
\quad
\sum_{n<N}\mathbb E[c(Z_n)]\le R_0+Ns,
$$

其中 $\kappa>0$、$\lambda$ 来自同一故障—修复系统，资源条件包括
$c_vV_0/\kappa\le R_0$ 与 $c_m+c_v\lambda/\kappa\le s$。这不是逐路径零故障或逐路径预算定理。其“有限”主要限定状态、动作及程序表示；不表示已证明必然有限寿命。

### 4.3 C1–C7 的真实开放面

| 端口 | 现在已有 | 真正后继责任 |
|---|---|---|
| C1 | 标准 Borel 潜态及相应可数生成条件下，参数化、联合可测的后验/信念递归 | 规范预测商上的递归降落、零事件版本相容、具体非紧长期问题；不重造已完成的常用 belief kernel |
| C2 | 三值区间、固定注册校准、共同 Good 与选择后风险；另有特定 predictable OLS 源条件链 | 对正在使用的主动/相关/停止采样建立确切源匹配；不笼统说所有适应采样都未研究 |
| C3 | 同一通道校准；真实 exact-oracle 顺序程序、query trace、首个正项及族内极小性 | oracle 自身计算/样本成本、有噪声三值返回、实际删除/frame；未知 gap 不能免费消除 |
| C4 | 形成—binding—运输的条件相容及误差传播 | 时变真实源、表示选择与误差的同源关系；结构接近不等于祖先身份 |
| C5 | 共同二维驱动的必要秩约束与稳定拒绝 | 从秩相容到可识别机制所需的干预、规范固定与非退化条件 |
| C6 | 在 observation faithfulness 下识别目的排序类；无忠实性 no-go | 从可干预机制证明足够忠实性，区分行为偏好、维持功能和规范目的 |
| C7 | 失败分型、注册/保留协议与可复算方法 | 真实外部源和全部尝试保留；旧记录缺失不能被新 runner 追溯修补 |

## 5. 已成立的同源数学主线

本节给出统一记号，说明现有定理为何有实质价值，以及拼接时必须核对哪些量。为清楚起见使用有限状态 $X$、有限动作 $A$、观察 $q:X\to Y$；实际接口中有些允许任意 $Y$，有些概率部分仍需其可测结构。

### 5.1 共同实验先于各个结构

固定 $p_0$、核序列 $P_n(x,a,x')$、按观察历史选择的策略 $\pi_n(a\mid h_n)$。真正路径质量是

$$
\Pr(x_{0:T},a_{0:T-1})
=p_0(x_0)\prod_{n<T}
\pi_n(a_n\mid h_n)P_n(x_n,a_n,x_{n+1}).
$$

观察历史、后验 $b_n$、支持 $B_n$、占据 $U_n$、失败事件和参考比较都应从这个实验派生。给出两个同名的 `source` 字段不能证明两者同源；应有 PMF/测度相等或已证明的推送身份。

对正质量记录的 Bayes 更新是

$$
b_{n+1}(x')=
\frac{\mathbf1_{q(x')=y'}\sum_xb_n(x)P_n(x,a,x')}
{\sum_{z:q(z)=y'}\sum_xb_n(x)P_n(x,a,z)}.
$$

零分母需要一个总定义 fallback，并证明它不影响真实正质量历史。C1 已提供相应一般条件下的可测后验构造；有限源的实际后验/traceSupport 身份也已有生产桥。

### 5.2 精确预测商与控制提升

对状态压缩 $\phi:X\to Z$，若同一纤维有相同奖励及推送转移

$$
\phi(x)=\phi(x')\Rightarrow
\begin{cases}
r(x,a)=r(x',a),\\
\phi_\#P(x,a)=\phi_\#P(x',a),
\end{cases}
$$

则在相同可用动作及折扣 $0\le\gamma<1$ 下，Bellman 算子交换

$$
T_X(v\circ\phi)=(T_Zv)\circ\phi,
\qquad V_X^*=V_Z^*\circ\phi.
$$

这是真正的控制充分性，不能从“某组观察预测相同”无条件推出。安全运输还需安全集/认证条件与压缩相容。已有 `PredictiveOptimalControlLift`、`PredictiveViabilityTransport`、`CoreSourceAllTimesAssembly` 等端点应被复用。

安全与最优的区别可用两动作例说明：留在安全态的奖励为 0；一次危险动作给正奖励并进入吸收失败态。未受限最优可以选择危险动作；受限安全 Bellman 的动作域不同。将两者写成同一 GOA 会删掉实质假设。

### 5.3 支持生存、无限策略与有限记忆

对非空单观察支持 $B\subseteq X$，定义

$$
\operatorname{Succ}(B,a,y')=
\{x':q(x')=y',\ \exists x\in B,\ P(x,a,x')>0\}.
$$

有认证谓词 $\operatorname{Cert}(x,a)$。在支持关系和认证不随时间变化时，支持族上的算子是

$$
\mathcal F(W)=\{B\in\mathcal B:\exists a,
(\forall x\in B,\operatorname{Cert}(x,a))\ \land
\forall y',\operatorname{Succ}(B,a,y')\ne\varnothing
\Rightarrow\operatorname{Succ}(B,a,y')\in W\}.
$$

从全部合法支持 $W_0=\mathcal B$ 开始，$W_{k+1}=\mathcal F(W_k)$ 递减。令 $M=|\mathcal B|$，至多 $M$ 次严格删除即稳定到最大固定点 $W_*$。有限关系 checker 已给出可执行判定；存在性定理已给出有限记忆控制器，记忆可取非空支持加 fallback，共 $M+1\le2^{|X|}$ 个值。

已合并结果还证明固定非自治数据上的“所有有限 horizon 可行”与“存在同一个无限策略”的对应；不能把这些写成新的待证目标。**支持齐次允许正概率数值随时间变化；这与数值齐次是不同条件。**

### 5.4 认证不自动等于物理安全

令未认证占据

$$
U_n=\Pr\bigl(\neg\operatorname{Cert}(X_n,A_n)\bigr).
$$

$U_n=0$ 只表示策略没有实际使用未认证对。要得到安全集 $K$ 中的全时安全，还要

$$
p_0(K)=1,
\qquad x\in K\land\operatorname{Cert}(x,a)\land P_n(x,a,x')>0
\Rightarrow x'\in K.
$$

在同一实际过程上逐步归纳，再用可数交/下降事件，才得到
$\Pr(\forall n,X_n\in K)=1$。#367 已给正例和分别删除初始安全、支持保持的负例；以后综合算法应直接消费这些端点。

### 5.5 路径风险与数据后选择

若真实一步误差在已认证对上至多 $\varepsilon_n$，其余对上至多 1，则路径比较的典型上界是

$$
d_{\rm TV}(P_{0:T}^{\pi},Q_{0:T}^{\pi})
\le d_{\rm TV}(P_0,Q_0)
+\sum_{n<T}\bigl(\varepsilon_n\Pr(\mathrm{Cert}_n)+U_n\bigr).
$$

要求同一策略和正确的逐历史条件行；实际 API 的半径/初态版本需逐项匹配。可进一步放松为 $d_0+\sum_n(\varepsilon_n+U_n)$。对共同失败事件 $E$，有 $P(E)\le Q(E)+d_{\rm TV}(P,Q)$。这解释为何零未认证占据仍不消去模型误差和参考失败风险。

训练记录 $D$ 的选择器 $c(D)$ 必须进入同一个联合实验

$$
\mathbb P(dD,d\omega)=\mathbb P_D(dD)P_{c(D)}(d\omega).
$$

若共同好事件 $G$ 满足 $\Pr(G^c)\le\alpha$，且仅在 $G$ 上对实际选中的候选证明 $P_{c(D)}(E)\le\beta$，其中 $0\le\beta\le1$，则

$$
\Pr(E)\le\beta\Pr(G)+\Pr(G^c)
\le\beta+(1-\beta)\alpha.
$$

既有逐行注册采样、同 Good 包络与支持生存消占据已经实现这类实质组合。后续工作不应重复证明“把几个证书放在一起”，而应从实际 oracle/综合过程产生其中目前外给的证书。

## 6. 生存、QSD、Doob：已经证明的对象必须分开

### 6.1 从原实验到 killed 质量

对固定数值闭环核 $L$ 和安全域 $K$，定义

$$
Q(x,x')=L(x,x')\quad(x,x'\in K),\qquad
\eta(x)=p_0(x)\quad(x\in K).
$$

$\eta$ 是未归一化限制，保留初态可能已不安全的事实。设 $H_r=Q^r\mathbf1$，则

$$
s_T=\eta Q^T\mathbf1
=\Pr(X_0,\ldots,X_T\in K),
\qquad
\lim_Ts_T=\Pr(\forall n,X_n\in K).
$$

后一个等号来自同一个无限路径测度上的下降事件连续性；不要求有正特征向量，也不推出极限为正。存在一个数学上可写的 $Q$ 不够，必须先证明它就是实际过程的 killed 核。#363/#367 已完成相应当前观察反馈及真实路径桥。

### 6.2 QSD 和 Doob 不等于有限窗条件路径

左 QSD $\nu Q=\lambda\nu$ 描述终端条件稳定；正右特征数据 $Qh=\lambda h$、$h>0$、$\lambda>0$ 给 Doob 核

$$
\widehat Q(i,j)=\frac{Q(i,j)h(j)}{\lambda h(i)}.
$$

有限窗条件下一步则为

$$
R_{t,T}(i,j)=\frac{Q(i,j)H_{T-t-1}(j)}{H_{T-t}(i)}
$$

（分母正时）。它一般依赖剩余时间，不能直接替换为 $\widehat Q$。主干有真实源的反例

$$
Q=\begin{pmatrix}3/8&3/8\\1/8&1/8\end{pmatrix},
$$

其中真实 QSD 存在，两种路径初始边缘都可为 $(3/4,1/4)$，但 horizon $T=1$ 的两时刻路径 $(X_0,X_1)$ 的 TV 恰为 $1/4$。因此终端稳定和初始相同都不足以识别完整条件路径。

### 6.3 若研究无限 Q-process，真正需要证明什么

不能把每个有限 $T$ 的条件律直接作为同一无限过程的相容投影。反例取

$$
Q=\operatorname{diag}(a,b),\quad0<a,b<1,\quad a\ne b,
\quad\eta=(1/2,1/2).
$$

条件初始第一态概率为 $a^T/(a^T+b^T)$，随 $T$ 改变。它们通常不满足投影一致性。

若具体研究需要 Q-process，应在给定非退化谱条件后证明：对每个固定前缀长 $n$，当 $T\to\infty$ 时条件前缀律收敛，再证明这些**极限**相容；并控制 $H_{r-1}(j)/H_r(i)$ 到 $h(j)/(\lambda h(i))$ 的误差。必须注明初态极限倾斜、不可约性/周期性、可达类以及零生存状态。当前任务没有理由先启动这个完整谱工程。

## 7. 第 12 层候选：实质增量与发布缺口

### 7.1 总定义有限窗核的严格合同

本地 `TotalFiniteWindow.lean` 给任意 fallback PMF $F_r(i,\cdot)$ 的总定义行

$$
R_r(i,j)=
\begin{cases}
Q(i,j)H_r(j)/H_{r+1}(i),&H_{r+1}(i)>0,\\
F_r(i,j),&H_{r+1}(i)=0.
\end{cases}
$$

在 $Z_T=\eta H_T>0$ 下，初始律为 $\eta_T(i)=\eta(i)H_T(i)/Z_T$，第 $k$ 步使用 $R_{T-k-1}$。对每个 $n\le T$ 及所有状态前缀，候选证明

$$
\Pr_T(x_{0:n})=
\frac{\eta(x_0)\prod_{k<n}Q(x_k,x_{k+1})H_{T-n}(x_n)}{Z_T}.
$$

零行正确性使用非负求和：$H_{r+1}(i)=0$ 蕴含所有 $Q(i,j)H_r(j)=0$。因此这些 fallback 不会影响真实有质量前缀。它进一步证明生成前缀、原实验条件前缀的状态边缘相等，以及安全域外 fallback 不影响时窗内结果。

重要区别：生成律不是直接定义为过滤条件律，所以这个相等确实消除一个独立路径身份输入；但结论是**状态边缘**，不重建完整动作轨迹。它不涵盖 $Z_T=0$、$n>T$、跨 horizon 自动一致或无限条件过程。

非空洞见证使用 $f\to t\to\bot\to\bot$，初态三态均匀，$K=\{f,t\}$：

$$
Q=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
\eta=(1/3,1/3),\quad Z_1=1/3,\quad Z_2=0.
$$

两种不同零行 fallback 都给完整一步条件路径 $\delta_{(f,t)}$。这同时证明初始不安全质量必须保留、零行不能删掉、一步条件窗不能被提升成无限存活。

### 7.2 真实记忆控制器的齐次数值核

设记忆 $m\in\mathsf M$、动作律 $\sigma(m,a)$、动作后真实更新 $U(m,a,q(x'))$。候选 `HomogeneousMemorySurvival.lean` 构造

$$
\bar P((x,m),(x',m'))=
\sum_a\sigma(m,a)P(x,a,x')
\mathbf1\{m'=U(m,a,q(x'))\}.
$$

它证明这个核与既有真实有限记忆实验的数值行、整个无限增广轨迹测度相同。对 $\bar K=K\times\mathsf M$、$\bar\eta$、$\bar Q$，得到

$$
\Pr_{\rm actual}(X_0,\ldots,X_n\in K)=\bar\eta\bar Q^n\mathbf1,
\qquad
\lim_n\bar\eta\bar Q^n\mathbf1
=\Pr_{\rm actual}(\forall n,X_n\in K).
$$

这消除从有限记忆控制器到固定 killed 过程的来源隔断。仍需固定**数值**核；支持齐次不够。$(X,M)$ Markov 不推出 $X$ 自身 Markov。等式允许极限为零，也不包含 QSD 存在或存活最优性。

### 7.3 当前证据和本轮失败检查

候选所在工作树：

`/Users/murphyhoops/Documents/ueotlean-worktrees/core-books-handoff-20261020/total-kernel-memory-20261023`。

真实证据原件在相邻 `total-kernel-memory-evidence-20261023/`。已核：

- 完整 build receipt exit 0；694 源文件、三个环境文件、Lean/Lake 二进制哈希、九个依赖 revision 且 clean，与当前候选完全匹配；原 build log 哈希一致。
- native export / fixed verifier 的历史运行均 exit 0；12 public source candidates、80 compiler-owned theorem constants、27 直接边。传递公理仅标准 `propext`、`Classical.choice`、`Quot.sound`。
- 52,140 次跨层和 66 次内部 stored-type definitional-equality 比较没有 collision；这不证明一般逻辑独立性、科学新颖性或没有可复用的旧抽象。
- canonical UMC 历史收据 exit 0；95 research modules / 694 global modules，并明确 `global_strong_unified_closure=NOT_ESTABLISHED`。

但 `TOTAL_KERNEL_MEMORY_REUSE_OVERLAY_V1.json.registration_provenance.inputs` 所列 **39 个** `total_kernel_memory_v1/actual-execution/...` 路径都尚未归档到当前候选；研究报告与注册收据链接也缺失。最小实跑命令：

```bash
python3 -B formalization/ueot-core/docs/compression/theory_completion/knowledge/reuse/test_fkrg_reuse.py -k total_kernel_memory
```

结果：**exit 1；4 tests；3 通过；`test_total_kernel_memory_registration_preserves_raw_execution` 因 39 个缺失输入及后续 raw overlay 读取产生 40 个错误记录。** 这是一项 consumer 测试失败，不是 40 项不同数学定理失败，也不是 Lean 构建失败。

### 7.4 R0：先完成这个既有候选的发布

1. 后继接管已有 `compression/theory-completion-total-kernel-memory` 工作项，先核当前 main/PR/WIP，保全原改动；本次文档 PR 不夹带候选。
2. 按清单逐文件从真实原件恢复 39 个归档输入，核原 SHA。不能改写历史 `PENDING`、捏造旧独审，或把新运行冒称旧运行。
3. 恢复/新做真实数学与来源审查，写清所审源码和日期，补齐 `RESULTS_AND_BOUNDARIES.md` 与 registration receipt；修复消费者链接。
4. 先让上述 4 项检查通过，再运行受到实际归档/consumer 变更影响的现有回归。源码和环境不变时复用匹配 full-build/native 证据；若源码变更，按变化范围重建。
5. 提交后用既有基线授权 `pr_preflight.py` 对 immutable base/candidate Git 对象执行预检，再完成 PR、独审、合并、resulting-main 源身份核验。当前 overlay 的 `git_object_pr_preflight=NOT_PERFORMED_SEPARATE_GATE` 不得被文档文字消掉。

完成条件是“第 12 层成为可从 Git 完整恢复的已审已合并证明包”，不是“世界统一理论闭合”。

## 8. R1：优先补可执行控制器综合

本节以后均为**建议研究合同 / 待实现与验证**。数学推导不是本轮新 Lean 结果；示意标识也不是声称生产 API 已存在。

### 8.1 已有基础与真正新增点

文件 `SupportMemoryCheck.lean` 中的 `finiteMemoryCheck` 已经是有限表上的可执行 Bool 判据，cutoff 为 $2^{|X|}-1$；`finiteMemoryCheck_iff_exists_all_times_policy` 已连接全时策略存在，已有 `by decide` 正负见证。不要重写 checker。

但是文件 `SupportMemoryController.lean` 中的 `supportWinningAction` 仍用 `Classical.choose`，初态支持还来自任意 PMF；目前不是从显式有限输入到可执行动作表的完整综合。上述常量均在 `UnifiedClosure.SupportViabilityClosure` 命名空间下，文件名不是其命名空间。R1 应只填这一段。

**需要消除的外给输入：** 不再要求调用者给未知获胜策略或接受不可计算的 winning-action 选择；由有限、可判定的表直接产生可执行控制器，并证明它自己的真实过程正确。

### 8.2 明确输入、输出与失败值

输入是有限枚举 $X,A$，非空动作域或明确失败分支，可计算 $q$ 及 $Y$ 上可判定相等，可判定支持关系 $R$ 与认证 $C$，显式初始支持 $I\subseteq X$，固定完整无重复动作列表。

输出应为

$$
\operatorname{synth}(R,C,q,I)=
\operatorname{None}\quad\text{或}\quad\operatorname{Some}(\mathcal C),
$$

其中 $\mathcal C$ 的初始记忆、动作、更新均为可执行有限表函数。记忆先用 `Finset X`；空集作不可能记录的 fallback。无需先求最小记忆，也无需构建通用策略框架。

实际概率桥独立陈述：对给定真实 $p_0,P_n$，

$$
x\in I\iff p_0(x)>0,
\qquad R(x,a,x')\iff P_n(x,a,x')>0\ \ (\forall n),
$$

并证明认证表与实际 `Cert` 一致。若只知道 $P_n>0\Rightarrow R$，得到的是保守安全综合；这时通常保留 soundness，不能自动保留相对真实系统的 completeness。

### 8.3 算法与数学不变量

复用现有有限后继运算与固定点 checker；在 $W_*$ 上定义

$$
a_*(B)=\text{动作列表中首个使}\quad
\bigl[\forall x\in B,C(x,a)\bigr]\land
\bigl[\forall y,\operatorname{Succ}_R(B,a,y)\ne\varnothing
\Rightarrow\operatorname{Succ}_R(B,a,y)\in W_*\bigr]
\text{成立的动作}.
$$

计算时只需遍历有限像 $q(X)$；像外的后继为空，另证这个等价即可保留任意观察类型 $Y$。固定点性质保证每个 $B\in W_*$ 的搜索成功。初始观察 $y$ 对应 $B_0=I\cap q^{-1}(y)$；真实可达初始观察的 $B_0$ 必须在 $W_*$。更新为

$$
B_{n+1}=\operatorname{Succ}_R(B_n,a_*(B_n),Y_{n+1}).
$$

应依次证明：

1. `find` 的结果在动作列表中且满足条件；没有结果等价该支持不具此固定点见证。
2. 在同一源匹配下，每个正质量实际历史的记忆等于实际 `traceSupport`，从而包含真实状态。
3. 归纳得 $B_n\in W_*$；所以新控制器自己的 $U_n=0$ 对所有 $n$ 成立。
4. 加第 5.4 节两个物理安全前提，推出新控制器的无限实际状态律全时安全。
5. 固定数值源下，将新控制器实例化到第 12 层 $\bar P$、$\bar Q$；需要风险时再消费既有 joint-risk 端点。

不要证明它与旧 `Classical.choose` 控制器路径相等：多个获胜动作时两者可以合法选择不同动作。要证明的是新控制器的独立同源正确性。

### 8.4 终止、复杂度与反例

设 $M$ 为合法非空单观察支持数。已有数学保证至多 $M\le2^{|X|}-1$ 轮；若采用显式逐轮固定点表并复用已算 membership，每轮至多 $M|A|$ 个动作条件检查，即至多 $M^2|A|$ 次此类检查，另计每次有限后继枚举成本。若直接反复调用现有递归 checker，只先声明有限终止，实际重复计算成本另计，不能套用这个表算法界。不能把指数支持空间写成关于 $|X|$ 的多项式算法。

复用 Bool flip 见证：恒定观察，隐状态交替，认证要求动作等于隐状态，已知单点初态。两记忆控制器可全时认证；固定当前观察随机反馈有 $U_0+U_1=1$。混合初态支持则应拒绝。再用一个含多个获胜动作的小表验证固定顺序选择确定、可执行，但不要求旧选择器相同。

**验收：** 编译产物实际运行并输出有限控制器表；固定点、traceSupport、零占据和物理安全链接有 Lean 证明；至少一个严格记忆正例和一个不可行负例。计算定义不含 `Classical.choose` 不意味着全部证明的公理闭包无 `Classical.choice`，两项必须分开报告。

## 9. R2：真实有噪声 oracle 与可认证风险

### 9.1 必须先承认的支持识别 no-go

用有限样本未见某转移，不能证明它的真实概率为零。本节 $N\ge1$ 为整数、$0<\alpha<1$。设 $N$ 次独立试验每次有危险概率 $p$，未见危险的概率是

$$
\Pr_p(\text{零危险})=(1-p)^N>0\quad(0<p<1).
$$

更强地，对固定有限 $N$ 的任意认证规则，$p\downarrow0$ 时记录分布趋向 $p=0$ 的分布。如果在 $p=0$ 上宣告“$p=0$”的概率是 $\rho$，则在任意小正 $p$ 上错误认证概率可任意接近 $\rho$。因此不能同时有对全部 $p>0$ 的错误率 $\le\alpha$，又在 $p=0$ 有 $\rho>\alpha$ 的非平凡认证功效。

这解释为何把观测到的边集当精确支持会破坏 R1 的真实源桥。要么支持来自独立可验证结构/有理模型，要么使用保守支持上包络，要么退到定量风险；不能用更多有限样本悄悄替代这个逻辑边界。

零危险记录能给的是固定样本单侧界：选

$$
\varepsilon_N=1-\alpha^{1/N},
$$

则任何 $p>\varepsilon_N$ 产生零危险记录的概率小于 $\alpha$。多行注册时分配 $\alpha_j$ 并保证 $\sum_j\alpha_j\le\alpha$；数据后停止需要额外序贯证明。有限时域可支付 $T\varepsilon$ 等风险预算；若每步独立危险概率 $p>0$，无限生存概率 $\lim_T(1-p)^T=0$。**有限数据的低风险不等于无限时间零风险。**

### 9.2 接到已有 C3 程序的三值 oracle

先选有限历史/候选域 $H$、有限注册实验族 $\mathcal I$、有限输出 $Y$，候选读出 $r_j$ 构成细化链。定义真实缺陷

$$
d_j=\max_{i\in\mathcal I}
\max_{r_j(h)=r_j(h')}
d_{\rm TV}(K_i(h),K_i(h')),
$$

空比较族约定为 0。$d_j=0$ 等价该注册响应族可在读出纤维上精确下降；细化缩小比较对，因此 $d_{j+1}\le d_j$。注意这是此定义得到的单调性，不是所有称作“缺陷”的量都单调。

在同一 Good 上，若全部响应估计满足 $d_{\rm TV}(\widehat K_i(h),K_i(h))\le u$，三角不等式给

$$
|\widehat d_j-d_j|\le2u\qquad(\forall j).
$$

固定实用阈值 $\tau$，oracle 返回：

| 返回值 | 条件 | 可断言 |
|---|---|---|
| PASS | $\widehat d_j+2u\le\tau$ | $d_j\le\tau$ |
| FAIL | $\widehat d_j-2u>\tau$ | $d_j>\tau$ |
| AMBIGUOUS | 其余 | 现有信息不足 |

若要称返回位置 $j$ 为链内首个真实合格者，必须所有 $k<j$ 都已经 FAIL，且 $j$ PASS；跳过歧义再返回后者只能称“一个已认证候选”。现有 `C3ExecutableSearch.scan` 是 Bool exact-oracle 程序；三值扩展应保持这个区别，不能把 AMBIGUOUS 强转 false。

### 9.3 预算、停止与同源用途

令 $H,\mathcal I,Y$ 非空有限，$N\ge1$ 为整数、$u>0$、$0<\alpha<1$。每个 $(h,i)$ 有 $N$ 个实际独立重复输出，$|Y|=q$ 时，对所有输出事件做 Hoeffding 并合可得一个保守界

$$
\Pr(G^c)\le 2|H||\mathcal I|2^q e^{-2Nu^2}.
$$

因此足够取

$$
N\ge\frac{\log(2|H||\mathcal I|2^q/\alpha)}{2u^2}.
$$

这是可复用既有校准的简单预算，指数因子必须诚实保留，不声称最优。若所有所需比较都有 $|d_j-\tau|>\gamma$，取 $4u<\gamma$ 足以消除该族内歧义；无已知 gap 时算法允许未决，不能保证任意精确判定都有限终止。

若真的需要数据依赖停止，可先用按行和样本数分配的可求和预算（例如对 $m\ge1$ 个固定注册行、$n\ge1$，取 $\alpha_{j,n}=6\alpha/(\pi^2m n^2)$）建立 simultaneous-in-$n$ 置信事件，再允许停在随机 $n$。每行第 $n$ 个样本的源条件必须成立；主动选择时需可预测采样与相应条件分布/鞅证明，不能仅给 $\alpha_{j,n}$ 公式就认为相关单轨迹已合法。先检查现有 predictable OLS 和 rowwise 端点，能实例化就不新增重复集中不等式。

最后必须证明具体 oracle 的 PASS 意味着控制/风险端点所需的那条认证条件；“观察预测缺陷小”并不自动意味着真实物理支持安全。该桥是 R2 的核心新增义务，而非测试数量。首版可以针对已知结构支持、只未知非零数值参数的有限族，使 R1 的安全合同与 R2 的统计合同不矛盾。

### 9.4 两条合法的正向支持合同

**结构上包络。** 如果能独立证明 $\operatorname{supp}(p_0)\subseteq I^+$ 和 $R_{\rm true}\subseteq R^+$，以 $I^+$ 初始化并对 $R^+$ 的所有后继综合安全策略，那么实际支持递推满足 $B_n^{\rm true}\subseteq B_n^+$。动作在 $B_n^+$ 上全部认证，就在实际支持上认证；这个包含归纳足以给安全 soundness。它可能因额外假边拒绝实际可行系统，因此不能谎称 completeness。

**已知最小正质量。** 若独立前提保证每条真实正边概率至少 $p_{\min}>0$，每个注册状态动作行有 $N$ 次真实独立采样，所有可能边数至多 $L$，则

$$
\Pr(\exists\text{真实正边从未被看到})
\le L(1-p_{\min})^N\le Le^{-Np_{\min}}.
$$

在无观测误标且完整注册下，取 $N\ge p_{\min}^{-1}\log(L/\alpha)$ 可在概率至少 $1-\alpha$ 的共同事件上恢复支持，并接 R1。初态支持、认证表和部署来源仍有各自匹配责任。$p_{\min}$ 不能从“目前未见更小边”推出。

这两条合同把信息代价写清：不存在无条件免费零风险，但有明确额外结构时可以得到真实、可审计的保证。

## 10. R3 及后继数学：按具体阻塞启动

### 10.1 R3a：压缩已合成控制器，而不是先追求最小世界模型

若 R1 的支持记忆过大，先对**同一个控制器**做可计算压缩。对其有限记忆定义等价 $m\approx m'$，要求

$$
m\approx m'\Rightarrow
\left[\sigma(m)=\sigma(m')\ \land
U(m,a,y)\approx U(m',a,y)
\quad(\forall a,y\text{ in the declared finite domain})\right].
$$

动作分布与更新因此可降落到商。把原初始记忆推到商，按前缀归纳证明所有有限观察/动作/状态路径分布保持；在已有路径测度唯一性条件下保持无限路径律。因此安全、值和存活结论随实际律运输。

对 R1 的确定性动作表（或具有可判定相等的有理 PMF 表），有限分割细化可以计算满足这些条件的最大等价关系；任意实 PMF 的相等不能默认可判定。先查现有商与有限自动机工具是否可直接用。这个“最小”最多相对给定控制器、允许输入与行为等价，不是所有策略中的全局最小记忆，也不是唯一物理对象。若 R1 的规模尚未阻塞，就不启动此优化。

### 10.2 R3b / C1：从现成 belief kernel 到规范预测商

复用文件 `C1ParametricBelief.lean` 中、`TheoryCompletion.ScientificClosure` 命名空间下的 `c1_parameterized_belief_recursion` 与 `c1_countablyGenerated_belief_recursion`。给可数测试族，定义

$$
T(b)=\bigl(\Pr_b(E_j)\bigr)_{j\in\mathbb N}\in[0,1]^{\mathbb N}.
$$

真正待证箭头是：从测试族对动作—观察—未来拼接的闭合，推出

$$
T(b)=T(b')\Rightarrow
T_\#B_a(b,\cdot)=T_\#B_a(b',\cdot),
$$

然后在明确的 Borel 像/可测下降条件下构造 $\bar B_a$，使
$T_\#B_a=\bar B_a\circ T$。奖励和安全要各自经 $T$ 分解，才能消费既有控制提升。

证明任务必须包含四件事：测试量可测；一步拼接确实封闭；零概率观察上版本变化只影响零测集；商像及下降核可测。可数可测坐标的像不自动是 Borel，不能把此点省略。先选具体可实现模型和像，再推广；不要先宣布“任意可测世界都已有规范最小递归状态”。

### 10.3 时变数值源：复用零行论证，替换错误的幂

若真实控制器面对 $Q_t$，定义

$$
h_{t,T}=Q_tQ_{t+1}\cdots Q_{T-1}\mathbf1,
\quad h_{T,T}=\mathbf1,
\quad Z_T=\eta h_{0,T}.
$$

当分母正时

$$
R_{t,T}(i,j)=\frac{Q_t(i,j)h_{t+1,T}(j)}{h_{t,T}(i)};
$$

零行用 fallback，证明同样的非负零项和前缀归纳，再证明生成律等于真实时变源条件律。有限相位周期源可以把相位并入状态后再使用齐次链，但必须证明这个相位确实驱动原核；把任意时间 $n$ 叫“有限相位”是错误的。

只有应用真的需要时变数值条件窗时才启动；它不能自动给长期谱极限或一般非自治 QSD。

### 10.4 条件生存的误差会被稀有事件放大

设两条相同样本空间的完整路径律 $P,Q$ 满足 $d_{\rm TV}(P,Q)\le\varepsilon$，同一可测存活事件 $S$ 满足 $P(S),Q(S)\ge s>0$。任意事件 $A$ 有

$$
\begin{aligned}
\left|\frac{P(A\cap S)}{P(S)}-\frac{Q(A\cap S)}{Q(S)}\right|
&\le\frac{|P(A\cap S)-Q(A\cap S)|}{P(S)}
+\frac{Q(A\cap S)|P(S)-Q(S)|}{P(S)Q(S)}\\
&\le\frac{2\varepsilon}{s}.
\end{aligned}
$$

所以一个不声称最优的充分界为

$$
d_{\rm TV}(P(\cdot\mid S),Q(\cdot\mid S))
\le\min\{1,2\varepsilon/s\}.
$$

若只知 $Q(S)=q>\varepsilon$，可用 $s=q-\varepsilon$；若 $q\le\varepsilon$，该证据不足以认证真实条件预测。反例：$P(a)=\varepsilon,Q(b)=\varepsilon,P(c)=Q(c)=1-\varepsilon$，其余为零，$S=\{a,b\}$。无条件 TV 为 $\varepsilon\to0$，条件 TV 恒为 1。

这个合同可作为 R2 后的稳健性端点，但需先查标准条件测度/TV 引理并复用。它只涉及同一事件 $S$；事件定义本身失配要另付误差，不能藏进归一化。

## 11. C4–C6：不能被总装定理替代的三个问题

### 11.1 C4：点态有后继，不等于给定边缘有合法概率历史

现有形成—binding—运输定理可给

$$
d_P(B_1(f_1(t_Xx)),t_P(B_0(f_0x)))
\le L\varepsilon_F+\varepsilon_B.
$$

证明是在两端间插入 $B_1(t_F(f_0x))$，应用 Lipschitz 与三角不等式；形成关系、binding 相容及真实源身份仍是前提。

若下一实例给有限对象集 $P,Q$、概率质量边缘 $\mu,\nu$（更一般可取非负、等总质量）和合法关系 $R$，要求联合质量 $\pi$ 具有这些边缘且仅落在 $R$，令 $R(A)=\{q\in Q:\exists p\in A,\ R(p,q)\}$，其准确可行条件是有限加权 Hall 条件

$$
\forall A\subseteq P,\qquad \mu(A)\le\nu(R(A)).
$$

必要性由质量只能流往 $R(A)$ 得到；充分性可由有限运输网络的 max-flow/min-cut 证明。首版有理质量可以整数缩放，先复用已有有限流/LP 工具；不为了这项问题另造一套优化框架。

反例：$\mu(a)=\mu(b)=1/2$，$\nu(c)=1/10,\nu(d)=9/10$，仅允许 $a\to c,b\to c$。每个源点都有合法后继，但 $A=\{a,b\}$ 要求 $1\le1/10$，不成立。

即使合法耦合存在，它仍只是一个可能历史。要断言**实际**形成/身份延续，必须证明它就是原过程 $(f_t(X_t),f_{t+1}(X_{t+1}))$ 的推前。不能用任意合法耦合制造真实祖先。

若确有逐时真实关系和误差，误差递推

$$
e_{t+1}\le L_te_t+\delta_t
$$

给

$$
e_T\le\Bigl(\prod_{t<T}L_t\Bigr)e_0
+\sum_{j<T}\delta_j\prod_{j<k<T}L_k.
$$

应复用 M-TC；新的内容是实际过程产生这些 $\delta_t,L_t$，不是再证明一次求和公式。

### 11.2 C5：共同二维性可以被拒绝，不能仅凭秩识别 Π/Φ

若所有环境在同一预算点共享 $z(B)\in\mathbb R^2$，$m_e=g_e\circ z$，且 $z$ 在 $B$、每个 $g_e$ 在 $z(B)$ 可微，则

$$
J=\operatorname{stack}_e Dm_e
=\operatorname{stack}_e Dg_e(z(B))\,Dz(B),
\qquad\operatorname{rank}J\le2.
$$

若 $\|\widehat J-J\|_2\le\eta$，奇异值扰动给
$\sigma_3(\widehat J)>\eta\Rightarrow\operatorname{rank}J>2$，从而拒绝该共同二维假设。反向若 $\sigma_3(\widehat J)+\eta\le\tau_0$，只能说真 $\sigma_3(J)\le\tau_0$，不是精确秩二或机制唯一。

线性分解的规范自由度已经足够说明问题：$J=GH=(GA^{-1})(AH)$，任何 $A\in GL(2)$ 都可换轴。更一般的可逆潜在坐标变换也保留可观察映射。要把两轴叫作具体 Π/Φ，需规定单位、方向、选择性干预与测量锚点，并证明这些限制只留下被允许的规范群。

后继合同应包括竞争三驱动模型、共同预算点、预先固定误差范数、独立留出环境。可靠秩三结果应限制或否定二维主张，而不是事后更换环境、坐标或阈值使其“重新成立”。本轮不捏造这类实测结果。

### 11.3 C6：目的、奖励、程序与谱系的信息来源

现有 `MechanismTeleologicalFaithfulness` 本来就是“相同机制观察推出相同目的排序”。若把它移入更大的 record，再投影取回目的等价，独立假设没有减少。

一个可研究的具体模型应先给资源演化 $s'=g(s,a,\xi)$、明确的存活/复制读出 $W$，假设 $W\circ g$ 对噪声律可测可积（有界可测读出足够），从真实机制定义

$$
V_M(a)=\mathbb E_M[W(g(s,a,\xi))].
$$

然后从可观测/可干预机制的条件推导 $V_M$ 的排序可识别性。不能事后选 $W$ 拟合任意行为；即使该排序已识别，也不证明所有行动最大化它，更不证明伦理或宇宙目的。

程序源方面，已有严格正反结论：对编码 $e:\mathsf{Program}\to\mathsf{Information}$，程序域有 fallback 时，存在全域解码器满足 $d\circ e=\mathrm{id}$ 当且仅当 $e$ 单射。左逆推出单射；单射时像内取唯一前像，像外 fallback。**下一研究需解释编码/解释器如何在同一机制中存在、保持或复制**，不是再把左逆定理命名为自发生程序。

若同一物理输入要求两个不同正确程序，任何只读物理输入的确定性合成器都不可能同时正确。同样，当前完整微观状态若能由两个不同历史生成，预测/状态身份本身不能恢复真实祖先。应增加真实生成记录或干预可区分信息，或接受等价类目标；不能把 parent token 当推导出的历史事实。

## 12. C7 与世界接口：把理论变成会失败的主张

当前本轮是数学研究，C7 的任务是**给清楚应用合同**，不强迫先选一个现实系统才允许完成文档。任何将来接入的实例至少明确

$$
(\mathcal M,\mathcal E,O,\Theta,\mathcal L_D,\mathcal L_{\rm deploy},
G,\alpha,\text{失败事件与停止规则}).
$$

应保存哪些模型尚未被排除，而不仅是一个拟合最优点。若置信集合满足

$$
\inf_{M\in\mathcal M}\Pr_M(M\in\mathcal C(D))\ge1-\alpha,
$$

则可报告 $\Theta(\mathcal C(D))$ 或该集合所有模型共同满足的结论。该覆盖保证只对声明模型类成立；真实源不在模型类中时不能凭族内置信度掩盖失配。

对训练后实际部署失配，可复用已有 TV/joint-risk 工具：若 Good 上基准风险为 $b(D)$、真实与基准部署 TV 至多 $d(D)$，则

$$
\Pr_{\rm actual}(E)
\le\Pr(G^c)+\int_G\min\{1,b(D)+d(D)\}\,\mathbb P_D(dD).
$$

这里的新增科研工作应是从具体模型/实验得到 $d(D)$，而不是把最终误差上界再次作为字段输入。实际训练/部署条件匹配、初态、失败语义、可实施行动、未注册行都必须明确。

失败至少分四层：

| 观察结果 | 首先检查/更正 |
|---|---|
| Lean 类型或证明失败 | 形式命题、实现、依赖或所用前提 |
| 数学正反例违反声称结论 | 量词、定义、隐含假设、自然语言与源码匹配 |
| 数据违反预测但协议正确 | 模型类、源匹配、机制解释或外部假设 |
| 数据/日志/停止规则不能核验 | 证据有效性；不能据此证明模型正确或错误 |

既有 C7 历史中全部中止尝试的保留不能充分验证；新持久 runner 不能追溯修复旧证据。应保留该限制，不把“没有看见失败”算作新确认。

## 13. 执行顺序、文件责任与验收

### 13.1 不并行扩张全部开放端口

| 优先级 | 工作单 | 复用基础 | 必须新增的结论/能力 | 停止或转向条件 |
|---|---|---|---|---|
| 立即 R0 | 第 12 层证据归档和发布 | 已有 694 模块候选与原始 receipt | Git 可恢复、consumer 真通过、独审与合并身份 | 原件哈希不符先查来源；不伪造旧审查 |
| 主线 R1 | 可执行支持控制器综合 | 固定点、checker、有限记忆真实路径与安全 | 从显式有限输入计算动作/更新表，证明自身全时正确 | 若实际要求不需要算法而只需要存在性，不重复造框架 |
| 接续 R2 | 具体 noisy oracle 与支持/风险合同 | C3 scan、三值区间、rowwise、joint risk | 实际采样产生可用证书；支持 no-go 与正向条件都保留 | 无 gap/无源匹配则未决或改实验，不调弱真值 |
| 按规模 R3a | 同一控制器记忆商 | 有限商与行为相容 | 保持真实律的有限表压缩 | 规模不阻塞就暂缓，不以最小性拖延 R1 |
| 按模型 R3b | 规范预测商递归 | 现成 C1 belief kernel、预测/控制 lift | 从测试闭合推出可测降落，不外给目标宏观核 | 像/共同版本条件不成立则保留边界或限定空间 |
| 按实例 | 时变条件窗、条件风险稳定性、C4 | 同源路径、零行证明、M-TC/TV | 替换一条真实失配或概率身份输入 | 没有使用者不先做全泛化 |
| 长期主线 | C5/C6/C7 机制与来源 | 已有秩拒绝、信息 no-go、机制/目的接口 | 可识别规范、独立信息来源与可失败预测 | 不可辨识就报告等价类或 no-go，不宣称唯一世界机制 |

这些不是另造 C8 或重开 P0–P12，也不把 frozen 106 当可随手重定义的清单。R0 完成后第一张数学工作单应是 R1；R2 先选一个有限源族，优先已知结构支持而未知数值参数，使新统计层确实能接入已建立的安全链。

### 13.2 R1 的建议最小文件边界

建议先在注册 TC / `UnifiedClosure/` 下添加一个实现模块和一个必要见证模块，名称在实施时按现有习惯确定。复用这些现有端点：

| 生产文件 | 本次建议消费的内容 |
|---|---|
| `FiniteSupportFixedPoint.lean` | 最大固定点、cutoff、winning step、有限基数界 |
| `SupportMemoryCheck.lean` | `finiteMemoryCheck` 及其全时策略存在等价 |
| `SupportMemoryController.lean` | 控制器语义与记忆/traceSupport 桥；保留旧非计算实现 |
| `FiniteMemoryPhysicalSafety.lean` | 通用控制器自身全时物理安全端点 |
| `FiniteMemorySeparation.lean` | 严格记忆增益的真实源反例 |
| `FiniteMemoryCheckWitness.lean` | 已有可执行正反判定，不复制同样测试 |
| 第 12 层 `HomogeneousMemorySurvival.lean` | 合并后消费实际增广核及 killed 生存身份 |

新增公共语义应只有“可计算选择器/控制器、正确性、必要负例”。若需要改变已有共享接口，先说明为什么 additive adapter 不足，再按现有 L2 规则处理；#368 的具体例外不授权所有未来分支任意改旧文件。

### 13.3 实施检查的准确次序

每个新数学工作单先写：输入空间、量词、源时序、目标结论、真实消去的前提、可推翻它的例子。然后按以下顺序执行：

1. **复用检查。** 搜具体 theorem 名称、类型与消费者；先判断旧定理实例化是否已经够用。类型不 definitionally equal 不等于不可复用。
2. **书面数学。** 完整给正向证明、零/空/未决分支和至少一个反例。总装 theorem 不能把待证结论搬进输入 record。
3. **最小运行。** 对新增模块作 focused Lean 检查；计算逻辑给一个真实运行的正负断言，不能以 0 tests 通过。
4. **增量证据。** 公共进口、source/native/axiom、有关 consumer 和不可变 Git preflight 按实际影响更新。存在 `Classical.choice` 不应被报告为新数学公理；`sorry`、`admit`、新 `axiom` 或逃逸不能用绿色治理掩盖。
5. **发布门。** Lean 源有变化时按现有操作规则完成一次所需 namespace/full `lake build UEOT`、独立精确候选审查与 PR。源/环境完全一致的重型证据只在规则允许的条件下复用，并记录比对。
6. **合并后。** 核 resulting-main 的确包含所审源和证据，再更新接续入口；不把 `proof=SKIPPED` 写作云端证明成功。

从仓库根可复用的实际命令：

```bash
git fetch origin main
git status --short --branch
git diff --check
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/validate_unified_closure.py --repo-root .
python3 formalization/ueot-core/docs/compression/theory_completion/unified_closure/test_validate_unified_closure.py
```

Lean 源变更的正式构建在 `formalization/ueot-core/` 下执行 `lake build UEOT`；本轮只有审查文档，未将这条未来源变更门伪报为已经重新运行。具体 FKRG/native/preflight 命令复用相应版本的脚本说明，参数绑定真实 base/head，不能从候选自增授权。

### 13.4 什么时候可以说“本阶段闭环”

R1 的完成不要求证明宇宙目的、连续状态普适性或最小记忆。它要求

$$
\text{显式表}\xrightarrow{\text{实际执行}}
\text{控制器}\xrightarrow{\text{同源证明}}
U_n=0\xrightarrow{\text{初态安全+支持保持}}
\Pr(\forall n,X_n\in K)=1.
$$

每个箭头的输入都能从同一个实例追到来源，至少有一个非空正例和一个必要条件反例；实现可运行，证明可复查，发布可恢复。这是足够强、又确实可完成的阶段闭环。

R2 的完成要求说明有限数据到底支持哪种声明：精确支持来自额外结构、在 gap 条件下以置信恢复，还是仅得到有限时域风险。不能把三者在最终输出中统一写成“系统已经安全”。

整个强统一任务仍需逐项完成机制/程序/身份与世界接口，或者对不可识别部分给正式边界。阶段结束不是全项目结束；未来未解决的端口也不反过来取消已经正确闭合的阶段。

## 14. 后续接续卡

**先读本报告第 1、7、8、9、13 节，再读实际代码类型。** 不要重读全库旧审计后才开始最小下一步。

- 本轮基准：`41c4b27ef8d993c797b2414311f0934eeb4cb561`；将来先 fetch/查 PR，不能把此 SHA 永久叫 current main。
- 本轮变更仅为审查文档、证据摘要与阅读入口；第 12 层原工作树保持原状，不属于本轮合并的 Lean 内容。
- 第一剩余事项：R0 的 39 个原始证据归档与 consumer 失败；先查是否已由其他会话完成。
- 下一数学工作单：R1 显式有限表综合，两个不可计算入口都要解决——winning action 和初始支持；复用通用实际过程安全端点。
- 不重复：106 冻结证明、常用条件的 C1 联合可测 belief kernel、无限策略存在、有限记忆存在、Bool exact-oracle 扫描、已有有限窗 Doob 反例。
- 不跨越：QM/physics、冻结计数、绝对独立性、无条件目的/祖先恢复、有限数据零危险认证。
- 记忆：仍用原 GI 的 `MurphyHoops/UEOT` 相关流；记忆只作有来源的接续，真实 Git/Lean/receipt 优先。新会话权限以当次用户及仓库规则为准。

## 15. 主要来源与可复查入口

以下相对链接指向受审源码。未来源码变化时，应切换到本报告顶部的审查 SHA 看原版本，而不是把后继源码自动当成本文原始证据。

| 来源 | 用途 |
|---|---|
| [冻结原文](../source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) / [覆盖账本](../../formalization/ueot-core/docs/V3_COVERAGE_STATUS.md) | 106 的原语义、hash、HJB 范围 |
| [数学主文](../UEOT_MATHEMATICS.md) / [Lean 范围](../LEAN_API_SCOPE.md) | 章节证明与出版版本接口，不冒充最新 census |
| [哲学主文](../../philosophy/UEOT_PHILOSOPHY.md) | 真理、对象、目的解释的哲学责任 |
| [统一任务合同](../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/UNIFIED_CLOSURE_MISSION_V1.md) | 单源主线、九门、条件/边界裁决 |
| [P0–P12 状态](../../formalization/ueot-core/docs/compression/theory_completion/THEORY_COMPLETION_STATUS.json) / [C1–C7 状态](../../formalization/ueot-core/docs/compression/theory_completion/scientific_closure/SCIENTIFIC_CLOSURE_STATUS.json) | 原阶段状态及开放端口 |
| [同源全时总装](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreSourceAllTimesAssembly.lean) | 共同有限源到预测/控制/安全 |
| [参数化 belief](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C1ParametricBelief.lean) | 已解决的常用可测后验递归 |
| [支持固定点](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteSupportFixedPoint.lean) / [可执行判定](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SupportMemoryCheck.lean) | R1 复用基础 |
| [现有支持控制器](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SupportMemoryController.lean) | `Classical.choose` 与初态支持缺口 |
| [实际记忆安全](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryPhysicalSafety.lean) / [严格记忆分离](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemorySeparation.lean) | R1 的真实过程消费者和正负例 |
| [C3 实际程序](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/C3ExecutableSearch.lean) | exact Bool oracle 的已有边界 |
| [逐探针校准](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SISCRowwiseProbeCalibration.lean) / [逐行联合风险](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredJoint.lean) | R2 与选择后风险复用 |
| [同源有限窗](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SameSourceFiniteWindow.lean) / [有限窗 Doob](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteWindowDoob.lean) | 条件路径与 Doob 区别 |
| [C4 集合值 FBT](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C4SetValuedFBT.lean) | 点态覆盖和概率耦合区别 |
| [C5 二维检验](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C5DualDriveTest.lean) / [C6 目的机制](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C6PurposeMechanism.lean) | 必要秩、faithfulness 和识别边界 |
| [程序/目的信息边界](../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ProgramPurposeInformationBoundary.lean) | 编码单射、不可辨识输入与无条件主张 |
| [#367 数学报告](../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1/RESULTS_AND_BOUNDARIES.md) / [原 full-build receipt](../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1/actual-execution/full-build-02/FULL_BUILD_RECEIPT.json) | 主干实际增量与构建证据 |
| [执行规则](../../formalization/ueot-core/docs/compression/COMPRESSION_OPERATIONS.md) / [分支规则](../../docs/REPOSITORY_BRANCH_GOVERNANCE.md) | 按风险比例验证与发布 |
| [本轮机器证据摘要](./MATHEMATICAL_CLOSURE_EVIDENCE_2026-10-26.json) | 观察时间、主干/候选身份、检查范围与结果 |

本报告所有未来建议均须在对应真实模型、源码与当前授权下实施；没有把书面推导、文档合并或 GI 记载晋升成新的生产 Lean 定理。
