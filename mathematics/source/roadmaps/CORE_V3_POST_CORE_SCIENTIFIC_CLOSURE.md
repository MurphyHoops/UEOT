# UEOT Core v3：核心理解、独立复核与科学闭合纲领

版本：1.0｜编制日期：2026-10-07｜项目：ueot

本文件与《CORE_V3_OPEN_PORT_MATRIX.md》《THEORY_COMPLETION_ROADMAP_V2.md》共同组成任务书。它是一份基于冻结 Core v3 的新增研究规划，不自行替换仓库 frozen Mission、修改 Core、增加 counted theorem 或宣布开放问题已解决。

## 1. 核心判断

UEOT 的核心是一套**相对于实验协议的对象识别、实现、运输和评价理论**：先约定我们能观察、干预和预测什么，再识别承载这些响应的最小预测信息；检查它是否有合法的动态、因果和物理实现；在历史或表示变化中检验身份保真；另外引入有来源的评价桥，才能讨论最优动作及长期组织。

它不是“所有东西都自维持”的理论，也不是“存在天然推出目的”的理论，更不是已经验证的宇宙普适二维动力学。Core 的力量恰在于把这些更强主张变成有条件、可检验、可失败的接口。

用户提供的审计正确找到了路线偏航：应把 Core §31.2 的七个开放端口作为后续工作入口。但复核也发现，审计对 v1 的部分指责过强、对当前 P6 的描述已过时，并遗漏压缩范围、形式化适配、发现可执行性和秩检验设计中的重要限制。新版保留成果，修正依赖和验收标准。

## 2. 证据边界与权威顺序

数学含义按以下顺序裁决：冻结 Core v3 的定义、假设、命题和证明 → 与其逐项对应的 Lean 表面及适配前提 → post-Core 扩展。原始哲学文稿解释动机，不覆盖 Core 的精确定义。实时工程状态另按确切提交、工作流、合并记录和当前状态入口裁决；历史审计不能冒充当前 CI。

本轮证据如下：

| 层次 | 实际工作 | 能支持什么 | 不能支持什么 |
|---|---|---|---|
| Core 原文 | 完整阅读 3,983 行主文、证明及附录；106 个唯一 P-ID 锚点 | 原文语义和主要推导检查 | 所有领域假设已实现 |
| 原始哲学稿 | PDF 文本抽取及关键概念对照 | 理解 Being/Becoming、Ω、Π/Φ 的重构关系 | 以旧语义覆盖 Core |
| 形式化账本 | 固定 main 的覆盖状态、106 行索引、压缩账本及选定源码 | 仓库记录的 106/106 FULL-GREEN、声明和分类可追踪 | 本轮独立重编译全部 Lean |
| 后续研究 | 复核 v1 总纲、P1/P3/P4/P5 审计、P2 关键组合源码及 H/X/RLSR/RH/Post-QT/Track-S 的选定终审 | 路线定位与关键依赖检查 | 声称本轮逐字重读全部 188 份历史文档 |
| P6 | 读取 PR #285 修正提交的资源审计及核心记账、储备、边界源码 | 当前有限资源扩展的前提和集成状态 | 已合并或 resulting-main 已绿 |
| 可执行复核 | 原文附录 D 原样提取复跑：2,371 项检查；另运行 7 个审计边界反例 | 有限例子、数值计算和反例可重现 | 新的一般数学证明、Lean 重验或现实实验 |

冻结源文件 SHA-256：`ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`。附录 D 提取代码 SHA-256：`4d4072377cbae485f595eddc239ea6962a7bdc5cf7ad400e8d75086ce485c5f7`，与主文声明一致。

远程核对仓库为 [MurphyHoops/UEOT](https://github.com/MurphyHoops/UEOT)，固定 main：`fe211cbccdf5a19fedccf185f54f46ff6345ff19`。本地同名空仓库不是证明或状态来源。本轮没有修改上游源码或 PR，也没有本地 `lake build UEOT` 成功记录。

截至本轮最终状态采样（2026-10-07 下午，Asia/Shanghai）：P0–P5 已关闭；P6 #283 活跃，PR #285 开放、未合并。修正 head：`749e0f5577a28853b2d262d029995535e2f29ef8`，对应 Core Lean `37586259110` 与 Compression Guard `37586259042` 均已 completed/success；这证明该 head 的两项 CI 通过，不等于全部 review/合并门完成。工作流查询工具仅返回 PR 触发的 runs；main 返回空列表不表示 main 无 CI 或 CI 失败。当前 main 的两项 matching resulting-main CI 本轮未独立核实，应在执行第一步补齐。

## 3. 从世界到对象：正确的推导链

### 3.1 对象首先相对于问题和协议

令历史为 h，允许的实验协议为 π，声明未来为 Y。世界和协议给出响应核 K^π(h,·)。规范预测状态把全部声明响应打包为：

\[
C(h)=(K^\pi(h,\cdot))_{\pi\in\Pi}.
\]

如果 T(h) 已能因子化每一个响应核，则在 Core 声明的可测、可数协议和共同几乎处处条件下，C 可经 T 因子化。因此 C 是**对该响应问题**的规范最小预测信息，不是物体无条件的全部本质。

可数协议的共同满测集由可数交得到。不可数协议不能逐个丢掉零测集后就宣称同时成立：例如协议 i 的例外只有 h=i，每个例外零测，但所有例外的并可能覆盖全空间。这是共同版本问题，不能用“每个协议各自成立”替代。

**对 C1 的纠正：Core §4 已经包含 Standard Borel、可数协议下的规范预测状态和可测最小性。C1 应补可测递归更新、实现、非紧极限和共同版本等具体缺口，而不是重新证明一个已关闭的有限→Standard Borel 阶段。**

### 3.2 预测充分不自动是动态闭合

静态地知道声明未来的分布，与能用当前状态递归更新，是两个问题。有限字母情形可以通过条件化更新，但零概率分支必须处理；一般空间需要可测条件分布和一致版本。若宏观状态要成为 Markov 核，还必须证明相同纤维上的转移读出一致，而不是只有集合层面的商映射。

相同策略下的一步 TV 缺损 ε_t 可以通过耦合/望远镜累积得到有限时域界；它不允许比较两条任意不同的策略，也不保证无限时域误差有限。控制商还需奖励、动作可行性、策略提升和 Bellman 等接口，不能仅凭预测商宣布控制等价。

### 3.3 D-OBJ 是接口证书，不是生命定义

基本证书把候选因子、自己的声明未来、环境接口、预测与必要的动态闭合、允许干预下的因果接口、表示运输及协议/支撑/时域/误差记录组合起来。历史、恢复、自维持、遗传、功能目标等按主张另加模块。

预测成功本身不消除隐藏混杂、介入不覆盖和实际部署越界。因果接口只对已声明的干预族负责。误差阈值必须在试验前确定；不能看到结果后缩小“自己的未来”来免除失败。

原文 `D-OBJ-STRONG` 是特定更强证书用语，也不能仅凭名称把它等同于自创生对象。后续 self-maintenance lane 应明确它增加了哪几个恢复、组织和资源条件。

### 3.4 Ω 是证书相对的因果完整性

先冻结证书和时域，再令 χ(D) 表示删除机制集 D 后证书失败。如果机制集有限且失败关于删除单调，失败集能由其极小元重建；这些极小毁损集构成 Ω 超图。

这是有限偏序的极小元重建，不是“所有对象都有几何回路”的普遍定理。如果删除会解除抑制、激活备份，单调性可能失效，此时应保留完整删除响应或换用有明确定义的条件性接口。

完整性裕量是到固定失败集的距离；对同一非空失败集，距离函数 1-Lipschitz。若目标失败集、证书或允许扰动本身变了，不能直接套用这个稳定性结论。

### 3.5 载体对偶不能偷换成物理毁损

能够读出预测信息的访问集，与删除物理机制后的动态，是两种操作。blocker 对偶给出访问/击中结构；升级为物理完整性需要 Core 的 frame 条件保证剩余机制、动力学和接口按约定保持。C3 必须分别记录“读取 oracle”和“物理干预 oracle”的语义及误差。

## 4. 从评价桥到 GOD/GOA：目的不是对象存在的推论

### 4.1 N-TEL-01 的反例是决定性的

固定同一个对象和动力学，只要两个动作 a、b 可选，分别定义 J_a=1{A₀=a}、J_b=1{A₀=b}，即可得到相反的最优动作。故对象存在不确定唯一目标。实际目的解释要来自预先约束的目标类或独立可观测的机制。

完整依赖是两条输入汇合：

```text
世界 + 协议 → 候选表示 → 预测/动态/因果/身份/实现证书
评价主体/层级 + 机制/约束 → 评价桥 + 可行策略 + 目标与时域
两者对接 → 值函数 → GOD 最优动作对应 → 指定种类的 GOA
```

J 的存在不等于其经验识别；目标是标量也不意味着响应维数为一。不同目标可以通过势函数变换等保留最优行为，因此目的识别通常只能到某种等价类。

### 4.2 P1 的正确位置及未关闭的小边界

TeleologicalContract 扩展一般 admissible futures 与 preorder。有限、全序偏好允许序数表示，但这不自动赋予期望效用或 Π/Φ 表示；更一般偏好可能无标量表示。这是 Core §18 的表示扩展。

P1 文档中的 “P1.0 PARTIAL / EXPLICIT BOUNDARY” 还保留一个区别：抽象同证据、异偏好反例，不自动就是两个完整物理 UEOT 实现的同对象反例。总体 P1 CLOSED 表示阶段合同闭合，不意味着所有更强实例主张 FULL。规划无需重开 Core N-TEL-01，应补一页范围说明，只有实际用途要求物理见证时才补构造。

### 4.3 对用户审计的纠正：v1 已有 no-go，P2 已显式消费桥接

v1 Mission 并非数学上断言 Object→唯一 Purpose：它已经禁止这项推论。P2 源码也不是从空白对象自动生成目标。`ParentTeleologicalControlRealization` 显式保存 contract、actionFuture、objective 及表示条件；`endogenous_sameObject_agency_god_goa` 还消费 `BellmanTeleologicalFaithfulness` 和 `GreedyPreservesObjectPersistence`。

因此应纠正的是总图和标题容易造成的“阶段必然生长”印象，以及 P0 OperationalObject 的强持续性范围。不要把叙事问题写成现有证明错误，不要删 theorem，也不要为了更名大规模重构 Lean。

P2 终审应分别列清：对象身份锚点、目标桥来源、合同表示、Bellman 忠实性、策略保持合法性/持续性，以及 stationary 与完整 causal policy 版本。对象、最优性和 viability 是独立验收门。

### 4.4 GOD/GOA 的存在和唯一性必须分开

GOD 是最优动作的集合值对应，非唯一动作不能强选后又称“理论唯一”。梯度只有在特定光滑局部控制结构中才是实现方式。

GOA 可以是不变分布、Cesàro 极限、条件生存/QSD、ω-limit 或其他指定长期对象。这些输出不能互换。有限周期翻转链拥有唯一不变分布，却不从点质量混合收敛；所以唯一不变律不是 mixing。Track-S 的残差隔离可覆盖这类静态唯一性，不宜全部换成更强的 Dobrushin 收缩条件。

## 5. Π/Φ：必须识别共同机制，并允许拒绝二维

### 5.1 标量目标不识别两种驱动

若 J=Π−λΦ−C，则任意 χ 下 Π'=Π+λχ、Φ'=Φ+χ 保持 J。仅拟合 J 不能识别 Π、Φ 的独立物理意义。必须预先指定量纲、尺度、独立测量和允许的规范等价；两个实验旋钮也不自动就是两种独立机制。

### 5.2 共同二维潜变量给出必要秩条件

若各环境共享同一 z(B)∈R²，且响应 y_e(B)=f_e(z(B)) 可微，则在**同一个 B**：

\[
J_{\rm stack}(B)=\begin{bmatrix}Df_1(z(B))\\ \vdots\\ Df_E(z(B))\end{bmatrix}Dz(B),\quad \operatorname{rank}J_{\rm stack}(B)\le2.
\]

环境一响应依赖 (B₁,B₂)，环境二依赖 (B₂,B₃)，各自 rank 2，堆叠却 rank 3。因此逐环境 rank 2 不足以支持共同 latent。

**新增的实验设计纠错：不同预算点不能直接堆叠后按同一必要条件拒绝。** 例如 z(x,y,w)=(x,y+xw) 确实只有两个潜坐标，但在 (0,0,0) 与 (1,0,0) 的 Jacobian 行空间堆叠 rank 3。应在同一点跨环境堆叠，或明确建模随点变化的共同潜空间。

局部 rank≤2 也不足以证明全局共同 latent、唯一 Π/Φ 分解或机制因果性。反例拒绝是单向有力的，低秩支持则需额外可积性、跨环境验证和独立锚定。

### 5.3 有限误差检验不能把“不显著”当零

若 ||Ĵ−J||₂≤η，Weyl 界给 |σ̂₃−σ₃|≤η。预注册 H₀：σ₃≤τ₀，可在 σ̂₃−η>τ₀ 时拒绝；τ₀=0 是精确二维必要条件的特例。

支持“阈值 τ 下有效维数恰为二”至少要 σ̂₂−η>τ 且 σ̂₃+η<τ，并说明只在测量点、环境和误差界范围内成立。中间区域输出“不确定”，不能改阈值获得成功。

实验至少有三个独立预算方向和三个合计响应维度，否则第三奇异值可能结构性不可测试。有限差分带来截断偏差与噪声放大：例如三阶导数有界时中心差分偏差 O(h²)，测量噪声贡献 O(ξ/h)，应联合选择 h、重复数和误差界。响应归一化规则提前冻结，避免事后调单位压低 σ₃。

## 6. 106/106 和四生成器究竟完成了什么

### 6.1 106 是声明表面的形式化覆盖，不是无条件科学闭合

固定 main 的 `V3_COVERAGE_STATUS.md`、`FORMALIZATION_STATE.md` 和唯一 P-ID 索引支持 106 proved / 106 unique / 0 partial / 0 pending。本轮逐行核对索引和压缩映射，不独立重证 106 个 Lean theorem。

例如 P-CTL-03 的形式化把模型特定的 Itô/局部化/可积性输出装入 `ItoRun`，再证明 HJB 残差、终端衰减及无限时域最优性。这个已记录的 adapter 边界不意味着 theorem 是空证明，也不意味着全部受控 SDE 基础已在 Lean 内构造。其他动力学/信息接口同样应分清“库内推导”和“模型提供的分析前提”。

### 6.2 四生成器的精确范围

当前账本：106 项已分析和 final disposition；11 generated，89 retained_adapter，6 retained_boundary；counted generators=4。

M-QD 是商/下降，M-TC 是有限定量运输，M-PE 是正特征结构，M-OI 是占据极限/不变闭合。最小性声明是 `nonredundant_under_declared_derivation_system`，即在注册 theorem-surface DAG 内不可删减；不是所有可能数学证明中的绝对独立性。

所以“四生成器压缩了理论”应带这个限定：它们提供复用骨架，仍保留 95 项领域适配或边界。不得宣称全部 106 无额外数学地由四项推出，更不得把它们称作四条物理定律。

### 6.3 状态治理的三个实际问题

1. 固定 main 的旧 `PID_STATUS.yaml` 仍写 83/106；`PID_AUDIT_MATRIX.yaml` 仍是空 entries 模板。它们应明确标成历史 fallback，不能与当前覆盖入口等权使用。
2. 形式化状态仍记录“canonical source exact bytes in public repo pending synchronization”。源字节可复现卫生与证明数目分开处理，先定位和授权维护，不重开已绿定理。
3. 当前索引 SHA-256 为 `8161c03779663f819312d70e8218d084768e5056b7b660c6b0e9c4bcf83570bd`，与压缩 mission-start baseline 记录的旧索引哈希不同。基线差异不是自动错误；必须做版本差分，确认只是合法索引更新还是追踪断裂，再新增 current manifest。

## 7. 后续成果重新归位

| 成果 | 正确定位 | 保留内容 | 下一步 |
|---|---|---|---|
| P0 | post-Core typed interface；部分操作类型偏强对象 | 明确边界、类型隔离 | 做 D-OBJ 字段对照，说明强持续性范围 |
| P1 | §18 一般偏好/表示扩展 | 序数、效用与 Π/Φ 表示 no-go | 澄清 P1.0 partial 与 stage closed |
| P2 | 同对象 + 已给定桥的控制组合 | 身份、历史、有效状态、GOD/GOA、viability | 补严格终审，区分忠实性和机制识别 |
| P3 | C2 的有限统计基础 | 误差→值/策略/不变律和固定编码极限 | 相关样本、阈值可执行性、协议选择 |
| P4 | C2 的有限候选发现基础 | 标签/证据/对象等价/有效性/控制编码分离 | 动态候选族与独立验证 |
| H/X | typed hierarchy 与条件 parent assembly | 同子证据不唯一父语义及定量正向接口 | 在 C3/C4 使用已有 assembly，而非统一万能层级算子 |
| O/ER/AR/GCR/RLSR/RH/QT/Post-QT/P5 | 强对象、自维持支线 | 同父修复、可变组织、重复故障和均值稳态 | 保留 trusted substrate 与 mean/pathwise 边界 |
| P6 | 强对象资源扩展 | 泛型记账→状态适配→均值/有限期望→额外路径条件 | 完成自己的远程门；不自动启动 P7 |
| P7/P8/P12 原计划 | 构造、繁殖/谱系、自创生应用研究 | 历史合同与有价值问题 | 有具体机制/数据需求再激活 |
| P9 原计划 | 一般对象尺度运输归 C4；物理 RG 为领域桥 | 运输和尺度模块 | 不混同 hierarchy 与 Wilsonian RG |
| P10 原计划 | C1 的具体一般状态缺口 | 可测/非紧存在问题 | 先缩小 theorem target |
| P11 原计划 | 按实际 theorem 需要提供随机分析底座 | Itô/Dynkin/Girsanov 等接口 | 不以补齐阶段编号为理由重写完整数学库 |

P3 一个额外限制：有限模型存在正分离 gap，不代表算法事先知道 gap 或已有可执行样本量。固定编码纤维一致性，不等于编码本身被发现；样本空间随 n 变化的边际依概率收敛，也不能宣称同一路径几乎必然一致。

P5/P6 的收益真实，但终端结果依赖有限、可校正的组织损伤和既定语义；可恢复 repair program 不代表对象重建 execution/codec/dynamics/object specification 这四类可信底座。

## 8. 独立复核的主要结果

原文附录 D 重现 2,371 项检查，包括 blocker/分辨率 2,316 项、响应采样、控制值、路径运输、XOR 协同、QSD、选择传递和 Girsanov 观察信息反例。固定模拟中响应最大误差 0.00545 小于认证半径约 0.01201；控制值误差约 0.00340 小于相应上界。一个动作的置信间隔不足以认证，脚本保留“不确定”，没有用实际正确性覆盖证书失败。

另行执行了 7 个独立小反例：同对象异目标；逐环境 rank 2 但共同 rank 3；跨预算点错误堆叠；指数规模极小载体输出；期望余额与路径破产；唯一不变律与混合分离；目标 gauge 保持但驱动改变。全部通过。它们强化了本规划的边界，并不宣布现实 UEOT 获得实验支持。

本轮未发现足以推翻 Core 上述主要推导的反例；这不是对全部领域适配、全部 Lean 106 项语义或现实普适性的无条件担保。当前最大缺口是从数学接口到可识别机制、可执行发现和独立数据检验。

## 9. 科学闭合的七条主线

后续不设“C1 完成才能 C2”或“C7 完成才算终点”的直线。C1 补确切可测和极限缺口；C2 做现实数据对象/协议联合发现；C3 做有输出边界的可扩展载体算法；C4 做非平稳身份及指定 GOA 运输；C5 检验共同低维驱动；C6 独立识别目的桥；C7 从第一天为其他六条提供预注册、估计、反例和复现链。

每项成果只允许四种结论：条件定理已证明；有限实例通过；指定应用获支持；指定假设被拒绝。**阶段合同关闭、Core P-ID 全绿、应用证书通过、整个科学开放端口关闭是四个不同状态。**

第一轮最优先做 R0 权威对账、P2 终审和 C2/C7 的有限独立数据闭环；同时把 C3 的非枚举任务和 C5 的必要条件反例纳入设计。一般状态、生命式构造与全套随机分析按具体依赖推进，避免为了“理论完备”的叙事继续堆叠阶段。

## 10. 主要可核对来源

- 项目资料库：`UEOT_Core_Mathematics_v3.0_Complete.md`，重点 §4、§7、§12–18、§19–23、§25–28、§31.2 与附录。
- [固定 main 覆盖状态](https://github.com/MurphyHoops/UEOT/blob/fe211cbccdf5a19fedccf185f54f46ff6345ff19/formalization/ueot-core/docs/V3_COVERAGE_STATUS.md)、[形式化状态与 Itô 接口说明](https://github.com/MurphyHoops/UEOT/blob/fe211cbccdf5a19fedccf185f54f46ff6345ff19/formalization/ueot-core/docs/FORMALIZATION_STATE.md)。
- [压缩账本](https://github.com/MurphyHoops/UEOT/blob/fe211cbccdf5a19fedccf185f54f46ff6345ff19/formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml)、[v1 Mission](https://github.com/MurphyHoops/UEOT/blob/fe211cbccdf5a19fedccf185f54f46ff6345ff19/formalization/ueot-core/docs/compression/theory_completion/THEORY_COMPLETION_MISSION.md)。
- [P2 同对象内生组合源码](https://github.com/MurphyHoops/UEOT/blob/fe211cbccdf5a19fedccf185f54f46ff6345ff19/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/SameObjectEndogenousAgencyClosure.lean)、[P2 评价实现源码](https://github.com/MurphyHoops/UEOT/blob/fe211cbccdf5a19fedccf185f54f46ff6345ff19/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/SameObjectTeleologicalControl.lean)。
- [P6 PR #285](https://github.com/MurphyHoops/UEOT/pull/285)、[修正 head 审计](https://github.com/MurphyHoops/UEOT/blob/749e0f5577a28853b2d262d029995535e2f29ef8/formalization/ueot-core/docs/compression/objecthood/P6_RESOURCE_CLOSURE_AUDIT.md)、[Core Lean run](https://github.com/MurphyHoops/UEOT/actions/runs/37586259110)、[Compression Guard run](https://github.com/MurphyHoops/UEOT/actions/runs/37586259042)。
- [实时恢复入口 #146](https://github.com/MurphyHoops/UEOT/issues/146) 和 [Theory Completion #265](https://github.com/MurphyHoops/UEOT/issues/265)；其 head 字段可能落后 PR API，应用确切提交交叉核对。

本地可复现证据置于本次任务 `output/research-evidence/`：原文复核脚本与 JSON、7 个反例脚本与 JSON、固定提交下载的选定文档。资料库任务书记录结果和来源；证据文件保留在本地，不冒充新的 synced 原文。
