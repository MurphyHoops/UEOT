# UEOT Core 后继扩展规范 1.0

**权威类型：独立参考规范补充（出口 B）。** 冻结 Core v3.0 仍是原 106 个 P-ID 的语义和形式化计数基准。本文件以新的 CSX 标识登记成熟后继合同；不替换冻结源，不宣布 Core v4.0，不把数学著作 v4.1 的出版版本当 Core 版本。

来源切片：2026-11-11；Git commit `16a89154183c22030d4526413167d095d94e6890`，tree `839321b98ddcf368d0673484f7239733b53a5180`。集成状态只由真实 PR/main 与 [REVIEW](REVIEW.md) 决定。中文与[英文对照](UEOT_Core_Successor_Specification.en.md)共享合同 ID、公式、接口清单及证据身份。

## 1. 使用与权威

调用一个结果时，先确定对象和任务，再读取相应 CSX 的论域、假设、量词和消费者义务，最后沿真实定义文件进入 Lean 或书面证明。合同标题、CLOSED 标签、导入成功或同类型 record 本身都不是对应用前提的证明。

| 层 | 权威与职责 | 本规范的处理 |
|---|---|---|
| [冻结 v3](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) | 原 0—31 章、附录及 106 个源 P-ID 的准确含义 | 按原字节和原定义继承 |
| [manifest](../manifest.yaml) 与 [覆盖账本](../../../formalization/ueot-core/docs/V3_COVERAGE_STATUS.md) | active_core=3.0；原覆盖／晋升记录 | 不更换身份和分母 |
| 本规范的 CSX 合同 | 后继定义、来源工厂、强化、实例、反例与消费者边界 | 一个合同可引用多个定理；不是定理计数单位 |
| [实际 Lean 来源矩阵](review/PROOF_SOURCE_AND_CONSUMER_MATRIX.md) | 真实定义文件、公共 import 路径与历史证据范围 | 静态身份与 kernel 证明分层 |
| [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md) | 解释、标准归因、完整书面推导及教学顺序 | 引用既有正文；出版版本独立 |
| [下游采用清单](DOWNSTREAM_BOOK_ADOPTION.md) | 数学、哲学、物理的后续采纳动作与领域条件 | 不从 Core 合同自动推得领域事实 |

冻结源为 183440 字节、3983 行，SHA-256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`；全部 106 个 P-ID 在 [逐项映射](V3_PROPOSITION_INTERFACE_MAP.json) 中保留原锚点。其 163 个登记的源向声明是接口数，不是 163 个源命题。新合同中的“相关 P-ID”表示调用／扩展导航；具体关系以逐项映射和实际定理为准，不暗示旧 P-ID 被改写。

原覆盖仍为 106/106 FULL-GREEN、0 partial、0 pending。后继内容状态沿用其现行来源的 CLASSIFIED_CORE_CLOSED，含明确修订及条件；自然经验适用性仍为 UNVERIFIED。本轮没有新经验验证，也没有用原覆盖比率宣称所有后继主张均已形式化。

## 2. 共同类型纪律与调用规则

### 2.1 六种对象角色

本规范继承数学书 §34.1 的六角色区分。一个角色成立不会自动推出另五个角色。

| 角色 | 对象与判断 | 必须提供的桥 |
|---|---|---|
| 预测身份 | 表示保留声明未来协议的响应律 | 可测因子化、观察纤维与同一未来权限 |
| 形成出处 | 候选由指定形成过程产生 | 实际生成像／形成关系、seed 与 cover |
| 相互作用区分 | 登记探针区分候选 | 同一探针、响应差或定量界 |
| 组成持续 | 源保留组成条件 | 实际核、初态、持续或安全证书 |
| 可恢复实现 | 受扰后由程序恢复 | 剩余信息、物理干预、解释器、费用 |
| 语义身份 | 不同实例被解释为同一对象 | 明确身份关系及保持运输 |

身体、预测状态、程序、真实个体及谱系均有各自类型。retained 保持原身份；newborn 是严格新生。一般 Markov 状态相同、观测等价、均值矩阵相同或标签同名均不足以证明个体身份相同。

### 2.2 “同一源”的最低要求

装配两个合同前，逐项核对初始律、完整转移／噪声、观察与历史、允许动作和记忆、真实记录、对象／父身份、支付和到账时序、时钟以及评价。实际构造可以证明这些等式；只给几个相同字段名不够。

概率变化、观察扩张、外供到账、目标变更、地址菜单扩大或历史权限增加都必须显式登记为新源／新合同条件。尤其不得用逐笔外供的再生模型证明零收入源的无限维持，不得用当前完整状态帮助一个只许看收据的控制器。

表示运输必须覆盖所声明任务：保持一步响应未必保持全部有限联合未来；保持终态不必保持动作历史；完整前缀恒等式与逐时边缘恒等式不同。无限路径事件要有相应可测性和同一实际路径律。

### 2.3 量词、零集与风险

“每个固定参数／时刻几乎处处”不等于对不可数参数／时刻存在同一满测事件。需要共同零集时，应由可数生成族、连续版本或明确统一定理取得。零概率历史的默认后验不提供实际条件事件的信息。

训练事件 Good、所选择候选、后续部署核和失败事件须属于同一实际联合律。联合失败界不等于条件于被接受的失败界。真实部署占据不能用训练样本均值替换；未观察到某转移不证明其概率为零。

有限时域的“每个 T 存在策略”与单一全时策略不同；CSX-07 给出受明确固定源及有限动作约束的量词交换。存在全时策略又不自动有有限记忆；数值核齐次与支持关系齐次分别处理。

### 2.4 目的、长期对象与费用

GOD 总相对于已登记评价、可行策略与比较范围；GOA 的长期对象须明确为不变律、吸引结构、条件存活律或其他对象。有限期净值、无限折扣净值、期望人口指数、随机选择份额、物理健康与个体续存不能互换。

数值目标相同、排序相同和最优集合相同是三种等价。Price 是实际群体上的代数恒等式，Perron 是带条件的均值谱论；两者都不单独产生因果适应或规范价值。

一次源构造减少哪些外部前提，应由其输出证明说明。Perron 工厂从 primitive 性生产证书；紧谱工厂仍需实际 killed 密度匹配；连续源工厂仍需其可预测／正则条件；资金生产者仍需所登记供给。不能把待证结论藏回输入 record 后称为闭合。

## 3. 继承的装配层与后继路线

以下是现行数学书 §32—34 的继承导航，不重立原命题。完整定义与证明继续位于[数学书](../../../mathematics/UEOT_MATHEMATICS.md)及其真实 Lean 接口。三路差异审计说明了哪些是原文已有内容、哪些需要新合同。

| 既有层 | 输入／输出责任 | 后继合同入口 |
|---|---|---|
| QD／TC／OI／PE | 纤维相容→降落；定量局部界→运输；占据极限在前提下→不变性；正特征结构→条件谱结论 | CSX-01、02、12、13；OI 不提供极限存在 |
| P0—P2 | 操作对象、目的表示、同一对象的 agency／控制／长期结构分型 | 本节类型规则；CSX-09、10、30 |
| P3／P4 | 有限数据与变化对象类的识别 | CSX-03、08、15—17 |
| P5／P6／P7 | 故障常返、资源累计、实际种子／程序修复组织 | CSX-04—07、14、18—19、30 |
| P8／P9 | 真实谱系及 Price/Perron；六类尺度性质分别运输 | CSX-12、14、24—25、30 |
| P10／P11 | 观察／信念和随机分析的真实来源 | CSX-03、11、29 |
| P12 | 已给桥的条件生命周期装配 | CSX-14、18—25；不同来源不得只靠类型拼接 |
| C1／C2／C3 | 参数化信念；含误差与漂移的三值区间判别；同一 Markov 通道的 TV 校准 | CSX-02、03、08；未决输出与共同通道条件保留 |
| C4 | formation—binding—transport 的条件误差组合 | 形成存在、binding 相容与定量运输是不同前提；CSX-02、14、19 |
| C5／C6／C7 | 共同二维／锚；目的忠实性；证据与失败分型 | CSX-09、10、27、30；真实世界支持独立 |

原 P12 历史条件接口、旧历史 OPEN 和后继实际来源是不同时间切片；后继生产者可履行具体旧字段，但不会追溯把历史记录改成无条件成功。现行缺口只能根据当前实际端点和其余前提判定。

## 4. 证据与形式化层级

| 标记 | 本文件中实际表示 | 不应推断 |
|---|---|---|
| existing_Lean / formal | 当前公开源码中的定义／定理；来源记录指明既有证明 | 本轮重新编译或自然模型为真 |
| source_identity_reuse / source_validation | 当前源字节与登记来源证据吻合，或引用其具体检查 | 任意改源后还能沿用旧回执 |
| executable / execution_evidence | 可运行函数或登记执行检查；语义正确性另由对应定理负责 | 实例运行替代全输入证明 |
| scoped_native_decide | PR443 的特定闭合数值证明含登记 native 信任 | 所有 Core 定理都用 native，或全 Core 无此信任 |
| written / exact_check / written_consequence | 书面证明、精确算术检查或分析推论 | 已有专用完整 Lean 端点 |
| registry | 来源／计数登记 | 新数学定理或新的覆盖晋升 |

导入本补充接口可使用 `import UEOT` 或相应 `UEOT.V3.Compression.TheoryCompletion` 公共入口；`import UEOT.V3` 单独不代表全部后继分支。每个声明的实际定义文件和完整 import 路线由 [CLAIM_INDEX](CLAIM_INDEX.json) 与原 106 映射给出；不得按命名空间猜定义文件。

本轮运行[静态校验器](validate_successor.py)检查冻结身份、原 106 映射、实际声明、公共 import、匹配回执、双语结构／公式、局部链接和只读范围。它不调用 Lean、不验证新的 kernel proof，也不能机械证明两种自然语言完全同义；后者由实际审读和 [REVIEW](REVIEW.md) 补足。具体结果见 [VALIDATION](VALIDATION.md)。

## 5. 合同目录

下列每张合同均包含十二字段。字段 8/9 将证明来源与当前形式化状态分开；字段 10/12 分别写实际失效例与不支持的更强结论。共用本文类型规则，但分支专有假设以各卡为准。

| ID | 合同 | 证据层 |
|---|---|---|
| [CSX-01](#csx-01) | 有类型的推导复用与冻结计数 | registry, existing_Lean |
| [CSX-02](#csx-02) | 数值缺陷的校准与运输 | existing_Lean |
| [CSX-03](#csx-03) | 同一源的可测后验与实际历史预测 | existing_Lean |
| [CSX-04](#csx-04) | 同一有限记忆控制器的实际路径、安全与生存 | formal, source_validation |
| [CSX-05](#csx-05) | 由同源可行核产生受限最优控制 | existing_Lean |
| [CSX-06](#csx-06) | 实际部署的路径误差与保留逃逸质量 | existing_Lean |
| [CSX-07](#csx-07) | 支持可行性：有限判据、全时策略与实际可执行综合 | formal, executable, source_validation |
| [CSX-08](#csx-08) | 注册采样后选择的真实联合风险 | existing_Lean |
| [CSX-09](#csx-09) | 同数值目标的 gauge 完备分类 | existing_Lean |
| [CSX-10](#csx-10) | 有限线性二维分解、rank-two 规范与含噪判别 | existing_Lean |
| [CSX-11](#csx-11) | 实际连续源的恢复、HJB 与完整路径 KL | existing_Lean |
| [CSX-12](#csx-12) | 由一般有限 primitive 矩阵生产 Perron 证书 | existing_Lean, source_identity_reuse |
| [CSX-13](#csx-13) | 实际 killed 半群的紧谱绑定 | existing_Lean, source_identity_reuse |
| [CSX-14](#csx-14) | literal 事务、当前亲本与同一联合律的生命周期 | existing_Lean, written |
| [CSX-15](#csx-15) | 未知持久源、有限钱包的实际联合决策 | existing_Lean |
| [CSX-16](#csx-16) | 全动作充分表示与接受后正确的共享决策图 | existing_Lean, execution_evidence |
| [CSX-17](#csx-17) | 实际机制分辨、允许实验与最坏后悔 | existing_Lean, scoped_native_decide |
| [CSX-18](#csx-18) | 实际可损坏程序的付费再生及不可恢复边界 | existing_Lean |
| [CSX-19](#csx-19) | 由同一物理响应产生非空形成候选 | existing_Lean |
| [CSX-20](#csx-20) | 有限行选择与实际全策略人口上界 | existing_Lean |
| [CSX-21](#csx-21) | 严格正概率域的最小统一期望增长底数 | existing_Lean, source_identity_reuse, written_consequence |
| [CSX-22](#csx-22) | 两内部程序达到最优的 iff 与同一受损 founder | existing_Lean |
| [CSX-23](#csx-23) | 实际继承反馈、有限 cohorts 与比例反例 | existing_Lean |
| [CSX-24](#csx-24) | 实际标记血缘的 many-to-one 恒等式 | existing_Lean |
| [CSX-25](#csx-25) | 实际全历史与全策略评价的合法表示商 | existing_Lean |
| [CSX-26](#csx-26) | 固定内部程序任务的 2／3／4 最小表示 | written, exact_check |
| [CSX-27](#csx-27) | 同一实际源的秩三响应与二维瓶颈边界 | written, exact_check |
| [CSX-28](#csx-28) | 实际有限响应表的最小载体与 blocker 枚举 | existing_Lean, executable |
| [CSX-29](#csx-29) | 实际 Brownian 源、完整可预测积分、Itô 与固定 Q 底座 | formal, source_validation |
| [CSX-30](#csx-30) | 真实资源、修复检查与全价格目的的独立合同 | existing_Lean, written |

## 6. 规范合同

<a id="csx-01"></a>

### CSX-01 · 有类型的推导复用与冻结计数

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-01`

<!-- contract-field: name -->

#### 2. 精确名称

有类型的推导复用与冻结计数

<!-- contract-field: definition -->

#### 3. 数学定义

将商降落、定量运输、占据极限不变性、正特征结构作为已登记推导系统中的四类生成机制；生成、适配和边界是不同关系。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

原冻结的 106 个源 P-ID 及其登记重导出，不是全部 Lean 声明集合。

<!-- contract-field: assumptions -->

#### 5. 必要假设

每条重导出须采用原源语义与明确桥接前提；账本中的源匹配、正式导入和已完成晋升记录继续有效。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

只对登记推导系统及逐项登记结果计数；不对所有数学定理或所有可能生成系统断言最小性。

<!-- contract-field: conclusion -->

#### 7. 结论

现行分解为 11 项生成、89 项适配、6 项边界、0 项未决；四生成器的最小性是该登记系统内的非冗余性。

<!-- contract-formula: CSX-01 -->

$$
11+89+6=106.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

复用 COMPRESSION_LEDGER 的 final_dispositions 与原覆盖账本；该卡是一项来源登记，不是新的压缩证明。

书稿定位：32 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [COMPRESSION_LEDGER.yaml](../../../formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml)
- [V3_COVERAGE_STATUS.md](../../../formalization/ueot-core/docs/V3_COVERAGE_STATUS.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

登记事实与既有形式证明分别记录；本轮静态映射不触发任何计数晋升。

本卡没有登记独立 Lean 端点；证据层以上述文字为准。

<!-- contract-field: failure -->

#### 10. 反例与失效边界

把 89 个适配器的前提删掉、把声明数量当源命题数量，都会改变所述结果。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

原 106 项全部经逐条 JSON 映射定位；任何后继调用仍须提供实际定理的类型条件。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不声称四条公理推出整个 UEOT、全数学或自然界，也不以 106/106 证明经验普适性。

<a id="csx-02"></a>

### CSX-02 · 数值缺陷的校准与运输

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-02`

<!-- contract-field: name -->

#### 2. 精确名称

数值缺陷的校准与运输

<!-- contract-field: definition -->

#### 3. 数学定义

同一零关系的两个非负缺陷 d、d′ 由正下界 a 与上界 b 校准：a d≤d′≤b d。精确标量规范 d′ₙ=cₙdₙ 是更小的情形。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

RelationDefectPresentation、显式校准、有限链与非负运输系数。

<!-- contract-field: assumptions -->

#### 5. 必要假设

a>0、b≥0，双边比较在所声明的全部点上成立；使用三角结论时原 d 满足三角界，使用跨阶段结论时原收缩/局部误差已成立。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对任意符合校准的三点、相邻阶段和有限链成立；系数只随相应阶段校准改变。

<!-- contract-field: conclusion -->

#### 7. 结论

一般双边校准只保证带 b/a 的准三角界及目标上界/源下界的收缩系数。正标量规范保留精确三角形式，并运输整个带权链。

<!-- contract-formula: CSX-02 -->

$$
d'(x,z)\le\frac ba\{d'(x,y)+d'(y,z)\},\qquad L'_n=\frac{c_{n+1}}{c_n}L_n,\quad\varepsilon'_n=c_{n+1}\varepsilon_n.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

DefectGaugeCovariance 对已有校准与带权链逐项证明；零关系本身不能提供数值尺度。

书稿定位：33 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 一般结果；不是本轮新增证明。

- [DefectGaugeCovariance.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/MinCore/DefectGaugeCovariance.lean):
  - `UEOT.V3.Compression.TheoryCompletion.MinCore.DefectCalibration.triangle_quasi`
  - `UEOT.V3.Compression.TheoryCompletion.MinCore.rescaled_weighted_chain_bound`

相关冻结 P-ID：[P-ID-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-id-02), [P-API-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-api-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

同一个零集可以配许多数值距离；一般双边比较不保留常数 1 的精确三角不等式。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

固定度量、单位、方向与阶段来源；不能把未校准的两个缺陷误差相加。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不从等价关系唯一识别距离，不证明此 b/a 是每一具体表示的最优常数。

<a id="csx-03"></a>

### CSX-03 · 同一源的可测后验与实际历史预测

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-03`

<!-- contract-field: name -->

#### 2. 精确名称

同一源的可测后验与实际历史预测

<!-- contract-field: definition -->

#### 3. 数学定义

同一潜状态转移 P 与观察 O 生成 belief/action 的联合律、共同后验、全有限动作词响应和实际完整观察历史。未来有记忆时状态保留响应与所登记记忆。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

非空标准 Borel 潜状态 Z。参数化单步动作 A 可为任意可测空间，精确条件 CountableOrCountablyGenerated (ProbabilityMeasure Z × A) Y 指参数空间可数，或观察 σ 代数可数生成。响应共同坐标另用可数动作；总空间后验更新、所列 fresh-adaptive 与 retained-memory 端点另取标准 Borel 观察 Y，联合动作更新还取可数且单点可测的 A。

<!-- contract-field: assumptions -->

#### 5. 必要假设

P、O 和实际过去策略是可测 Markov 核；全部响应来自同一源。共同模零版本、动作/观察可测结构及未来记忆须按所调用端点固定，不能用任意 Y 代替。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

每个固定 belief/action 的后验等式对其预测观察律几乎处处成立；对任意可测完整历史过去及有限前缀成立。仅在 fresh future 的比较中使用 canonical-alone 最小性。

<!-- contract-field: conclusion -->

#### 7. 结论

实际保留潜状态的条件律就是递推后验；全词响应生成合法预测递归，并对新鲜自适应未来给出充分性与最小性。保留未来记忆时相应因子是 (response,memory)。

<!-- contract-formula: CSX-03 -->

$$
\mathcal L(\mathrm{past},Z_n)=\mathcal L(\mathrm{past})\otimes b_n,\qquad K_{\mathrm{future}}=\widetilde K\circ(C,\mathrm{memory}).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

C1ParametricBelief 的参数化解体（条件测度分解），MeasurablePredictiveResponseRecursion 与 MeasurablePredictiveHistoryCanonical 的同源路径构造。

书稿定位：39.7;39.11–39.12;39.69 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 来源与消费者；源中没有假定 response image 是 Borel 或存在未经证明的可测截面。

- [C1ParametricBelief.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C1ParametricBelief.lean):
  - `UEOT.V3.Compression.TheoryCompletion.ScientificClosure.c1_parameterized_belief_recursion`
- [MeasurablePredictiveResponseRecursion.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/MeasurablePredictiveResponseRecursion.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveResponseRecursion.actual_C1_response_kernel_factor`
- [MeasurablePredictiveHistoryCanonical.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/MeasurablePredictiveHistoryCanonical.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryCanonical.actual_prefix_latent_consistency`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryCanonical.actual_response_adaptive_ae_minimal`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.MeasurablePredictiveHistoryCanonical.futureKernel_response_memory_factor`

相关冻结 P-ID：[P-PRED-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-pred-01), [P-PRED-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-pred-03), [P-REF-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ref-02).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

零概率历史没有点态经验保证；不同记忆的控制器不能仅因响应相同而识别；一动作边缘不是完整自适应未来。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

声明 P/O、过去律、允许动作和 fresh/retained-memory 模式；优先使用准确端点，不借共同 import 消除可测性前提。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明任意可测空间上的无条件共同后验，也不证明所有对象具有有限记忆或唯一自然划分。

<a id="csx-04"></a>

### CSX-04 · 同一有限记忆控制器的实际路径、安全与生存

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-04`

<!-- contract-field: name -->

#### 2. 精确名称

同一有限记忆控制器的实际路径、安全与生存

<!-- contract-field: definition -->

#### 3. 数学定义

控制器由初始记忆 i:Y→M、动作核 σ:M→PMF(A) 和更新 U:M×A×Y→M 组成；动作和更新不另读时间或完整过去。原源先从 p₀ 初始化 X₀，按 σ(mₙ) 选动作、按 Pₙ(Xₙ,aₙ) 转移，再更新 mₙ₊₁=U(mₙ,aₙ,q(Xₙ₊₁))。增广状态是 (X,M)。实际无限状态律是这个增广律的逐坐标状态投影。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

有限历史 PMF 推前恒等式适用于任意类型 X,M,Y,A。现有无限律接口取有限 X、M 及可测单点；原历史事件质量、安全与 killed 消费者另取有限 A 及相应可测单点。Y 不要求有限。K⊆X 是另外声明的物理安全集。数值齐次 killed 分支还明确要求 A 非空。

<!-- contract-field: assumptions -->

#### 5. 必要假设

所有步骤使用同一个 p₀、q、控制器和完整数值序列 Pₙ；Pₙ 可时变。物理安全另需 supp(p₀)⊆K、同一策略每时未认证行占据为零，以及安全态上的认证动作，其全部实际后继支持仍在 K。固定 killed 矩阵的结论另需一个数值齐次的原 Model；只有支持齐次不够。该 Model 的奖励／折扣由增广保留，但未用于生存最优性。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个固定控制器及原源、每个有限 n，重放原动作所得状态—记忆前缀律精确相等；无限律的每个有限前缀均是这一推前。满足独立物理条件时，同一个无限律以概率一在所有自然数时刻安全。数值齐次分支对任意 p₀、K、n 给 killed 质量恒等式及 n→∞ 的生存极限，允许空 K、初始失败及零极限。

<!-- contract-field: conclusion -->

#### 7. 结论

增广核和完整状态—记忆前缀身份由原执行构造；抹去记忆恢复全部原状态历史。安全桥由实际零占据和两个物理前提推出全时安全。对固定数值核，在 X×M 上取未归一化安全初始行 η̃ 和 killed 矩阵 Q̃，实际有限安全概率为 η̃Q̃ⁿ1，并趋于同一状态路径的全时安全概率。

<!-- contract-formula: CSX-04 -->

$$
\begin{aligned}\widetilde P_n((x,m),(z,m\prime))&=\sum_a\sigma(m,a)P_n(x,a,z)\mathbf1_{\{m\prime=U(m,a,q(z))\}},\\ (\operatorname{augmentHistory}_n)_*\mu_n&=\operatorname{Law}_{\widetilde p_0,\widetilde P}(0{:}n),\\ \Pr(X_0,\ldots,X_n\in K)&=\widetilde\eta\widetilde Q^n\mathbf1\ \longrightarrow\ \Pr(\forall n,\ X_n\in K)\quad\text{(numerically homogeneous source).}\end{aligned}
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

依赖 PMF map/bind 恒等式的前缀归纳先证明实际增广；Ionescu–Tulcea 使用同一数值行序列，有限前缀恒等式连接无限律。物理安全在实际支持历史上归纳，再以可数事件交得到全时结论。数值齐次时先证明闭环行及完整无限律等于原增广律，再消费既有 killed 幂与递减事件连续性。

书稿定位：§2; §8; §27; finite-memory production interfaces — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [CONTRACT.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/path_realization_v1/memory-realization/CONTRACT.md)
- [RESULTS_AND_BOUNDARIES.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/total_kernel_memory_v1/RESULTS_AND_BOUNDARIES.md)
- [RESULTS_AND_BOUNDARIES.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/RESULTS_AND_BOUNDARIES.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

已存在生产 Lean 定理及历史实际编译／源合同。本轮核读这些声明与范围，未重新编译。通用 FiniteMemoryController 记录不要求 M 有限；有限性是对应无限律／有限实现接口的显式条件。CSX-07 的真实可执行综合程序是另一生产者，不把旧 Classical 选择器误称运行算法。

- [FiniteMemoryPolicy.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryPolicy.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryController`
- [FiniteMemoryRealization.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryRealization.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryRealization.actual_augmented_history_law`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryRealization.augmented_history_state_projection`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryRealization.actual_augmented_prefix_eq`
- [FiniteMemoryPhysicalSafety.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemoryPhysicalSafety.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety.actual_state_prefix_eq`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety.controller_all_times_physical_safe`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemoryPhysicalSafety.supportMemoryController_all_times_physical_safe`
- [HomogeneousMemorySurvival.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/HomogeneousMemorySurvival.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.HomogeneousMemorySurvival.actual_augmentedTrajMeasure_eq_homogeneous`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.HomogeneousMemorySurvival.actual_finite_survival_eq_killed_mass`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.HomogeneousMemorySurvival.killed_mass_tendsto_actual_infinite_survival`
- [FiniteMemorySeparation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteMemorySeparation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySeparation.flip_controller_zero_uncovered`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySeparation.stationary_uncovered_zero_add_one`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteMemorySeparation.stationary_feedback_cannot_certify_two_rows`

相关冻结 P-ID：[P-PROC-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-proc-01), [P-PRED-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-pred-03), [P-PER-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-per-03), [P-REF-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ref-01), [P-REF-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ref-02).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

恒观察 Bool 翻转源中，两状态自主记忆使每行认证，而任意齐次当前观察随机反馈的前两行未认证概率之和恰为一；这不排除可读外部时钟的反馈。另有全部行均认证却初态已不安全、或认证转移离开 K 的实际源：全时安全质量仍为零，说明两个物理前提不可删。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

按实际动作和下一观察更新记忆；保持原初态、全部数值转移行及所用策略。动作字段可能被增广投影遗忘，动作依赖事件须另给保留动作的映射。欲用 CSX-07 的检查／综合结果，先核对同一初始支持和转移支持；欲解释为物理安全或固定矩阵生存，再分别提交相应额外前提。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明任意历史策略具有有限记忆、状态投影本身 Markov、全部动作历史自动保持、认证标签自动代表安全、支持齐次自动给固定 killed 矩阵、正存活或 QSD 存在、最小记忆或目的最优。

<a id="csx-05"></a>

### CSX-05 · 由同源可行核产生受限最优控制

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-05`

<!-- contract-field: name -->

#### 2. 精确名称

由同源可行核产生受限最优控制

<!-- contract-field: definition -->

#### 3. 数学定义

安全动作是在可行域 K 内把原 PMF 仍留在 K 的原动作；K 外此限制按定义为空约束。受限模型沿用原奖励、折扣与实际转移。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

有限状态、有限非空动作、原有界折扣 Model 及其 viability 固定点。

<!-- contract-field: assumptions -->

#### 5. 必要假设

viabilityStep(P,K)=K；折扣 0<β<1；策略遵守该状态依赖动作类型，不能改用未受限比较类。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对任意遵守限制的、历史依赖且可随机化的因果策略，以及其每个记忆历史，给值上界。保持 K 的安全陈述从 K 内初态出发。

<!-- contract-field: conclusion -->

#### 7. 结论

固定点保证允许动作非空；受限 Bellman greedy 保持 K，且在完整受限因果策略类中最优。

<!-- contract-formula: CSX-05 -->

$$
A_K(x)=\{a:x\in K\Rightarrow P(K\mid x,a)=1\},\qquad V_R^\pi(h)\le V_R^*(x_h).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

SafeOptimalControlFromViability 直接消费原有限因果策略最优性；K 来自同一 PMF 源。

书稿定位：35 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [RESULTS_AND_OPEN_OBLIGATIONS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/conflict_family_book_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 一般桥；WaitingRepairControl 与 Conflict 家族是不同的具体源。

- [SafeOptimalControlFromViability.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SafeOptimalControlFromViability.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.viable_restricted_greedy_preserves_source_kernel`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.viable_restricted_optimal_dominates_all_causal_policies`

相关冻结 P-ID：[P-PER-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-per-03), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01), [P-QUO-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-quo-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

安全最优可异于未受限最优；K 外动作未受约束，所以不能从 K 内路径一致推出全空间唯一 GOA。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

保留原源、奖励、K、允许策略及初态；长期结论另检查相应闭环与复归/混合条件。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不由安全商推出物理自创生，不证明所有过程都存在非空可行核。

<a id="csx-06"></a>

### CSX-06 · 实际部署的路径误差与保留逃逸质量

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-06`

<!-- contract-field: name -->

#### 2. 精确名称

实际部署的路径误差与保留逃逸质量

<!-- contract-field: definition -->

#### 3. 数学定义

同一策略下逐真实历史取后验与部署行；有限观察像外的参考质量进入独立 escape 值，既不删去也不重新归一化。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

有限微观状态 X、有限动作 A、任意具有可测单点的观察 Y。路径源与参考行仍为 PMF；单次编码 TV 定理允许一般参考概率测度。

<!-- contract-field: assumptions -->

#### 5. 必要假设

相同策略与对应初始投影、有限源完整支撑、逐行误差在已认证行成立、真实未认证占据质量 κₙ 有界；事件风险使用可测参考事件。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个有限 T 的完整路径律和所声明可测失败事件；期望取真实部署律，不取训练采样律。

<!-- contract-field: conclusion -->

#### 7. 结论

编码精确保留相对有限源的 TV；逐时实际未认证占据进入有限路径误差和原空间风险界。

<!-- contract-formula: CSX-06 -->

$$
D_{\rm TV}(\mu,\nu)=D_{\rm TV}(e_\#\mu,e_\#\nu),\qquad D_{\rm TV}(P_{0:T},Q_{0:T})\le\sum_{n<T}\{\epsilon_n+(1-\epsilon_n)\kappa_n\}.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

FiniteObservationEscape 与 ArbitraryObservationRisk 对真实有限像构造并还原原参考路径和原 Q(F)。

书稿定位：36 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)
- [REGISTERED_INTERFACES_CLOSURE_V1.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/REGISTERED_INTERFACES_CLOSURE_V1.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 路径/风险接口；编码含非计算选择，与可执行有限支持检查器不同。

- [FiniteObservationEscape.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteObservationEscape.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteObservationEscapeCheck.tvDist_atomEncode_eq`
- [ArbitraryObservationRisk.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ArbitraryObservationRisk.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_certified_path_error`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ArbitraryObservationRiskCheck.coverage_arbitrary_observation_microscopic_failure_risk`

相关冻结 P-ID：[P-DYN-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-dyn-03), [P-STAT-09](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-stat-09), [P-QUO-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-quo-05).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

删逃逸质量可把原 TV 非零误报成零；训练误差不能无覆盖地替代部署误差。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

绑定同一观测投影、初态、策略、实际占据及参考事件；εₙ 是 [0,1] 内的认证误差。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不声称任意两个参考分布之间都等距，不把当前 PMF 路径风险升级为任意非原子连续 Markov 核。

<a id="csx-07"></a>

### CSX-07 · 支持可行性：有限判据、全时策略与实际可执行综合

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-07`

<!-- contract-field: name -->

#### 2. 精确名称

支持可行性：有限判据、全时策略与实际可执行综合

<!-- contract-field: definition -->

#### 3. 数学定义

V(n,k,S) 是支持 S 从时刻 n 起认证 k 行的后向谓词：V(n,0,S)=True；一步须有共同动作认证 S 的每个状态，并令每个非空观察后继继续可行。Uₙ(π) 是同一实际部署行律的未认证概率。固定支持关系 R 和认证 C 时，非空单观察纤维内的支持族 Bq 经后向消除得到最大固定点 W*。可执行 Program 保存 Finset X 记忆，按自身动作和新观察更新。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

实际概率与策略 iff 取有限 X、A、任意观察类型 Y，以及 X、A 的可测单点结构；有限／无限支持谓词可依赖时间。固定点的纯关系层不要求 A 有限，但实际概率和执行接口保留有限 A。执行器另需有限枚举、可计算 q、可判定的 X/Y/A 相等及 R、C，显式初始支持 I、动作次序表和 fallback；无需枚举整个 Y。

<!-- contract-field: assumptions -->

#### 5. 必要假设

一般全时定理在量化期限前固定 p₀、q、完整 Pₙ、certifiedₙ 和完整 fallback，不要求齐次。有限截止和综合分支另要求 I=supp(p₀)、R等价于每个 Pₙ 的正支持、C等价于每时 certified；数值概率仍可变化。synthesize 自行检查 I 非空、次序表覆盖全部动作及有限检查通过。物理安全另需初始安全和认证 R 后继保持 K；固定 killed 结论再需数值齐次。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

有限期限：全部非空初始观察支持可行 iff 存在完整可观察策略使每个 n<T 的 Uₙ=0。固定同一源后，∀T∃πT 与 ∃π∀n 的零占据条件等价，不预设各 πT 相容。固定 R/C 时，在 |Bq| 行内可行已足够；可执行检查使用上界 2^|X|−1。精确源表且动作表完整时，synthesize.isSome iff 存在全时零占据策略；每个实际返回 program 都有自己的全时保证。

<!-- contract-field: conclusion -->

#### 7. 结论

同一真实正历史的后验支持等于递归 traceSupport。有限与全时 iff 成立；固定点提供 |Bq|+1≤2^|X| 个总记忆值的经典支持控制器。后继可执行 synthesize 使用 List.find? 取次序表中首个合格动作，返回初始化／动作／更新三个确定函数；它们不调用 Classical.choose 或 PMF 支持 oracle。返回程序重放的记忆等于原 traceSupport（含零概率记录），其自身部署 Uₙ全为零。追加物理前提后，其实际无限律全时安全；数值齐次时同一增广 killed 质量每期为一。

<!-- contract-formula: CSX-07 -->

$$
\begin{aligned}S\prime&=\{z:q(z)=y,\ \exists x\in S,\ z\in\operatorname{supp}P_n(x,a)\},\\ V(n,0,S)&=\top,\\ V(n,k+1,S)&\iff\exists a\ [\ (\forall x\in S,\ C_n(x,a))\land(\forall y,\ S\prime\ne\varnothing\Rightarrow V(n+1,k,S\prime))\ ],\\ (\forall T\ \exists\pi_T\ \forall n<T,\ U_n(\pi_T)=0)&\iff(\exists\pi\ \forall n,\ U_n(\pi)=0),\\ \operatorname{synthesize}(I,R,C,\mathrm{ordered},\mathrm{fallback}).\operatorname{isSome}=\mathrm{true}&\iff\exists\pi\ \forall n,\ U_n(\pi)=0\quad\text{(exact tables and complete action list).}\end{aligned}
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

真实 PMF 支持与后验桥把逐支持认证等同实际占据。后向归纳给有限 iff；有限动作的嵌套非空选择给单一全时策略。有限支持族的单调消除在 |Bq| 步稳定。有限检查的纯关系正确性把 stepCheck 对齐 winning-step 条件；完整动作表使 find? 找到合格项。再对返回程序自己的支持历史归纳，证明真实记忆、winning不变式和零占据，最后调用 CSX-04 的安全／生存桥。

书稿定位：§37; infinite-support and executable-support production interfaces — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [INFINITE_POLICY_PROOF.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/infinite_policy_v1/INFINITE_POLICY_PROOF.md)
- [RESULTS_AND_BOUNDARIES.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/finite_memory_v1/RESULTS_AND_BOUNDARIES.md)
- [RESULTS_AND_BOUNDARIES.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/executable_support_v1/RESULTS_AND_BOUNDARIES.md)
- [RELEASE_ACCEPTANCE.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/executable_support_v1/RELEASE_ACCEPTANCE.json)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

有限 iff、非自治全时策略、固定点、Boolean判据与可执行综合均已有生产 Lean 证明和分别登记的历史证据。旧 supportMemoryController 的选择仍为非计算，但 ExecutableSupportSynthesis 已给真正运行接口，不能把旧计算缺口列成现行未完成。Program.toController 的 PMF.pure 语义解释是非计算定义，不影响三个运行函数可执行。本轮只审读复用，未重跑历史执行。

- [FiniteSupportViability.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteSupportViability.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.traceSupport_eq_fiberTerminalPosterior_support`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.initial_viability_iff_exists_zero_uncovered_policy`
- [FiniteSupportViabilityCheck.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteSupportViabilityCheck.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.finiteRelationViabilityCheck_correct`
- [InfiniteSupportViability.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/InfiniteSupportViability.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.arbitrarily_long_zero_uncovered_iff_single_all_times_policy`
- [FiniteSupportFixedPoint.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteSupportFixedPoint.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.supportWinning_fixed`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.supportMemory_card`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.supportArenaCard_add_one_le_pow`
- [SupportMemoryCheck.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/SupportMemoryCheck.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.SupportViabilityClosure.finiteMemoryCheck_iff_exists_all_times_policy`
- [ExecutableSupportController.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ExecutableSupportController.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportSynthesis.findAction_eq_some_iff`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportSynthesis.synthesize_isSome_iff_exists_all_times_policy`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportSynthesis.synthesize_some_zero_uncovered`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportSynthesis.synthesize_some_all_times_physical_safe`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ExecutableSupportSynthesis.synthesize_some_killed_mass_one`

相关冻结 P-ID：[P-PER-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-per-03), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01), [P-ALG-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-alg-01), [P-CORE-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-core-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

当前行可认证仍可能走入未来死路；整当前观察纤维可能无共同动作，而真实历史后验支持允许安全选择。常观察双相源的混合初态可被检查拒绝，即使两个单点初态分别可行。综合拒绝空初始表及不完整动作表；重复动作合法，首个合格项依输入次序。V(n,0,S)=True没有额外末态安全义务；零未认证占据也不自动是物理安全。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

以当前实际初态、完整数值源及认证谓词证明表的精确匹配，不能由有限样本中未见转移就认定概率为零。保留同一返回 program、全部非空观察后继与显式 fallback；不把它等同旧 horizon-dependent 或 Classical 选择器。跨到物理安全／killed模型时提交 CSX-04 所需条件；检查器不会重写参考过程或削减其完整历史风险核验预算。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不声称任意非自治问题都有自主有限记忆、最小记忆、最少查询或多项式时间。现有可执行综合重用递归检查器，未实现 memoized 固定点表。精确支持与认证的经验发现、奖励最优、正存活的一般保证、任意无限状态／动作推广及自动减少参考风险预算均不由此得到。

<a id="csx-08"></a>

### CSX-08 · 注册采样后选择的真实联合风险

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-08`

<!-- contract-field: name -->

#### 2. 精确名称

注册采样后选择的真实联合风险

<!-- contract-field: definition -->

#### 3. 数学定义

采样前固定真实源 P、注册行 J={(n,a,x):n<T 且 certified(n,x,a)}、逐行正样本量 N_j、每时非负半径 ρ_n 及微观失败 E。同一时间的注册行共用 ρ_n。Good 定义为所有注册行的 TV(P_j,经验行_j)≤ρ_n。训练后选择 c；候选含投影 q_c、初态、参考核 Q_c 和同一粗历史策略，Q_c^(T) 表示对应参考路径律。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

此选中联合风险端点的 Ω、X、A 有限；Y 只需可测单点；候选类型 C 无需有限。单独采样层允许更广训练空间。

<!-- contract-field: assumptions -->

#### 5. 必要假设

每条注册行的样本可测、行内 iid 且边缘为该真实行；行间独立非必要。N_j、ρ_n、注册及 E 在采样前固定。只对同一 Good 上实际选中的 c 要求以下五项。

- hfit：每条认证行的投影经验律与 Q_c(n,q_c(x),a) 的 TV≤η_n。
- hcap：选中策略在原实际部署律下的未认证行占据≤κ_n。
- hF：候选粗路径事件 F_c 可测。
- henvelope：固定微观 E 包含于投影路径事件 F_c 的原像。
- hchecked：以 ε_n=min(1,ρ_n+η_n)，完整参考风险加路径预算的截断值 min(1,Q_c^(T)(F_c)+Σ_{n<T}[ε_n+(1−ε_n)κ_n])≤β。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对任意选择映射及 β∈[0,1]，若 Good 上完整参考风险+路径预算≤β，则对同一训练/真实部署联合律给总体失败上界；Viable 版本内部消去占据输入。

<!-- contract-field: conclusion -->

#### 7. 结论

实际注册采样给 α=registeredConfidenceBudget=Σ_{j∈J}2^(|X|+1)exp(−2N_jρ_{n(j)}²)。同一真实训练—选中部署联合律满足 min(1,α+(1−α)β) 的失败界。Good 涉及未知真实行律；这一数学事件不因命名为校准而自动可观察或可执行检查。

<!-- contract-formula: CSX-08 -->

$$
\begin{aligned}\alpha&=\sum_{j\in J}2^{|X|+1}\exp(-2N_j\rho_{n(j)}^2),\qquad \varepsilon_n=\min(1,\rho_n+\eta_n),\\ \min\!\left(1,Q_c^{(T)}(F_c)+\sum_{n<T}[\varepsilon_n+(1-\varepsilon_n)\kappa_n]\right)&\le\beta\quad\text{on Good},\\ P_{\rm train,deploy}(E)&\le\min\{1,\alpha+(1-\alpha)\beta\}.\end{aligned}
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

VariableRegisteredSamples → VariableRegisteredJoint；ViableVariableRegisteredJoint 使用同一个 viableFamilyPolicy 与同一个 Good。

书稿定位：38 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)
- [REGISTERED_INTERFACES_CLOSURE_V1.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/REGISTERED_INTERFACES_CLOSURE_V1.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 概率保证；有限源数值见证是独立检查，不是自然数据实证。

- [VariableRegisteredJoint.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/VariableRegisteredJoint.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.VariableRegisteredJointCheck.registered_selected_joint_failure_of_cap_on_good`
- [ViableVariableRegisteredJoint.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/ViableVariableRegisteredJoint.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.ViableVariableRegisteredJointCheck.viable_registered_selected_joint_failure_on_good`

相关冻结 P-ID：[P-STAT-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-stat-01), [P-STAT-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-stat-02), [P-STAT-09](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-stat-09), [P-CORE-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-core-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

数据后挑 N、任意相关单轨迹采样、换一个失败事件或忽略拒绝/坏事件均超出合同。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

明确参考风险、全部实际支付及 E 的含义；若报告 P(Fail|Accept)，必须另证明接受概率与条件化转换。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不是条件接受失败率，不保证整个工作流必成功，也不解除实际覆盖和样本模型责任。

<a id="csx-09"></a>

### CSX-09 · 同数值目标的 gauge 完备分类

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-09`

<!-- contract-field: name -->

#### 2. 精确名称

同数值目标的 gauge 完备分类

<!-- contract-field: definition -->

#### 3. 数学定义

对同一对象集 X 和固定 λ，目标为 J(x)=Π(x)−λΦ(x)；gauge 变换由任意函数 χ:X→ℝ 给出。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

任意 X 上的实值函数。这里比较逐点目标数值，不只比较排序或 argmax。

<!-- contract-field: assumptions -->

#### 5. 必要假设

两个表示使用同一 λ 和同一 X。若从已锚定 Π 反推 Φ，还须 λ≠0；锚定 Φ 后 Π 不需该非零条件。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每对 (Π,Φ)、(Π′,Φ′)，逐点目标相等当且仅当存在逐点函数 χ 满足所列变换。

<!-- contract-field: conclusion -->

#### 7. 结论

同数值目标的全部不唯一性正是 gauge；额外的独立锚可消去相应自由度。

<!-- contract-formula: CSX-09 -->

$$
J'=J\iff\exists\chi,\quad \Pi'=\Pi+\lambda\chi,\qquad\Phi'=\Phi+\chi.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

逐点代数的双向证明；这是原 gauge 边界的完备分类，不把两项的名称当可识别性。

书稿定位：18;23;39 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)
- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 端点逐声明链接；本轮只检查其源码身份与可达性。

- [DualDriveGaugeCompleteness.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DualDriveGaugeCompleteness.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.same_objective_iff_gauge_related`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.pi_identified_of_phi_anchor`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.phi_identified_of_pi_anchor`

相关冻结 P-ID：[P-DDH-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ddh-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

λ=0 时目标完全不识别 Φ；无锚时非零 χ 保留 J 而改变分项。只有最优策略相同的目标可能不属于此数值 gauge。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

先区分数值、排序和最优集合三种等价；说明锚的数据来源、单位和独立性。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不由单个标量目标推导自然界两条独立轴、共同二维响应或规范价值。

<a id="csx-10"></a>

### CSX-10 · 有限线性二维分解、rank-two 规范与含噪判别

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-10`

<!-- contract-field: name -->

#### 2. 精确名称

有限线性二维分解、rank-two 规范与含噪判别

<!-- contract-field: definition -->

#### 3. 数学定义

J:X→ₗℝY 的秩是其像空间维数；共同二维分解要求同一 H:X→ₗℝℝ²、G:ℝ²→ₗℝY。含噪检验使用第三奇异值估计 σ̂₃、误差半径 η 和登记容差 τ₀。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

X 为有限维实向量空间；Y 为实向量空间。GL₂ 唯一性只作用于真实秩二的非退化分解；奇异值检验另有有限矩阵及有效扰动事件。

<!-- contract-field: assumptions -->

#### 5. 必要假设

精确因子定理需线性；规范唯一性需 H 满射、G 单射（秩二可导出）。登记单位必须由独立有效锚固定。噪声界须实际覆盖真实 σ₃。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个上述线性 J 给 iff；对同一秩二 J 的任意两组非退化分解给可逆换基。检验结论只在登记误差事件成立时有效。

<!-- contract-field: conclusion -->

#### 7. 结论

秩≤2 当且仅当经 ℝ² 因子化；秩二分解由 GL₂ 连接，锚可固定剩余自由度。三值判别先在 η<σ̂₃ 时 rejected 并排除精确秩≤2；未 rejected（σ̂₃≤η）且 σ̂₃+η≤τ₀ 时 compatible，只证明 σ₃≤τ₀；其余 ambiguous。

<!-- contract-formula: CSX-10 -->

$$
\operatorname{rank}J\le2\iff\exists H,G,\ J=G\circ H;\qquad \eta<\widehat\sigma_3\Rightarrow\sigma_3>0,\quad\widehat\sigma_3+\eta\le\tau_0\Rightarrow\sigma_3\le\tau_0.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

有限维线性分解、同像核诱导的可逆换基以及扰动区间推理；标准线性代数的项目内形式接口。

书稿定位：23;39 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)
- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

精确 iff、秩二规范、登记单位及判别 soundness 有既有 Lean 端点；非线性全局推广没有由此证明。

- [DualDriveFiniteRankFactorization.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DualDriveFiniteRankFactorization.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.finite_rank_le_two_iff_linear_factorization`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.rank_two_factorizations_unique_gauge`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.rank_two_registered_units_identify`
- [C5DualDriveTest.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/C5DualDriveTest.lean):
  - `UEOT.V3.Compression.TheoryCompletion.ScientificClosure.dualDrive_rejected_sound`
  - `UEOT.V3.Compression.TheoryCompletion.ScientificClosure.dualDrive_compatible_sound`

相关冻结 P-ID：[P-DDH-04](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ddh-04), [P-DDH-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ddh-05).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

秩零／一可以补零经 ℝ²，但不能套非退化 GL₂ 唯一性；逐环境秩二不保证同一共同 H；同源秩三见 CSX-27。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

说明共享输入空间、全部受测响应、线性化点及噪声事件；先作可识别性／规范审查，再赋予坐标领域含义。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明全局非线性二维、物理 Π/Φ 唯一性或有限数据下的精确零奇异值。

<a id="csx-11"></a>

### CSX-11 · 实际连续源的恢复、HJB 与完整路径 KL

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-11`

<!-- contract-field: name -->

#### 2. 精确名称

实际连续源的恢复、HJB 与完整路径 KL

<!-- contract-field: definition -->

#### 3. 数学定义

三个独立来源分支分别构造实际 OU 律、特定 Brownian 控制家族与其实际期望、完整可预测 L² 积分及有界倾斜后的 Q。原 v3 的漂移、ItoRun 和 KL 字段由对应源桥履行。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

OU 的 κ>0、σ、x₀ 与有限区间；HJB 的特定 V=2+sin 和登记的有界可预测控制；KL 的有限 T、完整可预测 L² 输入及可测路径读出。三类不是任意 SDE 的统一黑箱。

<!-- contract-field: assumptions -->

#### 5. 必要假设

保留各源的 Brownian、适应／可预测、L²、实际控制界、C²／终端及可积条件。KL 的有界条件在原输入律下 a.e. 成立；实际 Q、积分和能量须来自同一构造。HJB 不删去无限目标所需的趋近字段。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

OU 对每个 t∈[0,T] 给期望界；HJB 对该家族全部允许控制给值最优性；KL 对每个合格输入及每个可测路径读出给等式／数据处理界。

<!-- contract-field: conclusion -->

#### 7. 结论

OU 二阶矩含不可删的噪声底；特定 HJB 的实际控制族达到验证值；完整路径 KL 等于 Q 下半能量，观察 KL 至多该值。

<!-- contract-formula: CSX-11 -->

$$
\mathbb E[X_t^2]\le e^{-2\kappa t}x_0^2+\frac{\sigma^2}{2\kappa}(1-e^{-2\kappa t});\qquad D(Q\|P)=\tfrac12\mathbb E_Q E_T,\quad D(Q_R\|P_R)\le D(Q\|P).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际源工厂和分析定理连接原 P-REC-02、P-CTL-03、P-KL-05。标准 Itô／Girsanov／数据处理理论的归因由当前书稿保留；新贡献是此处明确来源的形式连接。

书稿定位：39.28;39.34;39.39;39.46 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)
- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

列出的生产端点已在现行源中；本轮不重编译、不把任意消费记录自动视为已构造的过程。

- [OUPhysicalRecoverySource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/OUPhysicalRecoverySource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.OUPhysicalRecoverySource.physical_source_p_rec_02`
- [BrownianControlledHJBSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianControlledHJBSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianControlledHJBSource.actual_p_ctl_03`
- [BrownianBoundedTerminalKLSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianBoundedTerminalKLSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedTerminalKLSource.actual_p_kl_05`

相关冻结 P-ID：[P-REC-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-rec-02), [P-CTL-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-03), [P-KL-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-kl-05).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

噪声非零时不能去掉 OU 噪声底；观察可丢信息而使 KL 严格减小；有限期验证数据不自动给任意无限期最优性。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

逐分支提供同一实际律、控制／积分域、正则性和读出；任何一般化须另建生产者，不能仅填入已包含结论的 record。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不支持所有非线性 SDE、所有 C² 候选、无界任意倾斜、观察等熵，或未经单位校准的热力学耗散等式。

<a id="csx-12"></a>

### CSX-12 · 由一般有限 primitive 矩阵生产 Perron 证书

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-12`

<!-- contract-field: name -->

#### 2. 精确名称

由一般有限 primitive 矩阵生产 Perron 证书

<!-- contract-field: definition -->

#### 3. 数学定义

对同一有限 primitive 非负矩阵 M，从其机制假设生产正左右特征向量、正增长根、根的单性及归一化幂的秩一极限，再组装原 KPF01Certificate。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

非空有限指标集上的实矩阵；primitive 性为该实际 M 的条件。

<!-- contract-field: assumptions -->

#### 5. 必要假设

仅在明确的 primitive 矩阵域内调用工厂；欲解释为出生／人口，还须另外把 M 的各行绑定到同一真实源的期望输出。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个合格 M 构造证书，不把归一化幂极限作为外给字段；原消费者随后对其合格初态给原结论。

<!-- contract-field: conclusion -->

#### 7. 结论

原谱字段的来源义务由工厂关闭，P-EVO-03 可在该一般矩阵域内消费实际生产的证书。

<!-- contract-formula: CSX-12 -->

$$
\rho^{-n}M^n\longrightarrow\frac{r\ell^{\mathsf T}}{\ell^{\mathsf T}r},\qquad r>0,\ \ell>0,\ \rho>0.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

有限维正矩阵谱论；使用既有正性和紧性／极限工具构造，而非重用假定所求极限的证书。

书稿定位：25;39.72 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FROZEN_SOURCE_CUT.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/general_perron_compact_spectral_source_v1/FROZEN_SOURCE_CUT.json)
- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

certificateOfPrimitive 与原命题的实际消费者均有既有 Lean 端点；源码身份复用已登记 receipt。

- [PrimitivePerronClosure.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PrimitivePerronClosure.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure.certificateOfPrimitive`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure.actual_root_simple`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure.actual_power_limit`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PrimitivePerronClosure.actual_p_evo_03`

相关冻结 P-ID：[P-EVO-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-03).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

可约的程序×标签展开矩阵可有多个闭块；不能把其中一个 primitive 身体块的唯一性搬到全矩阵。正期望增长也允许真实灭绝。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

证明 primitive 性并说明行方向、类型、均值与实际个体的关系；若需谱系，另用 CSX-24 的真实血缘桥。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不从矩阵代数产生身份、严格出生、路径级不灭绝或自然选择的规范最优性。

<a id="csx-13"></a>

### CSX-13 · 实际 killed 半群的紧谱绑定

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-13`

<!-- contract-field: name -->

#### 2. 精确名称

实际 killed 半群的紧谱绑定

<!-- contract-field: definition -->

#### 3. 数学定义

在有限测度 m 上，用紧对称 resolvent R、L² 轨道 S(t) 与实际 killed 演化律的密度等式生产原谱接口；q 为正主特征函数 φ 的归一化密度。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

实 Hilbert 空间 L²(m)；给定初始密度 g≥0、∫g=1 和单位正特征函数 φ。结论绑定这一实际初态与 killed 源。

<!-- contract-field: assumptions -->

#### 5. 必要假设

需 ResolventOrbit、S(1) 收缩、各演化密度非负、初始及所有 t 的实际密度匹配；λ₁>0、λ₂>λ₁；Rφ=(1+λ₁)⁻¹φ、正交补 Rayleigh 界及非零正交第二特征向量。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每组上述实际数据，存在 q、C_g、c_g>0、t₀，使所有 t≥t₀ 的条件存活律及存活质量满足界；常数依赖 g。

<!-- contract-field: conclusion -->

#### 7. 结论

由较底层的谱／源条件构造 SpectralData 并调用原 P-QSD-04，得到实际条件律向 q 的 TV 速率及存活质量下界。

<!-- contract-formula: CSX-13 -->

$$
\|\mathcal L(X_t\mid\tau>t)-q\|_{\rm TV}\le C_g e^{-(\lambda_2-\lambda_1)t},\qquad \Pr(\tau>t)\ge c_g e^{-\lambda_1t}\quad(t\ge t_0).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

紧对称算子分解及实际 killed-law 绑定。工厂不以原 SpectralData 作为输入；演化密度匹配仍是需由消费者证明的源前提。

书稿定位：10;39.73–39.74 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FROZEN_SOURCE_CUT.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/general_perron_compact_spectral_source_v1/FROZEN_SOURCE_CUT.json)
- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

ofActualSource／actual_p_qsd_04 等为既有 Lean；非零余项实例是明确的有限可逆源，不能称为一般 Brownian 示例。

- [CompactKilledSpectralBinding.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CompactKilledSpectralBinding.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactKilledSpectralBinding.ofActualSource`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CompactKilledSpectralBinding.actual_p_qsd_04`

相关冻结 P-ID：[P-QSD-04](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-qsd-04).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

没有实际密度匹配，抽象算子结论不能当实际过程 QSD；无正交谱隙不产生所列速率。条件存活收敛不等于原过程永久存活。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

证明 resolvent/semigroup、正性、初态与实际律的一致性，保留常数和时间门槛对初态的依赖。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不自动覆盖任意扩散、任意边界条件、非对称算子、量子 CP 半群或全部初态的统一常数。

<a id="csx-14"></a>

### CSX-14 · literal 事务、当前亲本与同一联合律的生命周期

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-14`

<!-- contract-field: name -->

#### 2. 精确名称

literal 事务、当前亲本与同一联合律的生命周期

<!-- contract-field: definition -->

#### 3. 数学定义

literal Register 家族以原 Store、ClockedOrganism、真实交易、当前 root 查找和允许记录为对象；有限 episode 的真实末 root、余额和已发生父链被送入随后登记的执行源。保留对象与严格新生对象分开。Price 分支的 N 是本轮旧 cohort 的亲本数，B 是这批亲本实际产生的严格出生数（不含前置 first birth）；z 为 owner-depth，传递差为1。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

离散原生执行、有限 episode、可数记录律与相应联合核；不是 CSX-18 的并行全人口再生时钟。活动端口 Legitimate 与全身体 BodyGoal 分属不同谓词。

<!-- contract-field: assumptions -->

#### 5. 必要假设

明确程序、允许传感器、身份/时钟与父标记、读取/写入费用、合法派发和源匹配。连接长期阶段时另登记供给、cap、初储备和原余额；world lookup 是证明桥，不自动成为控制器观察。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

原生与 primitive 的记录运输对所登记执行和同一噪声／程序成立；条件源定理在同一联合律及合法条件下 a.e. 成立。Price 的归一式只在实际总出生质量 B>0 时调用。

<!-- contract-field: conclusion -->

#### 7. 结论

真实有限边缘、实际同一 founder／current parent、执行后的余额、出生与谱系记录和相应 P6/native/Price 消费者可以在同一联合律下连接；B=0 保留未归一关系，不伪造出生分布。

<!-- contract-formula: CSX-14 -->

$$
\overline w\,(\overline z_{\rm child}-\overline z_{\rm parent})=\operatorname{Cov}_{\rm parent}(w,z)+\overline w,\qquad\overline w=B/N>0,\quad\Delta z=1\ \text{(owner-depth)}.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

复用真实事务投影、条件核、父链与实际 cohort 的来源证明；完整语义由列出的 current-parent 汇合端点及书稿各来源节给出。Price 是代数恒等式，不单独承担因果解释。

书稿定位：39.1–39.8;39.20–39.25;39.41;39.49–39.50;39.53;39.56–39.59;39.62–39.70 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)
- [REGISTERED_INTERFACES_CLOSURE_V1.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/REGISTERED_INTERFACES_CLOSURE_V1.md)
- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 来源与汇合消费者；本卡不重称所有历史 CONTRACT 目标都已无条件证明，附属边界由当前源包与书面证明定位。

- [RegisterPopulationCurrentParentContinuation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterPopulationCurrentParentContinuation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.finite_marginal`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.current_same_founder`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.same_joint_current_lifecycle`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.same_joint_p6_native_price`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.conditional_returned_word_source`

相关冻结 P-ID：[P-PROC-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-proc-01), [P-COMP-07](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-comp-07), [P-EVO-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-01), [P-BRG-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-brg-01), [P-BRG-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-brg-02), [P-CORE-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-core-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

有限永久个体集、严格增代且处处正规化的永久出生关系不能同时要求；保留亲本不是新生。轮末首次命中与微步命中不同。相同可见块记录可能隐藏不同 passive 状态，不能反向识别全身体。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

逐项给出实际记录等式、父身份与计时一致性；可数块运输另须其可测性／可求和条件。对 P5/P6/P8/P9/P12 的装配保留共同事件和同一执行，不把同型字段当同源证明。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不据 Price 推出适应、全体无限存活、自主身份或自然目的；有限期真实记录也不自动给无限期可支付性。

<a id="csx-15"></a>

### CSX-15 · 未知持久源、有限钱包的实际联合决策

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-15`

<!-- contract-field: name -->

#### 2. 精确名称

未知持久源、有限钱包的实际联合决策

<!-- contract-field: definition -->

#### 3. 数学定义

PR441 从有限有理先验只抽一次参数 θ；策略依允许的 birth/paidWrite 收据和自己的记忆，联合选择学习与部署动作。J 是同一原生交易的有限期折扣净值、零终端价值。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

有限时域、公开目标、地址0/1与原菜单、正写费、同一无收入钱包；stop 从本步起承诺 root idle。比较类为原实际允许历史上的实随机因果策略。

<!-- contract-field: assumptions -->

#### 5. 必要假设

参数持久而非每步重抽；在正概率历史上满足原支持合法性及预付 cap；原生 Realization 与源模型保持收据、成本、身份、None 和实际父链。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个合格有限模型和当前正支持历史，求解返回表不劣于每个允许的任意记忆、实随机竞争策略。闭式特例另要求 B=c 及登记高价条件。

<!-- contract-field: conclusion -->

#### 7. 结论

同一返回物在真实原生交易中实现源 Bellman 值并满足全比较类最优性及实际支付，不只在代理状态表中最优。

<!-- contract-formula: CSX-15 -->

$$
\mathbb E[J_{\rm native}(\pi)\mid h]\le\mathbb E[J_{\rm native}(\pi_{\rm returned})\mid h]\qquad(\pi\text{ supported-admissible}).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

有限动态规划、联合后验递推和原任意实随机策略的原生值运输；真实支付由同一执行源逐前缀证明。

书稿定位：39.75–39.81 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [README.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/joint_decision_closure_v1/README.md)
- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean returned_native_optimal／value 端点；源码不在本轮改写。

- [RegisterJointDecisionNativeConsumer.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterJointDecisionNativeConsumer.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer.returned_native_value`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer.returned_native_optimal`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterJointDecisionNativeConsumer.returned_native_payment`

相关冻结 P-ID：[P-PRED-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-pred-01), [P-INV-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-inv-05), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01), [P-QUO-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-quo-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

重抽 θ 会改变学习价值；把机制和身体边缘相乘会丢依赖；用期望预算代替每个正支持前缀预付会扩大策略类。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

使用相同先验、记录权限、成本、时钟、终端评价和真实钱包；若增加地址、传感器或收入，重新证明状态与优化合同。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明未知任意程序识别、无限人口 census 最优、无限期供给或一般 POMDP 多项式求解。

<a id="csx-16"></a>

### CSX-16 · 全动作充分表示与接受后正确的共享决策图

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-16`

<!-- contract-field: name -->

#### 2. 精确名称

全动作充分表示与接受后正确的共享决策图

<!-- contract-field: definition -->

#### 3. 数学定义

PR442 从 PR441 的允许历史提取 (t,q,s,f,k) 与计数后验，只将真正有信息的 00 记入计数；共享 DAG 的节点、动作、分支和 Bellman 值由 checker 验证。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

同一地址0/1、持久参数、原钱包和有限时域合同；returned 的类型为 Option，图是有限实际数组。

<!-- contract-field: assumptions -->

#### 5. 必要假设

充分状态对所有合法动作保持联合收据／状态律；图必须被 accept 接受，源与原生执行保持映射。生成器构造一个候选与该候选被接受是不同责任。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个已接受 Result 给原生正确性、最优性与节点界；不把有限示例成功提升为 ∀输入 returned≠none。

<!-- contract-field: conclusion -->

#### 7. 结论

同一已接受图的原生部署保持值和全比较类最优性；实际数组节点数至多 24(H+1)^4。

<!-- contract-formula: CSX-16 -->

$$
\operatorname{accept}(G)=\mathrm{true}\Longrightarrow\bigl(J_{\rm native}(G)=V^*,\quad \#G\le24(H+1)^4\bigr).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

允许历史的全动作充分性、checked-DAG soundness 与 THIS 返回物的原生桥；结果不同于只有静态接口或已选动作的模拟。

书稿定位：39.82–39.88 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/THEOREM_INDEX.md)
- [API_BOUNDARIES.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/API_BOUNDARIES.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean Result 消费端点和实际执行核对；JSON 往返检查按执行证据记录，没有新增完整 Lean JSON 解码往返定理。

- [RegisterDecisionRepresentation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterDecisionRepresentation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentation.result_node_bound`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentation.result_native_value`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterDecisionRepresentation.result_native_optimal`

相关冻结 P-ID：[P-PRED-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-pred-01), [P-PRED-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-pred-03), [P-QUO-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-quo-01), [P-ALG-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-alg-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

地址2的可达扩展可破坏旧统计充分性，必须细化状态；拒绝候选不享有接受后合同。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

先检查 Option/accept，再部署同一图；保持成本、None、身份和父链；分别报告节点数、整数／有理位数及运行成本。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

节点界不等于总内存或位复杂度界；不承诺总生成完备性，也不授权任意动作菜单。

<a id="csx-17"></a>

### CSX-17 · 实际机制分辨、允许实验与最坏后悔

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-17`

<!-- contract-field: name -->

#### 2. 精确名称

实际机制分辨、允许实验与最坏后悔

<!-- contract-field: definition -->

#### 3. 数学定义

机制 S 为登记的局部故障源，G 在故障后追加全 Store 共同损坏；两者共用允许收据与钱包。实验分辨距离是同一允许实验在两源下的 TV；regret 比较各机制已知时的同信息最优值。本卡 r 是 normal／repair chance，故障概率为1−r。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

真实有限原生 Store、任意允许历史实随机策略和独立私种子；分辨公式使用实 r∈[0,1]。后悔数值限定冻结 H3 参数与原预算。

<!-- contract-field: assumptions -->

#### 5. 必要假设

机制在执行前固定且与私种子独立；保留唯一坏 founder、地址菜单、真实全局故障时序及前缀 cap。H3 的精确距离达到需 B≥c>0；两个后悔常数精确绑定 r=1/2、H=3、B=2、c=1、λ=1/4、d=1、goal=true，其中 λ 是该有限期净值的费用权重。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

分辨上界覆盖所有允许实验，并有一可预付分离表达到；后悔下界覆盖原任意实随机竞争者，同一个私随机返回物达到该下界。H≤2 另有共同最优者。

<!-- contract-field: conclusion -->

#### 7. 结论

H3 最大实验距离为 r²(1−r)；root-only、H≤2、低钱包及 r=0/1 有相应零界。冻结 H3 的确定性最优最坏后悔为 1/32，私随机为 3/128。

<!-- contract-formula: CSX-17 -->

$$
\Delta_{3,B}=r^2(1-r)\ (B\ge c>0);\qquad R^*_{\rm det}=1/32,\quad R^*_{\rm rand}=3/128\quad\text{(frozen H3)}.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

真实 primitive 路径约束、同源耦合、私随机有限树归约与有限机制 Bayes 对偶证书。终端分辨不自动产生同一时限内可消费的后续控制收益。

书稿定位：39.89–39.95 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/THEOREM_INDEX.md)
- [AXIOM_AUDIT.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1/checks/AXIOM_AUDIT.json)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 一般界与原生端点；冻结数值 exact_two_data／exact_cached_data 使用 native_decide，保留其局部 Lean.ofReduceBool 等信任依赖。不能将该信任泛化到每个一般定理，亦不能省略。

- [RegisterMechanismExperimentSharp.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismExperimentSharp.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismExperimentSharp.H3_experiment_sharp`
- [RegisterMechanismDecision.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecision.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecision.returned_contract`
- [RegisterMechanismDecisionNativeConsumer.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterMechanismDecisionNativeConsumer.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNativeConsumer.all_native_regret_lower`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterMechanismDecisionNativeConsumer.returned_native_payment`

相关冻结 P-ID：[P-INV-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-inv-02), [P-INV-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-inv-05), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01), [P-INFO-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-info-05).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

相同前缀下 S/G 的机制—身体联合后验可不同；旧 S observer 不能直接迁到 G。H2 的共同最优与冻结 H3 正后悔不冲突。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

保留联合后验、同一允许历史、真实支付和独立私种子；明确采用一般实验定理还是冻结数值结果，并携带对应信任范围。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不将 H3 常数推广为所有期限／参数，不把世界真实机制、隐藏 Store 或噪声交给动作选择器。

<a id="csx-18"></a>

### CSX-18 · 实际可损坏程序的付费再生及不可恢复边界

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-18`

<!-- contract-field: name -->

#### 2. 精确名称

实际可损坏程序的付费再生及不可恢复边界

<!-- contract-field: definition -->

#### 3. 数学定义

身体含 H/D 两行三位重复码、gate、bootstrap、静默 tag。θ₀=(care,care)，θ₁=(bloom,care)；损伤翻转活动码位并关 gate。先按修复前诊断选行，付费修复后重读实际码，再执行动作。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

此有限实际事务源；每个旧个体每 tick 自有资本1并获外供5，总6。care 操作费1、bloom费2，输出储备2；损伤修复费3。输出是原对象续存与至多一个严格新生，下一 tick 才执行。

<!-- contract-field: assumptions -->

#### 5. 必要假设

可恢复重复信息及 bootstrap 保留；修复阶段资金足3。整个 damaged/care 事务需完整6；damaged/bloom cap7 超出6，沿用原拒绝分支并退还供给，不能发明免费 wait。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个 θ、H/D 状态与 tag，真实修复 rank 分别为0／1；同一受损程序修复后读取自身 restored code。切断与资金反例在相应受限修复协议下成立。

<!-- contract-field: conclusion -->

#### 7. 结论

健康体无需修复；受损规范体一步恢复，支付3后余额3，再执行自己的程序。bootstrap 切断、修复阶段仅有2且无新供给、或两程序全部可区分信息擦除，分别破坏相应恢复承诺。

<!-- contract-formula: CSX-18 -->

$$
\operatorname{repairRank}(H)=0,\quad\operatorname{repairRank}(D)=1,\quad 6-3=3;\qquad \neg\exists f\ \text{recovering both fully erased programs}.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

逐实际码位和收费的修复关系、可恢复集迭代及同输入不可区分论证；该来源实例化原恢复／载体合同。

书稿定位：核心总论 I–III;core synthesis I–III — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [CLAIM_STATUS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/CLAIM_STATUS.md)
- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 来源、repair-rank 与反例端点；rank1 是噪声前修复阶段的结论。

- [CoreRegenerativeSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.actual_program_reads_restored_code`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.no_decoder_recovers_both_erased`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.damaged_bloom_rejected`
- [CoreRegenerativeRepair.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeRepair.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.healthy_repairRank_zero`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.damaged_repairRank_one`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.same_program_restores_then_reads`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.bootstrap_cut_not_repairable`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.underfunded_not_repairable`

相关冻结 P-ID：[P-REC-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-rec-01), [P-CAR-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-car-01), [P-CAR-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-car-03), [P-OMG-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-omg-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

新噪声可以再次造成损伤；rank1 不等于永久健康。访问阻断不同于物理擦除；非恒定响应也可没有非空 Ω，必须保留实际切断协议。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

证明实际干预、剩余信息、bootstrap、费用与供给时序；需要增长时继续使用同一源和自有 founder 的 CSX-22。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不支持无信息再生、无可信底座恢复、封闭零收入无限维持、所有故障可修或经验生命普适性。

<a id="csx-19"></a>

### CSX-19 · 由同一物理响应产生非空形成候选

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-19`

<!-- contract-field: name -->

#### 2. 精确名称

由同一物理响应产生非空形成候选

<!-- contract-field: definition -->

#### 3. 数学定义

在 CSX-18 的同一身体与事务上，取 tag=false 的四个规范初态为 formation seed；物理子部件覆盖该 seed，响应为登记的一次严格新生概率。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

固定有限 seed 与物理组件／删除协议；采用旧 Valid 参数域。该一次响应不是全部未来实验。

<!-- contract-field: assumptions -->

#### 5. 必要假设

保留实际代码、门和可信 bootstrap、完整物理 seed 的零缺陷、子组件覆盖及源响应非恒定；所列端点针对精确零缺陷形成家族。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个满足旧 Valid 的 p，登记的 actual formed-candidate 家族非空，不额外引入阈值参数。

<!-- contract-field: conclusion -->

#### 7. 结论

候选非空由实际响应差、零缺陷和 cover 导出，不以“已存在形成候选”作为假设；空载体保留正缺陷。

<!-- contract-formula: CSX-19 -->

$$
\Pr(B_1=1\mid\theta_1,H)=b+\gamma,\qquad \Pr(B_1=1\mid\theta_0,H/D\text{ or }\theta_1,D)=b,\qquad\gamma>0.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际程序出生概率、有限物理 cover 与原形成规则的来源消费。

书稿定位：核心总论 III;core synthesis III — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [CLAIM_PREMISE_CONSUMER_MATRIX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/CLAIM_PREMISE_CONSUMER_MATRIX.md)
- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean physical_children_cover_seed 与实际 formed-candidate 非空端点。

- [CoreRegenerativeFormation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeFormation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.physical_children_cover_seed`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.actual_formed_candidate_family_nonempty`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeSource.actual_formed_candidate_nonempty`

相关冻结 P-ID：[P-COMP-04](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-comp-04), [P-COMP-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-comp-05), [P-CAR-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-car-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

常量响应没有该严格识别间隔；删 bootstrap 可改变未来，不能将访问等价替代物理 frame。扩大未来任务可细分表示，见 CSX-26。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

指定形成对象、seed、覆盖、任务响应、切断权限及精确零缺陷条件；若要求全历史保持，另外证明对应协议。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不把这一有限形成实例提升为任意自然系统自创生、唯一真实边界或普遍非空 Ω。

<a id="csx-20"></a>

### CSX-20 · 有限行选择与实际全策略人口上界

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-20`

<!-- contract-field: name -->

#### 2. 精确名称

有限行选择与实际全策略人口上界

<!-- contract-field: definition -->

#### 3. 数学定义

一般行模型用 m(i,a,j) 表示类型 i 采取动作 a 的期望输出 j 数。选择器逐行组合矩阵；实际再生源把每个原动作的续存／新生矩绑定到该行。W_n 为实际人口的正特征权重总和。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

一般部分：有限非空类型与各类型有限非空动作集。源消费者：CSX-18 的实际 State/Branch/Policy 和旧 Valid 域；Policy 可按允许完整历史实随机选择整个请求词，允许同代请求相关。

<!-- contract-field: assumptions -->

#### 5. 必要假设

一般工厂需每个逐行选择矩阵 primitive；行替换必须仍为允许选择。实际消费者的请求先于本次世界噪声，支付与输出来自原事务；stop 为零行，拒绝为保留身份的单位行。“所有选择矩阵 primitive”只属于一般工厂分支，不用于包含 stop 零行／拒绝单位行的整个实际菜单；实际消费者使用显式正势逐动作验证，拒绝行依赖 ρ≥1。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

一般域存在一个选择器及正 r，使所有类型、所有动作的行作用≤ρr；实际源上对每个原 Policy、每个有限 n 给统一期望上界，登记最优内部程序有匹配双边常数。

<!-- contract-field: conclusion -->

#### 7. 结论

逐行最优谱率产生对所有原允许动作的正势上界；经真实条件矩传到人口历史，得到有限时域条件超鞅型不等式和期望增长控制。

<!-- contract-formula: CSX-20 -->

$$
\sum_j m(i,a,j)r_j\le\rho r_i,\qquad \mathbb E[W_{n+1}\mid\mathcal F_n]\le\rho W_n,\qquad \mathbb E N_n\le \rho^n W_0/\min_i r_i.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

一般有限选择器比较、单行替换与 Perron；实际逐个体输出矩、条件核线性性和有限历史归纳。

书稿定位：核心总论 IV;core synthesis IV — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)
- [CLAIM_PREMISE_CONSUMER_MATRIX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/CLAIM_PREMISE_CONSUMER_MATRIX.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有一般 Lean 选择器定理及实际全 Policy 人口端点。条件矩接口不是本轮新构造的共同无限时间 Mathlib Martingale。

- [FiniteSourceGrowthControl.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteSourceGrowthControl.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteSourceGrowthControl.exists_optimal_selector`
- [CoreRegenerativeControlPopulation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.actual_population_upper`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.actual_population_bounds`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.actual_supermartingale`

相关冻结 P-ID：[P-EVO-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-03), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01), [P-EVO-04](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-04).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

只比较两个固定程序不足以证明全 Policy 上界；删除拒绝单位行会在亚临界域漏掉保持策略。均值行不自动承载真实祖先。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

证明真实行矩、允许行替换、付费和信息时序。不能把 primitive 性假设用于可约的整程序×tag矩阵；较宽参数域改用 CSX-21。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明每个有限 n 的人数最大化、逐路径增长、个体永生或普遍适应。

<a id="csx-21"></a>

### CSX-21 · 严格正概率域的最小统一期望增长底数

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-21`

<!-- contract-field: name -->

#### 2. 精确名称

严格正概率域的最小统一期望增长底数

<!-- contract-field: definition -->

#### 3. 数学定义

p=(s,δ,b,γ,q)，k_c=s+b，k_b=s−δ+b+γ，λ₀=k_c，λ₁=(1−q)k_b+qk_c。HasExpectedGrowth(K,I,ρ) 指存在 c,C>0，使所有有限 n 的 E N_n 落在 cρⁿ 与 Cρⁿ 之间。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

ProbabilityValid：0<δ<s<1、0<b、0<γ、b+γ<1、0<q<1。原36个噪声原子严格正；原动作、cap、拒绝、遗传和 Policy 不变。初态 I 为实际非空规范人口。

<!-- contract-field: assumptions -->

#### 5. 必要假设

同一真实源与初态；统一上界要求一个 C 同时覆盖全部原 Policy 和全部 n。旧 Valid 恰为 ProbabilityValid 加 δ<γ 与 1<s+b；这个扩域只服务已列增长端点。Lean 的 UniformExpectedUpper 只写 ∃C:ℝ；非空初态在 n=0 强制 C≥|I|>0，因此这里的正 C 表述等价。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个合格 p,I，ρ* 是集合 {ρ>0:∃C>0 ∀K:Policy ∀n,E_K N_n≤Cρⁿ} 的最小元素；存在实际 optimalPolicy 达到该底数的双边界。

<!-- contract-field: conclusion -->

#### 7. 结论

ρ*=max(1,λ₀,λ₁)。健康态选较优 care/bloom；损伤态在适当域选 care，亚临界保持使用原 damaged/bloom 拒绝分支。

<!-- contract-formula: CSX-21 -->

$$
\rho_*=\max\{1,\lambda_0,\lambda_1\}=\min\{\rho>0:\exists C>0\ \forall K:\mathrm{Policy}\ \forall n,\ \mathbb E_K N_n\le C\rho^n\}.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际全动作正势行界、同一人口条件矩及达到者双边界；正序列指数底数比较给最小性。

书稿定位：核心总论 IV;core synthesis IV;PR447 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [README.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/README.md)
- [LEAN_VALIDATION.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/LEAN_VALIDATION.json)
- [SOURCE_BINDING.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/SOURCE_BINDING.json)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

三个 PR447 生产模块已有历史编译 receipt 且当前源码匹配。本轮不重编译。正次根极限及一般策略 limsup 是双边／上界的书面分析推论，没有冒充新 Lean 端点。

- [CoreRegenerativeGrowthClassification.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthClassification.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.valid_iff_probability_advantage_supercritical`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.optimalRate_formula`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthClassification.actual_row_bound`
- [CoreRegenerativeGrowthPopulation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.optimal_population_upper`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.optimal_hasExpectedGrowth`
- [CoreRegenerativeGrowthAttainment.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.optimalRate_isLeast_uniform_upper`

相关冻结 P-ID：[P-EVO-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-03), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

在 λ₀<1 且 λ₁<1 时，ρ*=1 由原拒绝保持支撑，两个现有内部程序均不达到；这不排除更广 Policy 中混合修复与拒绝。q=0/1 或零原子端点不在本卡域内。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

先验证 ProbabilityValid 和非空初态；区别统一指数、有限期人数、存活及随机比例。旧反馈定理继续按 CSX-23 的旧 Valid 调用。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不宣称全部策略各自根极限存在、不把最小统一底数称为每期人数最优，也不扩展旧反馈或保证正存活。

<a id="csx-22"></a>

### CSX-22 · 两内部程序达到最优的 iff 与同一受损 founder

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-22`

<!-- contract-field: name -->

#### 2. 精确名称

两内部程序达到最优的 iff 与同一受损 founder

<!-- contract-field: definition -->

#### 3. 数学定义

programPolicy θ 首先是作用于任意人口的公开请求规则；只有该人口每个身体携带 θ、执行修复后实际读码且遗传保持 θ 时，才可解释为内部程序。两程序的增长率分别 λ₀、λ₁，见 CSX-21。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

CSX-21 的严格正域、非空规范人口；共同修复—达到见证使用该 θ 自己的受损 founderState，而不是借用另一程序的身体。

<!-- contract-field: assumptions -->

#### 5. 必要假设

全部原请求、支付、噪声、继承规则保持；内部解释需 ProgramPopulation θ 以及实际正质量 branch 的内部执行桥。两个程序参数域均含等号边界。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个 ProbabilityValid p 及合格非空初态，programPolicy θ 具有 ρ* 双边增长当且仅当对应区域条件；对其自有受损 founder，同时成立实际付费恢复与上述 iff。

<!-- contract-field: conclusion -->

#### 7. 结论

θ₀ 达到当且仅当 γ≤δ 且 k_c≥1；θ₁ 达到当且仅当 δ≤γ 且 λ₁≥1。同一受损身体支付3并恢复自己的程序，再实现所在区域的最优增长。

<!-- contract-formula: CSX-22 -->

$$
\theta_0\text{ attains }\rho_*\iff(\gamma\le\delta\land k_c\ge1);\qquad\theta_1\text{ attains }\rho_*\iff(\delta\le\gamma\land\lambda_1\ge1).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际各程序行的特征等式、双边增长、指数底数唯一性与代数区域分类；同一 founder 的恢复等式由 CSX-18 原源给出。

书稿定位：核心总论 IV;core synthesis IV;PR447 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [README.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/README.md)
- [LEAN_VALIDATION.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_growth_classification_v1/LEAN_VALIDATION.json)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean iff 与 same_damaged_program_repairs_and_attains_iff；原公开请求规则到内部执行有单独端点，不只名称相同。

- [CoreRegenerativeGrowthPopulation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthPopulation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.programPolicy_positive_branch_is_internal`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.founder_program`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthPopulation.damaged_founder_paid_repair`
- [CoreRegenerativeGrowthAttainment.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeGrowthAttainment.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.false_program_attains_iff`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.true_program_attains_iff`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.same_damaged_program_repairs_and_attains_iff`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeGrowthAttainment.subcritical_existing_programs_do_not_attain`

相关冻结 P-ID：[P-EVO-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-03), [P-REC-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-rec-01), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

把 θ₁ 规则施于 θ₀ 人口可作为外部请求策略，却不能称每个个体执行自己的 θ₁ 代码。两现有程序在严格亚临界区不达到，但一般策略类更广。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

明确是请求规则结果还是内部程序结果；提交 carries-program、真实修复读码和代际继承证明，并使用同一实际初体。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明所有可修复程序最优、修复与增长普遍等价、每个时刻健康或任何程序都能在无供给下自维持。

<a id="csx-23"></a>

### CSX-23 · 实际继承反馈、有限 cohorts 与比例反例

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-23`

<!-- contract-field: name -->

#### 2. 精确名称

实际继承反馈、有限 cohorts 与比例反例

<!-- contract-field: definition -->

#### 3. 数学定义

一个 cohort 从健康 θ₀、健康 θ₁ 各一个开始，按实际程序继承树演化至 T。n 个独立、分别付资的 cohort 汇总 inferior-count L 与 total N；随机份额 N=0 计失败。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

旧 Valid（CSX-21 的严格正域再加 δ<γ、1<s+b）；有限 T,n，0<ε≤1。这里的健康双 founder 不等于 CSX-22 的单受损共同见证。

<!-- contract-field: assumptions -->

#### 5. 必要假设

cohorts 独立且内部使用原实际噪声、程序和付费；实际二阶矩有限，E N>0。先选 T 降低均值劣势，再选 n 控制随机比例误差。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个 ε∈(0,1]、η>0，可选择有限 T 和正 n，使所登记有限选择成功概率≥1−η；对固定 T,n 给所列显式风险界与源资源上界。

<!-- contract-field: conclusion -->

#### 7. 结论

实际随机份额集中于均值比，其失败概率由实际方差控制；付费来源给 n[2+10(2^T−1)] 资源上界。高期望增长不排除最优谱系灭绝。

<!-- contract-formula: CSX-23 -->

$$
\Pr\!\left(N_n=0\ \text{or}\ [N_n>0\ \text{and}\ |L_n/N_n-\mathbb E L/\mathbb E N|>\varepsilon]\right)\le\frac{9(\operatorname{Var}L+\operatorname{Var}N)}{n\varepsilon^2(\mathbb E N)^2},\qquad R_{T,n}\le n[2+10(2^T-1)].
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际源均值／二阶矩、独立 cohort 的方差缩减与比率事件分解；常数9（及对应选择消费者的36）保留其原条件。

书稿定位：核心总论 V;core synthesis V — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)
- [CLAIM_STATUS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/CLAIM_STATUS.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 实际反馈和资源端点；本轮不重新运行 cohort 模拟或扩大参数域。

- [CoreRegenerativeFeedback.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeFeedback.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedback.actual_cohort_feedback`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedback.exists_finite_cohort_selection`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeFeedback.actual_sample_resource_bound`

相关冻结 P-ID：[P-EVO-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-01), [P-EVO-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-03), [P-STAT-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-stat-01), [P-REF-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ref-03).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

在 p=(s,δ,b,γ,q)=(3/4,1/8,3/8,1/4,1/3)、两个健康 founder、T=1 的登记实例，以下三个数都针对较优 θ₁ 的份额，非上式劣势 L/N：均值比10/19、零延拓份额期望2095/4096、条件非零期望2095/4006，彼此不同。同一实例全灭概率45/2048，优者灭绝而劣者非零概率243/2048。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

保留 cohort 来源、独立性、T 后 n 的量词、零人口失败及资源账单；共同噪声需要重建集中界。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不支持固定 n 无限期几乎必胜、均值比等于期望比例、条件存活等于无条件份额，或 ProbabilityValid 全域中的同一反馈常数。

<a id="csx-24"></a>

### CSX-24 · 实际标记血缘的 many-to-one 恒等式

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-24`

<!-- contract-field: name -->

#### 2. 精确名称

实际标记血缘的 many-to-one 恒等式

<!-- contract-field: definition -->

#### 3. 数学定义

从 CSX-18 的真实身份、父指针及 retained/newborn 标记构造祖先路径；均值矩阵 M 包含续存与新生两部分。以正 Perron 向量 r 和 λ 构造带标记 h-transform 核。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

实际 θ₁ 程序的继承树、旧 Valid、任意有限 T 和实值带标记路径测试 F；该固定端点不宣称全部程序／扩展参数域。

<!-- contract-field: assumptions -->

#### 5. 必要假设

初体确实携带 θ₁；实际步保留身份、出生时间与父边；M=L+B 的各部分来自同一执行源。带标记核需完整区分原对象续存与严格新生。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个合格初体类型 i、T 和 F，真实后代加权和的期望等于同一标记路径链的期望乘 λᵀr_i。

<!-- contract-field: conclusion -->

#### 7. 结论

many-to-one 是实际血缘测试的恒等式；忘掉标记可得相应未标记 Q 核，但不能反向补回标记语义。

<!-- contract-formula: CSX-24 -->

$$
\mathbb E\!\left[\sum_{u\in\mathcal N_T}r_{\mathrm{type}(u)}F(\mathrm{ancestry}(u))\right]=\lambda^T r_i\,\mathbb E_i^{\widehat Q}[F],\qquad Q_{ij}=M_{ij}r_j/(\lambda r_i).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

原事务的 retained/newborn 身份引理、同源第一矩与有限谱系归纳；不以抽象均值矩阵代替祖先来源。

书稿定位：核心总论 V;core synthesis V — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)
- [CLAIM_PREMISE_CONSUMER_MATRIX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/CLAIM_PREMISE_CONSUMER_MATRIX.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean actual_marked_many_to_one 及标记核／语义端点。

- [CoreRegenerativeLineage.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeLineage.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage.actualLineageSemantics`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage.retained_is_same_object`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage.newborn_is_strict_offspring`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage.actual_marked_many_to_one`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeLineage.markedKernel_unmarked`

相关冻结 P-ID：[P-EVO-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-02), [P-EVO-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-evo-03), [P-QSD-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-qsd-03).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

把所有 M 输出都称严格子代会把续存误作生殖；Q 加权抽样不等于均匀抽一个活体。固定 p=(3/4,1/8,3/8,1/4,1/3) 时，登记实例的原组成 (2/3,1/3) 与加权 (20/29,9/29) 不同。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

同一实际树、同一权重和相应标记测试必须保持；若将 Q 当控制律，另证明凸包可实现性、可见信息纤维一致及资源条件。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不从统计倾斜推出执行权限，不从平均谱矩推出严格出生，不从 many-to-one 推出某条真实谱系永存。

<a id="csx-25"></a>

### CSX-25 · 实际全历史与全策略评价的合法表示商

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-25`

<!-- contract-field: name -->

#### 2. 精确名称

实际全历史与全策略评价的合法表示商

<!-- contract-field: definition -->

#### 3. 数学定义

商映射只擦除静默 tag；身体 H/D、gate、程序、交易收费、refund、动作、身份、父指针和出生时间仍保留。对人口 State、Branch、next 和整个允许历史施加同一擦除。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

CSX-18 的有限实际源及原全部 Policy；有限期限和 tag 不变的终态／完整公开历史测试。概率解释采用合法参数域。

<!-- contract-field: assumptions -->

#### 5. 必要假设

逐事务修复、执行与联合记录的交换等式；初态及完整人口核相容；保留政策信息权限。一般实权重恒等式只有在权重合法归一时才称概率律。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对任意原 Policy、任意有限期限、任意相应拉回测试，期望相等；对于 tag 不变测试，全部允许策略可达到值的集合相等。

<!-- contract-field: conclusion -->

#### 7. 结论

这个非单射商保留实际全记录和有限人口未来的相关律与评价；它不只保留静态转移矩阵。

<!-- contract-formula: CSX-25 -->

$$
\mathbb E_{K,I}[F\circ e]=\mathbb E_{K,e(I)}[F],\qquad\{V_F(K,I):K\in\Pi_{\rm public}\}=\{V_F(K,e(I)):K\in\Pi_{\rm public}\}\quad(F\text{ tag-invariant}).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际局部联合记录交换、有限分支 pushforward，以及相同 K、相同公开历史下的人口核归纳。原 Policy 只读公开历史，擦 tag 后使用同一个 K，因此全部此类策略的可达到值集合保持。

书稿定位：核心总论 VI;core synthesis VI — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [THEOREM_INDEX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/THEOREM_INDEX.md)
- [CLAIM_PREMISE_CONSUMER_MATRIX.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/core_theory_closure_v1/CLAIM_PREMISE_CONSUMER_MATRIX.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 真实源商及人口全法则／可达到值端点；不能用单个 MH=H M̄ 等式替代这些证明。

- [CoreRegenerativeQuotient.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeQuotient.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeQuotient.step_joint_record_commutes`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeQuotient.programStep_joint_record_commutes`
- [CoreRegenerativeControlPopulation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CoreRegenerativeControlPopulation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.populationExpectation_eraseState`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.attainable_test_values_eraseState`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.public_history_test_expectation_eq`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.CoreRegenerativeControlPopulation.census_test_expectation_eq`

相关冻结 P-ID：[P-QUO-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-quo-01), [P-QUO-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-quo-02), [P-DYN-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-dyn-01), [P-FAC-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-fac-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

擦除 H/D 会合并 cap 不同的动作；擦除 gate 可改变程序能否执行。程序×tag 全展开矩阵可约，与每个身体块的 primitive 性并不冲突。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

给出真正无声的坐标、全部记录与动作的相容性及测试不变性；改变读出或允许操作后重新验证商。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不支持任意压缩、无条件最小表示、全身体同一性或领域中所有同名对象的等价。

<a id="csx-26"></a>

### CSX-26 · 固定内部程序任务的 2／3／4 最小表示

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-26`

<!-- contract-field: name -->

#### 2. 精确名称

固定内部程序任务的 2／3／4 最小表示

<!-- contract-field: definition -->

#### 3. 数学定义

固定旧 Valid 参数、tag=false 的四初态 θ₀H、θ₀D、θ₁H、θ₁D，并运行各自内部程序。B_t 为第 t 步整个实际人口的严格新生数；R₁ 为首步实际修复费。等价指登记任务的全部指定联合律相同。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

四初态、固定程序权限及三个明确任务；不增加外部自适应控制。

<!-- contract-field: assumptions -->

#### 5. 必要假设

实际继承、噪声与收费不变；任务一只看 B₁，任务二看全部有限联合 (B₁,…,B_T)，任务三在任务二上加 R₁，或使用全部公开历史。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个旧 Valid p，任务二的等价要求所有有限 T；最小性在该四元初态集合及固定任务内判断。

<!-- contract-field: conclusion -->

#### 7. 结论

任务一两类 {θ₀H,θ₀D,θ₁D}/{θ₁H}；任务二三类 {θ₀H,θ₀D}/{θ₁D}/{θ₁H}；任务三四个单点类。

<!-- contract-formula: CSX-26 -->

$$
\#\mathcal C_{B_1}=2,\quad\#\mathcal C_{(B_1,\ldots,B_T),\,T<\infty}=3,\quad\#\mathcal C_{(B_1,\ldots,B_T,R_1),\,T<\infty}=4;\quad \mathbb E_{\theta_1D}B_2-\mathbb E_{\theta_0D}B_2=(s+b)(1-q)\gamma>0.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

一次出生概率区分类，θ₀H/D 的同噪声全路径耦合证明所有有限历史等价；B₂ 的严格期望差拆开 θ₁D，首修复费进一步拆开 H/D。当前书中有完整书面证明和精确算术核对。

书稿定位：核心总论 II，task-dependent-representation;core synthesis II — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [UEOT_MATHEMATICS.md](../../../mathematics/UEOT_MATHEMATICS.md)
- [UEOT_MATHEMATICS.en.md](../../../mathematics/UEOT_MATHEMATICS.en.md)
- [README.md](../../../mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

书面分类及精确检查层。实际源和组成引理已有 Lean，但该完整 2／3／4 分类没有在此登记专用完整 Lean 端点。

本卡没有登记独立 Lean 端点；证据层以上述文字为准。

相关冻结 P-ID：[P-PRED-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-pred-02), [P-INFO-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-info-02), [P-CAR-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-car-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

只看 (B₁,R₁) 仍不能拆开两个 D 初态，故不能偷写为四类；加入外部控制或改成本任务须重新分类。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

明确响应变量、整个有限联合族和允许程序，引用书面证明层；不得将该分类当全部身体／组织／身份的最小性。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明任意有限模型三类、自然系统低维、普遍预测本体或独立新增 Lean 覆盖数。

<a id="csx-27"></a>

### CSX-27 · 同一实际源的秩三响应与二维瓶颈边界

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-27`

<!-- contract-field: name -->

#### 2. 精确名称

同一实际源的秩三响应与二维瓶颈边界

<!-- contract-field: definition -->

#### 3. 数学定义

同一再生源固定 δ、γ，健康 θ₀ 执行 care；在允许的开三参数域 (s,b,q) 记录续存、严格新生、新生且受损三个公开事件。其概率响应为 F(s,b,q)=(s,b,bq)。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

旧 Valid 内的开三参数邻域，b>0；比较在此邻域成立的 C¹ 共同因子 F=g∘h，h 值域 ℝ²。

<!-- contract-field: assumptions -->

#### 5. 必要假设

三响应均来自同一源、同一执行与明确公开事件；参数变化保留合法严格不等式。瓶颈障碍使用 C¹ 及开三维域。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

每个该域内点的 DF 秩为3；不存在在该开邻域成立的 C¹ 共同二维因子。

<!-- contract-field: conclusion -->

#### 7. 结论

一个单标量评价或两个命名分量不保证完整响应共同二维；此例在原实际源内给出明确反例。

<!-- contract-formula: CSX-27 -->

$$
DF=\begin{pmatrix}1&0&0\\0&1&0\\0&q&b\end{pmatrix},\qquad\det DF=b>0,\qquad F\ne g\circ h\quad(h:U\subset\mathbb R^3\to\mathbb R^2,\ U\text{ open},\ g,h\in C^1).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际事件概率、直接 Jacobian 与链式法则 rank( Dg Dh )≤2 的矛盾；当前书面证明和精确算术核对。

书稿定位：23.4;核心总论 VII;core synthesis VII — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [UEOT_MATHEMATICS.md](../../../mathematics/UEOT_MATHEMATICS.md)
- [UEOT_MATHEMATICS.en.md](../../../mathematics/UEOT_MATHEMATICS.en.md)
- [README.md](../../../mathematics/review/CORE_DEFINITIVE_FREEZE_2026-11-11/README.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

书面反例；实际源概率部分已有形式依据，但此完整微分秩三论证没有登记专用 Lean 端点。

本卡没有登记独立 Lean 端点；证据层以上述文字为准。

相关冻结 P-ID：[P-DDH-04](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ddh-04), [P-DDH-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ddh-05).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

限制到二维子族可降低秩；不连续编码不满足 C¹ 前提。这三参数不是已独立校准的三种物理预算。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

保留输入域、响应组、可变参数和正则性；领域应用要另外证明这些事件与可操作参数的对应。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明自然普适维数为三、不禁止二维任务压缩、不否定 CSX-10 的条件线性定理。

<a id="csx-28"></a>

### CSX-28 · 实际有限响应表的最小载体与 blocker 枚举

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-28`

<!-- contract-field: name -->

#### 2. 精确名称

实际有限响应表的最小载体与 blocker 枚举

<!-- contract-field: definition -->

#### 3. 数学定义

给有限对象集 X、观察端口 V、表 O(x,v) 与目标响应 R(x)。不同目标的每对对象产生一条区分边 {v:O(x,v)≠O(x′,v)}；载体是击中每条区分边的端口集，最小载体是包含最小的此类集合。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

实际有限确定表、可判定观察及目标相等、覆盖端口的登记次序列表；算法的纯边结构部分可更一般，实际有限表接口按其有限输入运行。

<!-- contract-field: assumptions -->

#### 5. 必要假设

表完整并且各行属于同一目标任务；端口次序确实覆盖 V。要称物理删除还需实际干预与 frame 条件，不能由表击中关系自动补出。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个完整有限表，返回集合恰为全部最小载体，相应 blocker/cut 集合也准确；每个返回载体具有该任务的解码器。

<!-- contract-field: conclusion -->

#### 7. 结论

Berge 型前沿逐边保留已击中的候选或加入边元素，并最小化当前前沿；不必先生成全部 powerset。返回结果与原表的充分性／最小性双向对应。

<!-- contract-formula: CSX-28 -->

$$
S\text{ is sufficient}\iff\forall(x,x')\text{ with }R(x)\ne R(x'),\quad S\cap\{v:O(x,v)\ne O(x',v)\}\ne\varnothing.
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

表区分关系到 hitting set 的 iff、前沿更新的不变式与最小化正确性，再连接原载体／cut 定义。

书稿定位：12;13;39.38 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)
- [LEAN_API_SCOPE.md](../../../mathematics/LEAN_API_SCOPE.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

既有 Lean 原表正确性及可执行列表端点；运行复杂度保留实际输出量边界。

- [FiniteResponseCarrierFrontier.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/FiniteResponseCarrierFrontier.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier.sufficient_iff_hits`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier.carriers_iff_original`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier.decode_returned`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier.carrierList_iff_original`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.FiniteResponseCarrierFrontier.cutList_iff_original`

相关冻结 P-ID：[P-CAR-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-car-01), [P-CAR-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-car-02), [P-CAR-04](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-car-04), [P-OMG-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-omg-01), [P-ALG-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-alg-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

2m 个成对冗余端口可产生 2^m 个最小载体，因此显式列全输出可指数大；常量响应允许空载体，未知表不享有完整表的保证。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

提交真实表、目标、观察与列表覆盖；若用于实际物理切断，另证明删除语义及其对非删除部分的保持。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不声称多项式输出总时间、寻找一个载体的一般复杂性下界、最小物理本体或自然 Ω 必非空。

<a id="csx-29"></a>

### CSX-29 · 实际 Brownian 源、完整可预测积分、Itô 与固定 Q 底座

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-29`

<!-- contract-field: name -->

#### 2. 精确名称

实际 Brownian 源、完整可预测积分、Itô 与固定 Q 底座

<!-- contract-field: definition -->

#### 3. 数学定义

P 是从有限 Gaussian 律实际扩张得到的全非负实时间 sourceLaw；B 是在同一 P 上构造的连续修改。Hᵖ_T 是原自然滤过可预测 σ 代数下、实际 dt_T×P 的原生 L² 子空间，独立于 elementary 闭包定义；有限维分支使用乘积源 P_d 和整个联合过去。Iᵖ 由原字面有限随机和构造。固定有界标量输入 u 的原积分与原时间能量定义 D_A=exp(Iᵖ_Au−能量/2)、Q_A=D_A·P；其同一有界可预测代表 û 给 W=B−∫ûdt。H^{Q_A}_U 同样以原滤过及实际 dt_U×Q_A 独立定义。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

时间为 ℝ≥0；有限噪声维 d、状态维 m 可为零。P_d 上每个完整输入 f∈H^{P_d}_T 取值于 ℝᵈ，积分输出为标量；状态使用同源输入族 fʲ，j∈Fin m。dt_T 为有限限制 Lebesgue 测度，总质量 T，不是默认概率测度。固定 Q 分支是原标量源，换测度窗 A 与积分窗 U 各为任意有限非负实数，允许 U>A；g∈H^{Q_A}_U 不要求有界。

<!-- contract-field: assumptions -->

#### 5. 必要假设

P 积分仅需原完整可预测 L² 条件。QV 另给确定性非降分割 τₙ，从 0 到 T 且网格趋零，允许重复时刻；不加 f 的 L⁴ 或本质有界前提。带漂移 Itô 取实际 Y=x₀+∫βdt+(M^{fʲ})ʲ，其中 β 对整个联合过去真正强可预测且对每个原样本有统一范数界，φ∈C² 的原生 Fréchet 一阶导数和 Hessian 均有全局界。Q 的概率性、Girsanov 与全部后续 Q 积分另需原 u∈Hᵖ_A 且 |u|≤K 在 dt_A×P 下 AE，K≥0。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

对每个有限坐标集证明原 Gaussian 律；对每个固定 t，B_t 与原坐标 P-AE 相等。对每个固定完整 P 输入构造连续鞅版本，其与原积分的身份仍逐固定时刻 AE；固定字面有限输入可另证一个满测事件上的全时路径身份。QV 对每个固定 f 及每个满足条件的分割列成立；Itô 为每个给定 T、x₀、β、输入族和 φ 的终点 AE 恒等式。固定同一 Q_A 后，对每个 U、完整 g 和每个观察时刻给积分／条件过程及能量；不对不可数输入或时刻任取共同 AE 交。

<!-- contract-field: conclusion -->

#### 7. 结论

实际 sourceLaw 与连续 B 给真正 Brownian 来源。原 elementary 闭包与独立完整可预测域相等，Iᵖ 为保留原字面输出的连续线性等距；其同源连续过程为原滤过真鞅。真实路径平方和在 L¹ 收敛到原 dt 能量，并给实际读出的依概率收敛；同源交叉／加权构造导出带真实漂移的有限维状态 Itô。满足有界控制条件时 E_PD_A=1，W 在同一 Q_A 下为 Brownian，且对每个 s，未来增量过程 (W_{s+t}−W_s)_{t≥0} 独立于原 F_s。固定 Q_A 的原 elementary 闭包等于全部 H^{Q_A}_U，返回等距积分及原滤过真鞅、逐时截断身份、真实能量和原字面输出。

<!-- contract-formula: CSX-29 -->

$$
\begin{aligned}\mathcal H_T^{P_d}&=L^2_{\mathrm{pred}}(dt_T\otimes P_d;\mathbb R^d),&\|I_T^{P_d}f\|_2^2&=\mathbb E_{P_d}\!\int_0^T\|f_s\|^2\,ds,\\ \sum_i\bigl(M^f_{\tau_{n,i+1}}-M^f_{\tau_{n,i}}\bigr)^2&\xrightarrow{L^1(P_d)}\int_0^T\|f_s\|^2\,ds,\\Y_t&=x_0+\int_0^{t\wedge T}\beta_s\,ds+(M_t^{f^j})_j,\\ \phi(Y_T)&=\phi(x_0)+I_T^{P_d}\!\left(\sum_j\partial_j\phi(Y)f^j\right)+\int_0^TD\phi(Y_s)[\beta_s]\,ds\\&\quad+\frac12\sum_{j,k}\int_0^T\partial_{jk}\phi(Y_s)\langle f_s^j,f_s^k\rangle\,ds\qquad(P_d\text{-a.e.}),\\ \frac{dQ_A}{dP}&=\exp\!\left(I_A^Pu-\frac12\int_0^A\widehat u_s^2\,ds\right),&W_t&=B_t-\int_0^{t\wedge A}\widehat u_s\,ds,\\ \|I_U^{Q_A}g\|_2^2&=\mathbb E_{Q_A}\!\int_0^U|g_s|^2\,ds,\qquad g\in\mathcal H_U^{Q_A},\quad U\text{ independent of }A.\end{aligned}
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

有限 Gaussian 一致性先生成可数源；将柱集覆盖置于同一可数源证明 σ 次可加性，再做实际扩张和连续修改。字面和的等距、核下降与连续线性扩张构造积分；可预测生成集和原生 Lp 归纳证明完整域相等。L² 密度与 L¹ 稳定性给固定输入 QV；实际漂移原函数、同状态加权交叉和 Taylor 余项给 Itô。有界控制的同界有限表与密度一致可积性导出真实归一化和原过去因子化。固定 Q 的截断输入及 Q-L² 控制收敛证明完整域；实际投影身份将条件期望过程绑定到同一截断积分。

书稿定位：§9.2; §19.4; §22.5; §39.9–15, 17, 19, 22–23, 26–28, 30–31, 34–35, 39–43, 45, 48 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [RESULTS_AND_OPEN_OBLIGATIONS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/canonical_brownian_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)
- [RESULTS_AND_OPEN_OBLIGATIONS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/predictable_finite_purpose_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)
- [RESULTS_AND_OPEN_OBLIGATIONS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/q_integral_vector_qv_program_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)
- [RESULTS_AND_OPEN_OBLIGATIONS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/bounded_control_carrier_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)
- [RESULTS_AND_OPEN_OBLIGATIONS.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/drift_ou_instruction_qfull_source_v1/RESULTS_AND_OPEN_OBLIGATIONS.md)
- [SOURCE_VALIDATION.json](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/drift_ou_instruction_qfull_source_v1/SOURCE_VALIDATION.json)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

以上分支各有生产 Lean 端点与对应来源验证记录；这是 v3 原连续恢复／控制／KL 合同的新增来源实现，不改原命题计数。本轮核读端点、前提及证据，未重新编译、采样或把非计算构造标成可执行算法。历史来源包中的 OPEN／下一步文字只描述各自当时切片；现行边界以此处明确列出的已集成端点为准。P 连续版本与 Q 完整域条件过程的不同证明范围必须保留。

- [BrownianProjectiveSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianProjectiveSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianProjectiveSource.sourceLaw_finite`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianProjectiveSource.source_isPreBrownian`
- [BrownianContinuousSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianContinuousSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousSource.process_eq_coordinate_ae`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousSource.process_isBrownian`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianContinuousSource.measurable_joint_process`
- [BrownianPredictableDensity.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianPredictableDensity.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableDensity.integralDomain_eq_fullPredictableL2`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianPredictableDensity.predictableIntegral_returns_literal`
- [BrownianVectorPredictableDensity.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianVectorPredictableDensity.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableDensity.integralDomain_eq_fullPredictableL2`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableDensity.predictableIntegral_norm`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPredictableDensity.predictableIntegral_returns_literal`
- [BrownianVectorIntegralContinuousVersion.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianVectorIntegralContinuousVersion.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralContinuousVersion.continuousIntegralProcess_eq_actual`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralContinuousVersion.continuousIntegralProcess_martingale`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralContinuousVersion.continuousIntegralProcess_energy`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorIntegralContinuousVersion.continuousIntegralProcess_returns_literal`
- [BrownianVectorPartitionQV.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianVectorPartitionQV.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPartitionQV.fullInput_partition_QV`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianVectorPartitionQV.fullInput_partition_QV_inMeasure`
- [BrownianFiniteStateDriftItoSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianFiniteStateDriftItoSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftItoSource.driftItoInput_coe`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianFiniteStateDriftItoSource.actual_drift_state_ito_integral`
- [PredictableDriftPointSamplingCounterexample.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/PredictableDriftPointSamplingCounterexample.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictableDriftPointSamplingCounterexample.rate_predictable`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictableDriftPointSamplingCounterexample.actual_integral_zero`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.PredictableDriftPointSamplingCounterexample.point_sampling_is_not_actual_drift`
- [BrownianBoundedExponentialLimitSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianBoundedExponentialLimitSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedExponentialLimitSource.fullDensity_mean_one`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedExponentialLimitSource.fullLaw_probability`
- [BrownianBoundedGirsanovSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianBoundedGirsanovSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedGirsanovSource.full_isBrownian`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedGirsanovSource.full_future_indep_original_past`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianBoundedGirsanovSource.full_process_martingale`
- [BrownianOwnQPredictableDensity.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianOwnQPredictableDensity.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQPredictableDensity.integralDomain_eq_fullPredictableL2Q`
- [BrownianOwnQIntegralMartingale.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianOwnQIntegralMartingale.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQIntegralMartingale.integralProcess_eq_truncated`
- [BrownianOwnQFullIntegralSource.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/BrownianOwnQFullIntegralSource.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFullIntegralSource.fullIntegral_norm`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFullIntegralSource.fullIntegralProcess_martingale`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFullIntegralSource.fullIntegralProcess_energy`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.BrownianOwnQFullIntegralSource.fullIntegral_returns_literal`

相关冻结 P-ID：[P-REC-02](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-rec-02), [P-CTL-03](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-03), [P-KL-05](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-kl-05).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

一个有界且真正可预测的有理时刻指标，在 [0,1] 的实际漂移积分为 0，而每个均匀有理网格的左端点和为 1；因此仅可测 β 不能用点取样和替代原函数增量。原 Lp 代表不自动逐点可预测；须使用已构造代表及证明的 AE 身份。零 T、零 d、零 A 和重复时刻是合法边界；A=0 仍允许 U>0 的非零噪声积分。缺少有界控制或其他独立的真密度条件时，不能由 u∈L² 推得 E_PD_A=1。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

CSX-11 的 OU、ItoRun／HJB 与路径 KL 消费者须绑定这里的实际源、原滤过、同一输入和真实积分，继续提交各自的状态、可积性、折扣、可观测性及选择器条件。部署窗 A 不随读取或积分窗 U 改写；原 u、实际有界代表、Q_A 与 W 保持一致。带漂移公式消费实际 ∫βdt；梯度输入和 Hessian 能量须由同一 Y 与同一 fʲ 计算。可迁移到其他源的结论必须另证实际律／过程身份及相关前提。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明任意隐式 SDE 的存在唯一性、无界导数的通用 Itô、一般随机／停止分割的 QV 或其几乎处处收敛、一般 L² 控制的指数规范化、W 的自然滤过等于原滤过，或全部完整 Q 输入的一般连续修改／Itô。原坐标与连续修改不被宣称逐样本全时相等；有限维向量 P 结果不自动推广为任意维 Q 控制。来源实现本身不证明任意 HJB 最优性、物理单位识别或经验效度。

<a id="csx-30"></a>

### CSX-30 · 真实资源、修复检查与全价格目的的独立合同

<!-- contract-field: id -->

#### 1. Claim ID

`CSX-30`

<!-- contract-field: name -->

#### 2. 精确名称

真实资源、修复检查与全价格目的的独立合同

<!-- contract-field: definition -->

#### 3. 数学定义

在 literal Register 源中区分三件事：原实际费用和余额的 P6 资源合同；提交 AST 的 restorationCheck；按出生收益减价格×费用登记的无限折扣目的。令故障概率 ε、修复机会 r=1−ε、写费 c、价格 p、κ=pc、折扣 d∈(0,1)。

<!-- contract-field: domain -->

#### 4. 论域与对象类型

原 one-port 细状态／动作历史策略类与实际全记录律；有限资源障碍仅在 ε>0、c>0、受保护 program=goal 且此策略实际零收入预算 a.e. 成立时适用。动态目的界按原非负价格、ε∈[0,1] 模型。

<!-- contract-field: assumptions -->

#### 5. 必要假设

零收入储备 R 的 ResourceViable 必须约束同一策略的真实 expenditure；并非假定所有策略都付得起。恢复检查枚举原真实状态并验证实际更新。全价格最优比较保留原评价和可行动作；资源可支付另证。长期接续的外供在每笔尾段交易前到账，不回填有限学习阶段。

<!-- contract-field: quantifiers -->

#### 6. 准确量词

资源界对每个实际预算合法的原因果策略及每个前缀成立，并给同一律下最终不再合法的 a.e. 结论。r>0 时 repair／idle 的 GOD iff 按阈值分类；全部价格下有返回动态程序及全因果比较。恢复检查 soundness 只承诺其检查的单步恢复性质。

<!-- contract-field: conclusion -->

#### 7. 结论

有限资金给实际健康总占据界；动态阈值 κ(1−dr)=1 区分 repair/idle，等号两者并列。通过恢复检查的提交程序及综合返回物保持相应修复性；其物理恢复、评价最优与资金仍是三个不同结论。

<!-- contract-formula: CSX-30 -->

$$
\varepsilon\!\left(H_0+\mathbb E\sum_{t\ge0}H_{t+1}\right)\le H_0+R/c\le1+R/c;\qquad r>0:\ \mathrm{repair\ is\ GOD}\iff\kappa(1-dr)\le1,\quad\mathrm{idle\ is\ GOD}\iff1\le\kappa(1-dr).
$$

<!-- contract-field: proof -->

#### 8. 证明与标准来源

实际净值势不等式与原零收入预算导出健康占据及可求和性；两区 Bellman 方程给全价格分类；真实解释器更新和 accepted synthesize 等式连接修复与目的运输。

书稿定位：39.18;39.24;39.32;39.44;39.47;39.51–39.55;39.58–39.61;39.67–39.70 — [当前数学书](../../../mathematics/UEOT_MATHEMATICS.md).

来源证据：

- [FINAL_ACCEPTANCE.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/whole_theory_formal_closure_v1/FINAL_ACCEPTANCE.md)
- [REGISTERED_INTERFACES_CLOSURE_V1.md](../../../formalization/ueot-core/docs/compression/theory_completion/unified_closure/REGISTERED_INTERFACES_CLOSURE_V1.md)

<!-- contract-field: status -->

#### 9. Lean 接口与实际证明状态

所列既有 Lean 资源、动态价格、恢复检查和同账本接续端点；数据选择与 P9 全六性质的汇合继续使用原 Good／源条件，不由单个 checker 代替。

- [RegisterFaultFiniteResourceMaintenance.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterFaultFiniteResourceMaintenance.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceMaintenance.actual_finite_health_time_bound`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceMaintenance.actual_total_health_time_bound`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultFiniteResourceMaintenance.actual_eventually_never_legitimate`
- [RegisterFaultDynamicPrice.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterFaultDynamicPrice.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPrice.dynamic_program_all_causal`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPrice.compiled_god_iff`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPrice.idle_god_iff`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterFaultDynamicPrice.threshold_tie`
- [RegisterInstructionRecoveryScale.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterInstructionRecoveryScale.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionRecoveryScale.restorationCheck_iff`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterInstructionRecoveryScale.returned_restoration_iff`
- [RegisterPopulationCurrentParentContinuation.lean](../../../formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/RegisterPopulationCurrentParentContinuation.lean):
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.whole_prepay`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.actual_balance_at_switch`
  - `UEOT.V3.Compression.TheoryCompletion.UnifiedClosure.RegisterPopulationCurrentParentContinuation.full_source_two_event_bound`

相关冻结 P-ID：[P-REC-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-rec-01), [P-CTL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-ctl-01), [P-TEL-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-tel-01), [P-API-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-api-01), [P-CORE-01](../../../mathematics/source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md#p-core-01).

<!-- contract-field: failure -->

#### 10. 反例与失效边界

ε=0 或 c=0 不适用正故障正费用障碍；某编译策略有正质量超支不等于所有策略 a.e. 破产。r=0 时所有允许动作可弱最优而无恢复；免费写有额外并列。有限零终端 episode 的真实修复净值可为 −3/40，不能从无限期 GOD 直接搬用。

<!-- contract-field: consumer -->

#### 11. 下游消费者义务

记明收入到账时序、完整训练和部署费用、同一余额及目标。接续模块要求 c≤cap≤g、R≥(2N+3)cap+B r_fee，实际 switch 余额等于未花有限钱包；不重置资金。恢复／综合的 soundness 与完备性分开，有限 truth-table 的 exact 合同才按其范围使用。

<!-- contract-field: nonclaims -->

#### 12. 不支持的更强结论

不证明生命普遍必须外供、不证明最优即能维持、不把修复恢复率当最优率、不赋予观察不到的信息，亦不把模型目标当唯一自然目的。
