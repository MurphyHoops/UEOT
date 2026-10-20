# UEOT Core v3 七开放端口：权威矩阵与工作包

版本：1.0｜日期：2026-10-07｜关联：《CORE_V3_POST_CORE_SCIENTIFIC_CLOSURE.md》《THEORY_COMPLETION_ROADMAP_V2.md》

## 1. 使用规则

下列 C1–C7 是 Core §31.2 的研究入口命名，不是新的 Core 公理或递进必经阶段。验收必须标注适用空间、协议、时间、误差及数据来源。完成某个工作包只关闭该包；除非覆盖端口中全部问题，否则不能把整个端口标记 CLOSED。

状态缩写：F=仓库记录的形式化表面闭合；A=有独立领域适配前提；E=扩展结果；U=本轮未核实或尚未完成。F 不代表现实支持，E 不增加 frozen 106 计数。

## 2. 总权威矩阵

| 开放端口 | Core 锚点/已有关联 | 已有结果 | 实质未闭合处 | 首个可验收成果 | 优先级 |
|---|---|---|---|---|---|
| C1 可测存在与一般状态 | §4/7/8/9/10/21；P-PRED、P-DYN、P-QSD、P-GOA | 可数协议规范预测状态；有限递归；若干一般空间条件接口 F/A | 一般空间共同递归版本、实现选择、非紧紧性/存在 | 一项明确空间中的更新/实现定理或障碍反例 | P2，先问题定位 |
| C2 现实数据的对象+协议发现 | §16/17/20/28；P-STAT、P-INV、P-ALG、P3/P4 | 有限候选、已定协议和估计误差后的控制接口 F/E | 相关轨迹、适应干预、漂移、协议选择、未知 gap | 相关轨迹有限发现→独立认证的闭环 | P1，首轮主线 |
| C3 可扩展载体/毁损发现 | §13–16；P-CAR、P-RES、P-STAT、H/X | blocker、分辨率区间、有限误差族恢复 F | 不枚举全部集合的可执行算法、query/sample 复杂度 | 特定结构的 output-sensitive 发现及失败诊断 | P1，范围先冻结 |
| C4 非平稳/尺度身份与 GOA | §7/11/14/15/21；P-DYN-04、P-ID、P-RES、P-GOA、Track-S/H/X | 静态/局部运输、残差隔离、typed assembly F/E | 真实非自治过程跟踪、拓扑变化、分岔附近失证 | 静态 GOA 运输与时变占据分开的证书 | P2，可与 C2 联用 |
| C5 Π/Φ 识别与维数拒绝 | §23；P-DDH-01–05 | gauge、变分、共同 latent 必要条件及有限误差秩检验 F | 独立机制锚、共同潜维、真实试验功效与阈值 | 正/反/曲面三类基准 + 一份预注册协议 | P1，直接关系强主张 |
| C6 机制来源的目的桥 | §18/25/26/27；P-TEL、P-EVO、P-BRG、P1/P2 | 目标不可从存在唯一推出；条件选择/学习/桥接 F/E | 独立机制识别、目的等价类、域外预测 | 一个有来源、有对照、可失败的桥 | P2，单机制起步 |
| C7 形式化↔现实反例链 | §28/31.2；P-CORE/P-API 与全部 lanes | 数学装配、有限演示、形式化 F | 真实系统预注册、独立数据、错误预算、失败归因 | 首条完整 claim→observable→estimator→failure 链 | P0，全程横切 |

P0=立即先做；P1=第一轮重点；P2=先缩小目标后推进。优先级是安排建议，不覆盖仓库研究治理。

## 3. R0：先把权威和范围对齐

### R0-01 确切版本与状态清单

输入：冻结源、当前 main、106 索引、覆盖状态、压缩账本、P0–P6 tracker、实际 PR/Actions。产物只用一张当前 manifest，记录源 SHA、main SHA、P6 head、工作流 run、文档版本和未核实项。

验收：106 行、106 unique，源哈希一致；11/89/6 分类相加 106；4 generators 与正式账本一致；每条 CI 与对应提交相符。旧 83/106 和空 audit matrix 明确标历史。当前索引与 baseline 索引哈希差异有版本解释。canonical 源字节未公开同步单独列项，不抹掉证明覆盖。

停止条件：提交不对应、源字节不一致或漏行时，停止“当前全绿”发布，保留已有历史状态；先辨别来源差异，再决定是否真的重开定理。

### R0-02 D-OBJ 与扩展字段对照

逐项列 Core D-OBJ 所需接口、P0 已提供接口、P0 额外强持续性要求及未对接字段。只新增说明/adapter 清单；名称歧义先通过文档范围处理，实际调用需要再加最小类型适配。

验收：generic object、历史对象、强持续对象、self-maintaining organization、autopoiesis 不再混用。每个扩展 theorem 的额外前提显式列出，没有把它们反填成 Core 定义。

### R0-03 P2 终审与 v1/v2 边界

产物建议名称：`P2_SAME_OBJECT_AGENCY_GOD_GOA_AUDIT.md`。需覆盖 identity/history/effective-state、contract 表示、Bellman faithfulness、greedy viability、stationary/causal policy、GOD/GOA 输出种类、可信底座及独立机制非声明。

验收：每一主张可指到 theorem 和假设；没有“给定 faithfulness 证明了机制识别”的换词；没有把 P1.0 partial 隐藏在 P1 CLOSED 里。v1 留作历史合同，v2 明确哪些条目只调优先级，哪些涉及受保护共享语义。

### R0-04 P6 既有门与排程隔离

P6 继续完成它已有的独立 review、确切 head 的 Base Policy/Core Lean/Compression Guard、合并后的两项 matching CI、tracker 和分支收尾。最新修正增加公共根导入，不能沿用旧 head 的审核结论。

验收：记录 expected accounting 与 realized pathwise 分别来自什么 theorem/前提；资源单位仍抽象。P6 关门不是自动激活 P7。此任务书没有执行合并或关闭 tracker。

## 4. C1 工作包：先定位真正的可测与一般空间缺口

### C1-01 已证/未证分解（预估 2–3 工作日）

从 P-PRED-01 的可数共同版本起步，列出状态空间、概率测度空间、协议族、输出核、商 σ-代数、时间索引和已有 Mathlib 接口。区分规范 measure-valued state、具体低维载体、递归核、对象实现、长期极限这五个目标。

验收：每个拟新增 theorem 说明为何不是已有 theorem 的直接 specialization。没有仅把 Finite 类型改成 Infinite 来宣称存在理论推进。

### C1-02 一个可测递归更新接口（5–10 工作日，依问题缩小调整）

候选目标：Standard Borel 历史/观测、有限或可数动作和允许续接的可数协议族下，在适当条件分布共同版本及零概率分支约定下，构造可测 U，使预测状态的下一步更新在合法运行中因子化于 (C_t,A_t,Y_{t+1})。

证明义务：续接协议确实覆盖所需未来；条件分布有可测版本；相同预测纤维在更新后仍相容；共同 null set 与递归运行一致；零概率观测不会引入虚假全空间断言。若假设已直接包含所求 U，则不是存在定理，应改为接口声明并保留构造缺口。

验收：完整数学证明 + 适用空间中的 Lean 最小可复用部分 + 一个必须额外假设的反例。若无法建立 jointly measurable update，发布边界报告，而非把结论塞进结构字段后宣布闭合。

### C1-03 非紧长期存在的最小问题（5–10 工作日，可后置）

先审计现有 compact/Feller、有限 occupation/QSD 接口。选择一个非紧但有明确紧性/漂移条件的模型，证明占据测度相对紧、子极限不变并说明边界项。不要把弱收敛、TV 收敛、唯一性、mixing 合成一条未证明声明。

验收：正向存在 + 无紧性时逃逸反例 + 每种拓扑的合法连续性条件。目标是一个可用一般状态适配，不是“所有 general kernel 统一完成”。

## 5. C2 工作包：对象与协议发现的可信数据链

### C2-01 相关轨迹下有限响应认证（4–6 工作日）

先用 Core §16 已有 blocking 思路：在已知或保守上界的 β-mixing 条件下选 m 个隔离块，得到形如独立估计误差概率 + (m−1)β(b) 的预算。明确有效块数、间隔、每个协议的访问次数和覆盖支撑。

验收：估计半径含相关项；模拟不同 mixing 强度时不会把原始时间点数当独立样本量；无法可靠给出 β 上界时，输出模型敏感性或未认证，而不是换一个 bootstrap 名称就声称严格置信。

### C2-02 有限候选+协议的发现/认证分离（5–8 工作日）

先限制为声明的有限候选表示、有限协议库和有限干预预算。训练数据选候选和下一轮协议；冻结选择后用独立数据认证，或采用已证明对可预测采样/停止有效的误差预算。控制部署另有覆盖验证。

真实 adaptive干预可能改变过程，不能机械套固定平稳链 mixing。第一版采用分轮冻结或重置协议；若确实需要在线适应，再引入对应 martingale/likelihood 条件。

可复用参考：[Howard 等的时间一致置信序列](https://arxiv.org/abs/1810.08240)。其条件应在采样模型中逐项核对；它不能无条件修复所有相关样本或分布漂移。

验收：发现阶段和认证阶段数据 ID 不重用；每个样本解释它支持的协议/动作；低覆盖动作拒绝认证；预算累加不重复计算同一好事件。

### C2-03 未知 gap、漂移及带拒答的发现（4–6 工作日）

若响应误差各为 η，则两响应距离误差最多 2η。若已知非零分离下界 γ，η<γ/4 时可用 γ/2 阈值恢复零/非零类；如果仅知道有限族中存在某个未知 γ，则这个存在性本身不能给可执行停止规则。

第一版输出距离区间与未决类；容差 τ 周围若区间跨阈值，继续采样或保留 ambiguous，不宣布精确恢复。漂移模型要定义窗口内变化预算，误差半径增加漂移偏差。跨窗口对象身份通过 C4 认证，不靠候选标签相同。

验收：小 gap、大漂移、低覆盖和训练拟合过度四类压力测试都产生预定失证/拒答；正常条件下能恢复已知有限对象并给合法控制证书。

### C2-04 面向运行的数据字典（2–3 工作日）

最少字段：run/episode、时间、协议版本、动作及分配概率、原始观测、候选编码版本、声明未来、干预成本、错误/故障标签、训练/认证分区、缺失原因。先用普通文件/现有记录格式，不建新平台。

验收：从记录可重算每个估计值和证书；只对有限注册候选声称发现，不能泛化为发现全部现实对象。

## 6. C3 工作包：有输出边界的载体发现

### C3-01 复杂度和 oracle 语义冻结（2–3 工作日）

分别定义：顶点/机制数 n、显式超图输入长度、响应 oracle 的一次成本、噪声/容差、输出极小载体数 N_out。区分从已知超图求 transversal、从黑盒响应发现超图、从物理删除恢复机制三类问题。

单调阈值性质 |S|≥⌊n/2⌋ 的极小载体数是二项式系数 C(n,⌊n/2⌋)，已具指数输出下界。因此不得承诺“任意对象全载体以 n 的多项式时间全部输出”。可做 output-sensitive、有限查询恢复或结构特例。

背景参考：[Mary，受限 VC 维超图的极小 transversal 枚举](https://arxiv.org/abs/2407.00694)。论文的结构性算法结果针对其输入/输出问题；不可自动转成噪声物理 oracle 的 query guarantee。

### C3-02 一个结构特例的最小实现（5–8 工作日）

在实际数据支持后，选有界边大小、有界结构参数或明确模块装配中的一种。优先复用现有 blocker/分辨率算法；只实现一个有证明保证的搜索器，不先造万能 discovery framework。

验收：输出对小 n 穷举基准完全一致；记录 query、sample、时间、内存和输出量五种成本；与相同任务、相同准确度的穷举/现有方法比較，不能通过少输出冒充提速。

### C3-03 噪声与物理 frame 失效（4–6 工作日）

把 oracle 响应区间接 C2，查询预算按实际调用分配。阈值不确定的集合不能当已确定正/负；提供确定子集和未决集合。访问单调性的推理与物理删除 frame 分别验证。

验收：同一预算下有上下证书；备份激活、解除抑制等非单调例子触发协议诊断；不能用 blocker's algebra 推出未验证的物理完整性。

## 7. C4 工作包：分清静态运输与非自治运行

### C4-01 冻结对象的静态 GOA 运输（3–5 工作日）

先复用 Track-S 的 κ₁ 残差隔离和 typed transport。证明给定编码/核缺损与隔离裕量下，指定 invariant-law 结果的定量稳定；记录裕量趋零导致上界失效。唯一律不要求全部链一阶 Dobrushin 收缩，周期链作为必须保留的基准。

验收：正例、周期例、双不变律和接近分岔四种例子；不把 invariant-law transport 写成逐时实际轨迹收敛。

### C4-02 真实时变过程的有限时域跟踪（5–8 工作日）

在共同坐标或已认证运输后，定义 μ_{t+1}=μ_tP_t、参考 π_t，并分别量化核误差 ε_t 与参考变化 d_t。若适当 contraction 系数 a_t 可证，可推：

\[
e_{t+1}\le a_t e_t+\varepsilon_t+d_t.
\]

展开为乘积衰减与累计缺损；若只能多步收缩，则按块证明。静态 κ₁>0 并不自动给这条逐时跟踪界。没有均匀收缩/累计条件时，只交付有限时域证书，不能凭每个 P_t 都有唯一不变律就宣布长期 GOA。

验收：慢漂移支持界、快漂移失败、隔离裕量丢失后停止外推；每次转换都有时域和缺损账。

### C4-03 分裂/合并/多尺度的类型化身份（4–6 工作日）

部分关系、pushforward、父层 assembly 与子层保真分别处理。对象分裂不默认双射，父对象也不由共同子证据唯一决定。物理 RG 只在指定 domain bridge 有效时另列。

验收：每个跨尺度主张明确是 predictive quotient、resolution、composition、history、value、selection 还是 GOA；H/X 的 no-go 不被“统一 scale operator”绕过。

## 8. C5 工作包：共同驱动维数的可失败检验

### C5-01 机制与计量锚（3–5 工作日）

冻结 Π/Φ 的候选物理/信息量、单位、可测程序、允许 gauge、干预选择性和替代机制。测量接口由外部实验变量/机制给出，不从待解释的最优行为事后反推。

验收：至少一个可预测的新预算/新环境对照；若缺独立锚，只能声称低维响应，不得称识别 Π/Φ。

### C5-02 必要秩条件与误差功效（4–6 工作日）

同一预算 B，跨环境堆叠 J_e(B)；至少三个可识别预算方向、三个合计响应维度。冻结归一化、有限差分带宽、误差矩阵 η、阈值 τ₀、总 α、多点多环境检验分配及不确定输出。

验收三类基准：共同二维模型不误拒；各环境二维但无共同二维能够拒绝；共同二维 curved latent 在不同预算点切空间变化时不被错误拒绝。将相关样本/漂移误差纳入 η。

### C5-03 2-drive 与 3-drive 的留出预测（4–6 工作日）

模型在训练环境拟合，预先指定留出环境/预算。比较受相同复杂度控制和同一数据规则约束的二维、三维、灵活基线；报告预测误差与机制锚一致性。

验收：可以输出“拒绝共同二维”“阈值下局部有效二维”“功效不足”三类；任何支持都有范围。即使局部秩通过，仍保留全局 latent 和 Π/Φ 分解的独立义务。

## 9. C6 工作包：只做一个可独立检验的目的机制

### C6-01 机制选型与不可识别性表（3–5 工作日）

优先选一项已有 Core 桥：固定适合度复制、明确损失/反馈的学习、指定协调外部性或可观察生存/资源机制。列出评价主体、层级、时域、可行策略、奖励等价类和 nuisance 变量。

验收：桥由独立机制信息限定，不能“行为是什么就定义目标是什么”。若目标只能识别到行为/势函数等价类，明确输出等价类。频率依赖选择、改变适合度、复制误差等条件不会被当作静态优化器。

### C6-02 桥校准→新情景预测（5–8 工作日）

独立测量复制/学习/协调机制参数，再生成受约束的 J 或 preorder。只使用训练阶段校准；用新动作、干预或环境测试最优响应。至少一个替代目标/机制预测不同结果。

验收：目的桥预测先于数据；失败阈值和可排除 nuisance 提前声明；桥失效只否定所用机制解释，不自动否定 generic Objecthood。

### C6-03 接回 P2 的三个独立门（3–5 工作日）

先检查合同表示，再检查 BellmanTeleologicalFaithfulness 或对应 causal-policy 版本，最后检查 viability/保持合法性。使用相同父对象的动力学和编码；另证明的身份运输才能跨对象。

验收：GOD/GOA 输出种类与范围准确；机制识别、偏好表示、控制忠实性、持续性四列分别为 PASS/FAIL/UNCERTIFIED。单列通过不得替代其他列。

## 10. C7 工作包：所有研究从第一天带着失败标准

### C7-01 一页预注册模板（2–3 工作日）

最少内容：claim ID；Core/extension 来源；全部关键假设；声明对象/协议/时域；observable；估计器与单位；样本分配和停止规则；总错误预算；支持/拒绝/不确定阈值；正负对照；数据版本；独立复现人/角色。

验收：注册时间早于认证数据；同一好事件跨 theorem 重用只记一次 α；多个不同事件用 union bound 不需假设独立。探索结果与确认结果分表保存。

### C7-02 最小现实试点（5–10 工作日，取决于数据可得性）

建议首选可观测、可干预、可重置的小型实际数字过程，例如有组件失效和备份的真实运行服务。它可同时连接 C2/C3/C4；明确它是一个数字领域对象，不用仿真代替实际运行。若没有可用服务或干预权限，先完成模拟方法基准，把现实验证保持 UNVERIFIED。

首轮最低标准：一个候选对象；两个有不同信息/干预作用的预注册协议；一个留出扰动；完整运行日志；一个朴素基线；一个已知会失败的负对照。C5/C6 若缺计量锚，不强塞进这个对象。

验收：其他人能从原始记录重算估计和证书；隐藏状态不同但观察相同的情形保留不可识别结论；报告失败案例而非只保留成功轨迹。

### C7-03 失败归因与复现包（3–5 工作日）

失败分四级：数学推导/源语义不匹配；测量/估计违反假设；指定机制或 domain bridge 被拒绝；数据覆盖/功效不足。只有第一类有证据时才启动 Core theorem 的重审。

验收：正例、反例、未决三类均可再现；每个 reported number 追到数据分区和运行版本；原文脚本数值检查与现实证据不混计。

## 11. 交付与关闭判据

每个工作包交四样最少材料：范围和假设页、证明或算法/试验主体、正负见证、验收记录。已有文档足够时直接引用，不复制全文、不建立第二套 counted ledger。

形式化包须经符合现行治理的 exact-head 构建、proof-escape/axiom 检查、必要独立审查、公共导出以及合并后 matching CI。文档规划包不自动触发 counted promotion。涉及 frozen 主张、共享语义或新 generator 时另走对应风险等级。

### 统一验收表

| 维度 | PASS 的最低条件 | 失败或未决时 |
|---|---|---|
| 语义 | Core/extension、类型、单位和前提不混用 | 缩小声明或修正 adapter |
| 数学 | 定理不把结论作为输入；证明与范围一致 | 发布 no-go/未完成证明义务 |
| 机器 | 若宣称 Lean，确切 head 与公共入口已覆盖 | 不称 machine-complete |
| 数据 | 支撑、相关性、漂移、选择过程有记录 | 输出 uncertified |
| 科学 | 有独立机制/预注册失败标准/负对照 | 仅称内部模型结果 |
| 工程 | 复杂度按相同任务和输出衡量 | 不以缩水结果称加速 |
| 状态 | phase closed 与 stronger claims 分开 | 保留 partial/open 标签 |

## 12. 附录：106 个 P-ID 的源—Lean—压缩追踪表

下表由固定 main 的 `CORE_COMPRESSION_THEOREM_INDEX.csv` 和 `COMPRESSION_LEDGER.yaml` 自动对齐。源行数指冻结主文；Lean 表面来自账本已有审计记录。本轮检查唯一性、覆盖、映射一致性及分类计数，**不宣称逐个独立重证全部 theorem**。G=generated；A=retained_adapter；B=retained_boundary。完整 theorem 列表仍以固定提交账本为准；表内列首个入口以便阅读。

| P-ID | Core 章节/源行 | 首个 Lean 对应入口 | 压缩分类 |
|---|---|---|---|
| P-MET-01 | §1 / 140 | `UEOT.V3.TotalVariation.tvDist_map_le` | A |
| P-MET-02 | §1 / 153 | `UEOT.V3.TVSpan.abs_integral_sub_le_span` | A |
| P-PROC-01 | §2 / 199 | `UEOT.V3.ConcreteHistoryMarkovization.p_proc_01_history_markovization` | A |
| P-FAC-01 | §3 / 254 | `UEOT.V3.RepresentationCovariance.p_fac_01_covariance_bundle` | A |
| P-PRED-01 | §4 / 294 | `UEOT.V3.PredictionDependent.canonical_ae_minimal` | G |
| P-PRED-02 | §4 / 330 | `UEOT.V3.PredictionRefinement.pushTargetDependent_apply` | A |
| P-PRED-03 | §4 / 351 | `UEOT.V3.PredictionUpdate.p_pred_03_recursive_update` | A |
| P-INFO-01 | §5 / 376 | `UEOT.V3.InformationStatistic.mutualInfo_eq_statistic_add_conditional` | A |
| P-INFO-02 | §5 / 397 | `UEOT.V3.InformationPInfo02.p_info_02_finite` | A |
| P-INFO-03 | §5 / 432 | `UEOT.V3.InformationPredictiveRateZero.predictiveObjectRateZero_eq_sourceEntropy` | A |
| P-INFO-04 | §5 / 450 | `UEOT.V3.InformationPInfo04.p_info_04` | A |
| P-INFO-05 | §5 / 468 | `UEOT.V3.InformationPacking.merged_histories_decoder_lower_bound` | B |
| P-INT-01 | §6 / 488 | `UEOT.V3.InformationPInt01Common.p_int_01` | A |
| P-INT-02 | §6 / 524 | `UEOT.V3.StructuredQuotient.p_int_02` | G |
| P-INT-03 | §6 / 570 | `UEOT.V3.MarkovBoundary.p_int_03_boundary_unique` | A |
| P-DYN-01 | §7 / 587 | `UEOT.V3.DynamicsKernel.strongLumpability_iff_pathLaw_of_surjective` | A |
| P-DYN-02 | §7 / 603 | `UEOT.V3.CTMCSemigroupNonnegative.p_dyn_02_nonnegative_semigroup_iff_blockSum` | A |
| P-DYN-03 | §7 / 623 | `UEOT.V3.PathError.p_dyn_03_finite_path_error` | G |
| P-DYN-04 | §7 / 640 | `UEOT.V3.DynamicsCrossScale.p_dyn_04_cross_scale_tv` | G |
| P-PER-01 | §8 / 679 | `UEOT.V3.PersistenceOmega.p_per_01` | A |
| P-PER-02 | §8 / 705 | `UEOT.V3.PersistenceOccupation.FellerOccupationSystem.p_per_02` | G |
| P-PER-03 | §8 / 729 | `UEOT.V3.ViabilitySource.p_per_03` | A |
| P-PER-04 | §8 / 745 | `UEOT.V3.ViabilityTangency.p_per_04` | A |
| P-REC-01 | §9 / 760 | `UEOT.V3.RecoveryProbability.p_rec_01_mean_bound` | A |
| P-REC-02 | §9 / 783 | `UEOT.V3.RecoveryDynkin.p_rec_02` | A |
| P-REC-03 | §9 / 804 | `UEOT.V3.RecoveryHittingPoisson.p_rec_03` | A |
| P-REC-04 | §9 / 814 | `UEOT.V3.RecoveryHittingBound.p_rec_04_hitting_time_bound` | A |
| P-QSD-01 | §10 / 847 | `UEOT.V3.QSDTVLimit.p_qsd_01` | A |
| P-QSD-02 | §10 / 879 | `UEOT.V3.QSDPerron.p_qsd_02` | G |
| P-QSD-03 | §10 / 901 | `UEOT.V3.QSDDurationWindow.p_qsd_03` | A |
| P-QSD-04 | §10 / 928 | `UEOT.V3.ReversibleKilledSpectralQSD.SpectralData.p_qsd_04` | A |
| P-ID-01 | §11 / 971 | `UEOT.V3.TransportDefect.FrozenTransportSystem.p_id_01` | G |
| P-ID-02 | §11 / 1007 | `UEOT.V3.DevelopmentTransport.development_pipeline` | G |
| P-OMG-01 | §12 / 1077 | `UEOT.V3.OmegaMinimalFailure.p_omg_01` | A |
| P-OMG-02 | §12 / 1095 | `UEOT.V3.OmegaIntegrityMargin.p_omg_02` | A |
| P-CAR-01 | §13 / 1135 | `UEOT.V3.Access.sufficient_mono` | A |
| P-CAR-02 | §13 / 1151 | `UEOT.V3.Access.erasure_survives` | A |
| P-CAR-03 | §13 / 1157 | `UEOT.Blocker.blocker_involution` | A |
| P-CAR-04 | §13 / 1196 | `UEOT.V3.DecoderRadius.decoder_radius_bounds` | A |
| P-RES-01 | §14 / 1223 | `UEOT.V3.ClosureResolution.minimal_property_coarse_graining` | A |
| P-RES-02 | §14 / 1233 | `UEOT.V3.ClosureResolution.closure_comp_of_nested` | A |
| P-RES-03 | §14 / 1267 | `UEOT.V3.BlockerNaturality.blocker_naturality` | A |
| P-RES-04 | §14 / 1294 | `UEOT.Resolution.lower_adjunction` | A |
| P-RES-05 | §14 / 1324 | `UEOT.V3.Resolution.pushFamily_realization_interval` | A |
| P-RES-06 | §14 / 1337 | `UEOT.V3.Resolution.endpoint_equality_iff_unique_active_fibers` | A |
| P-COMP-01 | §15 / 1364 | `UEOT.V3.CompositionPathSource.p_comp_01` | A |
| P-COMP-02 | §15 / 1386 | `UEOT.V3.CompositionInterventionJS.jsDiv_mem_Icc_logTwo` | A |
| P-COMP-03 | §15 / 1402 | `UEOT.V3.CompositionMargin.p_comp_03` | A |
| P-COMP-04 | §15 / 1422 | `UEOT.V3.CompositionParentInformation.p_comp_04` | A |
| P-COMP-05 | §15 / 1451 | `UEOT.V3.CompositionBooleanAtoms.p_comp_05` | A |
| P-COMP-06 | §15 / 1465 | `UEOT.V3.CompositionCarrierLift.p_comp_06` | A |
| P-COMP-07 | §15 / 1491 | `UEOT.V3.CompositionWindow.p_comp_07` | A |
| P-STAT-01 | §16 / 1512 | `UEOT.V3.FiniteAlphabetPStat01.p_stat_01_tail` | A |
| P-STAT-02 | §16 / 1536 | `UEOT.V3.StatisticalDefect.p_stat_02` | A |
| P-STAT-03 | §16 / 1555 | `UEOT.V3.Threshold.approximate_family` | A |
| P-STAT-04 | §16 / 1565 | `UEOT.V3.Threshold.exact_family` | A |
| P-STAT-05 | §16 / 1596 | `UEOT.V3.PredictiveClassRecovery.p_stat_05` | A |
| P-STAT-06 | §16 / 1617 | `UEOT.V3.HilbertMeanSourceRadius.source_meanError_tail_exact_radius` | A |
| P-STAT-07 | §16 / 1632 | `UEOT.V3.MMDTransportSource.p_stat_07_source` | A |
| P-STAT-08 | §16 / 1653 | `UEOT.V3.FiniteCandidatePStat08.p_stat_08` | A |
| P-STAT-09 | §16 / 1673 | `UEOT.V3.AverageErrorTransport.p_stat_09` | A |
| P-INV-01 | §17 / 1696 | `UEOT.V3.BinaryTesting.p_inv_01` | B |
| P-INV-02 | §17 / 1717 | `UEOT.V3.FisherGauge.p_inv_02` | B |
| P-INV-03 | §17 / 1723 | `UEOT.V3.FisherIntersection.p_inv_03` | A |
| P-INV-04 | §17 / 1747 | `UEOT.V3.DesignIdentifiability.p_inv_04` | A |
| P-INV-05 | §17 / 1757 | `UEOT.V3.PredictableOLSSourceConfidence.measure_source_goodGram_and_euclidean_error_gt_le_alpha` | A |
| P-TEL-01 | §18 / 1832 | `UEOT.V3.RewardInfinite.shaping_limit_value` | A |
| P-CTL-01 | §19 / 1877 | `UEOT.V3.FiniteDiscountedControl.p_ctl_01_causal_optimality` | A |
| P-CTL-02 | §19 / 1918 | `UEOT.V3.CompactFellerControl.Model.p_ctl_02` | A |
| P-CTL-03 | §19 / 1932 | `UEOT.V3.DiffusionHJBVerification.p_ctl_03` | A |
| P-QUO-01 | §20 / 1973 | `UEOT.V3.FiniteDiscountedControl.ExactControlQuotient.p_quo_01` | A |
| P-QUO-02 | §20 / 2001 | `UEOT.V3.FiniteDiscountedControl.ApproxControlQuotient.p_quo_02` | A |
| P-QUO-03 | §20 / 2024 | `UEOT.V3.CoreOperationalAssembly.macro_gap_certifies_micro_action` | A |
| P-QUO-04 | §20 / 2042 | `UEOT.V3.FiniteDiscountedControl.Model.p_quo_04` | A |
| P-QUO-05 | §20 / 2063 | `UEOT.V3.FiniteDiscountedControl.LocalApproxControlQuotient.p_quo_05` | A |
| P-GOA-01 | §21 / 2103 | `UEOT.V3.FiniteCesaroInvariant.p_goa_01` | G |
| P-GOA-02 | §21 / 2129 | `UEOT.V3.FiniteDobrushin.p_goa_02` | A |
| P-GOA-03 | §21 / 2155 | `UEOT.V3.FiniteRecurrentDecompositionStability.p_goa_03` | A |
| P-GOA-04 | §21 / 2186 | `UEOT.V3.SymmetricKilledSpectralStability.p_goa_04` | A |
| P-KL-01 | §22 / 2214 | `UEOT.V3.PathEventKL.p_kl_01` | A |
| P-KL-02 | §22 / 2227 | `UEOT.V3.PathEventIProjection.p_kl_02` | A |
| P-KL-03 | §22 / 2260 | `UEOT.V3.PathKLChain.p_kl_03` | A |
| P-KL-04 | §22 / 2271 | `UEOT.V3.FiniteCTMCPathKL.p_kl_04_holding` | A |
| P-KL-05 | §22 / 2302 | `UEOT.V3.GirsanovPathKL.TerminalGirsanovData.p_kl_05` | A |
| P-DDH-01 | §23 / 2348 | `UEOT.V3.DualDriveGauge.p_ddh_01` | B |
| P-DDH-02 | §23 / 2370 | `UEOT.V3.ExponentialFamilyCalculus.p_ddh_02` | A |
| P-DDH-03 | §23 / 2380 | `UEOT.V3.ExponentialFamilyIProjection.p_ddh_03` | A |
| P-DDH-04 | §23 / 2402 | `UEOT.V3.CommonBottleneckRank.p_ddh_04` | A |
| P-DDH-05 | §23 / 2426 | `UEOT.V3.SingularValueEffectiveDimension.p_ddh_05` | A |
| P-ALI-01 | §24 / 2462 | `UEOT.V3.AlignmentGlobalExactness.p_ali_01` | A |
| P-ALI-02 | §24 / 2489 | `UEOT.V3.AlignmentParentValue.p_ali_02` | A |
| P-ALI-03 | §24 / 2507 | `UEOT.V3.AlignmentThreshold.p_ali_03` | A |
| P-EVO-01 | §25 / 2551 | `UEOT.V3.EvolutionPrice.p_evo_01` | A |
| P-EVO-02 | §25 / 2568 | `UEOT.V3.EvolutionSharedLabel.p_evo_02` | B |
| P-EVO-03 | §25 / 2589 | `UEOT.V3.EvolutionPerronGrowth.p_evo_03` | A |
| P-EVO-04 | §25 / 2609 | `UEOT.V3.EvolutionReproductiveMartingale.p_evo_04` | G |
| P-BRG-01 | §26 / 2652 | `UEOT.V3.FixedFitnessRecurrenceUniqueness.p_brg_01_closedForm_of_recurrence` | A |
| P-BRG-02 | §26 / 2680 | `UEOT.V3.SelectionBridge.ReplicationBridge.behavior_equiv_fitness_eq` | B |
| P-REF-01 | §27 / 2710 | `UEOT.V3.ReflexivePRef01.p_ref_01` | A |
| P-REF-02 | §27 / 2729 | `UEOT.V3.PRef02.p_ref_02_general_joint` | A |
| P-REF-03 | §27 / 2739 | `UEOT.V3.FreeInformationValue.p_ref_03` | A |
| P-REF-04 | §27 / 2753 | `UEOT.V3.Decision.goal_regret` | A |
| P-REF-05 | §27 / 2779 | `UEOT.V3.Agency.feasibleValue_mono` | A |
| P-API-01 | §28 / 2878 | `UEOT.V3.ProcessInterface.p_api_01_exact` | G |
| P-ALG-01 | §28 / 2911 | `UEOT.V3.PAlg01.p_alg_01` | A |
| P-CORE-01 | §31 / 3198 | `UEOT.V3.CoreOperationalAssembly.p_core_01` | A |
