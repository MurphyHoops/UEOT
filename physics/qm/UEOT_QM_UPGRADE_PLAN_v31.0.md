# UEOT-QM 升级方案 v31.0

## 从 v30.11 与 Frozen Core v3 出发：可验证桥接、可观测对象与条件选择定理

日期：2026-10-19（Asia/Shanghai）  
类型：研究方案与数学审计升级；不是“v31 物理理论已经完成”的发布声明。  
远端目录：`MurphyHoops/UEOT / physics/qm/`。  
审计基线：`195ebb06fb8afcc592c69671dabfd2250e9d1989`。  
理论依据：Frozen Core v3；QM 分阶段版本见第 2 节，三代主线为 v30.11。  
本轮结论：方案完成；新增条件定理的纸面证明与独立精确算术检查完成；QM Lean、新实验与完整物理模型仍按下文任务逐项验收。

## 0. 本次升级的核心决策

UEOT-QM 已经拥有从有限维操作量子论到 QED、再到三代条件选择的研究链。下一步最有价值的工作，是把这条链与已经完成的 Core v3 形式化**精确对接**，形成能给出对象、误差、可区分协议和失败条件的计算与证明系统。

首轮安排两个互相支持的方向：

1. **量子对象与操作证书主线。** 回收 v23 的 FFIPS、instrument conditioning、公共交换代数、SRN/QDRR，构造受限协议下的可观测空间闭包；将其接到 M-QD、递归充分态与 M-TC。目标是对实际可执行的协议，回答“哪些状态差别会影响未来、哪些可以压缩、压缩误差能否认证”。
2. **三代条件定理主线。** 保留 v30.11 的规范异常方向，去掉最终选择定理中冗余的原子性前提，补齐完整谱和对照谱，并把“为什么采用这个粒子扇区”拆成可检验的物理问题。

SRN/QDRR 是已有的实验出口，优先于再添加一个未经定义的新坍缩模型。QFT/RG 工作首先迁移、复核既有计算和桥接，不重新从头编写标准量子场论。一般无穷维算子理论、非阿贝尔完整重整化和 HGP 现实适用性按确切依赖推进。

这一安排保留 UEOT 的统一目标：共同使用对象、协议、表示运输、评价桥与验证链。统一的强度由明确的定理和物理限制体现，不能用同一个名称替代两个不同数学对象。

## 1. 本轮证据究竟支持什么

### 1.1 来源与核验范围

已阅读给定 Core v3 全文及三份后续规划材料，抽取原始 PDF 的文字并核对量子、拓扑与对象部分；已取得 v23.0、v24.4、v25.2、v26.3、v27.1、两份 v28.1、v29.2、v30.11 的完整可读正文，复核关键定义、结论、前提和版本声明。另读取固定远端树、权威账本、工具链和与桥接有关的 Lean 声明。

这不是对所有历史数学证明的重新审定，也没有重新编译全部 Lean。历史 QM 的“回归通过”只作为其原报告的记录；本轮新写的精确检查与那些历史回执分别保存。历史原件的字节迁移未完成，正文读取不能替代原件哈希验证。

| 证据层 | 本次确认 | 合法解释 |
|---|---|---|
| Core 源 | 附件 SHA-256 为 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303` | 与所用 Frozen Core v3 源锚一致 |
| Core 覆盖 | 权威覆盖表 106 proved / 106 unique / 0 partial / 0 pending | 冻结 P-ID 合同的证明覆盖完成 |
| 压缩 | 11 generated / 89 retained adapters / 6 retained boundaries / 0 unresolved | 四生成骨架之外的适配与边界仍需保留 |
| 四生成器 | M-QD-01、M-TC-01、M-PE-01、M-OI-01 | 在声明推导系统中的不可删减骨架 |
| Theory Completion | P0–P12 的任务状态均 CLOSED | P12 的科学结论仍是 PARTIAL / EXPLICIT BOUNDARY |
| 工具链 | Lean 4.33.1；Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` | 新量子证明先保持同一工具链，另设量子包 |
| 基线 CI | Guard run 38263417684 success；proof job skipped | 此文档变更提交没有重新跑一次全量证明 |
| QM 机器表面 | 固定树及公共入口未找到 QM 专用的 Kraus/Choi/CPTP/Born 模块 | 不能把 106/106 报成全部 QM 已形式化 |

Core 定义、原 PDF 中需要独立证明的旧推论及 B0–B6 数学合同详见 [对象—协议桥接审计](audits/CORE_OBJECT_PROTOCOL_BRIDGE_20261019.md)。提交前 main 已推进至 e49dfd1139c50217269f47466717e7b1de52abbc（PR #329）；完整树比较只有 Core 入口 README 改动，已读取并保留，Lean/账本内容未变。详细 Lean 声明与固定链接见 [Lean 证据审计](audits/CORE_LEAN_TO_QM_AUDIT_20261019.md)。`PID_STATUS.yaml` 仍含旧 83/106 摘要；本方案采用明确指定为权威的 `V3_COVERAGE_STATUS.md`，不修改历史账本。

### 1.2 治理状态与数学状态分别记录

本目录遵循 [Core–Physics Contract](../interfaces/CORE_PHYSICS_CONTRACT.md) 的 C/B/S/P/E/O/X 输入分类，以及仓库现有 maturity 词汇。新纸面定理可以注明“完整推导、独立复核、精确有限检查”，但在仓库需要机器证明的 `proved` 字段上仍保持 `pending`，直到有真实 Lean 声明、导入、编译与公理回执。

Core 的语义定义以冻结源的数学合同为本次桥接依据。宪章中旧的本体论表述与新证书语义之间存在需要未来 RFC 解释的张力；本次 QM 文档不修改受保护概念，也不把旧的哲学承诺当作已证明的物理定律。

## 2. 已有 QM 成果的继承表

本表的“保留”指研究内容及其声明范围，不代表本轮重跑所有历史程序。源名、版本和读取状态见 [来源清单](status/SOURCE_MANIFEST_20261019.json)。

| 版本 / 阶段 | 必须继承的实质内容 | 关键前提与范围 | 本次升级动作 |
|---|---|---|---|
| v23.0 / 有限维核心 | 层析完备时的 FFIPS 唯一性；instrument conditioning；相干父级完成；稳定公共交换代数；SRN 的 Schur 分类；连续生成元 CPSD 条件；QDRR 有限样本界 | 复有限维操作量子扇区；Born/CP 等输入；单次 SRN 与有记忆过程不同 | 转成 Core v3 桥、受限协议算法和首个量子机器证明目标 |
| P2 / 写回 v24.4 | 在精确有限维 causal OPT 背景中，LE/CIT 与 ESP 的相对不可删选择；经典与实量子反例 | 采用 Nakahira 2026 预印本的完整背景；不是背景无关的“两条宇宙公理” | 锁定外部原文及每条背景假设，不再宣布 UEOT 独创重构数学 |
| v24.4 / P1 | separable normal sector；Weyl–CCR；Stone；自伴定义域；有限资源 CV 截断；canonical Weyl factor 与后续 spin multiplicity 分离 | 有限维操作重构不推出无限维扩张；非零中心类、ħ、正则性和表示条件仍需输入 | 优先完成有能量尾界的有限资源桥 |
| v25.2 / P3 | Wigner；Bargmann–Galilei；有质量分支 (m,s,E0)；置换扇区、Fock 与超选择 | 反幺正对称不是 CPTP 机器；普通置换不变性不能独自排除 para；非相对论 spin 不自动决定 statistics | 保留原 theorem-strength 分离；先迁移确切原件 |
| v26.3 / P4 | 有限多体基准、GKSL/Davies、过程张量、KMS/响应、SRN/记录、主动 causal break 的记忆区分 | Gibbs 存在、唯一平稳、热化和混合是不同结论；单时刻态不决定多时刻过程 | 将记忆诊断、误差与压缩算法接到同一协议数据链 |
| v27.1 / P5 | KG/Dirac/自由 EM；局域代数；谱条件、微因果性；无限模表示审计 | 算子值分布；type-III；无穷自由度不能套有限自由度 Stone–von Neumann | 继承局域代数而非锐边界密度矩阵的类型 |
| v28.1 / P6 | φ⁴ 一环、counterterm、unitarity、MS/MOM、Wilsonian/CS、EFT matching | 微扰/方案/截断范围；Object-RG、过程粗粒化、Wilsonian RG 分开 | 两个同版本文件不同，先记录冲突并逐项裁决，不能凭“(1)”自动认定新权威 |
| v29.2 / P7 | Abelian QED 一环计算层、renormalized Ward closure、散射、真空极化、Schwinger benchmark | 不是非阿贝尔全套重整化、非微扰 QED UV 完成或规范群选择 | 保留 P7 FINAL scope lock，只有实际错误才重开 |
| v30.11 / P8-R(G3) | replication barrier；GOIT 语义；水平异常的整数结构；generalized-331 与 331RHN 见证 | HGP、表示谱、补偿方式、复杂色表示、弱作用窗口均非 generic Core 定理 | 强化最终 selector；补 E^c；加入宽谱反例和完整模型门 |

早期“β1=3→Dirac index=3→三代”链继续退役。空间拓扑、规范群表示、纤维丛和 Dirac 指标各有独立数据；没有普遍定理允许从第一 Betti 数直接得到代数。原始“闭合中的相位一致性”可以在合适的规范实现中获得严谨语义，但需要独立的 QFT 异常理论。

## 3. UEOT 核心如何真正进入 QM

### 3.1 对象是相对于未来与协议的响应结构

对历史 h 和允许协议 π，给定响应律 K^π(h,·)。规范预测状态为

$$
C_{\mathcal P}(h)=\bigl(K^\pi(h,\cdot)\bigr)_{\pi\in\mathcal P}.
$$

相同对象表示首先意味着：对冻结的未来问题与协议，两个历史不可区分。最小性是信息因子化的泛性质；不是“一个微观实体的所有本质都已被唯一确定”。

量子接入先给合法的实验响应语义。例如在给定有限复量子扇区中，

$$
p(y_1,\ldots,y_T\mid a_1,\ldots,a_T,\rho)
=\operatorname{Tr}\!\left[
\mathcal I^{a_T}_{y_T}\circ\cdots\circ
\mathcal I^{a_1}_{y_1}(\rho)\right].
$$

这里的复态空间、正性和 trace pairing 必须来自显式 sector 输入或独立重构定理。给定这一步以后，Core 的响应商、递归闭包和误差运输才可以消费它。

### 3.2 预测商与可递归状态要分别证明

某些单步测量给出相同概率，不代表后续控制后仍相同。若效应族对所有允许 instrument 的 Heisenberg 拉回关闭，则相同响应状态在正概率分支上仍有相同后续响应；这才产生合法递归商。

即使 Hilbert 维数有限，密度矩阵的集合也不是有限集合。不能把一个 qubit 的连续状态空间直接实例化成要求 `Fintype State` 的有限控制定理。先使用 reachable response image、连续状态与有限操作族的正确接口。

### 3.3 Ω、载体、评价与长期结构的量子类型

Core §12 使用 χ(D)=1 表示删除 D 后证书仍通过；失败指示可另定义为 1−χ。极小毁损结构相对于冻结证书和干预族；它不是空间环、规范异常或 Dirac 指标。历史后续审计中曾有 χ 含义相反的文字，本方案采用冻结 Core 约定。

公共信息的访问支持，与物理删除子系统的后果不同。部分迹、丢弃读出、移除耦合项、禁用控制和 trace-nonincreasing 存活操作必须分别命名。只有证明 frame/保存条件后，载体对偶才有相应物理解释。

目的来自独立评价桥。GOD 是相对于明确目标、策略和时域的最优动作对应；一个 Hamiltonian 的真实演化或作用量驻值不自动等于 Bellman GOD。GOA 必须注明平稳态、Cesàro 极限、QSD、ω-limit 等输出种类。周期幺正演化可以有平稳平均而没有原轨道收敛。

Π/Φ 的分解存在 gauge 自由度；共同二维 latent 是可失败的额外结构。二驱动叙事不能推出复振幅、Born 法则或二能级系统。同一点跨环境的 Jacobian 堆叠秩约束，与跨不同参数点的堆叠不同；后者不能冒充共同二维假设的必要检验。

## 4. 已证 Lean 骨架的准确使用方式

| 骨架 | 可调用的真实表面（共同前缀 UEOT.V3.Compression） | QM 需要补的桥 | 不能自动推出 |
|---|---|---|---|
| M-QD | QuotientDescent.fiberCompatible_iff_existsUnique_descend | 合法量子响应、纤维相容、必要连续/可测性质 | CP、复线性、Hilbert、Born |
| 递归充分态（未增加 counted generator） | RecursiveSufficientState.existsUnique_reachableUpdate | 未来协议闭包与正概率条件化相容 | 任意 reduced ρ_S 对有记忆环境充分 |
| M-TC | TransportCertificate.twoStage_bound / weighted_chain_bound | 具体操作距离的三角、收缩、局部误差证书 | 自动的 trace/diamond norm 收缩 |
| M-PE | PositiveEigenstructure.qsdDoob_bundle | 对角交换代数→非负实 substochastic 矩阵及本征数据 | 任意 CPTP 的非交换 Doob、Perron 存在或混合 |
| M-OI | OccupationLimitInvariance.invariant_of_continuous_observable_residual | 密度态紧性、残差、分离观测与连续性 | 唯一吸引子或一般热化 |

M-PE 的正性是**有限实矩阵逐元素非负**；量子正性是**保持正半定锥**，两者不能互换。Hermitian Pauli 基下的 transfer matrix 为实矩阵，但可以有负元素；一般 matrix-unit Liouville 基下还可以出现复元素。

TC 的同对象、资源、恢复和生命周期定理可用于研究实验装置或逻辑量子信息的持续性。它们不会因“P12 CLOSED”而赋予粒子扇区新的基本物理定律。新的 QM package 只依赖合并后的 Core，保持量子输入在量子命名空间内。

## 5. 本轮实质数学升级：去掉三代 selector 的原子性前提

完整证明、谱检查和对照见 [三代条件定理精化](audits/G3_SELECTOR_REFINEMENT_20261019.md)。

令 Nc≥3、Nf>0、0≤k≤Nf 为整数，色群限定为 SU(Nc) 的复基本表示。在 v30.11 声明的同质 lepton-R 与 quark-R/Rbar 模板中，要求 A(R)=a≠0，且其余同通道异常补偿的总贡献为零；于是该通道三次异常抵消给出

$$
N_f+N_c(2k-N_f)=0.
$$

再要求那个已声明、全部 ordinary families 活跃的弱 SU(2)_L 微扰窗口中满足一环反屏蔽的必要预算

$$
N_f(N_c+1)<22.
$$

则无需另加 primitive/atomicity 公设，就有

$$
\boxed{N_c=N_f=3,\quad k=1.}
$$

证明要点：令 d=gcd(2Nc,Nc−1)=gcd(2,Nc−1)，**一般**正解为

$$
N_f=t\frac{2N_c}{d},\qquad
k=t\frac{N_c-1}{d},\qquad t\ge1.
$$

奇 Nc≥5 时预算至少 30；偶 Nc≥4 时预算至少 40；只剩 Nc=3，并由 12t<22 得 t=1。因此 primitive packet 是这些条件的结论，无需预设。

更准确的机理是：**异常方程给整除与下界，弱作用筛选预算给上界。** 异常方程本身对整包复制仍封闭；真正排除 t≥2 的是预算条件。

这个改进减少了一个假设，仍不等于 generic UEOT 推出自然界三代。剩余物理义务包括：为何存在相关 dynamical gauge parent；为何采用同质 lepton-R 及该 quark 模板；完整谱为何没有改变异常方程的额外补偿；为何有相应的低能匹配窗口；为什么该窗口要求 b2>0。有限窗口的一环系数为正，也不能被改写为完整理论跨阈值的 UV 渐近自由。

### 5.1 完整谱的具体修正

v30.11 的任意 β generalized-331 全异常公式，需要把带电 exotic lepton 的共轭 singlet E^c 明确列入谱。若只按文字列出的 e^c、u^c、d^c、J^c，缺少 E^c，则一般

$$
A_{\mathrm{grav}^2 X}=N_f q_E,\qquad
q_E=-\frac12-\frac{\sqrt3\,\beta}{2},
$$

并非恒零。β=−1/√3 的 RHN 见证因 q_E=0 不受此项影响。新审计同时给出含/不含 E^c 的结果，避免把特殊点的通过外推到任意 β。

### 5.2 一个必须保留的宽谱反例

允许 lepton 同时使用 R 与 Rbar 后，β=0、Nc=3、Nf=2、各一份 lepton 和 quark 取两种表示的局部异常谱，可以通过六项多项式异常检查和弱预算。它表明“广义 HGP+复杂色+弱预算”仍不足以唯一选择三代；**同质表示模板是有内容的额外限制**。该见证只是局部异常代数反例，尚不是完整全局规范、标量真空、质量谱或实验可行的理论。

## 6. 第一主线：受限协议下的量子对象闭包

### 6.1 一个明确可实现的算法

先给定 d 维量子模型、固定时齐的有限 instrument 字母表，并允许每一步使用这些操作及其所有有限因果组合。在这个明确的协议类中，从

$$
W_0=\operatorname{span}_{\mathbb R}\{I\}
$$

开始，迭代

$$
W_{n+1}=\operatorname{span}_{\mathbb R}
\left(W_n\cup
\{(\mathcal I^a_y)^*(E):E\in W_n,\ a,y\}\right).
$$

W_n 属于实 Hermitian 空间，维数最多 d²；严格增维次数最多 d²−1。达到不再增维的 W_* 后，定义

$$
\rho\sim_{\mathcal P}\sigma
\iff \operatorname{Tr}[(\rho-\sigma)E]=0
\quad\forall E\in W_*.
$$

W_* 张成这个协议类中所有有限记录词的效应；相同响应在同一个允许自适应控制策略下给出相同记录律。正概率 outcome 的归一化更新保持该等价关系。由此接到 Core 的 reachable recursive state，不需要人为把目标更新函数作为结构字段预先假定。

如果实际控制受协议自动机、时刻或有限时域限制，必须保留该协议状态/剩余时域，构造分层或带协议状态的闭包。直接对全部字母任意组合求 W_* 仍可给充分表示，但不能据此声称它是原受限协议库的最小表示。非时齐操作先标记时间或增广状态；线性最小维数还要相对于实际可达初态差分空间计算。

### 6.2 为什么它是一次真正的整合

v23 已有层析完备情形的 FFIPS 和 instrument conditioning；本轮不把这些旧成果重新命名为新发现。新增目标是：从**受限协议库**自动求出与任务相对的最小线性预测表示，并让状态商、可继续的协议、误差证书和已有 Lean theorem 彼此对应。

仅 Z 测量时，W_* 为 span{I,Z}，|+⟩ 与 |−⟩被合并；允许 Hadamard 后再测 Z 时，闭包必须加入 X，两态被区分。已有精确基准验证这个变化，后续必须证明任意有限词的结论，而不只验证两步例子。

W_* 给出的响应坐标集合一般不是某个更小 Hilbert 空间中的完整密度矩阵集合。若要求降阶模型仍为物理 CPTP/Lindblad 系统，需要额外的算子代数闭包、编码/解码、完全正性及动力学交织证明。

### 6.3 与成熟研究的关系

可观测/Krylov 空间、量子条件期望和保持 CP 的模型降阶已有明确研究。离散开放量子系统、连续 Lindblad、受控 Lindblad、2026 年近似降阶均有可复用的数学基线 [R2–R5]。

UEOT 的候选增量应定位为：统一管理协议变化、预测充分性、对象身份、误差预算和可失败证书；通过与相同任务/准确度的成熟降阶方法比较，验证是否减少模型维数、采样或计算成本。若仅把标准降阶结果换名，则该部分作为适配器发表。

### 6.4 六个最先机器证明的目标

| ID | 精确目标 | 真实依赖 | 必须的负例 / 出口 |
|---|---|---|---|
| QMB-01 | Kraus 完整性→PSD、trace、分支概率及记录律合法；p>0 时后验合法 | 新量子矩阵基础；之后接 Core 响应核 | 非完整 Kraus、零概率分支；不能先假定所求概率已合法 |
| QMB-02 | 效应响应商→唯一下降；层析完备才推出 ρ=σ | M-QD、QuotientGauge | Z-only 合并；扩协议后分离 |
| QMB-03 | W_* 闭包→正概率分支相容→reachable 更新 | RecursiveSufficientState、PredictionUpdate | 同 ρ_S、不同环境记忆的两步反例 |
| QMB-04 | 具体协议距离的收缩及有限链误差 | M-TC、记录律 TV | rare post-selection 放大；有限协议界不冒充 diamond 界 |
| QMB-05 | CPTP Cesàro 残差→任意极限点平稳 | M-OI，加紧性/PSD/连续性适配 | identity 多平稳态；幺正周期不逐点收敛 |
| QMB-06 | 保持对角交换代数的 CP 存活映射→substochastic→QSD/Doob | M-PE | 一般相干通道越出该代数；本征数据需独立来源 |

每个 ID 都需要 theorem statement、导入路径、假设表和匹配源码；本方案中的名称是任务标识，不是已经存在的 Lean declaration。QMB-03 的正概率条件化是 partial update：需显式限定合法的 (state,a,y) 域，或先构造 subnormalized/Option 型总更新，再向 Core 的 reachable 接口提供正确类型的纤维相容证明。零概率延拓不具有已认证后验的物理含义。

## 7. 误差、记忆与有限数据必须接在同一条链上

### 7.1 操作距离先从声明协议定义

先用

$$
d_{\mathcal P}(\rho,\sigma)=
\sup_{\pi\in\mathcal P}\mathrm{TV}
\bigl(P^\pi_\rho,P^\pi_\sigma\bigr)
$$

表达任务相关差别。有限测量集可以给可计算区间；但若要断言某操作下收缩，协议集合必须对相应继续/后处理满足所需闭包。对固定长度库，还需明确时间索引或把一步推进后的测试嵌入更长的库。

完整 CPTP trace-distance 收缩或 ancilla-uniform diamond 范数是更强的独立接口，不得由一小组测试未见差异推出。尤其不能把“positivity 在一个系统上成立”替代 CP；transpose 的半边 Bell 态例应成为永久对照。

### 7.2 可组合误差

先明确所有时刻的误差、局部预算与放大系数非负，即 e_t≥0、ε_t≥0、L_t≥0，再证明局部

$$
e_{t+1}\le L_t e_t+\epsilon_t,
$$

再调用 M-TC 得

$$
e_T\le e_0\prod_{j<T}L_j+
\sum_{t<T}\epsilon_t\prod_{t<j<T}L_j.
$$

在已证明 0≤L_t≤1 的情形，界简化为初始误差加局部缺陷之和。ε_t 分别说明截断、模型近似、参数估计和数据误差；共享的置信事件不得重复扣除或重复当作独立收益。

后选择归一化有 1/p 量级的敏感性，必须给成功概率下界，或用 subnormalized branch 直接比较。一次概率很小的事件可以把相近的先验状态变成彼此完全可区分的后验；已有新精确例专门保护这条边界。

### 7.3 记忆模型选择

同一个 ρ_S 不保证同一个未来。用实际可干预的 causal-break 协议比较：

- reset-state-only Markov predictor；
- 有限 memory extension；
- 必要时 process-tensor predictor。

复用 v26.3 的主动干预区分，而不是只拟合自由演化轨迹。若扩大模型减少了留出预测误差，要同时记录状态/参数量、训练预算、控制覆盖和失效时域。过程张量的完备表达不意味着它在每个问题上计算最便宜。

### 7.4 与 C2/C5/C7 的直接对接

量子侧的发现数据选 W、memory size、近似阶数或参数；认证数据评估冻结后的协议和模型。iid shots、时间相关轨迹、漂移和自适应采样使用各自合法的误差模型。不能把一条相关轨迹的每个时间点当作独立 shot。

Π/Φ 的共同维数检验若进入量子模型，必须先有独立可测的驱动锚、至少三个可检验方向及同一参数点的跨环境响应。低秩只给局部维数信息，不证明两驱动物理机制。

## 8. 第二个近期出口：保留并加强 SRN/QDRR

### 8.1 已有数学不要丢失

对固定正交记录块 {P_a}，v23 的 strong record-nondemolition CPTP 映射在相应类内写为

$$
\mathcal A_K(X)=\sum_{a,b}K_{ab}P_aXP_b,
\qquad K\succeq0,\quad K_{aa}=1.
$$

连续、时齐 SRN 半群还要求 Hermitian 零对角生成元 Λ 在零和子空间上 CPSD，且 K_ab(t)=exp(tΛ_ab)。逐对衰减率非正不保证全局 PSD。

标准无额外 SRN 作用的 kernel 为全 1 矩阵 J；完全去相干为 I。ORC/公共记录不决定二者谁真实发生，公共块对角读出也不能区分它们。要读出 inter-branch coherence，必须用相干写入—作用—擦除和两相位测试。

### 8.2 有限样本合同

取 m≥2、ε>0、0<α<1；m 个记录块需 L=m(m−1) 个实坐标设置，shots 数 n 取满足下界的整数。单次测量值在 [−1,1]，每设置 n 个 iid shots 时，沿用 v23 已修正的界：

$$
n\ge \frac{2}{\epsilon^2}\log\frac{2m(m-1)}{\alpha}
$$

可使全部实/虚坐标在共同概率至少 1−α 的事件上误差≤ε，进而

$$
\|\widehat K-K\|_{\rm op}\le
\|\widehat K-K\|_F\le
\epsilon\sqrt{2m(m-1)}.
$$

这只是所声明 SRN 类与 iid 设置的统计保证，不是任意非 Markov 新物理的完整层析，也不是现实设备已达到该精度。

### 8.3 第一份实验预注册要具体回答

固定候选 law、记录证书阈值、时域、memory 假设、SPAM/泄漏校准、最小可区分偏差及 α 预算。随机交错目标与基线协议；独立估计读写擦除误差；保留相同深度但不形成目标记录的控制；预先定义如何处理漂移和失败 shots。

硬件噪声可能与目标 SRN kernel 完全不可辨识。只有在它们确实属于相应独立 Schur 类时，才可使用逐元素合成公式；不能看到 coherence loss 就称为额外坍缩。无法通过独立校准/控制识别目标时，输出“总通道可估，目标机制不可识别”。

近期成功标准是：已知注入的 SRN 作用可恢复；标准噪声基线不被误报；超出 SRN 类的泄漏/记忆例会拒绝使用不适用的完整性声明。真实实验支持要等独立设备记录和预注册验证，不能用本轮算术例替代。

## 9. 无限维、QFT 与 RG 的升级方式

### 9.1 CV：从可认证有限资源开始

v24 已经处理无界算子、自伴性与 canonical Weyl factor。下一项实用桥应给：H0≥0、Λ>0、低能谱投影 P_Λ=1_[0,Λ)(H0) 及其有限秩证明，能量界 Tr(ρH0)≤E，以及尾概率

$$
\delta=\operatorname{Tr}[(I-P_\Lambda)\rho]\le E/\Lambda.
$$

这里使用 H0≥Λ(I−P_Λ)；任意有限秩谱投影并不保证该尾界。在 δ<1 时，选择 D(ρ,σ)=½‖ρ−σ‖₁、ρ_Λ=P_ΛρP_Λ/(1−δ)，可将明确目标写为 D(ρ,ρ_Λ)≤√δ：投影后的归一化纯化与原纯化重叠为 √(1−δ)，再用部分迹收缩。对应的纯化/收缩引理仍须在量子包内实际证明或合法引用，不能只提交这个结果字段。P_Λ 的有限秩必须另有 compact-resolvent/离散谱等保证；自由空间粒子的能量截断不自动有限秩。

随后将 cutoff、观测近似和有限样本误差接 M-TC。有限矩阵满足 Tr[Q_N,P_N]=0，不能在整个截断空间精确满足非零 ħ 的 CCR。通过合适态/能量约束与有界 Weyl 观测验证近似，而不要求不可能的全空间矩阵恒等式。

“有限 canonical 自由度”与“有限 Hilbert 维数”必须分开。Stone–von Neumann 的适用条件不能被扩到无限场模；Fock 或局域代数也不能从 qubit 模型直接推出。

### 9.2 QFT：保留局域代数与可实现协议

v27 的 O↦A(O)、局域状态泛函及仪器是合适起点。锐边界区域不能默认拥有 intrinsic density matrix 和有限 trace。若用 lattice/mode cutoff 或 split collar 获得近似 tensor factor，记录该选择、能量与分辨率误差。

首先验证同一自由场或可控微扰模型中的有界读出、相关函数和协议响应如何给出 Core 所需对象证书。先验地知道一个 commutator 在类空分离为零，与一个 Feynman propagator 非零不矛盾；证书应检验真实可控响应，不把关联当作信号。

### 9.3 RG：只做一座定义完整的小桥

保留三种类型：

| 类型 | 输入 / 输出 | 保存目标 |
|---|---|---|
| Object-RG | 固定性质、目标、时域和底载体下的分辨率/表示变化 | 嵌套闭包族及分辨率映射的复合律 |
| 过程粗粒化 | 动态状态、记忆或实验记录的缩减 | 指定过程律、干预与预测 |
| Wilsonian RG | 选定 cutoff、作用量与场模消去 | 低能关联/散射的有效描述 |

纯 Object-RG 沿用 Core §14.1 的固定条件。如果协议、时域或对象目标改变，需要另声明 Core §28.3 的协议 lift J_AB、读出 C_AB，以及 (C_AB)#P_A^(J_AB u)=P_B^u 或对应 TV 缺陷；不能直接引用纯分辨率定理。

第一项跨类型桥选有限正规化的 Gaussian 或重轻场模型，显式声明 split、初态、real-time contour/Euclidean 约定，分别计算消去后 influence functional、reduced process 和低能响应。只在指定观测/能标范围建立相等或误差界。

Euclidean 积分掉场变量不自动给实时间 CPTP 通道；counterterm 的重整化尺度 μ 与物理 cutoff 也不同。把 v28 的独立系数抽取、scheme 比较与 EFT 散射匹配作为回归基础，不用同一个公式两边重复求值伪装桥接。

## 10. 三代与规范前沿：从整数结果走向物理适用性

### 10.1 GOIT 的严格位置

Core 给“已声明的表示运输应保存操作响应”的条件结构。标准 chiral QFT 提供 determinant/Pfaffian line、局域曲率异常、全局 holonomy/η 数据及所需平凡化 [R6–R7]。二者的连接是明确的 realization bridge。

受限公共概率不变本身不能反推 anomaly line 可平凡化。必须核对 equivariant、connection-compatible 的完整规范实现，以及所有 matter/counterterm/inflow。未被提升为动力学规范对称的 global symmetry 的 ’t Hooft anomaly 与 dynamical gauge anomaly 不能混用。

### 10.2 将“只差 HGP”改成独立义务表

| 义务 | 应给什么证据 | 失败时影响 |
|---|---|---|
| HGP 存在 | 具体 gauge group、作用、连接场与表示，或能独立检验的 sector law | 三代定理不能用于真实粒子 |
| 同质 R/Rbar 模板 | 从额外结构导出该谱，或明确承认是模型假设 | 宽谱两代反例使唯一性失效 |
| 完整异常 | 全部 Weyl multiplets；所有局域、多项式与适用的全局检查；补偿机制列齐 | 单个 cubic equation 不能代表全局一致 |
| RG/匹配 | ordinary/exotic/scalar 的质量阈值、breaking pattern、窗口与 b2 | 一环预算无法用于不匹配的有效理论 |
| 动力学存在 | 标量势、可接受真空、质量与 Yukawa、幺正性及适用能标 | 代数谱尚未成为物理模型 |
| 可辨识后果 | 有确定参数依赖的额外耦合/谱/过程，独立数据竞争 | 只重现整数不能获得经验支持 |

CKM/PMNS mixing 不是局域水平 gauge symmetry 的证明。若提出新的评价桥选择某谱，该桥的目标、可行类和机制来源同样需要独立依据；不能把“优选三代”预装进目标再称为推导。

### 10.3 把谱模板接到具体耦合条件

331 的 SU(3)_L 是扩展弱群；它通过各代采用不同表示造成跨代异常约束，并不自动是直接作用于 family 指标的独立水平规范群。HGP 实现应分别登记这两种类型。

在固定的 SU(3)_L×U(1)_X 谱、无 exotic–light mixing 的近似内，ordinary lepton doublet 的两种表示给

$$
t_8^\pm=\pm\frac{1}{2\sqrt3},\qquad X=Y-\beta t_8.
$$

若某个重中性规范玻色子的耦合由完整协变导数和规范混合计算为

$$
\kappa_\pm=A t_8^\pm+B Y_L,
$$

则在 A≠0、相同 Y_L 且没有额外混合的条件下，κ_+≠κ_-。因此，**独立成立的重中性流轻子普适性**可能把同质表示模板转化为一个可计算条件。低能 SU(2) 耦合普适性本身不足以证明这个条件；此处也没有声称重中性流普适性已有实验支持。

这里的普适性要求 ordinary-light lepton 子空间上的完整耦合矩阵为 κI，包含该 mediator 不产生 flavor-changing 非对角耦合；仅有质量基底中的对角耦合相等不够。混合 κ_+、κ_- 的 Hadamard 旋转可使对角元相等，却留下非零非对角元，因此该负例必须保留。

下一步应从具体 gauge mixing 求 A、B，证明不退化条件，列出高维表示、vectorlike/exotic 混合及阈值的例外。如果不能独立接受上述普适性，该桥仍保留为模型假设。

### 10.4 从特殊 quark family 导出独立可观测关联

在已经声明并验收的 331-like 类内，k=1 意味着一个特殊表示的夸克代。若无 exotic–light mixing，且只有指定的中性流结构，则 gauge basis 中

$$
G_q=g_q I+\Delta g\,P,\qquad P^2=P=P^\dagger,\quad\operatorname{rank}P=1.
$$

幺正旋转到质量基底保留

$$
G_q^{\mathrm{mass}}=g_q I+\Delta g\,vv^\dagger,\qquad v^\dagger v=1.
$$

非普适部分 Δ_q 的二阶 minors 为零，例如

$$
(\Delta_q)_{ij}(\Delta_q)_{jk}=(\Delta_q)_{jj}(\Delta_q)_{ik}.
$$

当 Δg=0 时非普适部分退化为零，不能声称观察到了非零秩一信号。后续工作是证明特定 mediator 下 FCNC / Wilson coefficients 的对应关系，再为 exotic mixing、loop 和多 mediator 贡献计算误差预算；不能将上述矩阵恒等式直接当成一般 EFT 系数的现成恒等式。

用一组数据拟合参数，以独立过程检验关联。这里的标准 331 非普适耦合结构属于既有物理机制 [R8–R9]；UEOT 的工作是给出精确协议、表示不变量和可拒绝的误差证书。这一目标已进入 QMU-09，尚未完成完整模型或实验门。

### 10.5 搜索程序如何避免“为了三而三”

先冻结候选群、表示库、multiplicity 约定和补偿政策；算法接收这些数据，不接收目标 Nf=3。对每个谱从逐 Weyl 表计算异常与一环系数，输出所有 surviving spectra 及未完成的全局/动力学门。

在本次简化模板中，AF 预算已经给出解析有限边界，所以可以做真正穷尽的整数检查。扩大表示库后，如果尚无解析全域界，有限扫描只能报告其范围。primitive/Hilbert-basis 枚举可作组织工具，但不预设宇宙只实现一个基元。

将现有 331 算术列为 prior art [R8–R9]。UEOT 可能的增量应在“为何选择这个 realization class、它在新协议下限制什么结果”上获得证明或反例。参数拟合、相同标准模型预测与真正排除替代理论分开记账。

## 11. 工作包、依赖与验收

下表为后续执行顺序；除 QMU-00 与本轮已有的纸面/精确检查外，均是计划，不能按日期自动置为完成。

| 工作包 | 输入 | 交付物 | 完成标准 |
|---|---|---|---|
| QMU-00 权威/方案整合 | 本轮全部来源 | 本目录方案、审计、来源与 claim ledger | 来源可追踪、前提不漏、远端文件可读取 |
| QMU-01 三代精化 | v30.11 + 新对照 | 无 atomicity 的证明；完整谱/反例；随后 Lean 算术目标 | 纸面独立复核；机器状态单列；不把局部谱标为完整理论 |
| QMU-02 量子包最小建立 | 固定 Core/工具链，v23 | QMB-01/02 的最小矩阵、效应与响应商 | 实际导入与编译；无物理结论字段偷装；有限正负例 |
| QMU-03 协议闭包 | QMU-02 | W_* 算法、QMB-03、memory 对照 | 任意允许有限词的证明；reachable 更新；扩协议单调细化 |
| QMU-04 缺陷组合 | QMU-02/03 | QMB-04、有限置信证书 | 每个局部界有独立来源；后选择/漂移失证正确 |
| QMU-05 QDRR 方法闭环 | v23 + QMU-04 | 冻结模拟、噪声对照、预注册、数据合同 | 已知作用恢复与误报控制；真实实验另行验收 |
| QMU-06 长期/存活 | QMU-02/04 | QMB-05/06 | 平稳/混合/QSD 分开；M-PE 仅合法交换桥 |
| QMU-07 CV 资源桥 | v24.4 + QMU-04 | 能量尾界、有限秩与 Weyl 测试 | 有限资源误差；不宣称有限矩阵精确 CCR |
| QMU-08 QFT/RG 小桥 | v27–29 版本裁决 | 一个正规化模型的响应交织与误差 | 三种 RG 类型明确、两侧独立计算 |
| QMU-09 HGP 模型类 | QMU-01 + 物理谱输入 | 谱枚举、全局异常/真空/匹配与预测 | 每道门有证据；失败候选保留；不以 Nf=3 为筛选输入 |

### 11.1 第一轮投入安排

用三位执行角色和一位整合/独立审查角色时：

- 量子数学执行者拥有 QMU-02/03；
- 误差与验证执行者拥有 QMU-04/05；
- 粒子前沿执行者拥有 QMU-01/09；
- 整合者负责共享接口、源版本、审查、提交和验收。

第一轮约两至四周的目标是一个端到端有限维切片，而非上述所有包完成。第一周以 QMB-01/02 和 selector 算术为起点；第二周联通 W_*、记忆负例和有限链误差；后续按依赖完成 QDRR 方法验证。若 Lean 的量子线性代数底座不足，先缩小到明确的矩阵/trace 定理，不创建带待证结论字段的万能接口。

现实数据等待不会由模拟替代。并行收益来自不同文件与不同数学义务的独立推进；公共 import 根和 claim ledger 由整合者独占，消费其他工作时以已合并基线为准。

### 11.2 一个工作包的交接卡

```text
ID / owner / current status:
Base Core commit and toolchain:
QM source version and exact artifact identity:
Precise statement / protocol / domain:
Core theorem dependencies:
Sector / physical / effective assumptions:
Implementation or proof paths:
Positive example / counterexample / refusal condition:
Error budget and data split:
Evidence: hand proof / Lean / regression / experiment:
Review and exact commit:
Next still-needed action:
```

不重复建 Core 106 的第二套台账，不把 paper theorem 数或 benchmark 次数换算成 Core 覆盖。

## 12. 目录与执行约定

本次实际文件全部位于现有 QM 目录：

| 路径 | 作用 |
|---|---|
| `README.md` | 当前入口 |
| `ROADMAP.md` | 精简路线与版本入口 |
| `UEOT_QM_UPGRADE_PLAN_v31.0.md` | 本完整方案 |
| `audits/CORE_LEAN_TO_QM_AUDIT_20261019.md` | 精确 Lean 证据和接口边界 |
| `audits/CORE_OBJECT_PROTOCOL_BRIDGE_20261019.md` | Core 定义对照、旧推论边界与操作桥推导 |
| `audits/G3_SELECTOR_REFINEMENT_20261019.md` | 新 selector 证明、完整谱与反例 |
| `status/SOURCE_MANIFEST_20261019.json` | 来源、版本冲突与读取/字节核验范围 |
| `status/CLAIM_LEDGER_v31.json` | 非 counted QM 主张及机器/经验状态 |
| `status/CURRENT.json` | 方案接受范围与下一步 |
| `benchmarks/qm_bridge_benchmarks.py` | 新写的精确操作桥例 |
| `benchmarks/qm_frontier_exact_audit.py` | 新写的异常算术与谱对照 |
| `benchmarks/results/*.json` | 本轮新程序的实际回执 |

后续量子 Lean 建议放入 `formalization/ueot-qm/`，共享数学只在被证明为 domain-neutral 后通过正常治理回流 Core。QFT、RG/EFT 和通用 validation 产物沿现有架构进入各自目录；本目录保留研究总入口和链接。

本轮是用户明确要求的 QM 领域规划升级。采用领域审计与 `status/CURRENT.json` 的接受范围记录，限于方案、纸面精化与可复算证据，不变更宪章、Frozen Core、counted ledger、其他活跃 PR 的科学状态。

提交前检查同一目标是否已存在；使用一条临时 `qm/*` 分支与一个 PR。验证与变更范围匹配：本文档链接/JSON/脚本检查、相关精确回归；没有 Lean 变更时不借机跑全量 Core 来制造新的“QM 已证”标记。合并后核对文件树与内容，按仓库实际门禁收尾。

## 13. 成功与失败的明确含义

**首轮成功**：有限量子仪器产生合法记录律；从可执行协议求得的对象表示能递归预测；扩大协议暴露先前不可见差别；误差界覆盖已声明场景；不适用的记忆/后选择案例会失证；至少一条关键桥拥有机器证明；selector 的条件包更少且反例更清楚。

**方法结果**：如果压缩/证书与成熟方法相当，保留为可审计实现；如果在相同预算、准确度、协议范围下有优势，再提出该范围内的性能结论。

**物理结果**：新 law 只有在产生独立可观测约束并通过对应数据验证后，才升级为经验支持。标准 QM 的重述或三代整数的条件复现，不自动增加物理预测。

**有效失败**：假设不够、量子子代数不存在、Markov 记忆错误、稀有条件化失证、谱模板被反例打破、完整异常或匹配失败，都应成为可复用结果。失败不能通过重设目标、删去负例或更换“完成”的含义隐藏。

本计划的下一项主执行目标是 **QMU-02：有限 instrument→操作响应商的最小量子证明包**；QMU-01 的整数 selector 可作为独立、低耦合的首个算术形式化任务。QDRR 与 HGP 继续作为近期实验方法出口和长期粒子前沿出口，分别按各自证据推进。

## 14. 主要一手来源与来源性质

内部原文和固定源码的详细索引见来源清单及专题审计。下列文献提供外部数学与物理结果，不转记为 UEOT 原创：

- **[R1]** K. Nakahira, *Two Operational Principles Single Out Quantum Theory*, arXiv:2605.23217v1 (2026), [原文](https://arxiv.org/html/2605.23217v1)。本轮核对 Theorem 1、LE/ESP 与 Appendix A 入口；仍按外部预印本处理，没有声称其已进入 Lean。
- **[R2]** T. Grigoletto, F. Ticozzi, *Model Reduction for Quantum Systems: Discrete-time Quantum Walks and Open Markov Dynamics*, [arXiv:2307.06319](https://arxiv.org/abs/2307.06319)。量子物理性约束下的离散降阶基线。
- **[R3]** T. Grigoletto et al., *Exact Model Reduction for Continuous-Time Open Quantum Dynamics*, Quantum 9, 1814 (2025), [arXiv:2412.05102v3](https://arxiv.org/abs/2412.05102v3)。区分最小线性模型与保持 Lindblad 结构的量子模型。
- **[R4]** T. Grigoletto, L. Viola, F. Ticozzi, *Model Reduction for Controlled Quantum Markov Dynamics*, [arXiv:2510.25546v1](https://arxiv.org/abs/2510.25546v1)。受控时变 Lindblad 的降阶接口。
- **[R5]** T. Grigoletto et al., *Approximate Reduced Lindblad Dynamics via Algebraic and Adiabatic Methods*, [arXiv:2603.11982v2](https://arxiv.org/abs/2603.11982v2)（2026-08-07 修订）。近似、CP 保持和有限时间误差的现行基线；其具体假设仍须在选定模型逐项核对。
- **[R6]** K. Yonekura, *Dai-Freed theorem and topological phases of matter*, [arXiv:1607.01873](https://arxiv.org/abs/1607.01873)。determinant-line/η 的标准来源。
- **[R7]** I. García-Etxebarria, M. Montero, *Dai-Freed anomalies in particle physics*, JHEP 08 (2019) 003, [arXiv:1808.00009](https://arxiv.org/abs/1808.00009)。局域与全局一致性需明确拓扑/规范背景。
- **[R8]** C. Corianò, D. Melle, *The SU(3)C × SU(3)L × U(1)X (331) Model: Addressing the Fermion Families Problem within Horizontal Anomalies Cancellation*, [arXiv:2404.05821](https://arxiv.org/abs/2404.05821)。331 机制的已有研究背景。
- **[R9]** R. A. Diaz, R. Martinez, F. Ochoa, *SU(3)c × SU(3)L × U(1)X models for β arbitrary and families with mirror fermions*, Phys. Rev. D72, 035018 (2005), [arXiv:hep-ph/0411263](https://arxiv.org/abs/hep-ph/0411263)。不同谱选择会改变异常结论。
- **[R10]** G. Chiribella, G. M. D’Ariano, P. Perinotti, *Informational derivation of Quantum Theory*, Phys. Rev. A84, 012311 (2011), [arXiv:1011.6451](https://arxiv.org/abs/1011.6451)。比较重构背景与 purification 的独立来源。

