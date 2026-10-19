# UEOT Core Lean → UEOT-QM：固定主线证据与桥接优先级

审查日期：2026-10-19。只读审查基线：`MurphyHoops/UEOT@195ebb06fb8afcc592c69671dabfd2250e9d1989`。本报告依据固定提交树、权威账本和选定源码。本轮未重新编译 Lean；当前提交的文档门禁与历史证明回执分别记录。本文是本次 QM 规划的正式证据审计，不改变原有 Core 证明计数。

## 1. 可确认的成果与证据层级

| 项目 | 固定基线的证据 | 应如何表述 |
|---|---|---|
| Frozen Core v3 | `docs/V3_COVERAGE_STATUS.md` 声明 106 proved / 106 unique / 0 partial / 0 pending；最终账本 main `1e2a3924ef31b5dca589dca69c3838fc355b8850`，resulting-main CI `36249418600` | 106/106 是冻结源 P-ID 合同的完成，不是从零公理推出所有物理的证明 |
| Compression FINAL | `COMPRESSION_LEDGER.yaml`：11 generated，89 retained adapters，6 retained boundaries，0 unresolved，4 counted generators | 四个生成骨架确有跨族复用；89 个适配器与 6 个边界没有因压缩而消失 |
| TC P0–P12 | `THEORY_COMPLETION_STATUS.json` 全 CLOSED；program CLOSED；next_stage PROGRAM_COMPLETE | 程序关账不等于所有理论问题已无条件解决 |
| P12 科学结论 | 同一 JSON 明列 `PARTIAL / EXPLICIT BOUNDARY`；源码终点为 `p12_terminal_conditional_finite_lifecycle` | 有限、条件性的同一对象生命周期拼接；仍有程序源、物理模型、资源、谱系、尺度保存等输入 |
| 工具链 | `lean-toolchain` = `leanprover/lean4:v4.33.1`；lakefile 与 manifest 都固定 Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` | 下一步桥接先沿用固定版本，不能假定当前在线 Mathlib 新 API 已进入仓库 |
| 本次基线 CI | API 查询到 `UEOT Core Compression Guard` run `38263417684`，push/main，success；check `classify`、`governance` success，`proof` skipped | 不能写“本轮这个 SHA 刚重新完成全量 Lean 编译”；这是文档变更门禁，历史证明账本另有证据 |

账本存在可解释的历史漂移。`PID_STATUS.yaml` 顶层仍是 2026-09-16 的 83 integrated / 23 pending 摘要；`FORMALIZATION_STATE.md` 明确指定 `V3_COVERAGE_STATUS.md` 为覆盖率真值。部分 P0/P12 文档页首还保留 LOCAL / UNMERGED，canonical 状态应由 TC JSON 与固定主线源代码确认。本轮 QM 方案应注明权威源和版本，不应顺带重写冻结账本。

规模口径也需重新声明。固定提交递归树未截断，共有 640 个 `.lean` 文件，含 lakefile、文档类型检查和审计脚本。`formalization/ueot-core/UEOT/` 下 634 个，其中 `ThirdParty` 11 个；排除这 11 个得 623 个，加顶层 `UEOT.lean` 为 624 个第一方生产 Lean 文件。因此不能原样沿用别的时点或口径的“633 个第一方模块”。

`physics/qm/` 下没有 Lean 文件。读取官方 `UEOT.lean`、`UEOT/V3.lean`、`UEOT/V3/Compression.lean` 导入入口和完整文件路径树，未发现 Quantum、Kraus、Choi、CPTP、Born 命名的专门证明模块。这里的结论是**本轮未找到该仓库 QM 专门机器证明入口**，不是对其他仓库或所有未读声明作不存在断言。`HilbertMean*` 是 Hilbert 空间中的概率/统计浓缩工作，不能凭名称当成量子 Hilbert 重构或 Born 法则证明。

## 2. 四个 counted generators 的准确含义

### 2.1 M-QD-01：Quotient Descent

源码：`UEOT/V3/Compression/QuotientDescent.lean`；namespace `UEOT.V3.Compression.QuotientDescent`。

主要准确名称：

- `fiberCompatible_iff_existsUnique_descend`
- `countableAEFamily_descend`
- `strongLumpability_unique_setLevel_descend`
- `existsUnique_twoSidedDescend`
- `exactSeparatedFactorization_refines_responseEq`
- 源接口：`p_pred_01_via_countableAE_descent`、`p_int_02_via_twoSidedDescent`。

核心命题是：给定满射 `q : X → Y`，`g : X → Z` 在 q 的纤维上恒定，当且仅当存在唯一 `gbar : Y → Z` 满足 `gbar ∘ q = g`。这是集合层次的泛性质。概率、复线性、正性、完全正性、连续性、可测性、张量组合性都不从这个等式自动产生。

`countableAEFamily_descend` 明确要求可数协议指标、坐标解码器可测性和各自几乎处处因子化，才构造公共满测度事件及联合解码。`strongLumpability_unique_setLevel_descend` 的结论类型是 `DM → Measure DM`，而不是 `Kernel DM DM`；并且前提已给出 `Pbar : Kernel DM DM` 与 `StrongLumpability` 见证。该生成器不能被包装成“UEOT 已自动生成任何宏观物理过程”。

补充的真实可复用表面：`UEOT.V3.Compression.RecursiveSufficientState.existsUnique_reachableUpdate`。它把 `InputFiberCompatible C R` 变成 `Set.range C` 上唯一更新，避免假定所有坐标值都能实际到达。`existsUnique_ambientUpdate_of_surjective` 则需要状态编码真的满射。量子有限维不意味着密度矩阵状态集有限；不能把 qubit 的连续状态空间直接塞进 `[Fintype State]` 的控制定理。

### 2.2 M-TC-01：Transport Certificate Calculus

源码：`UEOT/V3/Compression/TransportCertificate.lean`；namespace `UEOT.V3.Compression.TransportCertificate`。

准确名称：`twoStage_bound`、`twoStage_exact`、`factorRoute_exact`、`chain_bound`、`weighted_chain_bound`、`multiplicative_chain_lower_bound`。

这是误差传递骨架。`twoStage_bound` 显式接收本对输入上的收缩不等式、三角不等式、旧误差和新误差；不在内部证明量子 trace norm 或 diamond norm 收缩。`weighted_chain_bound` 允许每步非负放大常数 L，得到

$$
e_n\le\left(\prod_{j<n}L_j\right)e_0+\sum_{k<n}\epsilon_k\prod_{k<j<n}L_j.
$$

UEOT-QM 的真正新工作是给出合适的实验可观测距离，证明物理通道作用的传输不等式，并把统计误差、模型误差、截断误差各自注入局部项。把希望成立的最终整体误差直接填入 certificate 不构成新证明。

### 2.3 M-PE-01：Positive Eigenstructure Calculus

源码：`UEOT/V3/Compression/PositiveEigenstructure.lean`；namespace `UEOT.V3.Compression.PositiveEigenstructure`。

准确名称：`qsdDoob_bundle`、`scale_le_one_of_substochastic`、`stochasticRightEigen_bundle`。源接口包括 `p_qsd_02_via_positiveEigenstructure`、`p_qsd_02_killed_via_positiveEigenstructure`、`p_evo_04_via_positiveEigenstructure`。

真实类型是有限 `Matrix I I ℝ`。`RightEigenData M` **输入** λ>0、每坐标严格正 h、Mh=λh；`BiEigenData M` 还输入逐元素 M≥0、q≥0、sum q=1、sum qh=1 和 qM=λq。由这些数据推出

$$
\widetilde M_{ij}=\frac{M_{ij}h_j}{\lambda h_i},\qquad \pi_i=q_i h_i,
$$

的行归一化、非负性、平稳性和 QSD 归一化公式；若行和 ≤1，还推出 λ≤1。Perron 存在性、唯一性、主导谱与收敛速度没有由本生成器给出。`stochasticRightEigen_bundle` 的适应性、可积性、非负坐标、确定初态及条件均值演化也都是输入。

**QM 最容易误用的地方**：量子完全正映射在任意 Liouville/Pauli 坐标中的矩阵，不是逐元素非负矩阵；正半定锥和坐标非负正交锥不同。不能把任意 CPTP 超算子直接当作 M-PE 的 M。第一步宜对保持对角交换子代数的 quantum channel 建立经典 substochastic 矩阵桥，再调用现有 theorem。非交换 Doob transform 需要平方根、逆、谱支持和 CP/TP 等新证明。

### 2.4 M-OI-01：Occupation-Limit Invariance

源码：`UEOT/V3/Compression/OccupationLimitInvariance.lean`；namespace `UEOT.V3.Compression.OccupationLimitInvariance`。

准确名称：`equal_at_limit_of_residual`、`invariant_of_observable_residual`、`invariant_of_continuous_observable_residual`；源接口 `p_goa_01_via_occupationLimit`、`p_per_02_via_occupationLimit`。

核心是：状态序列收敛、观测及推进后观测连续、观测族分离状态，并且推进前后观测残差趋零，则极限状态不变。它不自带紧性、可提取子列、量子密度算符归一化、原轨道收敛、唯一平稳态或谱隙。

因此它非常适合有限维 quantum Cesàro 平均的桥接，但应输出“任何收敛子列的极限平稳”；若要“唯一吸引子”须增加并验证新的收缩/不可约/原始性条件。幺正周期演化可有 Cesàro 平稳而原轨道不收敛。

### 2.5 不属于第五个最小生成器的内容

账本中的 `M-BU-01`（Bayesian Recursive Closure）状态仅 `candidate`。后续 `RecursiveSufficientState`、`QuotientGauge`、Bellman/agency-GOD-GOA 拼接等是有价值的 MERGED_UNCOUNTED 表面，不能把它们计成另一个 counted primitive。

`UEOT.V3.Compression.QuotientGauge.sameFibers_iff_existsUnique_equiv` 证明两个满射表示具有相同纤维时存在唯一标签双射。它没有证明 U(1) 电磁规范、非阿贝尔规范场、波函数相位或 Wilsonian RG 的动力学。上述物理关系必须各有明示 map、作用与保存定理。

## 3. 106 个已完成 P-ID 仍保留什么输入

一个已完成的条件定理并不意味着条件已经在每个物理模型中获得验证。仓库已有好的先例，应按同样严格程度扩展 QM：

- `UEOT.V3.DiffusionHJBVerification.p_ctl_03`：源码中的 `Model.ItoRun` 提供有限时域 Itô/localization 期望等式和相应可积性；Lean 推导 HJB 残差符号、折扣终项消失、任意控制上界与 selector 达到最优值。它没有从底层构造完整 SDE/Itô 系统。
- `UEOT.V3.GirsanovPathKL.TerminalGirsanovData`：提供末时刻密度/积分变换的随机微积分接口；`p_kl_05` 再证明完整噪声空间 KL 等于半能量与观测路径 KL 的数据处理上界。经典路径 KL 不是 quantum relative entropy，不可同名移植。
- `UEOT.V3.ReversibleKilledSpectralQSD.SpectralData.p_qsd_04`：给定真实紧自伴 resolvent 与对应谱数据、半群展开和 L² 余项估计，证明条件化分布的 TV 谱隙界。使用实 L² 的 killed diffusion 不是 Schrödinger unitary 或量子谱公理的推导。
- `UEOT.V3.PredictionUpdate.p_pred_03_recursive_update`：在 finite action/observation、countable continuation coordinates、`RecursiveCoordinateClosure` 和实际历史概率与坐标匹配下得到联合可测更新；零观测概率分支只是数学延拓，不能当作有物理证据的后验状态。

由此得到一个严格但有建设性的结论：现有 Lean Core 为 UEOT-QM 提供对象表示、商结构、递归统计、误差累积和长期不变性等数学基础；**量子 sector 的复线性、Born trace pairing、PSD 状态/效应锥、张量组合、允许操作的 CP 条件、初始系统环境关联约束并未被上述生成器自动消去**。经典有限 Markov 模型本身就能实例化这些生成器，所以仅引用它们不能区分经典和量子扇区。真正的工作是把量子 sector 输入与 UEOT 对象/协议接口相接，并明确哪些新假设能通过操作实验接受检验。

## 4. TC 对 QM 的约束，而非物理捷径

`THEORY_COMPLETION_STATUS.json` 的 P0–P12 CLOSED 不能覆盖掉 P12 的 PARTIAL / EXPLICIT BOUNDARY。`AutopoiesisClosure.lean` 的终点要求给定 TrustedRepairSubstrate、TrustedRepairCodec、repairProgramSource、physical policy implementation、fault envelope、reserve/supply 不等式、lineage、candidate-parent bridge、同一对象 carrier 桥及 scale preservation law。

真实补强是 `homeostaticMarginals_preserve_lifecycleParent`：若整个 maintenance carrier 的每个状态都映到同一谱系身份，则所有有限时刻边缘分布支持上的状态仍保持该身份。这为量子装置的“同一个实验对象在控制与修复过程中延续”提供了可模仿的论证方式，但装置身份、逻辑 qubit 等价、误差校正码空间和物理粒子身份必须各有类型。

真实 no-go：`UEOT.V3.Compression.TheoryCompletion.no_physicalOnly_synthesizer_for_samePhysical_distinctSeeds`。同一 physical component 对应不同程序源时，单凭这个分量不能恢复两个不同程序；这不是“物理系统永远不能形成组织”的普遍结论。

`SemanticBoundaries.lean` 已有 `invariantGOA_can_be_nonunique`、`bellmanGOD_can_be_nonunique`、`quotientMap_does_not_imply_dynamicIntertwining`。QM 计划应继承这种习惯：作用量极值与 Bellman GOD、能量本征态与 GOA、对象粗粒化与 Wilsonian RG 各自需要额外 bridge。不能凭概念相似直接定义为同一量。

## 5. 六个第一批可执行 QM bridge targets

以下均为 **PROPOSED / NOT COMPILED**。QMB 编号仅是建议，不应覆盖仓库已有 QM claim ID。每条产物应有 theorem statement、显式前提、counterexample、依赖 import、编译/axiom 回执，先从有限维/有限协议实例做起。

### QMB-01：有限 instrument 到合法历史响应

**要证明**：给定有限复矩阵 Kraus 族 K(a,o,k)，满足每个操作 a 的完整性 sum K†K=I，branch map `I(a,o)(rho)=sum K rho K†` 使 p(o|a,rho)=Tr(I(a,o)(rho)) 非负且 outcome 总概率为 1；p>0 时归一化后仍是密度矩阵；按时间复合后的 word probability 归一化并能定义 core 需要的 response kernel。

**真实复用**：Core 的 finite probability/response 表示与 `PredictionUpdate` 的概率接口，M-QD 后续因子化；Kraus→PSD/TP→合法概率部分本身是新增证明，不能声称由 M-QD 生成。

**新 sector 输入**：复 Hilbert 空间、密度算符 PSD/trace-one、trace pairing 的操作含义、Kraus 形式、有限 outcomes、可实现控制集合。Born pairing在这条线上是模型输入；若另一条线重构它，必须显式引用该独立 theorem。

**反例/验证**：非完整 Kraus 族导致总概率不足或超过 1；零概率 branch 不定义物理后验；transpose 在单系统正但对 Bell 态半边作用不正，揭示 CP 的 ancilla 义务。可在一个 qubit 的 projective measurement、dephasing、amplitude damping 上给 exact algebra witness。gate 必须编译 PSD/normalization theorem 本身，不能仅运行浮点样例。

### QMB-02：操作响应商与层析核空间

**要证明**：对已注册效应族 E，`rho ~ sigma ↔ ∀ e∈E, Tr(e rho)=Tr(e sigma)`；响应映射在该等价类上唯一下降。有限维线性版本是 `rho-sigma` 落入测量线性映射的核；只有当 E 分离 admissible states 时才得到 rho=sigma。两个同纤维编码间的标签双射由已有 QuotientGauge 提供。

**真实复用**：`QuotientDescent.fiberCompatible_iff_existsUnique_descend`、`existsUnique_twoSidedDescend`、`QuotientGauge.sameFibers_iff_existsUnique_equiv`。

**新前提**：QMB-01 的合法响应；效应族实际选择、完备性证明；重构标量域等另算。声明的商空间只是 reachable response class，不自动是完整 Hilbert/PSD 态空间。

**反例/验证**：仅测 Z 时 |+⟩ 与 |−⟩响应相同；加入 X 后分离。编译两个关系方向、quotient decoder、incomplete/complete 的 exact finite examples。该例能防止“有限测量相同即微观态完全相同”的偷换。

### QMB-03：顺序协议闭包与记忆边界

**要证明**：若效应/协议族对所有允许 instrument continuation 的 pullback 关闭，则当前 response-equivalent 状态在每个正概率 outcome 后仍给出相同后续响应，并由 `existsUnique_reachableUpdate` 获得 reachable quotient 的唯一更新。再接 `p_pred_03_recursive_update` 时必须提供 joint/observation coordinate 真正等于历史概率的引理。

**真实复用**：`RecursiveSufficientState.InputFiberCompatible`、`existsUnique_reachableUpdate`；`PredictionUpdate.p_pred_03_recursive_update`。协议规模有限不代表密度态空间有限。

**新前提**：fresh-environment/repeated-interaction 的重置或明确的有限 memory state；当前系统态已为未来协议充分的证明；正概率或显式 partial update。一般初始系统环境关联不能被无条件抹去。

**反例/验证**：两个 joint S–E 态有同一 reduced rho_S，但未来 joint coupling 可给不同结果；缺少 continuation 的测量族可能单步相同、两步不同。编译一次/两次 instrument composition、conditional law、reachable update 及反例。若 Markov 条件失败，扩大状态为 system+memory 或 process-level sufficient history，而不是继续宣称 rho_S 充分。

### QMB-04：量子/协议缺陷的可组合证书

**要证明**：先用有限协议输出分布的 TV 定义 operational defect；在已证明的合法后处理下给出收缩。更强任务是证明 CPTP 对 Hermitian differences 的 trace-norm 收缩，或适合所有 ancilla 的 channel norm 界。随后把局部通道误差、统计误差、近似表示误差接到 `twoStage_bound`/`weighted_chain_bound`。

**真实复用**：`TransportCertificate.twoStage_bound`、`chain_bound`、`weighted_chain_bound`；若已转成 classical record laws，既有 TV/data-processing 接口可直接使用。

**新前提**：明确 distance 定义、norm 归一化、协议或 ancilla 范围、局部缺陷来源和可靠性；每步收缩需独立证明。

**反例/验证**：post-selection 后归一化不是全局 nonexpansive，必须带成功概率下界或使用 subnormalized branch norm；小成功概率可放大误差。gate 编译具体收缩与归一化边界，然后才编译 generic chain specialization。禁止把数值拟合的经验误差当确定性上界。

### QMB-05：Quantum Cesàro GOA 的有限维桥

**要证明**：CPTP E 在有限维密度矩阵紧集内迭代；Cesàro 平均 `rhoBar_N=(1/N)sum_{k<N}E^k(rho0)` 的 residual `(E^N(rho0)-rho0)/N` 趋零。用分离的矩阵坐标或完备效应观测调用 `invariant_of_continuous_observable_residual`，得任意极限点满足 E(rhoStar)=rhoStar。

**真实复用**：`OccupationLimitInvariance.invariant_of_continuous_observable_residual`。紧性、密度算符 cone 封闭性、连续性、trace/PSD 保留、残差恒等式是新适配器义务。

**新前提**：finite-dimensional quantum channel、compact extraction。唯一性或指数混合必须另有可验证 contraction/gap，不放进 GOA 的定义。

**反例/验证**：identity channel 有多个平稳态；unitary cycle 原轨道不收敛但平均有不变极限。gate 编译 stationary limit 与 nonunique witness，随后才考虑 amplitude-damping 特定唯一极限。

### QMB-06：交换子代数的 QSD/Doob 回收

**要证明**：对保持固定对角交换子代数的 trace-nonincreasing CP map E，定义 row-oriented `M(i,j)=Tr(P_j E(P_i))`，证明 M≥0、行和≤1，且 diagonal states 的迭代与矩阵左作用精确对应。显式输入/构造正左右 eigenvectors，调用 `p_qsd_02_killed_via_positiveEigenstructure` 得条件存活分布、Doob 归一化及 stationary law，并保持 q 和 q*h 的区别。

**真实复用**：`PositiveEigenstructure.qsdDoob_bundle`、`scale_le_one_of_substochastic`、`p_qsd_02_killed_via_positiveEigenstructure`。正本征数据的存在或谱主导性没有从该调用自动获得。

**新前提**：fixed basis/projectors、diagonal algebra preservation、CP trace-nonincreasing、λ>0、h>0、归一化 q、左右 eigenrelations。

**反例/验证**：一般 coherent unitary 不保持声明的对角子代数；Pauli/Liouville entries 非负假设不成立。一个 classical killed two-state channel 的 exact embedding 可先验收，非交换 quantum Doob 作为后续独立证明路线。

## 6. 推荐次序与每条桥接的完成标准

建议顺序：QMB-01 与 QMB-02 → QMB-03/QMB-04 并行 → QMB-05/QMB-06。第一轮的核心价值是形成“具体量子操作 → 合法历史响应 → 操作商 → 递归闭包 → 观测误差证书”的真实演示。它比同时打开无限维 QFT、标准模型三代、Wilson RG 的底层形式化更容易获得可审查成果，也能为后者确立准确接口。

未来证明应使用新的 QM scope/namespace 和独立计数，消费固定 canonical Core，不重开 106 P-ID，不增加第五 counted generator。拟议独立量子包为 `formalization/ueot-qm/`，建立时按实际依赖和仓库治理注册；本轮尚未建立 Lake package 或改全局 imports。

每个桥接应分别记录：

1. 冻结数学 statement、类型、有效范围；区分 theorem / conditional theorem / adapter / no-go / empirical hypothesis。
2. 源码准确 theorem 名、依赖 Core SHA、新 sector assumption 和反例。
3. fixed toolchain 上 focused build；需要 root reachability 时 `lake build UEOT`，若建立独立 QM library 则运行其实际 target；没有实际运行不得填 PASS。
4. `#print axioms` 递归审计，禁止 sorry、admit、native_decide、无来源 axiom；审计接口有没有藏最终结论。
5. 语义审查要比较 mathematical target 与 theorem 参数，不以“编译通过”代替物理语义正确性。
6. 对有 proof-bearing 变更的 PR 运行相应 proof gate，并记录 resulting-main 的实际 proof 执行回执。docs-only proof skipped 不改成 proof success。

## 7. 固定远端来源索引

以下相对 Lean 路径的共同前缀为 `formalization/ueot-core/`；链接全部固定到本报告 SHA。

- [覆盖率真值 V3_COVERAGE_STATUS.md](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/docs/V3_COVERAGE_STATUS.md)
- [FORMALIZATION_STATE.md](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/docs/FORMALIZATION_STATE.md)
- [仍含旧摘要的 PID_STATUS.yaml](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/docs/PID_STATUS.yaml)
- [COMPRESSION_LEDGER.yaml](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/docs/compression/COMPRESSION_LEDGER.yaml)
- [TC 权威状态](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/docs/compression/theory_completion/THEORY_COMPLETION_STATUS.json)
- [P12 科学边界审计](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/docs/compression/theory_completion/P12_FINAL_AUTOPOIESIS_AUDIT.md)
- [P12 真实 Lean 源码](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/AutopoiesisClosure.lean)
- [M-QD 源码](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/QuotientDescent.lean)
- [M-TC 源码](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/TransportCertificate.lean)
- [M-PE 源码](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/PositiveEigenstructure.lean)
- [M-OI 源码](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/OccupationLimitInvariance.lean)
- [reachable recursive state](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/RecursiveSufficientState.lean)
- [PredictionUpdate](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/PredictionUpdate.lean)
- [QuotientGauge](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/QuotientGauge.lean)
- [SemanticBoundaries](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/SemanticBoundaries.lean)
- [DiffusionHJBVerification](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/DiffusionHJBVerification.lean)
- [GirsanovPathKL](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/GirsanovPathKL.lean)
- [ReversibleKilledSpectralQSD](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/UEOT/V3/ReversibleKilledSpectralQSD.lean)
- [H0 概念类型清单](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/docs/compression/hierarchy/H0_HIERARCHY_INVENTORY.md)
- [固定提交的实际 CI](https://github.com/MurphyHoops/UEOT/actions/runs/38263417684)
- [固定工具链](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/lean-toolchain)
- [固定 Mathlib 依赖](https://github.com/MurphyHoops/UEOT/blob/195ebb06fb8afcc592c69671dabfd2250e9d1989/formalization/ueot-core/lakefile.lean)

