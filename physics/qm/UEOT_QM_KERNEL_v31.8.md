# UEOT-QM v31.8 / Kernel 1.8：分离、完整纯性与逐动作记录预算

状态：**MAIN_VERIFIED**。本地统一科学验收和正式总著出版门已实际完成；v31.8 源码 PR、实际 PR CI、合入后独立 main CI 与逐项发布回读也已通过，身份以 [CURRENT](status/CURRENT.json) 为准。

## 1. 目标、基线与本轮意义

目标是基于 UEOT 建立完备、可解释、可检验的量子物理理论，并持续维护完整正式著作《UEOT物理学》。本轮从已闭环 v31.7 主线 `7d05d0369b6793e28f0e39efaa77c0c9887479d1` 接续；该旧版的源码 PR #347、PR/main CI 与元数据 PR #348 保留各自真实身份，不当作 v31.8 的 CI。

在完整有限复密度模型中，本轮证明全部合法效应分离实际密度，并证明全部产品效应识别任意联合态；从完整凸极点导出向量表示，再构造真实辅助酉和有类型的异维补齐；最后把原真实协议接到共同有限因果控制器，得到按底层实际动作记录缺陷求和的误差界。三路分别补足识别、纯化比较与可组合预测责任，没有把标准复量子背景改写成 Core 已唯一选出的自然理论。

## 2. 实际统一验收

35 个公共模块、747 条显式 theorem、985 个唯一命名公理审计；本轮新增 101 条 theorem、130 个审计目标。十组具体见证另计 193 条 theorem、71 个定义、5 个缩写，共 269 个审计。

`lake build UEOTQM` 实际 8799 jobs、退出0；命名公理审计退出0，允许基础仅为 `propext`、`Classical.choice`、`Quot.sound`。六个精确证书共42项审计，四个篡改真证明拒绝及四个同数据假值证明接受；100个运行测试方法与四个实际演示均通过。普通 Lean linter 警告按原日志保留，不写成零警告。

受验源共89项，SHA256 `a34337cd75cd70b0f2e1125899c4dcd09aa7b132642adaad2c17ef8a69f12f6e`，统一执行前后逐项相同；92项 QM/Core 源与 olean 绑定，实际递归 Core 源码56项保持与闭环基线相同。冻结 Core 的106项覆盖和四生成器没有改动。这些计数分别指包声明、具体见证、证书和运行方法，不是新物理规律数或实验数。

实际8799-job统一本地执行仍绑定原89源SHA256 `a34337cd75cd70b0f2e1125899c4dcd09aa7b132642adaad2c17ef8a69f12f6e`。实际远端受验发布输入的89源SHA256为 `054f2e01c50f25d2519a2200eeda5ccd9849c27cfc67141eeaaf552dd4d995d1`；仅一处文档注释把英文词 admit 改为 have，数学代码不变，未重跑本地编译。两份原始源码清单及追加的发布身份桥分别保留；最终发布原字节已通过实际PR运行 39420751354 与独立main运行 39424068985。 对应[实际发布源清单](kernel/evidence/v31.8/publication-source-manifest.json)和[单词注释修正身份桥](kernel/evidence/v31.8/publication-source-reconciliation.json)。

证据：[证明回执](kernel/evidence/v31.8/lean-verification.json)、[实际源清单](kernel/evidence/v31.8/source-manifest.json)、[命名审计](kernel/evidence/v31.8/proof-axioms.json)、[十组见证](kernel/evidence/v31.8/finite-witnesses/verification.json)、[精确证书](kernel/evidence/v31.8/lean-exports/verification.json)、[运行](kernel/evidence/v31.8/runtime-verification.json)、[演示](kernel/evidence/v31.8/demos-verification.json)。

## 3. 六个新增公共模块

| 模块 | 显式 theorem | 实际数学接口 |
|---|---:|---|
| `QuantumSeparation` | 9 | 合法效应实张成、完整密度分离及距离零的矩阵含义 |
| `ComplexLocalTomography` | 11 | 所有产品效应识别任意有限复联合态，并接回原 complexModel |
| `PureStateCharacterization` | 5 | 从完整凸极点和正 Gram 列导出归一向量，构成完整纯性 iff |
| `PurificationUniqueness` | 22 | 真实同载体辅助酉、矩形等距通道和异辅助载体共同直和 |
| `HistoryChannels` | 23 | 真实读取/去相干历史通道、PSD 块权重、合法块效应和同输入加权缺陷 |
| `ActionRecordBudget` | 31 | 共同有限因果控制器、原协议全态回接、逐动作和及完整记录 TV |

## 4. 正式总著与逐项主张

《UEOT物理学》正式3.4：63章（0–62）、6附录、147个稳定编号结果、229页实际PDF。旧131个编号结果保留，本轮新增16个编号结果位于第60–62章。完整正文、推导、反例与开放责任在[规范主文](book/UEOT_PHYSICS.md)、[完整PDF](book/UEOT_PHYSICS.pdf)和[逐章档案](book/CHAPTER_DOSSIER.json)连续维护；出版证据见[实际本地书门](book/evidence/v3.4/local-release-gates.json)。视觉审查范围以实际回执为准，不宣称逐页完整精读。

[v31.8主张台账](status/CLAIM_LEDGER_v31.8.json)保留旧54对象原数学和前提，新编号结果各有新条目；旧 QMK-40、45、52 的当时开放范围由新条目明确承接。QMK-13、无条件物理三代和新实验确证继续 NOT_CLAIMED。

### QMK-55 / P-SEP-01：Hermitian 算符的合法效应表示

正式总著：[第60章对应结果](book/UEOT_PHYSICS.md#p-sep-01)。

**实际量词：** ∀ finite ι, ∀ H : Matrix ι ι ℂ, H.IsHermitian；包括空载体。

**结论：** 存在 r∈ℝ、r>0 和实际 Effect ι，使 H=(2*r)•E.matrix−r•I；因此 H∈Submodule.span ℝ(range Effect.matrix)。实现取 r=‖H‖op+1，并证明 E=(H+rI)/(2r) 与 I−E=(rI−H)/(2r) 两侧正性。

**前提：**

- ι 是任意有限载体，Lean 使用 Fintype ι 与 DecidableEq ι。
- H 是全部复方阵空间中的任意 Hermitian 矩阵。
- 效应采用既有完整类型：E 与 I−E 均为正半定矩阵。
- 所用有限复欧氏算符范数/C* 次序界是已锁数学依赖；不添加物理谱、秩或分离假设。

**实际主声明：**

- `UEOTQM.QuantumSeparation.exists_effect_affine_of_hermitian`
- `UEOTQM.QuantumSeparation.hermitian_mem_real_span_effects`

**适用范围与开放责任：**

- H=2rE−rI 是 affine image 与实线性组合；两个系数一般不和为一，未称二效应凸混合或归一仿射组合。
- 不证明指定仪器库可实现构造中的全部效应，不给数值重建算法误差或采样复杂度。
- 不唯一选择复数结构，不覆盖无限维。

### QMK-56 / P-SEP-02：全效应分离与距离零的矩阵含义

正式总著：[第60章对应结果](book/UEOT_PHYSICS.md#p-sep-02)。

**实际量词：** ∀ finite ι, ∀ ρ σ : Density ι；无纯性、对角性、秩或实验样本前提。

**结论：** ρ=σ ↔ ∀ E:Effect ι, E.probability ρ=E.probability σ；并有 effectDistance ρ σ=0 ↔ ρ=σ。

**前提：**

- 任意同一有限复载体上的两份实际 Density，均 PSD 且迹一。
- 假设对每个合法 Effect 的实际实值迹概率都相等，量词不能改成固定受限测试库。
- effectDistance 保持原定义：全部效应概率差绝对值的实际上确界。

**实际主声明：**

- `UEOTQM.QuantumSeparation.density_eq_of_all_effect_probabilities_eq`
- `UEOTQM.QuantumSeparation.density_eq_iff_all_effect_probabilities_eq`
- `UEOTQM.QuantumSeparation.effectDistance_eq_zero_iff_density_eq`

**适用范围与开放责任：**

- 旧 UEOTQM.effectDistance_eq_zero_iff 仍保持“所有效应同概率”的原语义；新增矩阵等价另设名称。
- 不声明 Lean MetricSpace 注册、迹范数或 diamond 范数同一性。
- 不把受限仪器库的词响应商等同于完整密度矩阵。

### QMK-57 / P-CLT-01：完整有限复模型的普遍局部层析

正式总著：[第60章对应结果](book/UEOT_PHYSICS.md#p-clt-01)。

**实际量词：** ∀ finite ι ν, ∀ ρ σ : Density (ι×ν), [∀ E F, pρ(E⊗F)=pσ(E⊗F)]；无产品态、可分离态、纯态或相同局部维数前提。

**结论：** 所有局部产品效应同概率蕴含实际联合 Density 相等；OperationalSystems.LocalTomography OperationalSystems.complexModel 成立。

**前提：**

- ι、ν 是分别任意的有限复载体，联合类型真实为 ι×ν。
- ρ、σ 是全部 Density(ι×ν) 中任意联合态。
- 对全部合法 E:Effect ι 与 F:Effect ν 的真实 productEffect 概率相等。
- 使用原 OperationalSystems.complexModel 的完整状态、效应和张量产品呈现。

**实际主声明：**

- `UEOTQM.ComplexLocalTomography.density_eq_of_all_product_effect_probabilities_eq`
- `UEOTQM.ComplexLocalTomography.complex_localTomography`

**适用范围与开放责任：**

- 联合产品统计包含相关性；只给两侧边际不是本定理的前提。
- 实效应模型的局部实性限制保留，未扩大其允许测量。
- 不把局部层析升级为复理论对所有操作模型的唯一重建，也未从 Core 推导其物理必然性。
- 无有限样本误差、最少测试设置数、设备校准或无限维结论。

### QMK-58 / N-SEP-01：全部对角效应仍不能识别相干态

正式总著：[第60章对应结果](book/UEOT_PHYSICS.md#n-sep-01)。

**实际量词：** 一个确切二维实例；对每个满足 IsDiagonal 的实际 Effect，全称同统计分别适用于两对相干态。

**结论：** 全部合法对角效应分别不能区分 ρx+ 与 ρx−、ρy+ 与 ρy−；实际合法测试 Ex=(I+X)/2、Ey=(I+Y)/2 各自给出1/0，两对态均不同且全效应距离都精确为1。

**前提：**

- 二维复载体 Qubit=Fin 2；标准 X=[[0,1],[1,0]]、Y=[[0,−i],[i,0]]。
- 四态 ρx±=(I±X)/2、ρy±=(I±Y)/2，PSD 与迹一实际证明。
- 受限测试量词仍涵盖全部合法 Effect，但额外要求所有非对角元为零。

**实际主声明：**

- `UEOTQM.effectDistance_le_one`
- `UEOTQM.Effect.probability_sub_le_effectDistance`
- `UEOTQM.RealLocalTomography.plusProjector_posSemidef`
- `UEOTQM.RealLocalTomography.minusProjector_posSemidef`
- `UEOTQM.RealLocalTomography.involutionEffect`

**适用范围与开放责任：**

- 不否定这些对角效应的合法性；只证明其不完备。
- 全效应定理要求更多允许效应，未从受限库同统计推出两矩阵相等。
- 是精确有限形式见证，不是实验、采样模拟或经验确证。

### QMK-59 / P-PUC-01：完整有限复密度空间的纯性刻画

正式总著：[第61章对应结果](book/UEOT_PHYSICS.md#p-puc-01)。

**实际量词：** For every such iota and every rho : Density iota, both directions of the stated equivalence.

**结论：** IsPure rho iff there exists v : iota -> Complex with trace(outer v)=1 and rho.matrix=outer v.

**前提：**

- iota is a finite complex matrix carrier; equality is decidable in the Lean matrix interface.
- rho : Density iota carries actual PSD and complex trace-one proofs.
- IsPure means extremality in the entire Density iota convex set, not in a selected subset.

**实际主声明：**

- `UEOTQM.QuantumPurification.IsPure.exists_vector`
- `UEOTQM.QuantumPurification.isPure_iff_exists_vector`

**适用范围与开放责任：**

- No claim of a supplied rank-one/rank assumption; it is derived.
- No independently certified numerical Gram/square-root algorithm.
- Empty iota has no Density input; no additional Nonempty premise.
- Finite complex model does not establish Core-to-complex selection.

### QMK-60 / P-PUN-01：同辅助载体的完整纯化酉等价

正式总著：[第61章对应结果](book/UEOT_PHYSICS.md#p-pun-01)。

**实际量词：** For every finite system and common finite auxiliary carrier, and every pair of full convex-pure joint densities with equal actual system marginal.

**结论：** There exists U : Matrix alpha alpha Complex satisfying U^dagger U=I, U U^dagger=I and Phi.matrix=(I tensor U) Psi.matrix (I tensor U)^dagger. The unnormalized vector helper additionally fixes phi(i,a)=sum_b U(a,b) psi(i,b) exactly.

**前提：**

- iota and alpha are finite complex carriers, with decidable equality.
- Psi,Phi : Density (iota x alpha) are IsPure in the full joint Density type.
- The actual RectangularChannel.discardRight iota alpha state outputs are equal.

**实际主声明：**

- `UEOTQM.QuantumPurification.pure_states_unitarily_equivalent`

**适用范围与开放责任：**

- The two original auxiliary carriers are the same type in this theorem.
- U itself is not claimed unique; unused support complements and vector phase can vary.
- No full-rank or pre-supplied unitary hypothesis.
- No infinite-dimensional isometric-extension claim.

### QMK-61 / P-AUX-01：辅助等距嵌入的实际通道、边际和纯性

正式总著：[第61章对应结果](book/UEOT_PHYSICS.md#p-aux-01)。

**实际量词：** Every actual rectangular auxiliary isometry J; marginal identity for every complex input matrix X : Operator (iota x alpha); purity preservation for every full convex-pure density Psi.

**结论：** The actual one-Kraus RectangularChannel with Kraus I tensor J is CPTP, leaves the system discardRight marginal invariant on all complex matrices and preserves full convex purity on the enlarged density space.

**前提：**

- iota,alpha,beta are finite complex carriers with the decidable equality instances required by the actual matrix/channel interface.
- J : Matrix beta alpha Complex satisfies J^dagger J=I_alpha.
- No JJ^dagger=I_beta hypothesis is used.

**实际主声明：**

- `UEOTQM.QuantumPurification.auxiliaryEmbeddingChannel`
- `UEOTQM.QuantumPurification.auxiliaryEmbeddingChannel_discard_operator`
- `UEOTQM.QuantumPurification.auxiliaryEmbeddingChannel_discard_state`
- `UEOTQM.QuantumPurification.auxiliaryEmbeddingChannel_preserves_purity`

**适用范围与开放责任：**

- Rectangular isometry is not a two-sided unitary when auxiliary dimensions differ.
- Completely positive amplification is inherited through the actual RectangularChannel API; no new physical principle is inserted.
- No new numerical implementation certification is claimed.

### QMK-62 / P-PUN-02：不同有限辅助载体的共同扩展酉等价

正式总著：[第61章对应结果](book/UEOT_PHYSICS.md#p-pun-02)。

**实际量词：** All such systems and finite auxiliary carriers alpha,beta without a dimension-order or equal-cardinality assumption; all such pure densities.

**结论：** Canonical actual left/right auxiliary isometries embed both densities into iota x (alpha Sum beta); both retain purity and marginal; there exists U on alpha Sum beta with both unitary identities that relates the embedded joint densities by I tensor U conjugation.

**前提：**

- iota,alpha,beta finite complex carriers, with decidable equality.
- Psi : Density (iota x alpha) and Phi : Density (iota x beta) are each full convex-pure.
- Their actual system discardRight marginal densities agree.

**实际主声明：**

- `UEOTQM.QuantumPurification.pure_states_common_extension_unitary`

**适用范围与开放责任：**

- The common dimension is |alpha|+|beta|, not asserted minimal.
- No rectangular two-sided unitary between the original spaces.
- No direct whole-space isometry in an unspecified dimension direction.
- A reconstruction principle with a prescribed padding convention requires a further explicit interface theorem.

### QMK-63 / N-PUN-01：伴随、转置和逐项共轭不能替代实际辅助作用

正式总著：[第61章对应结果](book/UEOT_PHYSICS.md#n-pun-01)。

**实际量词：** Three separate exact concrete inequalities, one each for T=U^dagger,U^T,conj(U).

**结论：** Each wrong-direction transformed joint outer-product density differs from outer psi2. Entries are respectively 108i/625 vs108/625, -108i/625 vs108/625 and144i/625 vs-144i/625.

**前提：**

- Fixed rational complex U=[[3/5,4i/5],[4/5,-3i/5]].
- Fixed psi1=3/5|00>+4/5|11> and psi2=9/25|00>+12/25|01>+16i/25|10>-12i/25|11>.
- The action is exactly (I tensor T)psi1, with the second tensor index as auxiliary.

**实际主声明：**

- `UEOTQM.PurificationUniquenessExamples.wrong_adjoint_joint_density`
- `UEOTQM.PurificationUniquenessExamples.wrong_transpose_joint_density`
- `UEOTQM.PurificationUniquenessExamples.wrong_conjugate_joint_density`

**适用范围与开放责任：**

- These are joint-density inequalities, not claims that their system marginals differ.
- A vector-only difference could be hidden by global phase; the accepted controls compare joint outer products.
- Formal exact witnesses are not real experimental confirmation.

### QMK-64 / N-AUX-01：严格辅助扩维是等距嵌入，不是双侧酉等价

正式总著：[第61章对应结果](book/UEOT_PHYSICS.md#n-aux-01)。

**实际量词：** One explicit rectangular embedding and its separate equality/inequality witnesses.

**结论：** J^dagger J=I_2, but JJ^dagger != I_3; at the extra Sum.inr Unit coordinate the latter product has diagonal zero while I_3 has one.

**前提：**

- Fixed canonical auxiliaryInl from Fin 2 to Fin 2 Sum Unit.
- Actual source/output auxiliary dimensions are 2 and 3.

**实际主声明：**

- `UEOTQM.PurificationUniquenessExamples.strict_embedding_isometry`
- `UEOTQM.PurificationUniquenessExamples.strict_embedding_not_coisometry`

**适用范围与开放责任：**

- The concrete common five-dimensional unitary is supplied by the proved general existence construction, not an independently listed numerical 5x5 matrix.
- This does not negate isometric embeddings; it distinguishes them from two-sided unitary equivalence.

### QMK-65 / P-ARB-01：历史块、归一权重与合法块效应

正式总著：[第62章对应结果](book/UEOT_PHYSICS.md#p-arb-01)。

**实际量词：** ∀ finite H ι ν, ∀ ζ:Density(H×ι), ∀ h:H, ∀ E:Effect(H×ν), ∀ block family B:H→Operator ν.

**结论：** ζ_h 是PSD；p_h=mass ζ_h≥0、Σ_h p_h=1，p_h=0 iff ζ_h=0；E_h 与 I−E_h 均PSD，故为实际 Effect ν；pairing(E,block B)=Σ_h pairing(E_h,B_h)。

**前提：**

- H、ι、ν 均为有限载体，矩阵使用既有完整复矩阵、Density 与 Effect 类型。
- ζ 是任意 Density(H×ι)，实际 PSD 且复迹一；不要求预先块对角。
- E 是任意 Effect(H×ν)，矩阵及补矩阵均实际 PSD。

**实际主声明：**

- `UEOTQM.HistoryChannels.principal_posSemidef`
- `UEOTQM.HistoryChannels.weight_nonneg`
- `UEOTQM.HistoryChannels.sum_weight`
- `UEOTQM.HistoryChannels.zero_weight_iff_zero_principal`
- `UEOTQM.HistoryChannels.restrictEffect`
- `UEOTQM.HistoryChannels.pairing_block`

**适用范围与开放责任：**

- 不向零概率历史赋任意实际后验。
- 主块性质可用于任意联合态；后续控制器仍实际读取/去相干历史，不是相干控制器。

### QMK-66 / P-ARB-02：实际历史读取通道的动作加权界

正式总著：[第62章对应结果](book/UEOT_PHYSICS.md#p-arb-02)。

**实际量词：** ∀ such families C,D and every same actual joint input ζ; κ and η may differ; arbitrary complex X for the exact operator formula.

**结论：** 真实readKraus(h,K)的完整性给controlled通道；operator X=block(h↦C_h(principal X h))。共同输入输出距离≤Σ_h weight ζ h·δ(C_h,D_h)；统一≤ε，且ε≥0时controlled通道defect≤ε。

**前提：**

- 有限H、ι、ν和有限Kraus载体κ、η；两个族 C_h:RectangularChannel ι ν κ、D_h:RectangularChannel ι ν η均有实际完整性。
- 任意共同输入ζ:Density(H×ι)。
- uniform状态版本只需∀h δ(C_h,D_h)≤ε；supremum历史通道版本另显式要求ε≥0以控制插入的0。

**实际主声明：**

- `UEOTQM.HistoryChannels.controlled`
- `UEOTQM.HistoryChannels.controlled_operator_eq_block`
- `UEOTQM.HistoryChannels.pairing_operator_difference_le_mass_mul_defect`
- `UEOTQM.HistoryChannels.controlled_state_distance_le_weighted_defect`
- `UEOTQM.HistoryChannels.controlled_defect_le_uniform`

**适用范围与开放责任：**

- 读取Kraus确实消去历史相干；不能改称任意相干控制。
- 双方权重来自同一个ζ，未假定两个不同运行轨迹具有相同分布。
- 矩形通道完全正性的继承结论不把当前缺陷换成diamond或任意环境放大后的缺陷。

### QMK-67 / P-ARB-03：有限历史演化与原完整协议的矩阵一致性

正式总著：[第62章对应结果](book/UEOT_PHYSICS.md#p-arb-03)。

**实际量词：** ∀ fixed N, all such C,I,ρ and all actual full histories; no varying-depth generalization.

**结论：** 实际step读取历史、执行所选带标签仪器并经置换追加结果。run矩阵=block(h↦recordOperator I (C.word h) ρ.matrix)。原Protocol叶与History O N有真实双射并保持完整action/outcome词；重标记完整联合密度态相等，终端量子边际为原leaf operator和，leaf概率一致。

**前提：**

- 固定任意N:Nat，有限共同结果O和量子记忆ι；A为任意动作类型，不额外要求有限或非空。
- C:∀t:Fin N,(Fin t.val→O)→A 是同一实际因果控制器。
- I:A→Instrument ι O κ 有实际完整Kraus数据，ρ为任意Density ι。
- 协议π_C由该固定深度C完整生成，保留每个结果分支，包括零概率结果。

**实际主声明：**

- `UEOTQM.ActionRecordBudget.Controller.leafEquiv`
- `UEOTQM.ActionRecordBudget.Controller.protocol_word_eq`
- `UEOTQM.ActionRecordBudget.Controller.word_snoc`
- `UEOTQM.ActionRecordBudget.step`
- `UEOTQM.ActionRecordBudget.run_matrix`
- `UEOTQM.ActionRecordBudget.run_eq_protocol_state`
- `UEOTQM.ActionRecordBudget.terminal_memory_matrix`
- `UEOTQM.ActionRecordBudget.weight_run_leaf`

**适用范围与开放责任：**

- 原Protocol仍允许变长叶；此结果只量化由固定N的C构造的完整子类。
- 没有补齐任意停止树或处理停止后动作语义。
- 完整结果历史在给定C下恢复动作词，未假设动作选择可忽略历史。

### QMK-68 / P-ARB-04：实际逐动作和预算与完整记录TV

正式总著：[第62章对应结果](book/UEOT_PHYSICS.md#p-arb-04)。

**实际量词：** ∀ I,J,C,N,ρ,σ under the stated finite carrier conditions, and for the uniform corollary ∀ ε:Fin N→ℝ satisfying all selected-action bounds.

**结论：** a_t=Σ_h q^J_t(h) δ_rec(I(C_t h),J(C_t h))≥0。实际D_(t+1)≤D_t+a_t，因此最终joint distance与完整record TV均≤d_eff(ρ,σ)+Σ_t a_t，且≤d_eff(ρ,σ)+Σ_t ε_t。原Protocol完整leaf TV精确等于History TV并满足同界。

**前提：**

- 采用P-ARB-03的固定N、有限共同记录/记忆和同一C；I与J可有不同有限Kraus载体。
- ρ、σ为任意初态，无需相等。
- 第t项使用实际J前缀 run J (C.truncate t) σ 的PSD历史块质量作为共同输入权重。
- 可选统一预算假设是∀t h δ_rec(I(C t h),J(C t h))≤ε t；ε非负只在单步通道supremum统一界另显式需要。

**实际主声明：**

- `UEOTQM.ActionRecordBudget.actionCost`
- `UEOTQM.ActionRecordBudget.run_succ_distance_le`
- `UEOTQM.ActionRecordBudget.run_distance_le_actionCost_sum`
- `UEOTQM.ActionRecordBudget.run_distance_le_budget_sum`
- `UEOTQM.ActionRecordBudget.record_tv_le_actionCost_sum`
- `UEOTQM.ActionRecordBudget.record_tv_le_budget_sum`
- `UEOTQM.ActionRecordBudget.protocol_record_tv_eq`
- `UEOTQM.ActionRecordBudget.protocol_record_tv_le_budget_sum`

**适用范围与开放责任：**

- 没有用两种不同轨迹的权重互换；选择共同输入的J方向是显式定义。
- δ_rec本身为真实supremum，不自动给任意动作库可计算的数值或实验校准。
- 不扩大为diamond、相干控制、变长停止树、任意未建模环境或连续时间预算。

### QMK-69 / P-ARB-05：精确有理逐步预算的饱和见证

正式总著：[第62章对应结果](book/UEOT_PHYSICS.md#p-arb-05)。

**实际量词：** Exact finite concrete instrument/controller construction, with all input densities for the action supremum upper bound and same-input TV, and arbitrary ρ,σ for the initial-error bound.

**结论：** 真实第一动作记录defect=1/4（全输入全效应上界及真实事件下界）；第二对应动作defect=0；实际actionCost分别1/4与0，总和1/4。完整两步record TV=1/4；不同初态joint distance≤d_eff(ρ,σ)+1/4；同输入两终端量子态均=ρ；原Protocol TV=1/4。

**前提：**

- 具体Qubit=Label=Fin2，Kraus下标Fin4。
- certain b只有(o=b,k=0)单位Kraus；biased的标签0四元组为(I/2,I/2,I/2,0)，标签1为(0,0,0,I/2)。
- 同一个feedback在t=0选none，在t=1按首记录o选some o。
- exactActions none=certain0，approximateActions none=biased；两方some o都为certain o；量词覆盖任意二维输入Density。

**实际主声明：**

- `UEOTQM.ActionRecordBudget.run_distance_le_actionCost_sum`
- `UEOTQM.ActionRecordBudget.record_tv_le_actionCost_sum`
- `UEOTQM.ActionRecordBudget.protocol_record_tv_eq`
- `UEOTQM.ActionRecordBudget.run_matrix`

**适用范围与开放责任：**

- 精确有限形式见证，不是实验确证。
- 两方终端量子记忆同输入时相同；可区分性在实际记录。
- 实例不证明一般动作defect均能精确计算。

### QMK-70 / N-ARB-01：无标签动作零缺陷仍可给出最大完整记录误差

正式总著：[第62章对应结果](book/UEOT_PHYSICS.md#n-arb-01)。

**实际量词：** For each action a and every operator X, equality of unlabelled action maps; for every same input density ρ, exact final record/event/memory claims.

**结论：** 每个无标签动作channel在所有X上相等，旧channelDefect为0；完整两步record TV=1；第二结果为0的事件概率分别1和0；两方终端量子密度态均=ρ并相等；原Protocol全leaf TV同为1。

**前提：**

- 沿用P-ARB-05的二维记忆、结果类型、四Kraus certain仪器和同一feedback。
- flippedActions none=certain1，some o=certain o；参考exactActions none=certain0，其后相同。
- 任意共同输入ρ:Density Qubit。

**实际主声明：**

- `UEOTQM.ActionRecordBudget.run_matrix`
- `UEOTQM.ActionRecordBudget.protocol_record_tv_eq`

**适用范围与开放责任：**

- 记录不同且第二动作因共同控制器响应不同结果而分离；终端量子态保持相同。
- 不得把零无标签缺陷替换进本章的带记录动作预算。
- 此精确反例不构成新的实验数据或现实设备结论。

## 5. 正负控的实际含义

全部对角效应仍不能识别两组不同的 X/Y 相干态；合法完整效应能区分它们。实模型层析反例原样保留，未改其局部实性。辅助酉用有理复矩阵核验两侧单位关系和精确向量作用；错用伴随、转置、逐项共轭分别导致联合密度不等，但不声称系统边际因此不同。2→3维嵌入满足 J†J=I而JJ†≠I，两不同辅助态在共同5维载体上比较。

逐动作正控的第一项真实上确界缺陷为1/4，第二项为0，完整两步记录 TV 达到1/4；删除标签时各无标签动作完全相同且缺陷0，但完整记录TV为1、第二次事件概率为1/0。双方终端量子态分别等于同一个初态，不能写成终端量子态不同。这些都是精确形式化模型见证，没有新增真实实验。

## 6. 未完成责任与远端闭环

本轮没有从冻结 Core 唯一导出复量子理论；量子选择原则的独立物理理由、完整重建背景和其他模型排除仍开放。纯化共同直和不等于最小辅助空间或任意维数方向的直接等距定理；固定深度共同因果控制器预算不自动覆盖变长停止树、相干控制器、额外环境或 diamond 范数。一般谱存在/混合、无限条件过程、程序全输入细化、真实QDRR记录、完整谱与阈值、连续极限、QFT、真空和质量仍各有责任。

三代 selector 继续要求谱、表示、异常、阈值及有效窗口等前提。当前有限内核不等于完整自然理论已证，也不构成最终真理已完成的声明。

源码 PR、实际 PR CI、合入主线的独立 CI、受验源/Core/正文及338项发布文件逐项回读已经完成。当前独立元数据更新依据这些真实回执记录 MAIN_VERIFIED；本次元数据提交自身的Git身份与实际CI受验源码及主线身份分开。本轮仅维护当前合同与开放路线，没有创建下一版本合同。

## 实际远端验收与元数据身份

[PR #350](https://github.com/MurphyHoops/UEOT/pull/350)及[实际整合回执](kernel/evidence/v31.8/integration-verification.json)记录本版唯一科学源码发布、两次独立CI和逐项Git blob核对。

| 实际身份 | 值 |
|---|---|
| 源码提交 / tree | `d9a1858c86ca82e08ae862389b51c1ea76690c24` / `6717f47ff1a062f04cb0ba54e01ebaeddac5770a` |
| PR CI | [39420751354](https://github.com/MurphyHoops/UEOT/actions/runs/39420751354)，PASS；实际 8799 build jobs |
| 受验主线提交 / tree | `97c7b29c1aec470be58ca34b552e9d56ad06c197` / `2669b1fa73d37b442398d9c0fa7b2ffd3972cd9d` |
| 独立 main push CI | [39424068985](https://github.com/MurphyHoops/UEOT/actions/runs/39424068985)，PASS；实际 8799 build jobs |

最终89项发布输入、56项实际递归Core源码、三份规范正文和全部338项冻结发布载荷均与实际源码及受验主线逐项一致。原8799 jobs仍只绑定原a343…本地输入，实际CI绑定054f…发布输入；单词注释桥及原验收回执保留原字节。CI解码日志逐项核对39条源码hash、985个公共审计名、100个运行测试名，并核对证书/正反控的执行摘要及十组见证269项审计总数。见证193/71/5的种类分拆来自已绑定本地源码和回执；未下载artifact ZIP，不声称检查其内部逐名或演示JSON。

当前证据与导航元数据在后续独立提交中记录这些真实身份；该元数据提交自身不冒充上述任何CI受验提交。原12份本地元数据可按整合回执内的科学源码提交及Git blob精确恢复，旧本地待远端措辞按该历史检查点理解。此次未新增科学执行、实验、前提外结论或下一版本合同。
