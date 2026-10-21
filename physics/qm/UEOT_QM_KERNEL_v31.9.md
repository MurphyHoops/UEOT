# UEOT-QM v31.9 / Kernel 1.9：精确距离、最小纯化与停止协议

当前状态：**LOCAL_VERIFIED_REMOTE_PENDING**。本轮科学统一验收、独立数学审查和《UEOT物理学》3.5 本地发布门已经完成；v31.9 源码 PR、真实 PR CI、独立 main CI 及远端逐项回读仍待完成。[CURRENT](status/CURRENT.json)给当前状态，[执行合同](UEOT_QM_EXECUTION_v31.9.md)保留原目标及边界。

## 1. 实际成果与科学意义

本轮从已闭环 main `6b3ba80ec418ff04c4b6e2cd5c321b654540e9d1`、tree `d900109f97fd032bb3682ecbd5fdf7577b415307` 继续。在同一个完整有限复量子模型中，全效应距离已有实际半迹绝对值表达和最优判别效应；纯化所需的最小辅助维数已经精确等于原密度矩阵的实际复秩；原有限变长停止树已经与真实联合记录和逐动作预算接通。这些结论分别给出可辨识程度、辅助资源下界和具有停止记录的实际误差责任。

全效应公式是 $d_{\mathrm{eff}}(\rho,\sigma)=\tfrac12\operatorname{Tr}|\rho-\sigma|$，等先验二元最优成功率是 $(1+d_{\mathrm{eff}})/2$。半因子使用密度差的零迹前提；一般 Hermitian 矩阵只按其实际谱绝对值求迹。PSD 支持分解证书提供可核验的充分条件，输入中没有待证距离。

纯化存在的完整判据是 $\exists\Psi\text{ pure},\operatorname{Tr}_\alpha\Psi=\rho\iff\operatorname{rank}_\mathbb{C}\rho\le|\alpha|$；在 `Fin ρ.matrix.rank` 上达到下界。不同辅助载体同边际纯态的直接作用在 $|\alpha|\le|\beta|$ 下由 $J^\dagger J=I_\alpha$ 实现，严格扩维不称为双侧酉。

停止预算比较共同原树控制器下的两套实际动作库，使用 J 侧从 $\sigma$ 出发的真实前缀历史权重。已停历史因实际 idle 缺陷为零而消去，原叶记录与终端量子记忆保留独立边际界。不同停止规则的 TV=1 负控明确在共同规则前提之外，终端量子记忆仍相同。

## 2. 实际验证身份与执行范围

41 个公共模块、854 条显式 theorem、1123 个唯一命名公理审计；本轮新增 107 条 theorem、138 个审计目标。十三组具体见证合计 298 条 theorem、110 个定义、8 个缩写，共 416 个审计。 本轮统一门实际编译全部公共模块并执行公共公理审计，实际执行三份新增见证（147 个命名审计）。十份旧见证的 269 项审计、六精确证书的 42 项审计、四个篡改真证明拒绝与四个同数据假值证明、100 个运行方法和四个演示，按未变的科学输入、依赖闭包与既往真实执行回执复用；这些旧门本轮未重新运行。

实际统一 `lake build UEOTQM` 为 8805 jobs、退出 0；公共命名审计实际退出 0。允许基础仅为 `propext`、`Classical.choice`、`Quot.sound`；Lean 4.33.1 的普通 linter 警告如实保留。公共定理、定义/缩写/实例、具体见证、证书和运行方法分别统计，不作为新增物理规律数量。

全部 **98** 个受验源的统一与发布候选原字节身份相同，源集 SHA256 为 `bf026d2a1f7d8c8bd1f9f6c1ad9015aa20bdae6bd36b9d432c7ce6f0581effc0`。[实际证明](kernel/evidence/v31.9/lean-verification.json)、[源清单](kernel/evidence/v31.9/source-manifest.json)、[实际公共公理输出](kernel/evidence/v31.9/proof-axioms.json)、[见证执行与复用](kernel/evidence/v31.9/finite-witnesses/verification.json)及[旧门身份闭包](kernel/evidence/v31.9/legacy-reuse.json)分别记录证据。56 个实际递归 Core 源与基线保持相同，全部冻结 Core 106 项和四生成器不改动。

## 3. 新增编号结果、前提与实际证明

### QMK-71 · P-TDIST-01（有限 Hermitian 正负谱分解及实际绝对值）。

**实际结论：** 由实际有限复 Hermitian 矩阵的酉谱分解构造 PSD 正负部分，证明 H=P-N、CFC.abs H=P+N 以及实迹等于绝对特征值有限和。

**前提与量词：** 任意有限载体及 DecidableEq；实际复 Hermitian 矩阵 H 全部该类有限 Hermitian 矩阵，包括零特征值；谱存在来自已锁定数学库。

**证明链：** 酉共轭运输实际加、减、乘与迹。；两个非负标量部分给 PSD 矩阵；逐特征值减法恢复 H。；标准 CFC.abs 与 Hermitian 连续函数演算绝对值一致，标量绝对值等于两部分之和；取迹。

**实际主声明：** `UEOTQM.QuantumTraceDistance.positivePart_sub_negativePart`、`UEOTQM.QuantumTraceDistance.abs_eq_positivePart_add_negativePart`、`UEOTQM.QuantumTraceDistance.traceAbsolute_eq_sum_abs_eigenvalues`。

**边界：** 谱基为 noncomputable 存在选择；没有声称数值求谱算法。；未建立任意矩阵的全部范数公理或 NormedSpace 实例。

正式总著：[第 63 章对应结果](book/UEOT_PHYSICS.md#p-tdist-01)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-72 · P-TDIST-02（全效应距离的半迹绝对值公式及最优效应）。

**实际结论：** 原全效应距离等于 Tr|ρ-σ|/2，等于绝对特征值和的一半；正谱投影是合法效应，且其带符号概率差实际达到该距离。

**前提与量词：** 任意有限载体及 DecidableEq；ρ、σ 为原完整 Density 类型的实际态，均 PSD 且迹为一 全部有限复密度态对，不要求纯态、可交换或共同可对角化。

**证明链：** PSD 分解对全部合法效应给配对上下界，密度差零迹使正负迹相等。；正谱指示函数及其补函数皆非负，构成真实合法效应；实际支持等式给匹配下界。；上确界上下界相等；实际绝对值等于两部分和，因此出现且仅此处使用因子 1/2。

**实际主声明：** `UEOTQM.QuantumTraceDistance.effectDistance_eq_positivePart_mass`、`UEOTQM.QuantumTraceDistance.positiveSpectrumEffect_attains`、`UEOTQM.QuantumTraceDistance.effectDistance_eq_half_traceAbsolute`、`UEOTQM.QuantumTraceDistance.effectDistance_eq_half_sum_abs_eigenvalues`。

**边界：** 半迹公式使用密度差零迹；一般非零迹 Hermitian 配对不能直接套用。；未证明通道 diamond 范数或物理自然唯一性。

正式总著：[第 63 章对应结果](book/UEOT_PHYSICS.md#p-tdist-02)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-73 · P-DEC-01（等先验二元判别的真实最优成功率）。

**实际结论：** 实际效应和互补效应产生的等先验二元成功率对所有效应不超过 (1+d)/2，所构造正谱效应达到该值；因此最优成功率为 1/2+Tr|ρ-σ|/4。

**前提与量词：** 任意有限完整复密度态对；两个先验均为 1/2；效应 E 时猜第一态，互补效应时猜第二态 全部合法二元效应决定的概率优化；包含一个实际达到上界的效应。

**证明链：** 用互补概率将成功率写成 (1+带符号概率差)/2。；实际概率差的绝对值不超过原全效应距离。；正谱效应的达到性给实际最优决定和半迹表达。

**实际主声明：** `UEOTQM.BinaryDiscrimination.equalPriorSuccess_le`、`UEOTQM.BinaryDiscrimination.positiveSpectrumEffect_success`、`UEOTQM.BinaryDiscrimination.exists_optimal_equalPriorDecision`、`UEOTQM.BinaryDiscrimination.optimal_equalPriorSuccess_traceAbsolute`。

**边界：** 没有一般不等先验最优式。；概率最优性不指定或唯一确定测量后仪器动力学。

正式总著：[第 63 章对应结果](book/UEOT_PHYSICS.md#p-dec-01)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-74 · P-TCERT-01（PSD 支持分解距离证书）。

**实际结论：** 给实际 PSD 分解 ρ-σ=P-N、合法 E 和乘法证据 EP=P、EN=0，即精确得到距离 TrP 及最优决定；给实际有限酉对角化可独立构造这些条件并得到有限正部和/绝对值和公式。

**前提与量词：** 原实际密度态及合法效应；P、N 实际 PSD；实际差分解等式与两个支持等式；或实际 U 酉、d 实数及 H=Udiag(d)U† 任意有限复模型中的满足所列输入矩阵条件的证书；不将距离、最终上界或最优性作为输入。

**证明链：** PSD 分解给全部效应上界；实际支持等式使所给 E 的概率差正好为 TrP，提供下界。；给定酉数据时以 max(d,0)、max(-d,0) 和正谱指示系数构造独立矩阵证据。；迹零再次将两个正部和联系起来，得到一半绝对值和。

**实际主声明：** `UEOTQM.BinaryDiscrimination.effectDistance_eq_mass_of_support_certificate`、`UEOTQM.BinaryDiscrimination.success_eq_optimum_of_support_certificate`、`UEOTQM.BinaryDiscrimination.effectDistance_eq_sum_positive_of_unitary_data`、`UEOTQM.BinaryDiscrimination.effectDistance_eq_half_sum_abs_of_unitary_data`。

**边界：** 仅有任意 PSD 差分解只保证上界，不能保证精确；重叠正负部分给实际反例。；给定有限数据的精确核验不等于已实现对任意矩阵的数值求谱算法。

正式总著：[第 63 章对应结果](book/UEOT_PHYSICS.md#p-tcert-01)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-75 · P-PDM-01（矩形等距的精确维数方向）。

**实际结论：** 有限复载体α、β上，存在J:Matrix β α ℂ满足J†J=Iα，当且仅当|α|≤|β|；若|α|<|β|，任意这样的扩维矩阵不能同时有JJ†=Iβ。

**前提与量词：** α、β为任意有限载体，标量为ℂ；所用单位矩阵和乘法是实际矩形矩阵运算。 All finite source and target carriers, including empty carriers; no density input or pre-supplied isometry is needed for existence.

**证明链：** 有限基数界给单射；其0/1坐标矩阵逐项满足J†J=I。；必要性由rank(I)=|α|≤rank(J)≤|β|；反向单位恒等式在严格维数差时违反同一必要界。

**实际主声明：** `UEOTQM.QuantumPurification.exists_matrix_isometry_iff_card_le`、`UEOTQM.QuantumPurification.matrix_isometry_not_coisometry_of_card_lt`。

**边界：** 不把单侧矩形等距称为双侧酉。；不讨论无限维载体或物理制备复杂度。

正式总著：[第 64 章对应结果](book/UEOT_PHYSICS.md#p-pdm-01)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-76 · P-PDM-02（任意实际纯化的有方向直接等距）。

**实际结论：** 同一有限系统的任意两份完整凸纯态Ψ∈Density(ι×α)、Φ∈Density(ι×β)，在实际偏迹相同且|α|≤|β|时，存在J†J=Iα使Φ=(Iι⊗J)Ψ(Iι⊗J)†；向量作用为φ(i,b)=Σa J(b,a)ψ(i,a)。

**前提与量词：** ι、α、β为有限复载体。；IsPure仍为全部实际密度态中的凸极点。；实际discardRight边际相同。；明确维数方向|α|≤|β|。 Every pair of full convex-pure joint density matrices with the stated marginal and cardinal conditions; the vector theorem also handles unnormalized vectors with equal outer-product marginals.

**证明链：** 先从维数界构造J0并将第一向量等距扩展至目标辅助载体，实际偏迹不变。；同载体Gram/酉定理给U，定义J=U J0；由真实矩阵/Kronecker乘法得到作用。；完整纯性反向取得两向量，再用outer(Tv)=T outer(v) T†回到任意纯态密度矩阵。

**实际主声明：** `UEOTQM.QuantumPurification.pure_states_isometrically_equivalent`、`UEOTQM.QuantumPurification.exists_auxiliary_isometry_of_equal_marginal`、`UEOTQM.QuantumPurification.exists_auxiliary_isometry_action`。

**边界：** 不声称反向维数方向存在全空间等距。；右矩阵因子为AJᵀ；不将J†、Jᵀ、逐项共轭互换。；不从该结构事实推出Core唯一选择复模型。

正式总著：[第 64 章对应结果](book/UEOT_PHYSICS.md#p-pdm-02)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-77 · P-PDM-03（全部凸纯扩展的实际秩下界）。

**实际结论：** 任意Ψ∈Density(ι×α)若在完整态空间中为凸纯态，则rankℂ(Trα Ψ)≤|α|；实际向量重排A满足Trα Ψ=AA†且rank(AA†)=rank(A)。

**前提与量词：** 有限复载体与原Density/IsPure定义。；系统边际为原实际Kraus偏迹。 Every full convex-pure joint density, without a pre-supplied rank-one or Gram witness.

**证明链：** 完整纯性刻画给真实向量，将其重排为ι×α矩阵A。；原偏迹逐项等于AA†；固定库的Gram秩等式与矩阵列数界给结论。

**实际主声明：** `UEOTQM.QuantumPurification.rank_marginal_le_auxiliary_card`。

**边界：** 该下界量化所有纯化，不仅量化谱构造所得者。；单独的下界不声称已达到最小值；达到性由P-PDM-04另证。

正式总著：[第 64 章对应结果](book/UEOT_PHYSICS.md#p-pdm-03)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-78 · P-PDM-04（有限复纯化的精确最小辅助维数）。

**实际结论：** 任意ρ:Density ι与指定有限α，有实际完整凸纯扩展Ψ∈Density(ι×α)、TrαΨ=ρ，当且仅当ρ.matrix.rank≤|α|。Fin rank上真实达到最小值；任何更小辅助均不可能。密度秩严格为正，空辅助不可能。

**前提与量词：** ρ为完整有限复密度态，正性与迹一为实际矩阵条件。；辅助载体有限，秩为原复矩阵的精确秩。；只复用固定数学库的有限Hermitian谱定理；不预设谱支撑大小或所需纯化。 All finite complex density inputs and all specified finite auxiliary carriers; attained explicitly on Fin ρ.matrix.rank.

**证明链：** 必要性由任意纯化秩下界。；PSD给真实非负特征值及谱酉；仅取非零特征值索引，平方根加权列构成压缩Gram因子。；正性保证平方根平方回到特征值，零特征值项逐项为零，故压缩后的实际Gram仍为ρ。；向量化获得规范纯态与实际偏迹；非零特征值个数等于实际秩，再由坐标等距嵌入任意足够大的目标。；取Fin rank得到达到性；假设秩0则得到空载体迹一密度，矛盾。

**实际主声明：** `UEOTQM.QuantumPurification.exists_purification_iff_rank_le`、`UEOTQM.QuantumPurification.exists_minimal_purification`、`UEOTQM.QuantumPurification.no_purification_of_card_lt_rank`、`UEOTQM.QuantumPurification.density_rank_pos`、`UEOTQM.QuantumPurification.no_purification_empty_auxiliary`。

**边界：** 精确秩区别严格零与任意小的非零特征值。；noncomputable谱选择不是有舍入误差保证的可执行谱算法。；不覆盖近似纯化的最优资源、无限维、稳定秩或制备电路复杂度。

正式总著：[第 64 章对应结果](book/UEOT_PHYSICS.md#p-pdm-04)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-79 · N-PDM-01（同边际不允许省略直接等距的维数方向）。

**实际结论：** 实际二阶满秩边际diag(9/25,16/25)有二维和三维辅助的归一纯化；显示的复相位J:Matrix (Fin3) (Fin2)满足J†J=I2并实现真实联合密度作用，但JJ†≠I3，且不存在任何3→2全辅助空间等距。

**前提与量词：** firstFactor=diag(3/5,4/5)，secondFactor=[[9/25,12/25,0],[16i/25,-12i/25,0]]。；directIsometry=[[3/5,4i/5],[4/5,-3i/5],[0,0]]，实际系统为Fin2。；全部算术为精确复有理表达；无新增实验数据。 Displayed exact finite purifications and map, plus universal impossibility of every Matrix (Fin2) (Fin3) satisfying the full-space isometry identity.

**证明链：** 逐项计算两矩形Gram、归一和真实偏迹，得到同一满秩边际。；逐项验证J†J=I2及向量/外积作用；第三目标坐标的JJ†对角元为0，故非coisometry。；任意3→2等距若存在，其秩必要界将给3≤2，矛盾。

**实际主声明：** `UEOTQM.PurificationDimensionExamples.exact_rectangular_density_action`、`UEOTQM.PurificationDimensionExamples.generic_direct_isometry_instantiated`、`UEOTQM.PurificationDimensionExamples.direct_not_coisometry`、`UEOTQM.PurificationDimensionExamples.reverse_full_isometry_impossible`。

**边界：** 不否定支撑上的对应或第61章共同直和比较。；不把含复相位的精确形式化见证当作新增物理实验。

正式总著：[第 64 章对应结果](book/UEOT_PHYSICS.md#n-pdm-01)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-80 · P-STOP-01（原有限停止树的实际吸收补齐）。

**实际结论：** 活动 some 动作保留原分支、其 none 分支为零；idle 的 none 分支为恒等、some 分支为零。原叶编码为真实结果前缀加 none 后缀且单射，合法解码的历史恰为编码像。补齐 recordOperator 在原叶编码上逐矩阵等于原记录算子，在非法完整历史上为零；实际 run 全联合矩阵因此回接。

**前提与量词：** 原 Adaptive.Protocol 的完整有限树；有限结果载体 O；所有结果后续都有定义。；原动作族是实际完整 Kraus 仪器；量子载体及 Kraus 载体有限。；共同补齐深度 N 满足 height π ≤ N。 任意原协议 π、任意满足高度界的 N、任意原仪器族 I、任意全复矩阵 X、任意 Option 结果历史；不是只对密度态或迹的声明。

**证明链：** 用原 Kraus 完整性与唯一恒等 idle Kraus 构造实际扩展仪器。；对剩余深度归纳证明 encode/decode 两个方向及原词长度界。；按 stop/node 与 none/some 分支递归比较任意复矩阵，零分支经后续记录算子仍为零。；复用实际固定深度 run 的块矩阵表达，得到全部块的显示相等。

**实际主声明：** `UEOTQM.StoppingProtocols.record_eq_decode`、`UEOTQM.StoppingProtocols.record_encode`、`UEOTQM.StoppingProtocols.run_matrix`。

**边界：** 统一有限高度界不可删去；不是无限停止过程。；停止标签和原叶信息保留；没有把停止时间改名为 N。；控制器是明确经典历史的确定因果规则，不是相干控制器。

正式总著：[第 65 章对应结果](book/UEOT_PHYSICS.md#p-stop-01)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-81 · P-STOP-02（全效应距离保持与原叶联合态回接）。

**实际结论：** 等距像由实际单 Kraus CPTP 通道实现。E ↦ V E Vᴴ 在整个扩张空间上仍是合法效应且实际拉回为 E，因此全效应距离精确保留。原叶联合态的坐标等距像等于补齐实际 run；原联合距离和完整原叶 TV 分别精确等于补齐值。

**前提与量词：** 任意有限矩形矩阵 V 满足 Vᴴ V = I；比较完整合法效应和完整密度态。；原叶补齐实例使用 P-STOP-01 的单射及 N ≥ height π。 一般部分量化任意有限 α、β、实际等距矩阵 V 与两输入密度态；协议部分量化任意原有限停止树、两实际动作族及两初态。

**证明链：** 由 Vᴴ V = I 得 P = V Vᴴ 幂等自伴，Q = I-P 满足 Q = Q Qᴴ，故补空间投影为 PSD。；I - V E Vᴴ = Q + V(I-E)Vᴴ，得到扩张效应的互补正性；矩阵乘法给实际拉回。；CPTP 收缩给一个方向，全效应合法扩张逐概率保持给反向。；用原叶编码坐标等距逐项比较联合矩阵；TV 由单射求和及像外零质量保持。

**实际主声明：** `UEOTQM.StoppingRecordBudget.isometry_state_distance`、`UEOTQM.StoppingRecordBudget.run_eq_embedding`、`UEOTQM.StoppingRecordBudget.original_joint_distance_eq`、`UEOTQM.StoppingRecordBudget.original_record_tv_eq`。

**边界：** 没有选择默认叶，也没有额外假设原叶类型非空。；不由本结论自动获得 diamond 距离或任意辅助环境的误差预算。

正式总著：[第 65 章对应结果](book/UEOT_PHYSICS.md#p-stop-02)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-82 · P-STOP-03（共同有限停止规则的逐动作误差预算）。

**实际结论：** 原叶联合态距离 ≤ 初态距离 + Σ_t Σ_{h: C_t(h)=some a} q_t^J(h;σ) δ_rec(I_a,J_a)。原完整叶 TV 和终端量子记忆距离分别受同一个右端控制；此主加权预算不需要统一动作上界。活动 some 的真实缺陷精确等于原缺陷，idle 的真实缺陷为零。未停止概率 s_t 属于 [0,1]；若对所有历史 h（包括零权重历史）只要 C_t(h)=some a 就有 δ_rec(I_a,J_a) ≤ ε_t，则联合界进一步为初态距离 + Σ_t s_t ε_t。

**前提与量词：** 两套实际动作仪器共享同一个原完整有限树 π，故动作选择与停止规则相同。；Kraus 索引载体可不同，结果与量子记忆载体相同；N ≥ height π。；q_t(h) 是 J 从 σ 出发经过真实前缀 run 的 PSD 块质量。 任意上述 I、J、π、N 和原完整密度态 ρ、σ；每层求和包括全部完整经典历史，费用仅在该历史实际选 some a 时计入。

**证明链：** 先以实际等距像证明活动联合态和动作缺陷保持；直接比较双方 idle 状态后证明其上确界为零。；将共同停止树映射到已有固定深度控制器，复用已证真实逐步动作预算。；将 actionCost 精确重写为参考 J 从 σ 出发的真实历史块权重及原活动动作缺陷，消去 idle 项。；通过 P-STOP-02 回到原叶联合态；原记录和终端记忆分别用事件效应与实际偏迹收缩。；用非负块质量逐项乘实际活动动作的 ε_t 上界并求和。

**实际主声明：** `UEOTQM.StoppingRecordBudget.original_joint_distance_le_activeCost_sum`、`UEOTQM.StoppingRecordBudget.original_record_tv_le_activeCost_sum`、`UEOTQM.StoppingRecordBudget.terminal_memory_distance_le_activeCost_sum`、`UEOTQM.StoppingRecordBudget.original_joint_distance_le_probability_budget`。

**边界：** 参考权重明确属于 J 和 σ，不可更换成另一实现/初态而不另证。；共同停止规则不能删除，见 P-STOP-05。；不处理相干控制器、未建模外部量子记忆、稳定化通道距离或无界停止。

正式总著：[第 65 章对应结果](book/UEOT_PHYSICS.md#p-stop-03)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-83 · P-STOP-04（停止协议的精确 $1/16$ 记录差异）。

**实际结论：** 三个原叶概率为 I=(3/4,1/4,0)、J=(3/4,3/16,1/16)。第二动作实际全输入记录缺陷为 1/4，J 的第二步真实未停止质量为 1/4；总成本为 1/16，原叶 TV 和补齐 TV 均精确为 1/16。

**前提与量词：** 具体 qubit 完整有理 Kraus 仪器；首步双方共同以 3/4、1/4 记录 0、1。；原共同树在首结果 0 时早停，首结果 1 时执行第二动作后停止。；I 第二动作确定记录 0；J 第二动作仍以 3/4、1/4 记录 0、1。 任意共同输入密度态 ρ 的三个原叶概率、原叶 TV 与补齐记录 TV；联合态上界允许任意 ρ、σ。

**证明链：** 以四个幅度 1/2 的实际 Kraus 项构造偏置仪器，正性和完整性均为精确矩阵证明。；对全部合法联合效应证明 1/4 的动作缺陷上界，并用实际事件达到下界。；计算真实参考一步前缀分布和活动历史，得到 0 + (1/4)(1/4) = 1/16。；主预算给 TV 上界，晚停叶 (1,1) 事件给相同下界。

**实际主声明：** `UEOTQM.StoppingRecordBudgetExamples.stopping_record_tv_exact`、`UEOTQM.StoppingRecordBudgetExamples.completed_record_tv_exact`、`UEOTQM.StoppingRecordBudgetExamples.activeCost_sum_exact`、`UEOTQM.StoppingRecordBudgetExamples.completed_joint_bound`。

**边界：** 精确有理形式化正控，不是实验确证。；TV 等式比较相同输入；不同输入的联合态结论保留初态距离项。

正式总著：[第 65 章对应结果](book/UEOT_PHYSICS.md#p-stop-04)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

### QMK-84 · P-STOP-05（相同量子动作不控制不同停止规则的全部记录）。

**实际结论：** 立即停止记录确定为 none，一步后停记录确定为 some 0，补齐记录 TV 精确为 1。两原终端量子记忆均等于 ρ，因此相同。

**前提与量词：** 相同的完整原仪器族，量子操作为恒等且原记录确定为 0。；两个原控制器分别立即停止和执行一步后停止；因此它们不满足共同停止树前提。；用同一个 Option 结果载体及深度 1 比较保留停止标签的记录。 任意 qubit 输入密度态 ρ；两原动作族实际缺陷均为零，但停止规则不同。

**证明链：** 事件 none 在两完成记录中的概率分别为 1 和 0，事件下界结合 TV ≤ 1 得到等号。；实际原叶记录算子经 discard_record_operator 求和：立即停止为恒等，单步唯一非零分支仍为恒等。

**实际主声明：** `UEOTQM.StoppingRecordBudgetExamples.different_stopping_rules_tv_one`、`UEOTQM.StoppingRecordBudgetExamples.negative_terminal_memories_equal`。

**边界：** 此例位于共同控制器条件之外，不否定 P-STOP-03。；终端量子记忆相同，不声称终端量子态不同。；不能删除停止标签后再声称保留全部记录差异；不是经验实验。

正式总著：[第 65 章对应结果](book/UEOT_PHYSICS.md#p-stop-05)；具体见证名、源 SHA 与支撑声明见[当前台账](status/CLAIM_LEDGER_v31.9.json)。

## 4. 连续正式著作与历史保护

《UEOT物理学》正式 3.5：66 章（0–65）、6 个附录、161 个稳定编号结果、248 页实际 PDF，147 个旧编号结果保留，14 个新增结果在第 63–65 章；原 70 项主张对象逐值继承，当前台账共 84 项。已关闭的旧开放子责任用附加关系连接，历史对象与实际执行身份保持原样。[规范 Markdown](book/UEOT_PHYSICS.md)、[TeX](book/UEOT_PHYSICS.tex)、[完整 PDF](book/UEOT_PHYSICS.pdf)、[逐章档案](book/CHAPTER_DOSSIER.json)与[实际书门](book/evidence/v3.5/local-release-gates.json)共同给出论证与出版身份。

三遍实际排印成功，结构、视觉和档案门以各自真实回执为准。视觉范围是回执中列出的全书总览及指定完整页审查，不能称为每页完整精读。有限声明的形式化也不表示全书每句文字已经机器证明。

## 5. 远端待办与持续开放责任

本地检查点为 `LOCAL_VERIFIED_REMOTE_PENDING`；真实 v31.9 commit、PR、PR run、受验 main 与 main run 未由本地验收产生，当前字段保持空值或 PENDING。v31.8 的真实远端成功身份保存在[历史整合回执](kernel/evidence/v31.8/integration-verification.json)。后续须发布唯一源码 PR、核验其实际日志、合入后核验独立 main push CI，并逐项核对 98 源、56 Core、三份正文及冻结载荷，再由单独 metadata 提交记录 MAIN_VERIFIED；metadata commit 不能冒充实际 CI-tested source commit。没有下载 artifact ZIP，就不声称核验其内部内容。

本轮没有新增真实实验，不把形式证明、精确算术或合成模型称为实验确证。UEOT Core 唯一选择复量子模型、完整自然理论、一般谱与无限过程、独立物理适用性、真实 QDRR、完整母谱与阈值、真空/质量、连续极限和 QFT 继续开放。三代结论仍依赖谱、表示、异常、阈值及有效窗口等明确前提。
