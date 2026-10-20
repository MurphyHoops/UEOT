# QMB-05：真实有限 CPTP 的 Cesàro 平均与平稳态

状态：**LOCAL_FOCUSED_VERIFIED**。唯一新增 authoring 文件为 `formalization/ueot-qm/UEOTQM/Cesaro.lean`，命名空间 `UEOTQM.Cesaro`。源 SHA256：`64bc01d0f1ac484272aa8753be7c32bae6808cf26b0b9977ed1fd3cf1e5fc71b`。

## 1. 已证明的数学内容

固定一个实际 `Instrument ι O κ`。其有限 Kraus 完备性定义了真实完整通道 `I.channel` 与密度态映射 `I.channelState`。`iterateState I ρ n` 直接复用 `channelTrajectory (fun _ => I) ρ`；没有输入一个抽象轨道及其希望成立的性质。

对 `N > 0`，`orbitSum` 是 `Finset.range N` 上真实密度矩阵之和，`averageState` 是其乘以实数 `N⁻¹` 的密度态。半正定性与迹一均作为构造证明提供；`N=0` 不伪装为密度平均。

`orbitSum_telescope` 和 `matrix_residual` 给出：

\[
T(\bar\rho_N)-\bar\rho_N=N^{-1}(T^N(\rho)-\rho).
\]

`probability_residual_le` 使用同一矩阵恒等式、实际 Born 配对的线性性和两端概率都在 `[0,1]`，证明对 **每一个** `Effect`：

\[
|\Pr_E(T\bar\rho_N)-\Pr_E(\bar\rho_N)|\le 1/N.
\]

`effectDistance_residual_le` 将此提升为已定义的全效应上确界残差界。它没有以有限抽样效应代替全效应。

`density_operatorNorm_le_one` 从 Hermitian 谱分解、PSD 特征值非负以及特征值之和为迹一，得到密度矩阵的 **Euclidean operator norm** 不超过 1。因此 `matrix_residual_norm_le` 给出此算子范数下的 `2/N` 残差界，`matrix_residual_tendsto_zero` 证明残差趋于零。本文件没有证明 trace norm 与该范数相等，也没有把该算子范数界称为迹范数形式化结果。

`densityMatrices_closed` 从 C⋆ 非负锥的闭性和矩阵迹的连续性证明 PSD 且迹一集合闭；`densityMatrices_compact` 再用上述实际范数界与有限维 properness 证明紧。紧性不是结构字段或输入假设。`continuous_channel` 来自实际 `channelLinear` 的有限维连续性。

`subsequence_limit_invariant` 对任一严格递增指标函数的收敛 Cesàro 子列证明 `I.channel X = X`；`subsequence_limit_density` 另外证明极限的 PSD 与迹一。`exists_stationary_subsequence` 用已证明的紧性实际产生一个平稳密度态及收敛子列。`exists_stationary_of_density` 给出有任意真实初态时的存在性；最终 `exists_stationary` 在显式 `[Nonempty ι]` 下，以归一化单位矩阵 `normalizedIdentity` 自行提供初态，所以没有假设平稳种子。

## 2. 拓扑与范围

所有极限位于有限复矩阵的原生拓扑。模块局部打开 `Matrix.Norms.L2Operator`；所用 Mathlib `Analysis/CStarAlgebra/Matrix.lean` 明确通过 `replaceTopology` / `replaceUniformity` 保留原生逐项矩阵拓扑。因此谱范数估计、迹连续性、线性通道连续性与紧性证明使用的是同一拓扑；没有隐蔽切换到另一种收敛关系。

结论只针对固定、时齐、完整、逐步丢弃结果的有限 Kraus 通道。任意有限维数均在 Lean 数学合同内；本模块不是有限维数 1–4 的 Python 证书资源合同。选择性后验、时变控制序列、旁系统扩张和无限维动力学不由该长期定理自动覆盖。

本轮证明了 Cesàro 子列和至少一个平稳态。它没有证明唯一性、原始时刻轨道收敛、完整 Cesàro 序列收敛、谱隙、混合率或随机轨道经验频率。小残差也不自动给出到某个平稳态的定量距离界。这些结论均未被换成结构字段。

## 3. UEOT 对应与物理依赖

读取的原件为 `02-UEOT_Core_Mathematics_v3.0_Complete.md` 中 P-PER-02（§8.4）、P-GOA-01（§21.2）以及 §21.1 / §21.3 的类型与混合边界；总著 §1.4 的 M-OI 有限量子推导是本轮直接目标。原件的共同数学机制是“占据平均、消失残差、紧性/子列与不变闭合”。本模块在选定量子对象上重新给出完整矩阵证明，并没有把经典概率核类型与密度算子类型当作同一类型，也没有声称直接实例化了一个未导入的 Core P-GOA Lean 声明。

按 `physics/interfaces/CORE_PHYSICS_CONTRACT.md`，此为有清晰域和假设的量子 **B（bridge）** 数学切片；有限复 Hilbert / Born / Kraus 扇区来自明确的 S/P 输入。若把固定时齐 CPTP 用作真实器件模型，时间齐次和无记忆模型适用范围属于 E（effective/modeling assumption）。全效应残差是 O（observable consequence）形式的条件结果，不等于取得了新的实验数据。没有新加 UEOT 特有 X 猜想或将标准量子扇区升级为通用 Core 定律。

## 4. 实际验证与交叉审查

使用实际工具链：`Lean 4.33.1`，commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`。最终独占文件 focused 编译 exit 0，日志为空；已生成 `UEOTQM/Cesaro.olean`。本文件有 23 个显式 theorem、7 个 definition。

全部 30 个公开声明逐一实际执行 `#print axioms`，名称完整且唯一；依赖仅为允许的 `propext`、`Classical.choice`、`Quot.sound`，无新公理、`sorryAx` 或本地假定。记录见 `verification.json`、`axiom-audit.log`、`declarations.json` 与 `AxiomAudit.lean`。

`/root/finite_response` 完成独立只读语义复核，结论 CLEAR，特别核对了 Mathlib L2Op 的拓扑替换实现、真实紧性和 `[Nonempty ι]` 边界。本审查没有替代 root 的整包 build、公共 AxiomAudit 接入或远端 CI；这些集成动作尚由 root 完成。

本文件只增加数学证明。没有新增 Python 运行时功能、数值实验或物理实验，也没有修改 Core、公共入口或总著。
