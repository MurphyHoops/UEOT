# UEOT-QM v31.2 / Kernel 1.2

> 集成跟进（2026-10-19 UTC）：本版已通过 PR #333，并在主线 `c7aa925f338877d7338326f5cee8a165253f69dd` 的工作流 39294335590 完成 Lean/runtime 验收。见 [集成回执](kernel/evidence/v31.2/integration-verification.json)。下文的 LOCAL_VERIFIED_CI_PENDING 描述本报告生成时的历史检查点；当前继续建设见 [v31.3](UEOT_QM_KERNEL_v31.3.md)。

日期：2026-10-19。承接已合入的 [Kernel 1](UEOT_QM_KERNEL_v31.1.md)；研究基线为 `23d36e4d4b805ef138c9179c5b33c1a89a924dbe`。本轮是 QM 领域的结构增量，Core v3 的冻结定义、106 项覆盖与四个计数生成器保持不变。

**当前验收：`LOCAL_VERIFIED_CI_PENDING`。9 个 Lean 模块、128 个显式定理已由官方 Lean 4.33.1 实际构建通过，137 项真实公理审计通过；72 项运行测试和两个完整演示通过。** 已验证源码对应提交 `323db6d1c2e50a432bdcf6a6872212426cc826ce`。GitHub Actions 正值官方服务故障，PR #333 与主线集成验收仍待完成。机器状态与完整输出见 [v31.2 主张台账](status/CLAIM_LEDGER_v31.2.json) 和 [源码绑定证明回执](kernel/evidence/v31.2/lean-verification.json)。

## 1. 本轮建立的内核结构

Kernel 1 已有合法密度态、完整 Kraus 操作、全词响应商、正概率后验及可实现响应空间的闭合更新。本轮进一步把这个函数值响应对象连接到有限坐标，并使有限适应树的完整记录律进入同一数学接口。

| 层 | 本轮对象 | 所完成的桥 |
|---|---|---|
| 量子操作 | 实际 Kraus 分支与其 Heisenberg 拉回 | 从矩阵乘法与迹循环性得到真实对偶等式 |
| 可观测空间 | 全部有限词效应的实张成 `observableSpace` | 最小闭包、Hermitian 性、有限维及有限真实词生成存在性 |
| 有限表示 | 词见证、单位索引、分支系数、局部矩阵恒等式 | 有限坐标相等当且仅当全词响应相等 |
| 闭合更新 | `closedCoordinateUpdate` | 从当前坐标计算正概率分支的后验，输出仍在物理可实现坐标像中 |
| 自适应协议 | 每个结果均有延续的有限树 | 叶记录唯一、总概率一、坐标计算与实际叶概率一致 |
| 可执行证据 | 可导出的词效应证书与独立 checker | 无需重跑闭包搜索即可复查生成、独立性、全部局部等式和上下文 |
| 谱选择接口 | 实际有限 family、额外物质与窗口清单 | 逐项求和后导出 G3 的异常方程与必要弱预算 |

数学接口中的“全部有限词”具有统一量词。运行证书检查的是支持该量词的精确闭包条件；有限样本概率相等或有限深度搜索本身不提供这种结论。

## 2. 从原始理论到可检查的对象

本轮重新核对用户提供的原 PDF、Core 数学主文和三个 post-Core 规划文件，完整身份与章节对照见 [原件及表示审查](audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md)。上传 PDF 与当前仓库根目录 `UEOT_v3_top.pdf` 的 Git blob 一致；这只解决了该份原件的身份，其他历史档案继续保持各自状态。

Core 主文 §4.2、§4.5 和 §7 的共同要求是：对象相对于声明的未来与协议成立；递归更新必须保持同一等价类；条件化要处理正概率事件。一次测量边缘相同不足以支持全部未来相同。有限维 QM 内核据此采用

\[
\rho\sim_{\mathcal L}\sigma
\quad\Longleftrightarrow\quad
\forall w\in(A\times O)^*,\ R_\rho(w)=R_\sigma(w),
\]

其中操作库 \(\mathcal L\) 固定且时齐。对象在此处是协议相对的响应类，不能自动被解释为自修复组织、供能系统、独立的历史实例或目的主体。环境携带的相关记忆若没有纳入状态，系统密度矩阵也不自动充分。

Core 的 generic 对象、额外的持续／恢复合同、机制毁损结构 Ω、目的机制与 Π/Φ 经验假说继续分开。新响应坐标不是从数据识别出的双驱动；Z、HZ、HSZ 下的响应维数也不等于驱动数、熵、Hilbert 维数或控制收益。下一步如果引入优化，需要明确损失、资源、时域和策略类，并检查这些读出在响应类上是否良定义。

原 PDF 的 `β₁ = 3 → Index(D) = 3 → generations` 推论继续退役。重新提供原件不构成该几何桥的证明。本轮使用已有异常／弱窗口路线，并把输入谱到条件式的距离缩短了一步。

## 3. 实际量子记录的有限表示定理

### 3.1 Kraus 对偶与词效应

在有限复矩阵扇区，分支 \(e=(a,o)\) 为

\[
\mathcal I_e(X)=\sum_kK_{e,k}XK_{e,k}^\dagger,
\qquad
\mathcal I_e^*(E)=\sum_kK_{e,k}^\dagger E K_{e,k}.
\]

`trace_heisenberg` 从这两个实际定义证明

\[
\operatorname{tr}(E\mathcal I_e(X))
=\operatorname{tr}(\mathcal I_e^*(E)X).
\]

令 \(E_\varnothing=I\)、\(E_{e::w}=\mathcal I_e^*(E_w)\)。记录按时间顺序书写，因此 Heisenberg 计算从最后一个字母向前拉回。`mass_recordOperator_eq_pairing` 证明它与 Schrödinger 正向记录递推一致：

\[
R_\rho(w)=\operatorname{Re}\operatorname{tr}(E_w\rho).
\]

每个词效应 PSD。定义

\[
W_*:=\operatorname{span}_{\mathbb R}\{E_w:w\text{ 为有限词}\}.
\]

`observableSpace_pullbackClosed` 与 `observableSpace_le_of_closed` 证明它是包含 \(I\)、对所有允许分支拉回闭合的最小实子空间。实张成中的元素 Hermitian。有限复矩阵空间还给出 \(W_*\) 有限维，`exists_finite_wordEffect_generators` 进一步证明存在有限个真实词效应张成它。

这项存在性不依赖 Python 的搜索程序。此轮没有把逐轮 \(W_n\) 搜索的终止性、专门的 Hermitian \(d^2\) 维数公式或高斯消元正确性一并写成 Lean 成果。

### 3.2 局部证书为什么足够

`FiniteObservablePresentation` 只提供有限索引 \(j\)、实际词 \(w_j\)、空词索引 \(u\) 和局部恒等式：

\[
B_j=E_{w_j},\qquad B_u=I,\qquad
\mathcal I_e^*(B_j)=\sum_k A_{e,jk}B_k.
\]

它没有“全部词已覆盖”“坐标足够”或“后验保持相容”的字段。由生成性可得 \(\operatorname{span}B\subseteq W_*\)；由单位效应和局部闭包，按词长归纳得到另一包含。于是

\[
\operatorname{span}_{\mathbb R}B=W_*.
\]

定义 \(x_j(\rho)=\operatorname{Re}\operatorname{tr}(B_j\rho)\)。`coordinates_eq_iff_response_eq` 推出

\[
\boxed{x(\rho)=x(\sigma)\iff R_\rho=R_\sigma.}
\]

Lean 的有限 presentation 允许冗余生成元，因为充分性不需要独立性。运行 checker 另外验证实线性独立性，从而得到一个实基；这项更强的运行检查不应被反过来误述为 Lean 已证明最小物理 Hilbert 实现。

### 3.3 更新与物理可实现性

矩阵行约定固定为上式的 \(A_{e,jk}\)，所以分支在未归一化坐标上是

\[
y=A_ex,\qquad p=y_u,\qquad
x'=\frac{y}{p}\quad(p>0).
\]

`operatorCoordinates_branch`、`operatorCoordinates_record` 和 `coordinates_posterior_eq_normalizedBranch` 分别对应一步、任意有限记录与正概率条件化。完整记录先保留总质量，最终从单位坐标读出概率。

`closedCoordinateUpdate` 的值由 \(x\) 直接计算，类型为

```lean
Set.range C.coordinates → (A × O) → Option (Set.range C.coordinates)
```

实际后验只作为输出仍属于同一物理可实现像的证明见证。零概率分支返回 `none`。该接口不要求为任意外部实向量求解一个物理态，也不声称已经提供这样的可实现性判定器。

## 4. 完整有限自适应协议

`Adaptive.Protocol` 有停止节点以及动作节点；动作节点为每个结果指定后续子树。控制策略可以依赖已观察结果。通过树归纳，叶集合有限；`word_injective` 证明不同叶具有不同实际记录。

对任意输入算子，`sum_leafWeight` 从每个动作的 Kraus 完整性推出总叶权重等于输入质量。对于密度态，叶权重非负，且

\[
\sum_{\ell\in\operatorname{Leaf}(\pi)}P_\rho^\pi(\ell)=1.
\]

新组合定理直接连接有限表示与适应树：

\[
P_\rho^\pi(\ell)
=\bigl[\operatorname{recordCoordinates}(\operatorname{word}(\ell),x(\rho))\bigr]_u.
\]

因此同坐标态在每一棵完整有限自适应树上具有相同记录律。原来全词商的语义现在有实际有限表示与树解释器共同承接。

该数学树使用共同有限结果索引，属于确定性、有限、完整分支的控制策略。Python 的不同动作结果集合、具体序列化格式和深树遍历仍需数据适配与程序细化。数学接口成立不自动验证它们的实现。

## 5. 独立表示证书与运行证据

新公开入口：

```python
certificate = export_representation_certificate(model)
receipt = verify_representation_certificate(
    certificate, model.library,
    expected_context_fingerprint=model.context_fingerprint,
)
```

checker 从公开 Kraus 数据重算完整性和词效应，以 Frobenius Gram 行列式检查独立性，并检查每个分支、每个基元素的局部恒等式。测试中禁用闭包搜索、系数求解器与 `Instrument.adjoint` 后，手写证书仍可独立通过。它共享精确矩阵算术底座；这份 checker 本身尚未在 Lean 中验证。

运行端支持 \(1\le d\le4\)、\(1\le r\le d^2\)，证据词长度上限 \(d^2-1\)。这些是证据格式的资源界，允许预测的有限记录没有统一时域上限。整数位长及库的动作／Kraus 总数没有统一上限，不宣称总体固定时间或全面资源保证。

Z、HZ、HSZ 三个操作库的证书分别有 2、3、4 个响应坐标，均包含迹坐标。换用合法的新词效应基可以生成新上下文；若调用方固定旧模型指纹，则会拒绝该替换。不同 Kraus 清单即使物理等价也不自动共享指纹。

| 测试组 | 方法数 | 重点 |
|---|---:|---|
| 既有操作、协议、证书 | 32 | 干涉、相位、纠缠、非正反例、零分支、记忆与有限覆盖 |
| 表示证书 | 18 | 伪闭包、错词顺序、转置系数、缺失分支、依赖基、上下文及数值格式 |
| 谱桥与六项局域异常 | 22 | 实际行和、三代条件、模板／复制／补偿／阈值及完整谱遗漏 |
| 合计 | **72** | 每项可包含多个精确实例；测试方法数不是定理数 |

## 6. 从实际谱到条件三代

`Spectrum.lean` 与 `spectrum.py` 从 family 列表计算 \(n\)、轻子方向计数 \(\ell\)、夸克方向计数 \(k\)，并逐项累加异常、额外物质和弱屏蔽。family 计数没有预置为三，最终选择方程也没有作为数据字段。

以非零单位异常 \(a\) 为声明的表示数据，实际行和为

\[
A_{\rm family}=a[(2\ell-n)+N_c(2k-n)].
\]

若所有轻子同向、额外 cubic 组合总和为零、总 cubic 异常为零，就导出

\[
2N_ck+n=N_cn.
\]

固定普通弱 \(SU(2)\) 窗口、所有所计 ordinary 双重态活跃时，实际一环系数为

\[
b_2=\frac{22}{3}-\frac{n(N_c+1)}3-S_{\rm extra},\qquad S_{\rm extra}\ge0.
\]

Weyl、复标量、实标量按各自 Dynkin index 分别贡献 \(2/3,1/3,1/6\) 权重；约定的原始物理出处与换算见 [谱桥审查 §3、§8](audits/SPECTRUM_BRIDGE_v31.2.md)。从完整 \(b_2>0\) 导出必要条件 \(n(N_c+1)<22\)，再实际调用旧 Selector，得到

\[
N_c=3,\qquad n=3,\qquad k=1.
\]

`spectrum_selects_three` 仍要求 \(N_c\ge3\)、非空 family、非零异常单位、同质轻子、完整相关异常清单、额外组合和为零以及所声明的弱窗口。它关闭了有限谱算术适配，尚未证明现实为何满足这些物理前提。

| 实际输入 | 计算结果 | 选择状态 |
|---|---|---|
| 三代加一个 Higgs 双重态 | 总 cubic 为零，\(b_2=19/6\) | 声明合同下适用 |
| 混合轻子两代 | 总 cubic 为零，\(b_2=14/3\) | 同质模板失败 |
| 同质三代复制为六代 | 总 cubic 为零，\(b_2=-2/3\) | 正系数条件失败 |
| 一代加补偿项 | 总 cubic 为零，family 部分非零 | 额外组合和条件失败 |
| 三代加 20 个复标量双重态 | ordinary 预算为 12，完整 \(b_2=0\) | 必要预算不能代替完整系数 |
| 六代但第二组三代不活跃 | 完整窗口内 \(b_2=10/3\) | 全部所计 ordinary 活跃条件失败 |

另一个精确求和器按全左手 Weyl 清单计算 \(C^3,L^3,C^2X,L^2X,\mathrm{grav}^2X,X^3\) 六个局域异常。三代、混合两代及复制六代实例都可六零，说明单靠局域异常消除不足以唯一选择三代。删除一般带荷 \(E^c\) 的实例会产生非零重力／U(1) 残余。六项求和属于 Python 执行证据，本轮 Lean 谱模块覆盖选定 cubic 通道和弱预算。

## 7. 证明审计与证据层

九个模块的 128 个显式 theorem 已完成实际构建；137 个命名声明的真实 `#print axioms` 输出已经由审计脚本逐项验证，包括九个额外的携带证明构造。`lake build UEOTQM` 和公理审计均返回 0。日志中的 8729 个 build jobs 是包含依赖的构建任务数，与定理数不同。

标准基础允许 `propext`、`Classical.choice`、`Quot.sound`。这不是“完全无公理”的声明。命名审计覆盖所列显式定理与构造，不冒充全部编译器生成常量的枚举。

Core 的三个既有接口继续被量子模型实际复用：商下降、递归充分状态的闭合更新、加权误差链。本轮不改其证明，也不消费尚未合入的 Core 研究分支。构建继承固定工具链与锁定依赖；合入前核对 main 的并行变化，合入后核对集成结果。

源码、编译输出、公理输出、运行回执、原件语义审查和物理适用性是不同证据。旧 v31.1 回执保持原字节；新回执已写入 `kernel/evidence/v31.2/`。本地工作树、实际构建副本与远端已验证源码树的 30 个源码／锁定文件逐项一致；官方编译器归档 SHA256 及全部九项已安装 Git 依赖 revision 也已核对。回执明确记载本地执行来源，不把它写成 GitHub CI 成功。

## 8. 下一阶段按依赖推进

1. **把精确证书接入 Lean。** 先完成 Gaussian-rational 数据到复矩阵的解释、非负 weighted Kraus 到 ordinary Kraus、不同动作结果／项数的共同索引适配。优先验证短证书 checker 的可靠性，再决定是否需要证明完整搜索与消元程序。这将把本轮数学合同转成可由机器直接验收的实例。
2. **把误差链接到一种量子距离。** 固定状态／准备对应、允许协议及读出，选择操作 seminorm 或有限维 trace-distance，证明局部界，再调用现有 transport。后选择要保留事件概率下界，不能把其放大效应抹去。
3. **推进 QMB-05 与 QMB-06。** 有限 CPTP 的 Cesàro 残差与平稳极限点先行；对角存活 CP 到 substochastic 核、再到 Core 的存活桥。唯一性、混合速率及真实开放系统意义分别给出前提。
4. **建立一个可失败的数据接口。** 选择 QDRR 的具体准备、仪器、噪声与统计零假设，保存原始记录和注入控制。当前精确闭包证书不能代替含噪系统辨识的误差保证。
5. **推进谱的模型义务。** 具体表示系数、母谱与弱 EFT 阈值匹配、全局异常、规范群全局形式、标量势与质量。用真实模型补足合同，避免把窗口布尔声明当作物理推导。
6. **再扩大到 CV 与 QFT/RG。** 有限矩阵的迹恒等式禁止全空间精确 \([Q,P]=i\hbar I\)；应采用有界 Weyl 测试、能量和尾部界，再处理无界算子定义域。QFT/RG 按指定正规化模型、两侧记录及独立误差桥接入。

完整工作包与六桥状态见 [ROADMAP](ROADMAP.md)。这些下一项都有明确验收对象；本轮已形成可继续扩展的有限操作／表示核心，不登记整套量子场论或新经验确认已经完成。

## 9. 运行与文件入口

从仓库根运行：

```bash
python physics/qm/kernel/demo.py
python physics/qm/kernel/demo_v312.py
python physics/qm/kernel/verify_kernel.py --output /tmp/ueot-qm-runtime-v312.json
```

Lean 构建、完整模块表和 Core 复用入口见 [证明包说明](../../formalization/ueot-qm/README.md)。运行 API 与证书读写见 [内核说明](kernel/README.md)。

- [原件与有限表示审查](audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md)
- [谱桥与反例审查](audits/SPECTRUM_BRIDGE_v31.2.md)
- [本轮集成验收](audits/KERNEL_REVIEW_v31.2.md)
- [当前状态](status/CURRENT.json) 与 [主张台账](status/CLAIM_LEDGER_v31.2.json)

