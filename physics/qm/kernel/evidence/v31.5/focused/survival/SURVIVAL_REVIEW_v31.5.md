# QMB-06：真实量子分支到冻结 Core 的有限存活／QSD／Doob 桥

## 1. 冻结对象与验收结论

唯一新增正式模块为 `formalization/ueot-qm/UEOTQM/Survival.lean`，命名空间为 `UEOTQM.Survival`。源码 SHA-256：

`60147ec170cda07d39a225122dca064ec576fed41ebab3d630940eba48f82b1f`

该文件实际使用官方 Lean 4.33.1 编译成功，退出码 0，无警告。新增 **32 个显式 theorem、13 个 def**；全部 **45 个命名声明**均执行了真实 `#print axioms`。报告名称唯一、集合完整，实际依赖仅为 `propext`、`Classical.choice`、`Quot.sound`。没有新增结构公理，没有 `sorry`、`admit`、`native_decide`、新 `axiom` 或不透明证明逃逸。

正式模块通过普通数学证明构造实际复矩阵 Kraus 仪器。冻结 Core 文件未修改；原有 `UEOT.V3.QSDPerron` 的代数定理被真正应用于推导出的量子／经典恒等式。有限索引的判等实例通过 `Subsingleton.elim` 对齐调用方与 Core 的 `Classical.decEq`，没有改动矩阵运算的数学含义。

交叉语义审查由协作代理 `kernel_certificates` 只读完成，结论 CLEAR。这是 AI 协作审查，不能表述为独立人类同行评议。

## 2. 数学合同：行分布、测量与制备、失败补全

取有限指标类型 \(\iota\)，输入非负矩阵 \(Q\) 满足

\[
Q_{ij}\ge0,\qquad \sum_jQ_{ij}\le1.
\]

本模块固定**行分布约定**：\((pQ)_j=\sum_i p_iQ_{ij}\)。指标 \(i\) 是源态，\(j\) 是目标态。`matrixUnit j i` 是实际复矩阵单位 \(U_{ji}=|j\rangle\langle i|\)，满足

\[
U_{ji}^{\dagger}U_{ji}=|i\rangle\langle i|,\qquad
U_{ji}XU_{ji}^{\dagger}=X_{ii}|j\rangle\langle j|.
\]

这两条恒等式分别由 `matrixUnit_gram`、`matrixUnit_sandwich` 证明。成功结果为 Bool `true`，其实际普通 Kraus 矩阵是

\[
K^{\mathrm{success}}_{ij}=\sqrt{Q_{ij}}\,U_{ji}.
\]

为得到完整仪器，定义失败核

\[
D_{ij}=\delta_{ij}\left(1-\sum_kQ_{ik}\right).
\]

`failureKernel_nonneg` 从行和上界推出失败权重非负。失败结果为 Bool `false`，仍采用 \(U_{ji}\) 而取权重 \(D_{ij}\)。由逐项 Gram 计算，

\[
\sum_{ij}Q_{ij}U_{ji}^{\dagger}U_{ji}
=\operatorname{diag}\left(\sum_jQ_{ij}\right),
\]

\[
\sum_{ij}(Q_{ij}+D_{ij})U_{ji}^{\dagger}U_{ji}=I.
\]

`measurePrepare_gram` 和 `outcomeKernel_complete` 证明上述等式；`weightedInstrument` 随后取得非负性与完整性证据，`instrument` 通过既有 `WeightedInstrument.toInstrument` 引入真实平方根 Kraus 矩阵。因此完整性不是用户填写的结论字段。任意实数权重的 `measurePrepare` 仅是代数定义；物理 CP 仪器由 `instrument` 的非负性与行和前提保证。

## 3. 从真实量子分支推出经典存活概率和条件态

`diagonalOperator p` 把实向量嵌入真实复矩阵 \(\operatorname{diag}(p)\)。该映射是单射，保持实数缩放；非负向量给出正半定矩阵。若再有 \(\sum_i p_i=1\)，`diagonalDensity` 实际构造正半定且迹为一的 `Density`。

`measurePrepare_apply` 对**任意复矩阵** \(X\) 推出

\[
\mathcal S_Q(X)
=\operatorname{diag}\left(\sum_iQ_{ij}X_{ii}\right)_j.
\]

该公式明确显示测量制备映射去除非对角相干项。对角态得到

\[
\mathcal S_Q(\operatorname{diag}p)
=\operatorname{diag}(pQ).
\]

这一恒等式由 `success_branch` 从实际普通仪器的 Kraus 分支推出，没有作为结构假设。`success_probability` 进一步给出真正 Born 分支概率

\[
s(p)=\operatorname{tr}\mathcal S_Q(\operatorname{diag}p)
=\sum_j(pQ)_j.
\]

`success_posterior_matrix` 只接受严格正概率见证 \(s(p)>0\)，并证明真实 `Instrument.posterior` 的矩阵等于

\[
\operatorname{diag}\left(\frac{(pQ)_j}{s(p)}\right)_j.
\]

零概率事件没有被包装为有效归一化密度。此处的对角子代数与测量基是建模选择；上述结果不把任意量子仪器等同于经典 Markov 核。

## 4. 有限成功记录与 Core QSD 定理的真实调用

`killedIterate I n X` 不是孤立定义的经典递推：它就是既有 `recordOperator` 作用于长度 \(n\) 的真实时间顺序成功记录。`killedIterate_diagonal` 归纳证明

\[
\mathcal S_Q^n(\operatorname{diag}p)=\operatorname{diag}(pQ^n).
\]

`survivalMass_eq_response` 将其质量直接识别为既有 `response` 的记录概率。给定归一化非负左本征向量与关系

\[
qQ=rq,\qquad q_i\ge0,\qquad \sum_iq_i=1,
\]

正式证明按以下依赖完成：

| 新量子定理 | 实际调用的冻结 Core 定理 | 得到的量子结论 |
|---|---|---|
| `qsd_killedIterate` | `leftPerron_pow` | 真正成功记录算子为 \(r^n\operatorname{diag}q\) |
| `qsd_survival_pow` | `qsd_survival_mass_pow` | 真实记录概率为 \(r^n\) |
| `qsd_conditionalState` | `qsd_all_steps` | \(r>0\) 时正事件条件态为原 \(\operatorname{diag}q\) |
| `qsd_rate_le_one` | `perron_root_le_one_of_substochastic` | \(r\le1\) |

`qsd_survival_pos` 从 \(r>0\) 推出每个有限步的成功概率严格为正，从而可提供条件态所需见证。`conditionalState` 使用真实记录的正半定输出和既有 `normalize` 构造 `Density`。

这里的左本征关系是清楚声明的输入；没有把三条量子结论作为输入。Core 中一般 Perron 数据的存在、唯一性与渐近收敛仍不是本模块的证明成果。

## 5. Doob 过程：\(q\) 与 \(\pi=q h\) 必须区分

再给定严格正的右本征函数和正因子

\[
Qh=rh,\qquad h_i>0,\qquad r>0.
\]

采用冻结 Core 的

\[
Q^{\uparrow}_{ij}=\frac{Q_{ij}h_j}{r h_i}.
\]

`doobTransform_nonneg` 证明非负；`doobInstrument` 实际调用 Core `doobTransform_row_sum` 得到行和一，再走同一个完整 Kraus 仪器构造。因此右本征关系承担行随机性责任，并未被省略。

给定 \(q_i\ge0\) 和归一化 \(\sum_iq_i h_i=1\)，`doobDensity` 构造

\[
\rho_{\pi}=\operatorname{diag}(\pi),\qquad \pi_i=q_i h_i.
\]

它调用 Core `doobInvariant_sum`，而 `doob_success_branch` 调用 `doobInvariant_stationary`，把经典平稳关系提升为实际复矩阵分支固定点。接着 `doob_killedIterate`、`doob_survivalMass`、`doob_conditionalState` 分别证明有限全成功记录固定该算子、记录概率等于一、正事件条件态固定 \(\rho_\pi\)。`doob_success_probability` 还证明任意归一化对角输入在一次 Doob 成功分支上的概率为一。

Doob 密度自身只需要非负 \(q\)、正 \(h\) 与 \(\sum qh=1\)；只有把原 \(q\) 称为杀死过程的概率 QSD 时才另需 \(\sum q=1\)。这两组归一化在 API 中分开保留。

精确出版粒度：现有命名定理覆盖 Doob 的真实 `true` 分支、有限全成功记录和条件态。没有新增单独命名的 `.channelState` 平稳性定理。也没有证明一般初态的有限后选择等于 Doob 动力学，没有证明无限未来存活条件的极限过程，更没有证明 \(q=\pi\)。

## 6. 具体两态模型与核检查的反例

`TwoState.lean` 使用

\[
Q=\begin{pmatrix}1/4&1/2\\1/8&1/4\end{pmatrix},\quad
q=(1/3,2/3),\quad r=1/2,\quad h=(3/2,3/4).
\]

两行的存活率分别为 \(3/4\)、\(3/8\)，因此不是统一杀死率模型。Lean 逐项检查非负性、行和、\(qQ=rq\)、\(Qh=rh\)、\(\sum q=1\)、\(\sum qh=1\)，随后真正应用正式桥定理，证明任意有限 \(n\) 的量子生存概率为 \(2^{-n}\)，量子条件态为原 \(\operatorname{diag}q\)。

此外精确证明

\[
Q^{\uparrow}=\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix},
\qquad \pi=(1/2,1/2)\ne q,
\]

并证明实际 Doob 记录在 \(\operatorname{diag}\pi\) 上任意有限步概率为一。

| 负控 | Lean 证明的实际结果 | 被排除的误用 |
|---|---|---|
| 均匀初态 \(u=(1/2,1/2)\) | 仪器成功概率 \(9/16\ne1/2\) | 把 QSD 本征率套用所有初态 |
| 把核转置为 \(Q^\mathsf T\) | 以同一 \(q\) 输入的实际成功概率 \(5/8\ne1/2\) | 混用行作用与列作用 |
| 删除失败补全 | 成功 Kraus 的 Gram 和不等于单位矩阵 | 把仅迹递减成功分支称为完整仪器 |
| 把 QSD 与 Doob 平稳律合并 | \(q\ne\operatorname{doobInvariant}(q,h)\) | 忽略右本征函数的再加权 |

这些负控是成功编译的数值不等式证明，不依赖把任意编译失败解释为数学拒绝。实际数值均由 Lean 核检查；没有浮点容差，也没有 `native_decide`。

## 7. 明确开放义务

本轮闭合的是已声明有限对角／测量制备 CP 模型到冻结 Core 有限代数 QSD 层的语义桥。仍开放：一般不可约／本原核的 Perron 数据存在与唯一性；任意初态向 QSD 的吸引、速率与谱隙；无限未来存活条件与 Doob 极限的等价；连续时间生成元和无限维推广；一般相干量子分支的非交换准平稳谱理论；物理装置与数据对该测量基、核、杀死事件的识别。该结果不替代实验校准、G3 谱模板或完整现实 QFT 的独立义务。

## 8. 证据与复现

聚焦编译命令在 `formalization/ueot-qm` 下执行：

```sh
PATH=/tmp/lean-4.33.1-linux/bin:$PATH lake env lean UEOTQM/Survival.lean -o .lake/build/lib/lean/UEOTQM/Survival.olean
```

最终正式源码编译日志为 `build-07.log`，退出码 0，日志为空（没有错误或警告）。所有声明公理审计及具体例的可复现驱动为 `run_focused_checks.py`；该脚本固定正式源码 SHA，记录命令、工作目录、开始／结束 UTC、退出码、输入与日志 SHA、精确审计目标和实际公理集，并在运行后再次验证源身份。

关键文件均位于 `/tmp/qm315_survival/`：

- `declarations.json`：45 个正式声明的完整名称和种类。
- `Audit.lean`、`Audit.compile.log`：45 项真实公理执行。
- `TwoState.lean`、`TwoState.compile.log`：具体数学正反例和 11 个结论的真实公理执行。
- `focused-checks.json`：两个检查均 PASS，精确审计集合唯一完整。
- `run_focused_checks.py`：可复现驱动；只编译两个 scratch 检查文件，不进行全包构建。

下列完整声明清单由冻结源码解析并与实际审计输出对照。

### 8.1 全部 32 个显式定理

- `UEOTQM.Survival.diagonalOperator_posSemidef`
- `UEOTQM.Survival.mass_diagonalOperator`
- `UEOTQM.Survival.diagonalOperator_injective`
- `UEOTQM.Survival.diagonalOperator_smul`
- `UEOTQM.Survival.diagonalDensity_matrix`
- `UEOTQM.Survival.matrixUnit_gram`
- `UEOTQM.Survival.matrixUnit_sandwich`
- `UEOTQM.Survival.measurePrepare_apply`
- `UEOTQM.Survival.measurePrepare_diagonal`
- `UEOTQM.Survival.measurePrepare_gram`
- `UEOTQM.Survival.failureKernel_nonneg`
- `UEOTQM.Survival.outcomeKernel_complete`
- `UEOTQM.Survival.instrument_branch`
- `UEOTQM.Survival.success_branch`
- `UEOTQM.Survival.rowApply_nonneg`
- `UEOTQM.Survival.success_probability`
- `UEOTQM.Survival.success_posterior_matrix`
- `UEOTQM.Survival.killedIterate_posSemidef`
- `UEOTQM.Survival.killedIterate_diagonal`
- `UEOTQM.Survival.survivalMass_eq_response`
- `UEOTQM.Survival.survivalMass_diagonal`
- `UEOTQM.Survival.qsd_killedIterate`
- `UEOTQM.Survival.qsd_survival_pow`
- `UEOTQM.Survival.qsd_survival_pos`
- `UEOTQM.Survival.qsd_conditionalState`
- `UEOTQM.Survival.qsd_rate_le_one`
- `UEOTQM.Survival.doobTransform_nonneg`
- `UEOTQM.Survival.doob_success_branch`
- `UEOTQM.Survival.doob_success_probability`
- `UEOTQM.Survival.doob_killedIterate`
- `UEOTQM.Survival.doob_survivalMass`
- `UEOTQM.Survival.doob_conditionalState`

### 8.2 全部 13 个定义

- `UEOTQM.Survival.diagonalOperator`
- `UEOTQM.Survival.diagonalDensity`
- `UEOTQM.Survival.matrixUnit`
- `UEOTQM.Survival.measurePrepare`
- `UEOTQM.Survival.failureKernel`
- `UEOTQM.Survival.outcomeKernel`
- `UEOTQM.Survival.weightedInstrument`
- `UEOTQM.Survival.instrument`
- `UEOTQM.Survival.killedIterate`
- `UEOTQM.Survival.survivalMass`
- `UEOTQM.Survival.conditionalState`
- `UEOTQM.Survival.doobInstrument`
- `UEOTQM.Survival.doobDensity`

其中返回含证明对象的构造为 `diagonalDensity`、`weightedInstrument`、`instrument`、`conditionalState`、`doobInstrument`、`doobDensity`；其余定义也全部纳入本轮公理审计，没有遗漏委托构造。

### 8.3 实际执行证据身份

| 文件 | SHA-256 |
|---|---|
| `Audit.lean` | `bb2af60b0ea20c78f30577f0309e02c0aaa55f4c116d16f80d3ce0d5572a11da` |
| `Audit.compile.log` | `89c09ea5f0c92aaa257352b885ab6fc9125531a2614417922d450a49442e37ef` |
| `TwoState.lean` | `df78f563964fc081f98ce3c558978b0b479dc73f9fc202cbe34dfc7cc33398ec` |
| `TwoState.compile.log` | `1d9f5d93e2adb60f38b1d864fb796e04f7497f050ebe0578cd8f3d6da7ea4b20` |
| `focused-checks.json` | `1e51d1c778995979b89b6ba81f09d8adbeb548b293a72e96aa713845003ce91c` |
| `declarations.json` | `c594f68164d3214eeda65997df446ccb02cd2f28572958bb5545cc2c40f4fffa` |
