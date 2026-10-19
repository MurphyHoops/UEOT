# UEOT-QM v31.3 / Kernel 1.3

日期：2026-10-19 UTC（北京时间 2026-10-20）。承接 [Kernel 1.2](UEOT_QM_KERNEL_v31.2.md)。本轮把已实现的精确有限表示证书接入 Lean：**有限数值表 → 内核检查 → 真实复数量子仪器 → 全词响应坐标 → 闭合后验与完整有限自适应树。**

当前阶段：**LOCAL_VERIFIED_CI_PENDING**。13 个通用 Lean 模块、196 个显式定理的统一构建已经通过。完整公理清单为 213 项；六个具体生成实例另有 42 个命名审计目标。实例编译、四类数值篡改及同数据的 `check = false` 证明分别记录，不把实例重用计作新的通用定理。详细状态以 [CURRENT.json](status/CURRENT.json)、[本轮台账](status/CLAIM_LEDGER_v31.3.json) 和 [证明回执](kernel/evidence/v31.3/lean-verification.json) 为准。

前一版已完成正常集成：[PR #333](https://github.com/MurphyHoops/UEOT/pull/333) 合入 `c7aa925f338877d7338326f5cee8a165253f69dd`，该主线提交的 [工作流 39294335590](https://github.com/MurphyHoops/UEOT/actions/runs/39294335590) 中 Lean 与 runtime 均成功。新增的 [v31.2 集成回执](kernel/evidence/v31.2/integration-verification.json) 补充旧版本的本地回执，原始证据保持其原有源码身份。

## 1. 本次推进的是哪一层内核

Core 的协议相对对象观在 QM 中落实为：固定允许的操作库后，两态若对所有未来有限记录给出相同响应，就属于同一个响应类。Kernel 1 已证明商上的递归相容；Kernel 1.2 又把响应函数变为有限坐标，证明局部闭包足以覆盖全部未来词。本轮处理这个接口中的实际数值入口。

已有 Python 程序使用 Gaussian-rational 复矩阵、非负有理 Kraus 权重和可变长度的结果／项列表；数学 presentation 使用真实复数和共同有限指标。仅有一份通过 Python 检查的 JSON，尚不能作为 Lean 中该模型的证明。本轮增加独立、可计算的 Lean 检查器，并为导出的具体表产生必须由内核接受的证明。

| 层 | 对象与新增实现 | 本轮解决的接口 |
|---|---|---|
| 加权操作 | `WeightedInstrument` | 非负权重精确转成普通 Kraus 操作；分支、拉回、完整性、概率与后验一致 |
| 可变有限指标 | `RaggedInstrument`、`zeroExtend`、`padOutcomes` | 沿明确嵌入补零，保留原分支；新增结果概率为零 |
| 精确数域 | `Exact.MatrixData` | 两张有理矩阵解释为真实复矩阵，保持复乘法、共轭转置、有限和与实标量乘法 |
| 数值证书 | `ExactCertificate.Data / Conditions / check` | 独立核验五类有限条件，再构造已有数学 presentation |
| 具体证明产品 | `export_lean_representation` 与六份 fixture | 每份数值数据有独立 `checked` 定理和全词／树／闭合更新后果 |
| 重复验收 | `verify_lean_exports.py` | 重新生成、逐字节绑定、实际编译、公理核对、数值篡改与假值见证 |

本轮仍在明确输入的有限复数密度态／Kraus／Born 扇区工作。它没有从 generic Core 自动推出 Hilbert 空间、Born 规则、Planck 常数或现实粒子谱。Core v3 的冻结定义、106 项覆盖与四个计数生成器保持不变。理论来源及其科学端口的解释继承 [五份原件审查](audits/SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md)。

## 2. 有理加权数据如何成为真实量子仪器

程序保存非负有理权重 \(q_{aok}\) 和矩阵 \(M_{aok}\in M_d(\mathbb Q[i])\)。其实际分支为

\[
\Phi_{a,o}(X)=\sum_k q_{aok}M_{aok}XM_{aok}^{\dagger}.
\]

定义普通复 Kraus 矩阵 \(K_{aok}=\sqrt{q_{aok}}\,M_{aok}\)。`Weighted.lean` 从 \(q\ge0\) 证明

\[
KXK^\dagger=q\,MXM^\dagger,\qquad
K^\dagger EK=q\,M^\dagger EM,\qquad
K^\dagger K=q\,M^\dagger M.
\]

因此有理加权完整性

\[
\sum_o\sum_kq_{aok}M_{aok}^\dagger M_{aok}=I
\]

推出普通仪器的 Kraus 完整性。平方根可以不再是有理数，但生成证书无需近似平方根，也不需要在数值文件中输入无理矩阵元。普通仪器的正性、总概率一和正概率后验继续由已有定理提供；转换前后的实际分支与后验矩阵一致。[源码](../../formalization/ueot-qm/UEOTQM/Weighted.lean)

这对未归一化 Hadamard 矩阵尤其直接：保存 \(\begin{pmatrix}1&1\\1&-1\end{pmatrix}\) 和权重 \(1/2\)，精确完整性直接在有理数上检查。`Exact.Examples.hadamard_complete_complex` 将这份精确计算提升成真实复矩阵的完整性等式。

## 3. 可变结果与 Kraus 项数的精确处理

不同动作可以有不同数量的结果，同一动作的不同结果也可以有不同数量的 Kraus 项。`RaggedInstrument` 允许项指标类型依赖结果 \(o\)，再沿每个结果的注入 \(\kappa(o)\hookrightarrow\kappa'\) 扩展到共同有限类型。扩展出的权重和矩阵均为零。

`Ragged.lean` 证明补零保持加权分支、Heisenberg 拉回和 Gram 总和。结果类型也可沿 \(O\hookrightarrow O'\) 补零：原结果概率不变，新增结果的分支与拉回为零、概率为零。零概率分支仍保留在完整结果树中；它们不产生正质量叶，也不构造不存在的正概率后验。

这些是关于任意明确有限嵌入的数学定理。Python 输出的是明确的 `Fin` 数值索引、零权重、零矩阵和零闭包行，每份实例由精确检查器单独验证。声明“这六份数值模型已被检查”与声明“任意 Python 列表的索引转换程序已被形式化证明”具有不同范围，本轮完成前者及相应的通用数学桥。[源码](../../formalization/ueot-qm/UEOTQM/Ragged.lean)、[加权／索引范围审查](audits/WEIGHTED_RAGGED_REVIEW_v31.3.md)

## 4. 检查器的五个条件与可靠性定理

### 4.1 数域解释不是把两个实分量分别相乘

`Exact.MatrixData` 保存实部 \(A\) 和虚部 \(B\)，解释为 \(A+iB\)。乘法实际定义为

\[
(A+iB)(C+iD)=(AC-BD)+i(AD+BC),
\]

共轭转置实际定义为 \(A^T-iB^T\)。解释映射被证明为单射，并保持零、单位、加减、乘法、共轭转置、有理实标量乘法和有限和。特别的虚单位样例同时检查 \(i^2=-1\) 与 \(i^\dagger=-i\)，避免仅在实矩阵上“恰好通过”。[源码](../../formalization/ueot-qm/UEOTQM/Exact.lean)

### 4.2 有限数据中没有全词充分性的字段

`Data d a o k r` 保存权重、原始 Kraus 矩阵、数值基效应、词见证、单位索引及有理分支系数。`Conditions` 检查：

1. 每个权重非负。
2. 每个动作对全部结果和项求和后满足加权完整性。
3. 单位索引的词为空词。
4. 每个数值基矩阵确实等于其词见证的实际精确效应。
5. 每个分支、每个基效应的精确拉回都等于所载系数给出的有限展开。

记词效应 \(E_\varnothing=I\)、\(E_{e::w}=\Phi_e^*(E_w)\)，则后两项为

\[
B_j=E_{w_j},\qquad
\Phi_e^*(B_j)=\sum_i A_{e,ji}B_i.
\]

这里既核验数值基，又核验其生成词。若仅检查某个子空间闭合而不检查真实词生成，不能保证该坐标恰好表达允许协议的响应等价类。系数始终采用“第 \(j\) 行展开第 \(j\) 个被拉回效应”的约定，坐标更新为 \(A_ex\)。

`check D` 计算这些有限条件。`check_sound` 证明 `check D = true` 蕴含实际条件；`weightedInstrument` 通过数域解释构造真实仪器；`exactRecordEffect_toMatrix` 对任意词归纳；`basis_toMatrix` 绑定数值基与词；`presentation` 将局部拉回等式交给已经证明的 `FiniteObservablePresentation`。[源码](../../formalization/ueot-qm/UEOTQM/ExactCertificate.lean)

由此得到统一结论：

\[
\boxed{\operatorname{check}(D)=\mathrm{true}
\quad\Longrightarrow\quad
\bigl(x_D(\rho)=x_D(\sigma)\iff R_D(\rho)=R_D(\sigma)\bigr).}
\]

右侧是对所有有限未来词的响应相等。证书中的有限见证长度不变成未来预测的统一时域上限。对于任意完整有限确定性自适应树，相同坐标也给出相同叶概率律；每棵树的总叶概率为一。

### 4.3 后验更新是已有闭合内核的直接后果

从当前坐标计算 \(y=A_ex\)，以单位坐标 \(p=y_u\) 读出分支概率。若 \(p>0\)，后验坐标为 \(y/p\)，仍属于同一可实现坐标像；若分支概率为零，更新返回 `none`。这继承已有实际 Kraus 后验定理，不要求额外输入“更新兼容”等同于目标结论的前提。

Lean 的 presentation 允许冗余生成元。因此本轮 checker 不需要基独立性。Python 的实 Gram 行列式检查继续提供额外的独立性检验，但本轮没有将该消元／Gram 程序形式化为 Lean 定理。响应维数也不等于更小的物理 Hilbert 维数、驱动数或信息位成本。

## 5. 六个具体实例与严格负控

| 实例 | Hilbert 维数 \(d\) | 响应坐标数 \(r\) | 原分支局部等式数 | 核查重点 |
|---|---:|---:|---:|---|
| Z | 2 | 2 | 4 | 基础射影仪器、迹坐标和真实词生成 |
| H+Z | 2 | 3 | 9 | 有理权重 \(1/2\)、动作间结果数不同 |
| H+S+Z | 2 | 4 | 16 | 非零虚部、共轭符号、不同词顺序 |
| ragged | 2 | 3 | 15 | 三种动作、不同 Kraus 项数、显式不可能结果与补零 |
| d1 | 1 | 1 | 2 | 单复数 \(1+i\) 与权重 \(1/2\)、原有零结果 |
| d4 | 4 | 2 | 4 | 四维粗粒化射影，不预设响应维数等于 \(d^2\) |

“原分支局部等式数”不包含为了统一结果指标新加的零行；Lean 实际检查完整补零表。所有原标签保存在 companion manifest，Lean 标识符只来自证书 SHA256；词索引用显式有界构造，超界不能通过模运算悄悄折回合法索引。[六份完整输入](kernel/certificates/v31.3/exports.json)

每个实例包含一个必须由 Lean 核验的 `checked` 定理，以及全词响应 iff、有限树坐标、叶律一致、总概率一和闭合更新接口。生成源的 `decide +kernel` 使用内核计算有限有理条件；它的真实公理依赖另由 `#print axioms` 检查。生成器本身不会把源文件导出标记成编译成功：manifest 保留 `LEAN_SOURCE_EXPORTED_NOT_COMPILED`，独立编译回执通过源码哈希记录之后发生的实际验收。

负控在导出之后篡改四类数据：权重／完整性、数值基、局部系数、词顺序。每类均要求原 `checked : check data = true` 失败，而且保留相同数值定义的伴随文件必须成功证明 `check data = false`。第二个门排除将编译器缺失、导入错误、资源不足或单纯展开失败误报为“数学拒绝”。具体日志、真／假源身份及公理输出见 [实例验收回执](kernel/evidence/v31.3/lean-exports/verification.json)。

## 6. 实际验收与复现

本轮验证分为通用数学和具体实例两层。通用包统一构建为 13 模块、196 个显式定理；命名公理清单覆盖这些定理及 17 个列举的证明构造，共 213 项。六个实例另外核查 42 项声明，四个假值见证各核查其 `rejected` 声明。允许基础仅为 `propext`、`Classical.choice`、`Quot.sound`，不宣称无基础公理，也不将命名清单冒充编译器所有内部常量的普查。

运行测试共 87 个方法：原有 32 项操作／协议／误差、18 项表示证书、22 项谱桥，以及本轮新增 15 项导出／索引／格式／绑定检验。方法数量可以包含多个案例，不作为 Lean 定理数量。`demo.py`、`demo_v312.py` 与 `demo_v313.py` 继续分别保存已有内核、表示／谱以及新证书入口。

从仓库根目录运行：

```bash
python physics/qm/kernel/verify_kernel.py --output /tmp/qm-runtime.json
python physics/qm/kernel/demo_v313.py --output-dir /tmp/qm-exports
```

在 `formalization/ueot-qm` 中使用锁定的 Lean 4.33.1：

```bash
python3 scripts/check_dependencies.py
lake build UEOTQM
lake env lean scripts/AxiomAudit.lean > axiom-audit.log
python3 scripts/check_axioms.py
python3 ../../physics/qm/kernel/verify_lean_exports.py --output-dir /tmp/qm-lean-exports
```

新验证器重新生成六个实例，先与提交的完整源码和 manifest 逐字节比较，再执行正负编译与公理检查。CI 使用相同入口。源码 manifest 同时记录数学模块、运行程序、脚本、固定证书和工作流；本地 checkout 元数据与实际被测文件的 SHA256 分开记录。

## 7. 三代结论与整个 QM 的下一步

本轮没有添加新的三代选择前提，也没有改写已证明的 selector。已有谱桥从明确家族条目、非零异常单位、同质轻子模板、额外有符号立方贡献抵消、完整普通行活跃的有效弱窗口等条件，导出异常方程和严格弱预算，再得到 \((N_c,N_f,k)=(3,3,1)\)。这是条件下的严格选择结论。实际表示系数、完整母谱、补偿贡献、窗口匹配、全局异常、真空与质量仍属于物理适用性义务；六个局域异常数值为零本身不唯一选出三代。旧的 \(\beta_1=3\to\operatorname{Index}(D)=3\to\text{generations}\) 路线继续退役。[谱桥及反例](audits/SPECTRUM_BRIDGE_v31.2.md)

| 下一工作 | 具体入口 | 关闭标准 |
|---|---|---|
| QMU-04 真实误差合同 | 明确可观测算子 seminorm 或 trace distance，再接已有 M-TC | 证明量子一步收缩／缺陷；后选择单列概率下界；得到协议类内的统一误差定理 |
| QMB-05 长期行为 | 有限 CPTP 的 Cesàro 平均 | 残差界与平稳极限点；唯一性和混合率另证 |
| QMB-06 存活桥 | 对角 CP 存活操作 | 从实际矩阵得到 substochastic 转移，再调用既有 Core 存活结论 |
| 算法细化 | \(W_n\) 闭包搜索、Hermitian \(d^2\) 维数、消元 | 通用终止／正确性定理；保持本轮逐实例证书入口可先独立使用 |
| QDRR 数据入口 | 冻结准备、协议、噪声基线和零假设 | 原始记录、注入控制、统计检验与可失败的部署范围 |
| G3/HGP | 指定表示与完整谱及物理窗口 | 实际表示／阈值匹配、全局一致性、真空／质量和可观测关系 |
| CV 与 QFT/RG | 能量控制的有界响应、单一正规化模型 | 定义域、尾部／截断误差与两侧独立的协议运输证据 |

因此，有限量子操作内核已具有可以交给独立检查者的数值证明入口。后续优先把实际量子误差合同接入现有组合定理，同时推进长期／存活与物理谱义务；不以重复扩张版本号代替这些可验证的下一步。[完整路线图](ROADMAP.md)

## 8. 审查与证据边界

[精确证书语义与交叉审查](audits/EXACT_CERTIFICATE_REVIEW_v31.3.md) 核对复乘法、非循环条件、数值基绑定、词顺序和 exporter 语义；[加权／索引审查](audits/WEIGHTED_RAGGED_REVIEW_v31.3.md) 核对平方根解释、不同有限指标与零概率；[领域验收说明](audits/KERNEL_REVIEW_v31.3.md) 将代码、运行、回执与范围对齐。

本轮证明的是通用检查器的数学可靠性以及六份被实际内核接受的数据实例。它没有统一证明 Python、JSON parser、搜索器、消元器或树解释程序；没有新增实验确认；没有关闭全部 C1–C7 科学端口；没有将精确模型的证明自动推广到现实含噪系统。所有后续结论继续依赖所声明的操作库、准备、协议、资源和物理输入。
