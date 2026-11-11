# 原有限仪器树的条件记录实现：奇异支撑、零事件与成本边界

状态：本文件是完整书面证明与 Lean 实现的语义说明。主代理已反馈 `QuantumFiniteWindow.lean` 的完整 CQ 版与 `QuantumFiniteWindowSpectral.lean` 的规范谱工厂分别在 Mac 完成 Lean 构建；随后追加的源概率权重、效应上界和默认源仪器包装等待本轮最终构建。本文区分已核定理、最近新增连接和纸面物理解释。以下数学证明不限制后向效应正定，允许秩亏和零支撑。

## 1. 原始输入与所研究的事件

固定有限维复 Hilbert 空间 `H`、原始有限可见结果集 `O` 和有限隐藏 Kraus 指标集。给定一棵有限因果操作树。内部节点 `h` 已由过去可见结果决定，它使用原始完整仪器

\[
\mathcal I_{h,o}(X)=\sum_\mu K_{h,o,\mu}XK_{h,o,\mu}^{\dagger},
\qquad
\sum_{o,\mu}K_{h,o,\mu}^{\dagger}K_{h,o,\mu}=I.
\]

节点允许不同原仪器，因此包含已冻结的历史依赖反馈；节点结果数或 Kraus 数不同时，可用有限并集及零 Kraus 填充统一载体。这种表示适配不是本次 Lean 模块中的自动转换功能。`o` 是真正可见标签，`mu` 始终在分支内部求和，不得被临时提升为实验读出。

每个终止叶 `l` 有冻结的接受标记 `a_l∈{0,1}`。叶的原实际分支映射是按时间顺序复合原仪器。记

\[
X_l(\rho)=\mathcal I_{l}(\rho).
\]

其完整接受输出为未归一 CQ 算符

\[
\Omega_A(\rho)=\sum_l |l\rangle\langle l|\otimes a_lX_l(\rho),
\qquad
p_A(\rho)=\operatorname{Tr}\Omega_A(\rho).
\]

叶标签保留完整原可见历史和原停止位置。它不是只保留最后一个结果或最后的系统边缘。本任务的条件目标在 `p_A>0` 时是 `Omega_A/p_A`；在 `p_A=0` 时不定义条件密度态。

## 2. 后向效应及其原来源

从叶向根递推

\[
H_l=a_lI,
\qquad
H_h=\sum_{o,\mu}K_{h,o,\mu}^{\dagger}H_{ho}K_{h,o,\mu}.
\tag{1}
\]

有限树归纳给 `0≤H_h≤I`：叶显然；若各子效应在 `[0,I]` 中，每项共轭保持 Loewner 次序，求和得到

\[
0\le H_h\le\sum_{o,\mu}K_{h,o,\mu}^{\dagger}K_{h,o,\mu}=I.
\]

对节点后的任意原输入正算符 `X`，其所有后续接受叶总质量正好是 `Tr(H_h X)`。证明在叶成立；内部节点应用迹循环，交换有限和，再使用子树归纳。这一步确定了 `H_h` 的真正事件来源，不能把另一个类似效应直接代入。根处尤其有

\[
p_A(\rho)=\operatorname{Tr}(H_{\varnothing}\rho).
\tag{2}
\]

对于时间齐次仪器、固定长度 `T`、每一步只要求结果属于某成功集合 `S` 的特殊情形，式(1)化为

\[
H_t=(\Phi_S^*)^{T-t}(I).
\]

有自适应动作、不同停止叶或非乘积接受事件时，必须使用树递推(1)，不能继续套单一映射的幂。

## 3. 奇异支撑适配

令 `P_h` 为 `H_h` 的支撑正交投影；`S_h=H_h^{1/2}`；`T_h=H_h^{+1/2}` 为只在正谱上取倒数平方根、零谱上为零的 Moore–Penrose 支撑逆。有限谱定理给

\[
T_hS_h=S_hT_h=P_h,\quad P_h^{\dagger}=P_h,
\quad P_h^2=P_h,\quad P_hS_h=S_h,
\quad S_h^{\dagger}S_h=H_h.
\tag{3}
\]

`H_h=0` 时三者都为零。接受叶用 `S=T=P=I`，拒绝叶用 `S=T=P=0`。

关键支撑引理必须从后向递推推出。记 `A_{o,mu}=S_{ho}K_{h,o,mu}`，则

\[
H_h=\sum_{o,\mu} A_{o,\mu}^{\dagger}A_{o,\mu}.
\]

若 `v∈ker H_h`，则

\[
0=\langle v,H_hv\rangle=\sum_{o,\mu}\|A_{o,\mu}v\|^2.
\]

有限个非负实数之和为零，所以每项均为零。因此各 `A` 在 `ker H_h` 上消失，即

\[
S_{ho}K_{h,o,\mu}P_h=S_{ho}K_{h,o,\mu}.
\tag{4}
\]

这证明奇异支撑不会破坏望远镜关系。Lean 候选把(3)、后向 Gram 等式及(4)作为精确局部矩阵证书，最终记录等式不在证书输入中。配套规范谱适配器证明了这些证书的全称存在性，并由原后向 Gram 式独立推出(4)。因此调用规范源树构造时，使用者不需再提交核消去前提；局部证书接口仍可用于精确矩阵实例。机器证明范围以实际编译成功的声明为准。

## 4. 完整变换仪器与任意补集行动

在每个节点任选一个具有相同可见结果标签 `O` 的完整 fallback 仪器 `J_{h,o,nu}`，其隐藏 Kraus 指标可以与原仪器不同。定义两组隐藏 Kraus：

\[
\widetilde K_{h,o,\mu}=S_{ho}K_{h,o,\mu}T_h,
\qquad
R_{h,o,\nu}=J_{h,o,\nu}(I-P_h).
\tag{5}
\]

两组共用原可见结果 `o`，不增加对使用者可见的“主路／fallback”标签。其 Gram 和为

\[
\sum_{o,\mu}\widetilde K^\dagger\widetilde K
=T_h^{\dagger}H_hT_h=P_h,
\]

\[
\sum_{o,\nu}R^\dagger R
=(I-P_h)\left(\sum_{o,\nu}J^\dagger J\right)(I-P_h)=I-P_h.
\]

总和恰为 `I`，所以(5)在全载体上构成真正完整仪器。单独省略 fallback 得到的只是在支撑上的保迹图，不能声称是全载体 CPTP 仪器。

## 5. 实际分支的过滤运输

对任意复矩阵 `X`，不要求 Hermitian 或正性，由(3)、(4)得到

\[
\widetilde K_{h,o,\mu}S_h
=S_{ho}K_{h,o,\mu}T_hS_h
=S_{ho}K_{h,o,\mu}P_h
=S_{ho}K_{h,o,\mu}.
\]

而 `R_{h,o,nu}S_h=0`。逐隐藏 Kraus 求和，得到实际分支恒等式

\[
\widetilde{\mathcal I}_{h,o}(S_hXS_h^{\dagger})
=S_{ho}\mathcal I_{h,o}(X)S_{ho}^{\dagger}.
\tag{6}
\]

它是从原实际矩阵证明的等式，而不是定义“理想变换通道”后把等式放进结构字段。fallback 对所有实际可达过滤输入为零，包含途中遇到零效应子树的情形。

## 6. 任意有限树的完整条件 CQ 定理

对每个根到叶原可见历史，反复应用(6)，得到

\[
\widetilde{\mathcal I}_{l}(S_{\varnothing}XS_{\varnothing}^{\dagger})
=S_l\mathcal I_l(X)S_l^{\dagger}
=a_l\mathcal I_l(X).
\tag{7}
\]

这是有限树上的归纳，不要求树固定深度，也不要求每个 `H_h` 可逆。各内部节点用的是其真实完整变换仪器，叶之间不作新的后选择。

若 `p_A(ρ)>0`，定义

\[
\widetilde\rho_0=
\frac{S_{\varnothing}\rho S_{\varnothing}^{\dagger}}{p_A(\rho)}.
\tag{8}
\]

分子 PSD，迹由(2)等于正分母，故是合法密度态。变换分支是线性的，从(7)得到每个叶的精确量子块

\[
\widetilde{\mathcal I}_l(\widetilde\rho_0)
=\frac{a_l\mathcal I_l(\rho)}{p_A(\rho)}.
\tag{9}
\]

把所有真实叶作为正交经典寄存器标签，得到

\[
\boxed{\widetilde\Omega(\widetilde\rho_0)
=\Omega_A(\rho)/p_A(\rho).}
\tag{10}
\]

式(10)同时保持完整原可见记录、原停止位置、最终系统量子态以及二者相关性。它不只保持某个迹或最终边缘。接受叶末端 `S_l=I`，所以末态不需要额外逆过滤；拒绝叶输出块严格为零。

对任意两个完整 fallback 选择，右侧相同，所以完整条件 CQ 输出相同。这个无关性只针对精确可达支撑输入。若近似初始化或实际噪声将质量泄漏到补集，不同fallback会产生不同记录和后继态；极端补集输入可有TV为1的反例。近似实现不能直接删除这一部分责任，应计入初始化／动作误差预算。

## 7. 零事件与未获授权的中途干预

若 `p_A=0`，PSD 分子 `SρS†` 的迹为零，故该分子是零。原接受叶各为 PSD，且总迹为零，因此每个接受块都为零。不存在“除以零以后任选一个态”的经验解释；程序与定理入口应返回事件不可能或拒绝构造。

对一个中间前缀 `h`，原未归一前缀态记作 `X_h(ρ)`。变换前缀块为

\[
S_hX_h(\rho)S_h^{\dagger}/p_A(\rho),
\]

其迹为 `Tr(H_h X_h)/p_A`。这是被未来接受事件加权后的前缀概率，不是原过程仅存活到该时刻的普通后验态。改变未来控制器、插入额外测量或改变接受事件会改变后向 `H_h`；式(10)不能被提升为保留任意未冻结干预的一次通用因果实现。

## 8. 初始化与成本：可实现上界不等于普遍最优性

式(8)首先是数学状态。由于 `0≤H0≤I`，`S0` 本身是合法单 Kraus 筛选操作，成功率为 `p_A`。更一般地选 `c≥||H0||` 且 `c>0`，用

\[
A=S_0/\sqrt c
\]

完成合法 heralded 筛选，成功率为 `p_A/c`，成功态仍为(8)。在这类同一单 Kraus 实现中，最小 `c=||H0||` 给最大成功率。该结论不表示它在所有允许制备、输入先验或其它通道实现中都成本最优。

必须区分至少三类任务：原输入只有未知单份；原输入来自已知可重复制备族；目标只是生成指定条件输出而无需保留原输入的成功标志。不同任务的初始化和信息成本不同。

反例边界如下。

1. `H0=cI` 时，归一过滤为恒等，能确定性初始化。
2. `H0` 为非零秩一效应时，对所有 `p_A>0` 的系统输入，归一过滤的系统态都是同一个纯态；若任务只要求本章显式系统与记录的输出，可用 replacement 通道确定性制备。故“非标量就一定需要概率筛选”不成立。若要求同时保留任意纠缠外部参考在筛选后的相关，replacement通常失败：真实筛选会改变参考的条件边缘，确定性局部replacement不会。不能把系统边缘的等式升级成这种更强的资源结论。
3. 正定 `H0` 若有两个不同正特征值，归一过滤通常非线性：两本征纯态分别保持，等权混合却变成按特征值重新加权。单一确定性 CPTP 图不能对所有密度输入实现该非线性作用。
4. 秩亏高秩情况还须按输入允许域分别判定，不能将完整载体的不可实现结论直接移到受限已知输入族。

拒绝采样的独立重试基线成本应为 `E[一次尝试实际成本]/p_A`；一次尝试成本包含失败早停，不能机械替成固定 `T`。变换方案计入输入准备／筛选失败、实际动作、辅助系统、复位与数值证书成本。数学同分布不保证资源优势。

## 9. 允许动作必须保留结果标签

每个变换节点的目标是带原标签的仪器通道

\[
\mathcal J_h(\rho)=\sum_o|o\rangle\langle o|\otimes
\widetilde{\mathcal I}_{h,o}(\rho).
\]

允许动作库的精确凸混合实现应匹配该 flagged Choi 矩阵。只匹配丢弃标签后的系统通道，不能保证式(10)：交换可见标签即可保持未标记通道但使记录分布不同，极端时 TV 为1。

如仅有近似实现，需给同一联合输出距离下的动作缺陷和初始化缺陷，再使用已有共同控制器／有限停止预算运输到终端。奇异支撑附近的伪逆和平方根求解必须有特征值间隙或固定支撑证明；本章的精确代数恒等式本身不提供浮点稳定性。

## 10. 与现有源码的准确关系

本次不是重新证明第56章的固定左特征度量齐次 Doob，也不是重跑第59章指定模型，或重复第65章停止树预算。本章使用原来源有限接受事件构造随节点变化的过滤，保留真实多结果记录，并处理奇异支撑、补集完成和初始化成本。

Lean 候选关键声明：

- `SupportFilter`：允许奇异与零支撑的局部因子；
- `StepCertificate`：原后向Gram和与局部核关系；
- `tiltedInstrument`：完整带标签实际仪器；
- `tilted_branch_transport`：实际Kraus求和上的全算符运输；
- `FilterTree.sourceLeafOperator_eq_recordOperator`：接回原记录解释器；
- `FilterTree.leaf_transport`：任意有限树逐叶望远镜；
- `FilterTree.successMass_eq_filtered_mass`：原接受记录总质量；
- `FilterTree.metric_complement_posSemidef`：从源 completeness 和局部后向式推出真正效应界 `H≤I`；
- `FilterTree.sourceWeights` 与 `sourceWeights_accepted_sum`：由原叶块迹构造完整概率权重，接受和严格等于相同 `successMass`；
- `FilterTree.conditional_joint`：完整条件CQ密度矩阵；
- `FilterTree.fallback_independent`：补集选择无关；
- `FilterTree.zero_success_all_accepted_blocks_zero`：零事件真实拒绝。

配套模块 `QuantumFiniteWindowSpectral.lean` 提供 `spectralFilter`、`spectralFilter_metric`、`support_of_backward`、`SourceTree.canonical`、`SourceTree.canonical_valid` 与 `canonical_erases_to_source`；主代理已反馈这一版构建成功。新增的 `source_node_conditional_joint` 对含内部节点的原源树直接取其根原仪器为固定 fallback，将谱构造、原来源和完整条件 CQ 定理连成无额外谱证书的公共端点。

正式接口使用统一的有限系统载体、可见结果类型和隐藏 Kraus 类型，并让任意完整 fallback 仪器 `J` 在整棵树固定。上文逐节点选择 `J_h` 的书面推广使用同一局部恒等式，但未单独建立节点依赖 fallback 的 Lean 解释器。任何有内部节点的源树可用根原仪器作固定 fallback，因而无需假设另一物理仪器存在；只有接受停止叶的树是恒等情形，只有拒绝停止叶的树不满足正成功概率。主模块给局部证书到输出的定理，谱扩展进一步给任意原有限源树的非可计算规范构造。两者都不提供浮点谱算法，不覆盖任意外部干预、无界树或真实硬件实验，不得由本章计数或模拟成功替代这些证据。
