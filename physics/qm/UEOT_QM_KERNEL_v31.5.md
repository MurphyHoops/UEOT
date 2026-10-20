# UEOT-QM v31.5 / Kernel 1.5

日期：2026-10-20。研发基线：97d033ff83125822e9926f5bd36afd08dbd153ef。当前本地验收 PASS；远端验收状态以 [CURRENT](status/CURRENT.json) 和本版集成回执为准。

## 1. 本轮完成的科学任务

UEOT-QM 的目标是建立有明确假设、严格数学、可运行实现和可否证物理内容的完整量子理论。本版在已有的响应对象、有限全词坐标、精确证书和全效应稳定性之上，完成三项可以直接组合的有限数学扩展：可计算的同库随机化误差预算、实际 CPTP 通道的 Cesàro 平稳态存在、对角量子分支到 Core 条件存活及 Doob 变换的真实桥接。

这三项结论使用实际复矩阵、正半定态和 Kraus 操作；没有把所需结论放进抽象结构的字段。量子扇区的复数域、Born 概率解释、允许操作以及自然界模型适用性仍是明确的输入责任。Core 本身尚未无条件唯一选择复量子理论。

完整推导已进入 [《UEOT物理学》正式 3.1](book/UEOT_PHYSICS.md) 第 51–53 章；第 0–50 章及附录 A–F 连续保留并更新接口。阅读版为 [完整 PDF](book/UEOT_PHYSICS.pdf)，共 171 页；54 章、253 个编号节、101 个编号结果。正式著作的完整性指内容与维护责任完整，不表示所有物理开放问题已解决。

## 2. Mixture：从数学上确界到有限有理预算

设同一有限载体上有完整 Kraus 通道族 \(\Phi_b\)，概率权重满足 \(p_b,q_b\ge0\) 且各自求和为 1。实际混合由新的 Kraus 指标 \((b,k)\) 与矩阵 \(\sqrt{p_b}K_{b,k}\) 构造，因此

\[
\Phi_p(X)=\sum_b p_b\Phi_b(X)
\]

是已证明完整的通道，不是只有名字的凸组合。混合态、选择分支、Heisenberg 拉回、完整通道和归一输出均有实际矩阵恒等式。

沿用全部效应 \(0\preceq E\preceq I\) 定义的响应伪距离及全态通道缺陷

\[
d_{\rm eff}(\rho,\sigma)=\sup_E|P_E(\rho)-P_E(\sigma)|,\qquad
\delta(\Phi,\Psi)=\sup_\rho d_{\rm eff}(\Phi(\rho),\Psi(\rho)).
\]

本版证明

\[
\delta(\Phi_p,\Phi_q)\le
\operatorname{TV}(p,q)=\frac12\sum_b|p_b-q_b|.
\]

关键的一半系数来自两个权重的归一条件。对任意态和效应，令 \(f_b=P_E(\Phi_b(\rho))\in[0,1]\)，使用

\[
\sum_b(p_b-q_b)f_b
=\sum_b(p_b-q_b)(f_b-\tfrac12)
\]

即可把每项控制在 \(|p_b-q_b|/2\)。这是覆盖全部态与全部效应的上界；有限抽样最大值没有代替上确界。

对两个通道族 \(\Phi_b,\Psi_b\)，进一步证明

\[
\delta(\Phi_p,\Psi_q)
\le \operatorname{TV}(p,q)+\sum_bq_b\,\delta(\Phi_b,\Psi_b).
\]

共同的数学载体必需；两侧允许不同结果及 Kraus 指标类型。实际可执行的精确有理接口本轮实现同库权重预算，绑定具体成员库、精确权重与表示指纹。通用联合不等式已经证明；任意成员误差的自动求界程序未由此获得。

例如，恒等与 bit-flip 的混合，从 \(p=(1/2,1/2)\) 改为 \(q=(3/4,1/4)\)，对输入 \(|0\rangle\langle0|\) 和效应 \(|0\rangle\langle0|\) 达到 \(1/4\)，恰好等于 TV。两个成员均为同一通道时，改变权重可能给非零预算而实际缺陷为零，因此预算不总是精确缺陷。若两边换了成员库，即使权重完全相同，也不能使用同库 TV 界。

本版有理比较定理把 Lean 的有理权重解释到实权重，并证明 TV 的解释恒等式。运行程序计算同一个有理表达式，但 Python、JSON 或整个 exporter 的全输入细化没有被宣称完成。该接口可以为既有 Core M-TC 轨迹误差递推提供每一步的可靠数学预算。[Mixture 源码](../../formalization/ueot-qm/UEOTQM/Mixture.lean)

## 3. Cesàro：平均残差、实际紧性和平稳态

对固定完整通道 \(\Phi\) 和初态 \(\rho_0\)，定义 \(\rho_n=\Phi^n(\rho_0)\)。仅当 \(N>0\) 时定义平均态

\[
\bar\rho_N=\frac1N\sum_{j=0}^{N-1}\rho_j.
\]

本版先构造实际的 PSD、迹一平均态，再证明矩阵望远镜恒等式

\[
\Phi(\bar\rho_N)-\bar\rho_N=\frac{\rho_N-\rho_0}{N}.
\]

因此全部效应响应均满足

\[
d_{\rm eff}(\Phi(\bar\rho_N),\bar\rho_N)\le\frac1N.
\]

平稳存在部分没有把紧性作为无证明的字段。证明使用实际有限复矩阵的原有拓扑：PSD 集闭、迹一集闭、密度矩阵算子范数至多 1，故密度集合紧；线性通道连续。矩阵残差的算子范数至多 \(2/N\)，随 \(N\) 趋于无穷而消失。任意收敛的严格 Cesàro 子序列的极限均为密度态且满足 \(\Phi(\rho_*)=\rho_*\)。从紧性得到这样的子序列；在载体非空时，用归一单位阵提供初态，得到平稳密度态存在。

实际 Lean 使用 Mathlib 的矩阵 L2 算子范数结构，同时保留原来的矩阵拓扑与一致结构。这里的“平均后出现不变对象”与 UEOT 的长期对象研究方向相接；本模块没有直接调用一个 Core M-OI 或 P-PER 定理来完成上述矩阵紧性证明，不将类比记为 theorem composition。

bit-flip 的逐时轨道在两个正交纯态之间周期跳动，而平均态趋向 \(I/2\)；恒等通道的每个密度态都是不变态。这两项见证划清平稳态存在、唯一性、逐时 mixing 和路径经验平均之间的区别。当前 Lean 未登记整个 Cesàro 序列收敛、唯一平稳态、谱隙速度或每条量子测量轨迹的遍历定理。标准有限维平均遍历理论尚未迁入 Lean 的部分属于开发义务，不能因此标为未证的 UEOT 物理猜想。[Cesaro 源码](../../formalization/ueot-qm/UEOTQM/Cesaro.lean)

## 4. Survival：真实量子分支中的 Core 条件存活

约定 \(p\) 为行分布，\(Q_{ij}\ge0\)，每行和不超过 1。构造成功 Kraus 矩阵

\[
K_{ij}=\sqrt{Q_{ij}}\,|j\rangle\langle i|,
\]

并加入损失 Kraus 矩阵

\[
L_i=\sqrt{1-\sum_jQ_{ij}}\,|i\rangle\langle i|.
\]

成功与失败两类结果一起构成完整量子仪器。失败分支的定义保留被测源态；它不等于一个新增吸收墓地态。寿命协议在首次失败后停止计数。忽略失败项会把迹不增的成功分支错误当成完整通道。

对于任意矩阵，成功分支仅依赖输入对角元。对角态满足

\[
\mathcal S_Q(\operatorname{diag}p)=\operatorname{diag}(pQ),\qquad
\mathcal S_Q^n(\operatorname{diag}p)=\operatorname{diag}(pQ^n).
\]

第二式在 Lean 中直接对应真实仪器的连续成功有限记录。它的质量就是该记录的实际 Born 概率；正概率时才构造后验。

若给定合法左特征数据 \(q\ge0\)、\(\sum_iq_i=1\)、\(qQ=rq\)、\(r>0\)，本模块实际调用 Core 的 QSD/Perron 定理，得到

\[
\Pr_q(\text{前 }n\text{ 次成功})=r^n,\qquad
\rho_{\text{给定成功 }n\text{ 次}}=\operatorname{diag}q,\qquad r\le1.
\]

这些谱关系是明确前提；本版没有一般性证明它们总存在，也没有无条件把 \(r\) 识别成给定模型的主谱半径。

进一步给定 \(h_i>0\)、\(Qh=rh\)、\(\sum_iq_ih_i=1\)，构造

\[
\widetilde Q_{ij}=\frac{Q_{ij}h_j}{rh_i},\qquad \pi_i=q_ih_i.
\]

实际 Core 定理提供行归一、\(\pi\) 的归一及平稳性；量子桥构造对应完整仪器，并证明 \(\operatorname{diag}\pi\) 的成功分支、连续成功记录、概率 1 和正后验不变。没有把尚未另行登记的完整 channelState 等式或无限条件过程收敛定理列入证明清单。

精确二态例子为

\[
Q=\begin{pmatrix}1/4&1/2\\1/8&1/4\end{pmatrix},\quad
q=(1/3,2/3),\quad r=1/2,\quad h=(3/2,3/4).
\]

Doob 核两行均为 \((1/2,1/2)\)，其平稳律 \(\pi=(1/2,1/2)\) 与 QSD 的 \(q\) 不同。任意 \(n\) 的实际成功记录概率 \(2^{-n}\) 已有具体 Lean 见证。若换成均匀初态，第一步生存率为 \(9/16\)；若误用转置方向，对 \(q\) 算得 \(5/8\)。两者都揭示了不能删除的前提。

首次失败时间允许取无穷；在 \(r<1\) 的指定协议中，几何尾和给出期望寿命 \(1/(1-r)\)。这是正文的解析推导，当前未单列为 Lean 寿命随机变量定理。给定有限成功条件的 QSD、Doob 的 \(qh\) 不变律、无限时域条件极限是三个需要分别证明的对象。[Survival 源码](../../formalization/ueot-qm/UEOTQM/Survival.lean)

## 5. 已实际完成的验证

| 验收对象 | 本版实际结果 | 证据 |
|---|---:|---|
| 通用 Lean | 18 模块，334 显式定理；完整构建 8739 jobs，退出 0 | [统一证明回执](kernel/evidence/v31.5/lean-verification.json) |
| 命名公理 | 392 项 = 334 定理 + 58 个列入审计的定义／构造；新增 78 + 27 = 105 项 | [完整审计](kernel/evidence/v31.5/proof-axioms.json) |
| 运行内核 | 100 方法；4 演示 | [运行](kernel/evidence/v31.5/runtime-verification.json)、[演示](kernel/evidence/v31.5/demos-verification.json) |
| 既有精确导出 | 6 个实例、42 独立审计；4 种篡改真值证明被拒绝，4 个同数据假值证明通过 | [实际重验](kernel/evidence/v31.5/lean-exports/verification.json) |
| 新具体见证 | 29 定理、10 定义、39 独立审计；32 通用模块源与编译对象前后相同 | [见证门](kernel/evidence/v31.5/finite-witnesses/verification.json) |
| 来源与依赖 | 64 项最终源；9 个依赖修订吻合；13 个 Core 递归依赖源未改 | [源清单](kernel/evidence/v31.5/source-manifest.json)、[冻结协调](kernel/evidence/v31.5/source-freeze-reconciliation.json) |
| 总著出版 | 54 章，6 附录，101 编号结果，171 页；实际视觉检查 PASS | [结构](book/evidence/v3.1/book-structure.json)、[视觉](book/evidence/v3.1/pdf-visual-review.json) |

允许的 Lean 基础仅为 propext、Classical.choice、Quot.sound。具体数值见证、公理目标和 Python 测试数分别统计，不相互相加制造“证明数”。新模块的 focused 编译、完整构建、作者语义审查、不同子智能体交叉检查和总著审阅分别保留原始记录。[数学与实现审查](audits/FINITE_DYNAMICS_REVIEW_v31.5.md)

原 3.0 三个书内数值程序的 757 项历史检查所对应源码未改变。本版确认这些原始字节，保留原执行时间与身份，没有重跑后重标日期，也没有把历史数值检查转移成新版正文的全称证明。[继承核对](book/evidence/v3.1/legacy-source-reuse.json)

## 6. 核心目标下的下一轮合理任务

本版把已经具备输入、能够闭合的三条数学桥推进完成。下一轮最应优先研究的根本问题是量子选择：哪些独立可辩护的 UEOT 领域原则能够排除经典和实量子反模型，选择复量子复合、概率和演化结构？先明确反模型与缺失前提，再提出独立可检验的候选原则。

与该根本问题并行，工程上优先建立保留经典记录与量子记忆的联合通道，把新的可认证混合预算接入真正含记录的协议稳定性。长期结构则继续非交换 CP 的明确左右谱数据、条件化与吸引条件；平稳存在、全平均收敛、唯一性和 mixing 逐项验收。QDRR 必须固定可失败的协议、噪声与统计合同，并获得真实原始记录；G3 仍需完整表示／母谱、有效窗口、全局异常、真空和质量。

后续任务、资源分配、交付及停止条件详见 [路线图](ROADMAP.md)；本轮实际执行合同见 [推进任务](UEOT_QM_EXECUTION_v31.5.md)。冻结 Core 的 106 项覆盖和四个计数生成器不因 QM 新增证明而改变。
