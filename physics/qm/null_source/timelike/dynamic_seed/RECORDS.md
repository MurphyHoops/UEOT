# 完整动态记录、ensemble 一致性与时钟

## 1. 动态 O(2) 等价定理

令 Q(rho)=int U_R rho U_R^* dR 为内部 O(2) Haar 平均。输入 rho 必须包括实际物质、引力、设备、记忆和参考系统，可以直接使用物理约束代数；不假定引力物理 Hilbert 空间可以任意拆成 matter tensor gravity。

前驱明确构造的 old/new CQ 准备具有相同径向 R 律、同一中心化 O(2) 对称参考态、相同 thermal 壳及与对称交换的 K0/K1，因此相应联合 twirl 相同。完整相干制备自身不必 O(2) 不变。若另加初始 source–gravity 或 source–device 关联，必须重新检查完整联合 twirl；仅边缘相同不足。

设每步完整仪器 I_{y|h} 是线性 CP、迹不增，求和迹保持。所有 y 包含成功、失败、停止和实际保留设备结果；标签在 O(2) 下不变。要求每个结果映射分别协变，old/new 使用同一由既往公共记录决定的控制策略。

对完整记录词 w，协变复合仍满足 Q_out I_w=I_w Q_in，故

\[
p_{\rm old}(w)
={\rm Tr}\,I_w(Q\rho_{\rm old})
={\rm Tr}\,I_w(Q\rho_{\rm new})
=p_{\rm new}(w).
\]

对正概率条件支，归一化后两态的输出 twirl 也相同。归纳覆盖任意轮次、条件筛选及停止规则。全部有限 cylinder 记录一致时，存在的共同无限记录测度亦一致。若保留输出系统上的群作用平凡，则完整 CQ 输出状态也相同。

因此总记录 TV=0，等先验最优识别率=1/2。定理允许非 Gaussian、动态记忆和纠缠；其实际引力解释还要求共同通道因果、保持物理约束、包含设备相互作用的完整应力。这里没有构造这样的引力通道。

[records.py](records.py) 的三记录 adaptive 矩阵例给概率 41/108、17/72、83/216，并保留各条件 twirl；它是有限见证，一般定理依据上述证明。

## 2. 非线性 mean-SCE 的不同合同

CP 证明不能直接套给任意非线性状态到几何映射。若

\[
\dot\rho=-i[H(g),\rho],\qquad
\dot g=F(g,\{{\rm Tr}\rho T_\alpha(g)\}),
\]

并且 H、T_alpha 都与 O(2) 交换，则 q=Qrho 与 g 组成闭合商系统。相同初始 g/q 加上该系统的共同选解或唯一性，给出相同几何和 q。这个结论依赖闭合及选解条件，不能把 mean-SCE 宣称为 affine CP 通道来替代证明。本轮有限窗近似历史没有证明完整非线性商系统的唯一性。

## 3. 同一密度矩阵的完全有理反例

取 A=diag(2,0)。四个纯态密度为

\[
\rho_0={\rm diag}(1,0),\quad \rho_1={\rm diag}(0,1),\quad
\rho_\pm=\tfrac12\begin{pmatrix}1&\pm1\\\pm1&1\end{pmatrix}.
\]

两种未保留标签的混合都严格为 I/2。若逐个纯态规定确定性可读几何 g=Tr(A rho)，则

\[
P_Z=\tfrac12\delta_0+\tfrac12\delta_2,\qquad P_X=\delta_1.
\]

平均值都为1，但二阶矩为2和1；有界效应 f(g)=(g−1)² 的期望为1和0，TV=1。同一未标记密度输入不可能由同一个 affine 通道同时给出这两种完整记录。

一般地，若 affine 输出律对所有密度态都是 delta_{f(rho)}，混合律
delta_{f(t rho+(1−t)sigma)}=t delta_{f(rho)}+(1−t)delta_{f(sigma)}
迫使 f 在整个凸状态空间上为常数。这是可读输出的要求，不能直接用于否定仅作为辅助量的 mean-field 参数。

若保留四个正交物理 flag，完整联合输入不同。checker 明确构造同一 flag 控制 CPTP map，给出上述不同输出而无 same-input 矛盾。设备能量、因果性和引力约束仍须另验。只有同一二元 flag、或仅说联合态不同，都不自动保证任意所需输出可实现。

背景一手文献 [Simon–Buzek–Gisin, PRL 87,170405 (2001)](https://arxiv.org/abs/quant-ph/0102125) 在 Hilbert 射线、Born 概率和无超光速通信等假设下导出线性 CP 结构。本轮精确矩阵反例不作“所有非线性引力都可超光速通信”的泛化。

## 4. 同一轨迹的 proper-time 标定

对 u=z+beta z²、d tau=a d eta、V3=2pi²a³，若过去时钟满足 tau/A−eta→0，则

\[
\tau/A=\eta+z/s+(\beta+1/2)z^2/(2s)+O(z^3).
\]

令 w=epsilon exp(s tau/A)，则 z=w−w²+O(w³)，所以

\[
\frac{V_3(\tau)}{2\pi^2A^3}
=1+3w+(3\beta+3/2)w^2+O(w^3).
\]

本轮该二阶系数被包围于
[0.5000000001393602,0.5000000001393647]。固定共形时间的系数不同，不能混用。

若在 eta=0 校准 tau=0，令 r_clock=exp(s tau/A)，则

\[
\frac{V_3(\tau)}{V_3(0)}
=1+3\epsilon(r_{\rm clock}-1)
+\epsilon^2[(3\beta+3/2)r_{\rm clock}^2
-6r_{\rm clock}+9/2-3\beta]+O(\epsilon^3).
\]

初始归一化严格为1。以上是运动学展开；DYNAMICS 的残差界针对精确 a=A exp(z+beta z²)。此处没有把截断 clock 公式作为实际探针校准误差证书，也没有构造 clock/probe 仪器。

## 5. 对下一任务的实际影响

共同动态历史与 old/new 可辨认性现在有不同的验收出口。完善约束传播有助于前者；在同一联合 twirl、共同对称通道合同内，延长时间、更多记录或更复杂传播不能完成后者。

要提出可辨认引力效应，必须明确哪个物理输入使完整联合 twirl 不同，例如可实现的参考系统、实际设备耦合或有独立理由的对称破缺，并把其制备、总源及完整记录计入。不得把新的物理资源归功于原来单场边缘的“降噪”。
