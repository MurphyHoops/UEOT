# 严格排序双窗的完整 TT 量子 RSET 响应

直接基线：**f2b09fb2b8fd2235bde7017b060fc07ecc44b441**。本目录新增检查器、说明和实际有向区间回执；继承输入逐字节冻结到该提交。[检查程序](check.py) · [数值回执](result.json)。

本次把 [局部 TT 完整噪声](../../metric_response/tensor/README.md) 接成一个真实的量子度规导数。对过去的紧支撑 TT 度规脉冲，测量严格较晚的四维 TT 应力涂抹，得到完整 RSET 的推迟响应及全模式数值上界。局域 contact、显式度规变化和背景压力项在这对支撑上确实为零；它们没有被一般性地删掉。进一步得到两个明确分离的测试空间之间的连续双线性响应界。

这不是完整 Einstein–Langevin 解、量子背景 SCE 解或重叠时间反馈的 resolvent 证书。固定双窗的上界不证明实际响应非零，也不证明存在不稳定模。

## 1. 物理输入和两个窗口

沿用单位三球 \((S^3,\gamma)\)、最小无质量实标量、原静态准备的 Hadamard 参考态，以及
\[
 A^2=3\cos2\eta,\quad a_\lambda=\lambda A,\quad
 4\pi G=\hbar=1,\quad \lambda=32768.
\]
共形坐标和协变空间应力的归一与父证书一致。父证书构造的 Cotton 张量 \(\tau\) 光滑、非零、空间 TT，支撑在 \(\chi<1/8\)，有固定整数归一 \(M=7640\) 和 \(\|\tau\|_{F,\infty}\le1\)。这里没有重新缩小它来改善数值。

令 \(b(x)=e^{-1/(1-x^2)}\)（\(|x|<1\)），在区间外延拓为零。选取
\[
\begin{aligned}
 \psi_P(\eta)&=b(32(\eta-3/32)),&I_P&=(1/16,1/8),\\
 \psi_F(\eta)&=b(64(\eta-11/64)),&I_F&=(5/32,3/16).
\end{aligned}
\]
闭支撑之间的时间间隙为 \(1/32\)。“排序”仅指每个输出点的 \(\eta\) 都大于每个输入点；不声称两个空间球中的每一对点都为类时分离。可能存在的光锥奇性由合法四维光滑涂抹及下述 Hilbert–Schmidt 界处理。

输入度规族为
\[
 (g_\epsilon)_{ij}=a_\lambda^2(\gamma_{ij}
               +\epsilon\psi_P\tau_{P,ij}),\qquad
 \delta g_{0\mu}=0. \tag{1}
\]
\(|\epsilon|<1\)、\(\|\tau_P\|_\infty\le1\) 保证空间度规正定。共同过去的量子态与 Cauchy 数据固定；这里只求 \(\epsilon=0\) 的导数。

定义过去和未来的涂抹算子
\[
 O_I=4\int A^2\psi_I\tau_I^{ij}
       \widehat T^{\rm ren}_{ij,\rm cov}\,d\eta\,d\Omega_\gamma . \tag{2}
\]
各 \(\tau_I\) 可分别取上述冻结张量，定理也允许任意光滑紧支撑空间 TT 张量。背景各向同性使其均值为零；协方差始终取 connected 部分。有限重整化 c-number 在 connected 噪声及交换子中消去。

## 2. 生成元符号与完整导数

固定 canonical 数据 \((\Phi,\pi)\) 下，空间度规 \(q=\gamma+\epsilon h\) 的 Hamiltonian 为
\[
 H_\epsilon=\frac12\int\left[
 \frac{\pi^2}{a_\lambda^2\sqrt{\det q/\det\gamma}}
 +a_\lambda^2\sqrt{\det q/\det\gamma}\,
       q^{ij}\partial_i\Phi\,\partial_j\Phi
 \right]d\Omega_\gamma .
\]
TT 条件给 \(\delta\sqrt{\det q}=0\)、\(\delta q^{ij}=-h^{ij}\)，故
\[
 \delta H=-\frac{a_\lambda^2}{2}
          \int h^{ij}\partial_i\Phi\,\partial_j\Phi\,d\Omega_\gamma,\qquad
 \boxed{G_h=\int\delta H\,d\eta=-\frac{\lambda^2}{8}O_P}. \tag{3}
\]
这模去一个不影响交换子的中心常数。负号来自空间逆度规的变化。检查器对一般对称无迹矩阵逐项验证 determinant、inverse 和 Hamiltonian 的一阶导数，避免把作用量变分的符号直接移给 Hamiltonian。

采用固定过去态的 retarded 演化约定，
\[
\begin{aligned}
 \chi_{F\leftarrow P}
 &=\left.\frac{d}{d\epsilon}\langle O_F\rangle_{g_\epsilon}
                                      \right|_{\epsilon=0}\\
 &=i\langle[G_h,O_F]\rangle\\
 &=-\frac{i\lambda^2}{8}\langle[O_P,O_F]\rangle
 =\frac{\lambda^2}{4}\operatorname{Im}
       \langle O_P O_F\rangle_{\rm conn}. \tag{4}
\end{aligned}
\]
这是弱二次型意义的公式；有限方差使最后一行可由
\(\langle O_P\Omega,O_F\Omega\rangle\) 定义，不需要假设两个无界算子的乘积在整个 Hilbert 空间有界。这里直接使用扩展 Wick 代数的 retarded 度规导数，不仅援引 Weyl 生成元的公式；其存在性与应力导数关系见下述 Hollands–Wald 结果。使用的是实际非平稳参考态，不引入 KMS、平稳性或 fluctuation–dissipation 假设。

外部理论依据：[Hollands–Wald, §4.3 与 Appendix A](https://arxiv.org/pdf/gr-qc/0404074) 直接处理扩展 Wick 代数中的复合场。Eq. (111) 定义 retarded 度规导数，Appendix A 证明该导数作为扩展代数元素存在；Eq. (112) 同时保留 retarded product 与复合场的显式度规变化。Eqs. (119)–(121) 则通过 relative Cauchy evolution 给出 advanced 与 retarded 导数之差为应力交换子。对于本文严格较晚的输出，固定未来数据的 advanced 导数为零；令 \(T(h)=\int\delta g_{ab}T^{ab}d{\rm vol}=\lambda^2O_P/4\)，该差公式立即给 \(\delta^{\rm ret}O_F=-i[T(h),O_F]/2=-i\lambda^2[O_P,O_F]/8\)，与独立 Hamiltonian 推导一致。

[Brunetti–Fredenhagen–Verch, Theorem 4.3](https://arxiv.org/pdf/math-ph/0112041) 是 Weyl 生成元版本的先行结果；本文的最终符号以式(3)及上述 retarded 约定为准。[Anderson–Molina-París–Mottola, §III, Eqs. (3.6)–(3.9)](https://arxiv.org/pdf/gr-qc/0209075) 明确区分非局域 retarded 交换子与局域 contact，并要求在一般响应中共同重整化。没有把该文的 Minkowski 稳定性结论移到当前背景。

### 为什么这里是完整 RSET 导数

\(h\) 及其任意阶时空导数，在整个输出支撑的一个开邻域上恒为零。因此：

1. 输出点的度规、逆度规、标架、体积元以及定义应力的局域微分算子的显式一阶变化均为零。
2. 同一局域协变重整化方案给出的局域曲率反项导数，是 \(h\) 的有限阶局域微分表达式，故在输出邻域为零。用分布表述，支撑在对角线的 contact 及其导数与 \(F\times P\) 测试配对为零。
3. 背景压力没有遗漏。有效 TT 各向异性响应一般应取
   \(a_\lambda^2\gamma_{ik}\delta\langle T^k{}_j\rangle^{TT}\)。
   协变应力的纯背景 \(p\,a_\lambda^2h_{ij}\) 与提升指标带来的
   \(-p\,a_\lambda^2h_{ij}\) 抵消；检查器独立验证这一抵消。
   在本输出邻域，二者分别就是零。
4. retarded 核中的 \(\theta(\eta_F-\eta_P)\) 在整个测试乘积上等于一。
   此处无需在对角线定义 \(\theta\) 与奇异核的乘积。

于是式(4)正是本输入、输出对的完整协变 RSET 导数。换一种固定局域有限曲率方案仍给相同的分离窗导数；这不从本实验反推出这些局域系数，也不表示重叠情形的 contact 为零。

父状态中的齐性经典位移同样不改变本导数。原背景上 \(O_P,O_F\) 都只含空间梯度，故其算子及交换子对任意齐性位移保持不变；从演化方程看，齐性标量的线性 TT 度规 forcing 为零，固定过去数据给 \(\delta f=0\)。此结论仅针对这一阶 TT 路径，不延伸到之前的非齐性 lapse 路径。

## 3. 从完整噪声到响应：不假设未知范数

对实测试，Cauchy–Schwarz 给出
\[
 |\langle[O_P,O_F]\rangle|
 \le2\sqrt{\operatorname{Var}O_P\,\operatorname{Var}O_F}.
\]
若 \(\operatorname{Var}O_I\le\lambda^{-4}C_I\)，则
\[
 \boxed{|\chi_{F\leftarrow P}|
       \le\frac{\sqrt{C_PC_F}}{4\lambda^2}.} \tag{5}
\]
关键是同时认证两个 \(C_I\)，而非把未证明的完整反馈 operator norm 写成前提。

### 3.1 全模式空间行与低块

实三球谐波标签 \(n=(k,\ell,m)\) 的频率为
\(\omega_k=\sqrt{k^2-1}\)，简并度 \(k^2\)。定义
\[
 N_{nm}=\int\tau^{ij}\nabla_iY_n\nabla_jY_m\,d\Omega_\gamma.
\]
父证书的梯度 Bessel、\(\operatorname{div}\tau=0\)、Parseval 和三球 Bochner 恒等式给
\[
 \sum_m\frac{|N_{nm}|^2}{\omega_m}
 \le\|\tau\|_\infty^2\omega_n^3,\qquad
 \|\operatorname{Hess}Y_n\|_2^2=\omega_n^4-2\omega_n^2. \tag{6}
\]
零模行和列严格为零；从不除以其零频率。设
\(L_j=\|\psi^{(j)}\|_{L^1}\)、\(K=256\)、
\(S_4=\sum_{k=1}^{K}k^4\)。场模增长界
\(|Au_k|^2\le H_I/\omega_k\) 给完整低行上界
\(N_L=H_IL_0\sqrt{S_4}\)；
\(LL^2+2LH^2\le2N_L^2\) 包含所有混合块。

### 3.2 未来窗必须更新的两类常数

旧 \(H\) 只覆盖到 \(1/8\)。这里用
\(A_{\rm phys}(\eta)=\sqrt{3\cos2\eta}\) 表示辅助解析曲线，记
\(A_0=\sqrt3\)、\(A_L=A_{\rm phys}(-1/8)\)、\(A_R=A_{\rm phys}(-1/16)\)。
实际准备尺度在过渡区为 \(A_{\rm prep}=A_0+s(A_{\rm phys}-A_0)\)，
其中 \(0\le s\le1,\ s'\ge0,\ \int s'=1\)。
其左端实际值是 \(A_0\)；\(A_L\) 只是整个过渡区的下界。
由
\[
|A_{\rm prep}'|\le s'(A_0-A_L)+A_{\rm phys}'
\]
及辅助曲线在过渡区的单调增加，得到
\(\int|A_{\rm prep}'/A_{\rm prep}|\le(A_0+A_R-2A_L)/A_L\)。
这不要求实际拼接尺度自身单调。在 \(\eta\ge-1/16\) 后，
实际尺度等于 \(A_{\rm phys}\)。检查器对每个正终点 \(r\) 重新计算
\[
\begin{aligned}
 V_{\rm prep}&=(A_0+A_R-2A_L)/A_L,\\
 R(r)&=V_{\rm prep}
       +\log(A_0/A_R)+\log(A_0/A_{\rm phys}(r)),\\
 H(r)&=\tfrac12e^{2R(r)}. \tag{7}
\end{aligned}
\]
静态初始 \(\alpha=1,\beta=0\) 及
\(|\alpha|+|\beta|\le e^{\int|A'/A|}\) 保证其对每个非零模成立。
未来 \(H(3/16)\) 严格大于过去 \(H(1/8)\)，程序检查这个事实。

未来 bump 是平移并压缩后的过去 bump，精确满足
\[
 \|\psi_F^{(j)}\|_1=2^{j-1}\|\psi_P^{(j)}\|_1,\quad j=0,1,2,3. \tag{8}
\]
父时间导数的已认证上界按 \(1/2,1,2,4\) 缩放。位移不影响此等式；不存在漏掉 Jacobian 的 \(2^j\) 因子。

高频主项使用三次 IBP。检查器对各自时间区间重新构造 \(q\) 的七阶时间 jet，覆盖全部独立 \(k,l>K\) 的 W2 振幅和
\(\phi'_k+\phi'_l=k\sigma_k+l\sigma_l>0\)，得到四个系数 \(g_{I,j}\)，使
\[
 L_{\rm grad,I}\le\sum_{j=0}^3g_{I,j}L_j. \tag{9}
\]
未来区间的 \(g_{F,j}\)、正相位下界及 W2 场模界全部重新认证，不搬旧窗数值。compact smooth 边界保证所有 IBP 边界项为零。

原 W2 制备余项证书本来就均匀覆盖 \([0,3/16]\)，故其
\(|\widetilde\alpha_k-1|+|\widetilde\beta_k|\le E_5/k^5\)
可合法复用。程序检查此区间、\(K\)、输入哈希及
\(E_5/(K+1)^5<1\)；没有把平均应力的 UV tail 当成噪声 tail。

### 3.3 可直接审查的数值公式

\[
\boxed{
 C_I\le32\|\tau_I\|_\infty^2
 \left[
  2(H_IL_0)^2S_4+
  \left(\frac{\sum_{j=0}^3g_{I,j}L_j}{2\sqrt K}
      +\frac{4L_0E_5}{\sqrt{5K^5}}\right)^2
 \right].
} \tag{10}
\]
这包括低模、混合块、全部高频正相位主项和真实制备余项。每一数值端点在回执中按精确二进制有理数保存；十进制只用于报告。

| 回执字段 | 含义 |
| --- | --- |
| windows.past.C_T_upper | 过去窗完整 \(C_P\)，独立重算并核对父证书 |
| windows.future.C_T_upper | 新未来窗完整 \(C_F\) |
| windows.*.preparation_growth | 各窗新的全模式增长界 |
| windows.*.positive_frequency_phase | 各窗新的时间 jet、正相位和 IBP 系数 |
| response.susceptibility_absolute_upper | 式(5)的完整 RSET 导数上界 |
| separated_test_space_bound | 下节的连续性范数及数值常数 |


### Actual numerical receipt

The following decimals approximate the certified rational upper endpoints; the exact endpoints are in result.json.

| Quantity | Decimal |
| --- | ---: |
| C_P | 918803363.3182 |
| C_F | 1249049401.7154 |
| Full separated susceptibility at lambda=32768 | 0.24942572011332 |
| Separated projective test-space norm | 2.3283064365387e-10 |
| Coarser W31 test-space norm | 1042.6008204814 |

## 4. 已证明且定义域明确的响应算子界

式(10)允许超出单一 bump。对 \(\psi\in C^\infty_c(I)\)，用实际的
\(L_j=\|\psi^{(j)}\|_1\) 定义
\[
 n_I(\psi)=\sqrt{32}
 \left[
 2(H_IL_0)^2S_4+
 \left(\frac{\sum_jg_{I,j}L_j}{2\sqrt K}
       +\frac{4L_0E_5}{\sqrt{5K^5}}\right)^2
 \right]^{1/2}. \tag{11}
\]
这是范数：非退化性来自 \(L_0\)，齐次性显然；三角不等式来自每个 \(L_j\) 的次可加性和正系数二维欧氏范数的 Minkowski 不等式。
空间测试空间为光滑紧支撑 TT 张量，范数为 \(\|\tau\|_\infty\)。

在有限和 \(F=\sum_r\psi_r\tau_r\) 上取 projective norm
\[
 \|F\|_{\pi,I}
 =\inf_{F=\sum_r\psi_r\tau_r}
    \sum_rn_I(\psi_r)\|\tau_r\|_\infty . \tag{12}
\]
式(10)给
\(\|(O_F-\langle O_F\rangle)\Omega\|
 \le\lambda^{-2}\|F\|_{\pi,I}\)。因此
\[
 \boxed{|\chi(F,P)|\le\frac1{4\lambda^2}
       \|F\|_{\pi,I_F}\|P\|_{\pi,I_P}.} \tag{13}
\]
双线性型唯一连续延拓到这两个范数完备化。
\(\lambda=32768\) 时常数为精确的
\(1/4294967296=2^{-32}\)。范数中的四个导数权重均由式(7)、(9)、(10)的全模式估计明确计算。

另以
\(\|\psi\|_{W^{3,1}_{\rm sum}}=\sum_{j=0}^3L_j\) 计，检查器使用
\[
 n_I(\psi)\le B_I\|\psi\|_{W^{3,1}_{\rm sum}},\quad
 B_I^2=32\left[
 2H_I^2S_4+
 \left(\frac{\max_jg_{I,j}}{2\sqrt K}
       +\frac{4E_5}{\sqrt{5K^5}}\right)^2\right]
\]
输出更粗的可计算双线性常数 \(B_FB_P/(4\lambda^2)\)。

完备化中的元素用于连续延拓的测试二次型；没有声称每个元素本身都定义光滑有限度规族。对于一般任意时空张量，也没有给出同一范数控制。

## 5. 为什么尚不能关闭重叠量子反馈

严格的时间排序允许把 retarded 响应写成两个完整涂抹算子的交换子。重叠窗口会重新引入局域 contact、显式变分，以及不能移除的因果时间截断。

检查器给一个反控：振子的涂抹可观测量与自身的交换子为零，而因果排序的正频 sine 核在 \([0,T]\) 上有
\[
 \int_0^T(T-u)\sin2u\,du
 =\frac{2T-\sin2T}{4},\qquad
 T=\pi/4:\ \frac\pi8-\frac14>0.
\]
矩形时间轮廓可由光滑正轮廓近似，正性持续；取支撑宽度小于 \(\pi/2\) 的正 compact bump 也直接给正性。因此全涂抹自身交换子不能替代 overlapping retarded response。此反控只证明时间排序的逻辑必要性，不借振子数值代替当前场论。

真正量子反馈仍需在指定函数空间上处理
\[
 \mathcal D_Th-4\mathcal R_T^{\rm cov}[h]=4\xi,\qquad
 \mathcal R_T^{\rm cov}[h]
 =a_\lambda^2\gamma_{ik}
        \delta\langle T^k{}_j\rangle_{\rm ren}^{TT},
\]
包括局域项、重叠核、引力侧有限曲率项及可控 retarded inverse。本证书不给这些环节未经证明的 operator norm，也不把式(5)较大的保守上界解释成实际不稳定。

旧 μ=1、α=0 及同一局域重整化方案的固定合同保持原义。齐性均值和当前分离响应均不能测定所有可能的局域四阶 TT 系数；若另改物理净曲率耦合，必须显式声明。仅重排 RSET 方案与引力侧补偿项不改变物理模型。

## 6. 执行和可复现边界

    python -B physics/qm/null_source/timelike/operational_response/kernel/check.py --write --check

检查器比较继承文件与 f2 提交、核对父 receipt 内的 SHA256、冻结自身代码和本说明；使用 70 位 outward interval 运算及精确符号核对。只调用旧背景/W2 的解析 jet 函数，不运行旧检查器入口、不做新模式 ODE、不模拟硬件、不给出新 Lean 数据，Core 保持只读。

实际数值、零新模式积分计数和仍开放的范围均在 result.json 中明示。误差常数可继续收紧；本轮闭合的是严格排序测试类上的完整 RSET 导数与明确范数，不是整个半经典自洽问题。
