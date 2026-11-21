# 自伴源荷和正常 canonical 近似准备：可做什么，付出什么

MIXED_BOUNDARY 给出两条弱行，READOUT_WITNESS 拒收它为受控弱涨落候选。
本页继续处理初始关系 h_i δP_u+H_i=0 的正常状态问题。
先补齐 H_i 的自伴性，再在明确声明的 canonical 几何模型中构造正常近似态。
这个模型不是已从原理论确定的完整物理 Hilbert 空间或局域装置。

## 1. L² 向量不足以定义门：另证实际 H_i 自伴

此前 H_i=lim_K δ(H0,K−V_i Q_K)_i 只先按当前 source GNS 向量验收。
定义 exp(−iQ_g H_i/h_i) 需要自伴算符，不能从有限方差直接推出。

令 M=Σj=0³||V^(j)||L1(past)<5ε，M<0.1。
对非零模 k≥2，ν_k=√(ω_k²−V_i)>0。
在实际 incoming Fock 表示中，以
\[
 b_{kr}={\nu_k q_{kr}+i p_{kr}\over\sqrt{2\nu_k}}
\]
定义瞬时 H0−VQ 的标准 annihilator。
若 v_k=e^−iωη F_k/√(2ω)，其混合系数为
\[
 \beta_k={e^{i\omega i}\{(\nu_k-\omega_k)F_k^*(i)
                       +iF_k^{*\prime}(i)\}
                  \over\sqrt{4\nu_k\omega_k}}.                \tag{C1}
\]
实际 Jost 初端 F_k'=iV_i/(2ω_k)+O(M/ω_k²)；
ν−ω=−V_i/(2ω)+O(M²/ω³)，两个 leading 项精确相消。
已有统一余项给 |β_k|≤10M/ω_k³。
因此
\[
 \sum_{k\ge2}2k^2|\beta_k|^2,\quad
 \sum2k^2\nu_k|\beta_k|^2,\quad
 \sum2k^2\nu_k^2|\beta_k|^2<\infty .                          \tag{C2}
\]
乘积 squeeze 存在 Fock unitary 实现。
其非零模能量是 unitary conjugate of dΓ(ν)，加一个有限常数；
当前 finite-shell 态属于 operator domain，其 centered cutoff 向量等于此前 H_i 极限。
证明只需 Dom H，不把它升级为 Dom H²。

两个零模是有限维实二次算符
½(p_bulk²−V_i q²)。V_i>0 时经 metaplectic 变换为 dilation，
V_i=0 为 free，V_i<0 为 oscillator；在 Schwartz 核上本质自伴。
张量谱和、有限常数减除给完整 H_i 的自伴实现。
原 compact annular 波函数经实际有限零模运输仍在所需 domain。
这个实现使下面全局门的 spectral calculus 合法；
不证明门后的源态继续是同一 incoming Hadamard 态。

## 2. 原正常 tensor 空间内没有精确零约束态

明确声明 toy 运动学：
\[
 {\cal H}_g=L^2(\mathbb R,dq),\quad Q_g=q,\quad
 P_g=-i\partial_q,\quad
 {\cal A}=h_iP_g\otimes I+I\otimes H_i,\quad h_i>0 .           \tag{C3}
\]
两个强对易自伴算符的谱和定义 A。
P_g 的谱测度无 atom；对任意简单张量和任意 λ，
\[
 \langle E_{\cal A}(\{\lambda\})\rangle
 =\int \mu_H(dE)\,\mu_P(\{(\lambda-E)/h_i\})=0.
\]
简单张量稠密，故 E_A({λ})=0，特别 ker A={0}。
这一步甚至不要求 H_i 连续谱。

于是不存在 trace-one 正常联合态满足
Tr ρ A²=0，或等价 Aρ^(1/2)=0；
均值〈A〉=0 的正常态当然仍可存在。
谱原理沿用前驱 QUANTUM_FLOOR，本轮新增是实际 H_i 的自伴实现及以下明确准备。

Dirac/group averaging 可在分布 δ(h_i p+E) 上另建 physical inner product，
形式权重含 |h_i|^−1；这属于另一约束后空间。
本页没有以运动学正常性条件排除这种物理量子化，也没有完成它。

## 3. 一份明确正常联合态及完整资源

取几何 Gaussian
\[
 \psi_s(q)=(2\pi s^2)^{-1/4}e^{-q^2/(4s^2)},\quad s>0,
\]
和当前正常 source ρ_S，H_i 已中心化，v_H=Trρ_S H_i²。
用 spectral calculus 定义
\[
 U=\exp(-iQ_g\otimes H_i/h_i),\qquad
 \rho_{\rm out}=U(|\psi_s\rangle\langle\psi_s|\otimes\rho_S)U^\dagger.
                                                                  \tag{C4}
\]
它是正、trace one、正常联合态。
U†P_gU=P_g−H_i/h_i，U†AU=h_iP_g，Q_g 和 H_i 各自保持。
所以
\[
 {\rm RMS}({\cal A})={h_i\over2s},\quad
 {\rm Var}(Q_g)=s^2,\quad
 {\rm Var}(P_g)={1\over4s^2}+{v_H\over h_i^2},\quad
 {\rm Cov}_{sym}(P_g,H_i)=-{v_H\over h_i}.                     \tag{C5}
\]
原始方差与交叉来自同一 U，没有独立填相关系数。
若给定约束容差 δ>0，取 s=h_i/(2δ)，则
\[
 {\cal A}\sim{\cal N}(0,\delta^2),\quad
 \Delta Q_g={h_i\over2\delta},\quad
 \Delta P_g={\sqrt{\delta^2+v_H}\over h_i}.                    \tag{C6}
\]
δ ΔQ_g=h_i/2 饱和 [A,Q_g]=−ih_i 的不确定关系。
当前 W8、W11 还给
\[
 \Delta P_g>{10^{-3}\over h_i}>10^{-3}e^{19980}.
\]
所以近静态动量成本没有被相关门消掉。
这不是完整装置能量估计；controller、耦合应力和真实作用量未算。

## 4. 完整源态必改变，原平均历史须重新验收

迹去 geometry 后
\[
 \rho_S'=\int {dq\over\sqrt{2\pi}s}e^{-q^2/(2s^2)}
              e^{-iqH_i/h_i}\rho_S e^{iqH_i/h_i}.
\]
在 H_i 的双谱表示，offdiagonal 乘
\[
 \exp[-s^2(E-E')^2/(2h_i^2)]
       =\exp[-(E-E')^2/(8\delta^2)].                         \tag{C7}
\]
H_i 的完整谱律保持，能量间相干改变。

设 P_M 是原 rank-two 支撑，CONSTRAINT_RESIDUAL 已证
L=Σp_j||(1−P_M)H_i u_j||²>0。
对小 q，支撑泄漏为 q²L/h_i²+o(q²)；
Gaussian 对该区有正质量，故 TrP_Mρ_S'<1，
\[
 D_{\rm tr}(\rho_S',\rho_S)\ge1-\operatorname{Tr}(P_M\rho_S')>0.
\]
不能把这份正常构造描述成保留完整裸源边缘的修复。

H_i 含实际初片 Q/D，通常不与 H_in 对易。
因此保 H_i 谱不等于保 incoming C 谱、原 thin-energy 律或原应力观测限制。
门后 mean RSET、noise、Hadamard 性及 quiet history 都必须重新检验。
本页没有把门后态直接塞回原 mean 解。

对纯 source ψ，若只作额外对照，
F=∬exp[−(E−E')²/(8δ²)]dμψ(E)dμψ(E')，
1−F≤Dtr≤√(1−F)；仅当该谱无 atom 时 δ→0 才推出 F→0。
不把这个附加条件自动赋给当前 H_i。

## 5. 已闭合与下一项

已闭合：实际源 H_i 的合法自伴实现；明确运动学模型中的正常精确约束阻断；
一族正常近似联合态；全部初始协方差、约束精度和完整源态扰动。
这些回答“允许改变态后，相关能否产生、付出什么”。

待完成：从 ACTION_LIFT 的真正 constrained phase space 确定 ordering、
物理内积和几何可观测代数；从局域自主准备作用量导出相同效果；
重新解门后同一总源 mean/noise，并纳入装置与校准。
不能将 C4 的全局受控门直接称为引力制备器。

## 6. 完全正仪器、主动准备与约束守恒的区别

在 toy 中读取 z=−h_iP_g，对应
\[K_z=(2\pi\delta^2)^{-1/4}\exp[-(z-H_i)^2/(4\delta^2)],\quad {\cal I}_z(\rho)=K_z\rho K_z.\]
全部 z 的积分 trace-preserving，POVM 是 H_i 谱的 Gaussian smearing；非选择 map 正是 C7。这里所有记录都计入，没有只保留窄带成功分支。
若把 U 只用作 canonical 坐标变换并同步运输态和观测量，不产生物理准备；本页明确固定原因子代数与 A，主动改变 boundary density。U†AU=h_iP≠A，因此这不是封闭总约束守恒的自主实施。controller 的 constraint/stress 不能省去。

当前 V_i>0 的零模 inverted oscillator 经线性 symplectic 变换及 y=log|x| 化为 dilation 的平移生成元，具有纯绝对连续谱；与其余模的张量谱和仍如此。故对当前有限秩源，δ→0 时 Tr(P_Mρ′_δ)→0，Dtr→1。这个结论来自 Fourier 矩阵元的衰减及宽 Gaussian 平均，不把正常精确极限当作存在。

C3 的精确分布解还可写 Ψ(q)=e^(-iqH_i/h_i)ψ，范数沿q恒定，故在整轴不平方可积。若将q作为 clock/gauge，取q=0截面的ψ及其内积可构造此 toy 的 relational Hilbert空间；这说明运动学normal阻断不等于没有任何物理解。它尚未转为原 ACTION_LIFT 的全部约束量子化。
