# 有限模式准备后的实际源 mean：精确运输与重匹配入口

HADAMARD_GATE 的有限 K 修正已经通过 normal 与 Hadamard 门。
本页继续计算它怎样改变实际初片源，而不复用门前 mean 解。
K 是 preparation cutoff；应力 cutoff L 先在固定 K 下取全场极限。

## 1. 同一门参数运输全部矩

令 τ=Q_g/h_i，Gaussian 方差为 1/(4δ0²)。
对受控 real oscillator，x=(q,p_bulk)，ν²=ω²−V_i，
\[
 S_\nu(\tau)=
 \begin{pmatrix}\cos\nu\tau&\sin\nu\tau/\nu\\
                 -\nu\sin\nu\tau&\cos\nu\tau\end{pmatrix}.
\]
C 是原实对称 canonical 二矩，当前均值为零。
门后 C'=Eτ[S C Sᵀ]。对 ν²>0，χ=exp[−ν²/(2δ0²)]，
\[
 C_{qq}'={(1+\chi)C_{qq}\over2}
                  +{(1-\chi)C_{pp}\over2\nu^2},\quad
 C_{pp}'={(1+\chi)C_{pp}\over2}
                  +{(1-\chi)\nu^2C_{qq}\over2},\quad
 C_{qp}'=\chi C_{qp}.                                       \tag{P1}
\]
ordered covariance 的反对称 iJ/2 完整保持；
不能把整个 ordered Cqp 都乘 χ 而破坏 CCR。

零模 ν²=−V_i<0，写 χ0=exp[V_i/(2δ0²)]，
\[
 C_{qq}'={(1+\chi_0)C_{qq}\over2}
                 +{(\chi_0-1)C_{pp}\over2V_i},\quad
 C_{pp}'={(1+\chi_0)C_{pp}\over2}
                 +{(\chi_0-1)V_i C_{qq}\over2},\quad
 C_{qp}'=\chi_0 C_{qp}.                                     \tag{P2}
\]
每固定 δ0>0 这些量有限，但可能非常大。
对零模退化 ν=0 使用 free shear 的连续极限，不能除以 ν²。

四阶及不同模的混合矩必须用同一个 τ：
\[
 M'_{abcd}=\mathbb E_\tau[
 (S_a\otimes S_b\otimes S_c\otimes S_d)M_{abcd}].              \tag{P3}
\]
原 zero–shell 相关和门产生的跨模相关一起保留。
逐模分别平均后相乘通常给错四阶量。

## 2. 完整 finite-K 初片 mean 差

全部受控 real modes 求和，未受控模相消：
\[
 \Delta\rho_K={\sum_{\alpha\le K}
 [\Delta C_{pp}-2h_i\Delta C_{qp}
                      +(h_i^2+\omega_\alpha^2)\Delta C_{qq}]
                \over2V_0a_i^4},
\]
\[
 \Delta p_K={\sum_{\alpha\le K}
 [\Delta C_{pp}-2h_i\Delta C_{qp}
                      +(h_i^2-\omega_\alpha^2/3)\Delta C_{qq}]
                \over2V_0a_i^4}.                             \tag{P4}
\]
同 g 的 AE/U0 state-independent 项在差中相消。
这些是精确有限式，不需重跑旧几何或 mode ODE。

对每个零模，P2 给
\[
 \Delta H_{{\rm raw},z}={\chi_0-1\over4}
 \left[(1+h_i^2/V_i)C_{pp}+(V_i+h_i^2)C_{qq}-4h_iC_{qp}\right].
                                                                  \tag{P5}
\]
方括号对应实对称矩阵的行列式
\[
 (V_i+h_i^2)(1+h_i^2/V_i)-4h_i^2
 ={(V_i-h_i^2)^2\over V_i}={(h_i')^2\over V_i}>0 .
\]
对当前 h_i'>0、V_i>0 和正常非退化二矩，严格有
\[
 \Delta\rho_{\rm zero}=\Delta p_{\rm zero}>0.                 \tag{P6}
\]
这不是完整源净变化的符号，也不是装置工作；其他模按 P4 保留。
等价正性证明是 X=p−h_iq，Y=√V_i q−h_i p/√V_i，
Gaussian 平均使 Δ〈X²〉=(χ0−1)〈X²+Y²〉/2。

## 3. 新共同 mean 的正确方程

准备后在固定候选 g 的自由演化区间，完整差满足
\[
 \Delta\rho_K'+3h(\Delta\rho_K+\Delta p_K)=0.
\]
脚本从同一 KG 二矩系统逐项核验这条 Ward 等式。
真正要解的是
\[
 E_{\rm new}[g]=E_{\rm base}[g]-{2\over3}a^2\Delta\rho_K[g]=0,
 \qquad
 S_{\rm new}[g]=S_{\rm base}[g]+a^2\Delta p_K[g]=0.           \tag{P7}
\]
P7 中原 incoming 态、I[g]、H_i[g]、全部 C[g] 和 finite-K 门
都必须随同一个 g 运输，然后再求实际正窗口。

只在旧 Ebase=Sbase=0 解族中换 seed，会把新条件缩成
ΔρK=ΔpK=0；旧解族存在性没有证明这两个新条件。
若把门当作瞬时 mean 跳变，自由 Ward 会出现 δ_i ΔρK，
必须由实际准备过去与装置/相互作用应力补齐。
本页尚未解 P7，也未给准备期间完整总源。

## 4. 为什么不能只调一个几何初导

固定旧 source 高频 Cauchy density、a_i、h_i、u_i''，
仅改变 u_i'''，会使 V_i 相同而 ΔV_i'=Δu_i'''。
新 Hadamard 参考要求 Cqp,k=Vnew'/8ω³+O(ω^−5)；
旧固定数据与其差为 −ΔV'/8ω³+O(ω^−5)。

S³×S³ 上该双 kernel 的 H^s 范数平方高频级数为
Σ k^(2s−4)，因此 ΔV'≠0 时只允许 s<3/2，
不在 H^(3/2)，更不 smooth。
Hadamard 差必须平滑，故有限 L 代数调 u''' 不能冒充全场重匹配。
当前 h_i>0 时同 AE density 相对新参考还有
\[
 \Delta\rho_L/\log L\longrightarrow
                 h_i\Delta V_i'/(4V_0a_i^4).
\]
h=0 使该 density 系数为零也不能修复 smoothness 失败。
需要共同运输全部高频初态，使所有 adiabatic jets 匹配；
可从同一 incoming 态沿新完整历史合法 KG 运输，再施同一有限 K 规则。

## 5. 本页的交付范围

已交付：实际有限准备后的全部二矩公式、共同四矩规则、
零模 mean 严格改变、自由区间 Ward、重匹配方程及错误单-jet 修复的拒收。
未交付：P7 的新正时间窗解、全装置守恒总源、局域实现及 calibrated gravity。
下一次推进应从这些明确方程开始，不重试已被拒收的旧 mean 复用。

## 6. 稳定求值与 incoming 能量的实际改变

可令 r=ν²、d=−expm1[−r/(2δ0²)]，写 ΔCqq=d(Cpp/r−Cqq)/2、ΔCpp=−rΔCqq、ΔCqp=−d Cqp；r→0 使用 d/r→1/(2δ0²) 的解析极限。当前极小c下不能因 1−χ 浮点相消就当准备没有改变源。zero 的大 χ0 用其对数和区间界表达。P3每个元素由有限个 exp(zτ)组成，Gaussian平均为 exp[z²/(8δ0²)]，可以闭式计算而无须旧ODE。

还可确定原 incoming Hamiltonian 的均值严格增加：zero 有 P_in=A(p_bulk−h_iq)，所以 ΔH_in,zero=ΔH_raw,zero/A>0；每个非零incoming mode原 anomalous二矩为零，Hi flow 的 a→ατa+βτa†给 Δ〈N〉=(2n+1)E|βτ|²≥0。故有限K门不保原 H_in 均值，尽管保 H_i 全谱。这个号不是 total raw density/p 的号，也不等于已计算 controller 工作或完整总能量。
