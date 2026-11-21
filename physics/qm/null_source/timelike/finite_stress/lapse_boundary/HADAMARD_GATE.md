# 正常 Gaussian 门的实际 UV 拒收，以及有限模正常 Hadamard 修正

CANONICAL_PREPARATION 的全局门给正常联合态与明确 constraint tolerance。
正常性不足以保证同一自由场模型的 Hadamard / AE 应力验收。
本页实际计算该门后的高频差，拒收全场版本，再给有限模近似正例。
没有把候选失败扩大为所有局域准备失败。

## 1. 实际 incoming 态在瞬时 H_i 频率下的高频相干

在初片取 ν_k=√(ω_k²−V_i)，b_k 如 C1。
原 incoming mode 的 WKB 频率满足
\[
 W=\omega-{V\over2\omega}+{V''-V^2\over8\omega^3}+O(\omega^{-5}).
\]
在所需平滑实际解上可继续任意有限阶；余项由已有 Jost/adiabatic 构造控制。
原 incoming 真空的 anomalous moment 为
\[
 m_k=\langle b_k^2\rangle
 ={\,\nu^2-W^2-(W'/2W)^2\over4\nu W}
                  -{iW'\over4W^2}
 ={iV_i'\over8\omega^3}-{V_i''\over16\omega^4}
                    +O(\omega^{-5}).                        \tag{G1}
\]
n_b 和这些相干一起组成原合法高频结构。

CANONICAL_PREPARATION 的 Gaussian tolerance δ>0 保 n_b，
却将 m_k 乘
\[
 \chi_k=\exp[-\nu_k^2/(2\delta^2)].
\]
所以任何固定有限 δ 的高模都失去 G1 的多项式相干，尽管全态仍正常。

## 2. 同一 AE 差中出现明确 logarithmic 发散

每个 real oscillator 有
D=Im m，Q=(2n+1+2Re m)/(4ν)。
门后减门前因此为
\[
 \Delta\langle D_k\rangle=-{V_i'\over8\omega_k^3}
                                      +O(\omega_k^{-5}),\qquad
 \Delta\langle Q_k\rangle={V_i''\over32\omega_k^5}
                                      +O(\omega_k^{-6}).       \tag{G2}
\]
H_i 的谱保持，但物理 stress 还含 D 和 Q。
两场的 multiplicity 是 2k²，故
\[
 {\Delta\langle D_K\rangle\over\log K}\to-{V_i'\over4},
 \qquad\Delta\langle Q_K\rangle\ \hbox{收敛}.
\]
由
ρbar=(H_i−h_iD+(V_i+h_i²)Q)/(V0a_i⁴)，
同一 AE counterterms 在前后差中精确相消，得到
\[
 \boxed{\lim_{K\to\infty}
 {\Delta\langle\bar\rho_K\rangle\over\log K}
 ={h_iV_i'\over4V_0a_i^4}>0}.                               \tag{G3}
\]
压力同样有
\[
 \lim_{K\to\infty}{\Delta\langle\bar p_K\rangle\over\log K}
 ={h_iV_i'/4-V_i''/12\over V_0a_i^4}.                        \tag{G4}
\]
G3 已足以拒收同一 AE 的 finite mean，应力不必靠 G4 的符号决定。

严格正号来自这轮固定 c：
U_i''=(s²(-c)+σF²b)+quadratic remainder>0，
U_i'''=(s³(-c)+σF³b)+quadratic remainder>0，
b≥0.9c，h_i>0。
E4 系数范数给两个 remainder 均为 O(c²) 且小于 c；
σF>9·10^5、s<2，故 V_i'=U_i'''+2h_iU_i''>0。

系数非常小也不能使 log K 极限有限。
本页没有对 h=0 的静态情况使用这一正号，也没有把 finite K 数值当无限模。
Hadamard 两点函数之间必须有 smooth 差；
G1–G3 的多项式高频差和实际应力发散明确违背该门。

## 3. 继续构造：只控制有限低模

对任意 K≥2 分解 H_i=H≤K+H>K，
low 包含全部正常零模及 k=2 相关壳；原态的 high 是独立 incoming 真空。
用同一正常 geometry Gaussian，h_iP 的输入 RMS 为 δ0>0，定义
\[
 U_K=\exp[-iQ_g H_{\le K}/h_i].
\]
它仍是实际自伴算符定义的 unitary。
在同一输出态内
\[
 U_K^\dagger(h_iP+H_i)U_K=h_iP+H_{>K}.
\]
完整 constraint 特征函数等于
exp(−δ0²t²/2)χ_tail(t)；
这里的独立性来自已给的 low⊗high 原态，不是任意拆噪声。
因此
\[
 \operatorname{Var}(h_iP+H_i)_{\rm out}
     =\delta_0^2+v_{\rm tail},\quad
 \operatorname{Var}(P)_{\rm out}
     ={\delta_0^2+v_{\le K}\over h_i^2},\quad
 \operatorname{Cov}_{sym}(P,H_i)=-{v_{\le K}\over h_i}.         \tag{G5}
\]
现有 H pair 余项与
Σk>K k²/ωk⁴≤81/(64K) 给保守共同界
\[
 0\le v_{\rm tail}<1000M^2/K,\qquad M<5\epsilon .
\]
选 δ0=δ/√2 及有限整数 K>max(2,2000M²/δ²)，
即可得到严格小于任意给定 δ>0 的 constraint RMS。

## 4. 正常性和 Hadamard 性均通过，但总物理准备尚未通过

每个有限 K 的 source 两点函数仅改变有限空间模。
有限 quadratic flow 的矩至多随门参数指数增长；
Gaussian 积分使这些矩有限，所以两点差是平滑双解。
高模完全保留原 incoming Hadamard 结构。
因此每个有限 K 确实给正常且 Hadamard 的近似联合算例。

[U_K,H_i]=0，故 H_i 总谱保留；当前完整裸源边缘仍改变。
原 H_in 谱和 mean/noise 不自动保持；全场 K→∞ 的同 AE 应力
恰受到 G3 的非一致极限阻断。
不能把“每个有限 K 合法”写成“极限准备也合法”。

该有限模门仍是空间全局谱控制，没有从局域、协变、自主的原总装置 action 推出。
几何 momentum 成本约 √v≤K/h_i 仍在；controller、interaction stress 和校准未算。
后续需要对明确有限 K 的输出重算同一总源 mean，并寻找其实际共同演化，
而不能继续沿用门前 quiet mean 历史。

## 5. 两种截止与不一致极限

始终用同一原态中心化 H≤K，减去的 Σν|β|² 收敛；未中心化的零点相位不能偷渡进门。先固定 preparation cutoff K，再令 stress observable cutoff L→∞，得到合法有限 RSET。随后改变 preparation K 时，其差满足 Δρ(ρ_K)/logK→h_iV_i′/(4V0a_i⁴)。
共同自伴谱实现给中心化 U_K→U strong，正常输入的输出于是 trace-norm 收敛。这里每个有限 K 的 source 都 Hadamard，极限 normal source 却不 Hadamard。这一实例明确要求在 trace/constraint 收敛之外另验统一应力界。
