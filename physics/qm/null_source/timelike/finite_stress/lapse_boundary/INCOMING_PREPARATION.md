# 保持原应力观测的正常近似准备：incoming 能量门

在全场 H_i 门被 UV 拒收、有限模修正须重做 mean 之后，本页继续改变控制量：
用 B=AδH_in 代替 H_i。当前 B 与原平滑 source charge 只差固定归一化。
此方案复用 OPERATIONAL_STATE/RELATIONAL 的观测代数原则及既有 normal Gaussian encoding，
新增的是实际初片 H_i 约束残差、正常 geometry-pointer 态及完整资源。

结论是明确的正常、Hadamard、保持原 source 应力限制的近似 canonical 对照。
它没有把 pointer P_g 认作原完整高阶 action 的 P_u，
没有证明 geometry joint mean 沿 quiet U 演化，也没有实现真实引力仪器。

## 1. 正常门与精确保留的物理内容

保持同一 source ρ±、同一 actual quiet U、原 incoming Hilbert 表示。
令
\[
 B=A\delta H_{\rm in},\qquad
 U_B=\exp[-iQ_g\otimes B/h_i],\quad
 \psi(q)=e^{i\mu q}(2\pi s^2)^{-1/4}e^{-q^2/(4s^2)},
 \quad s={h_i\over2\delta_0}.                                \tag{I1}
\]
δ0>0，输出 U_B(|ψ〉〈ψ|⊗ρ±)U_B† 是正常正 trace-one 态。
B 自伴：正常零模动量平方加正频 oscillator number 能量，减有限常数。

当前 P-diagonal source fiber 对 oscillator 总能量分块，
每支固定 N=0 或2，NOON内相干处于同一能量壳。
因此 e^(-itB(P)) 与每个 source fiber density 对易。
非选择 source 输出在整个已声明 A_P 代数上的限制精确保持。
这包括自由场全部 derivative/stress 矩、同一合法 history transport 的 source influence；
并非只保持〈C〉或某个二阶核。
该原则来自前驱，不计作新代数定理。

source W2 只增加每 species 的光滑时空常数
\[
 \Delta W_j(x,x')={E_z\over4A\delta_0^2V_0}.                  \tag{I2}
\]
高模 source 态完全不变，零模只改变 Q²；故 Hadamard 性保持。
原 mean-RSET functional 与原 quiet U 的 mean-SCE 解资格保持。
这句话只涉及 source functional，不证明新增 geometry density 的均值轨道。

完整裸态确实改变。条件记录下的 source 状态也不保持上述非选择限制。

## 2. 原实际初片约束有可算而非假定为零的余项

目标仍取原中心化
\[
 {\cal A}=h_iP_g+H_i,\qquad H_i=\delta(H_0-V_iQ)_i .
\]
没有把 H_i 悄悄换成 B。设 t=Q_g/h_i，则
\[
 U_B^\dagger{\cal A}U_B=h_iP_g+R(t),\quad
 R(t)=e^{itB}H_i e^{-itB}-B.                                 \tag{I3}
\]
零模 incoming 坐标 Q,P 的 flow 是 Q→Q+tP/A²、P不变。
保留实际 primitive I_i，
\[
 R(t)=R_0(t)+tR_1+t^2R_2,
\]
\[
 R_1=-h_i'\mathcal D+(h_i/A^2-h_i'I_i)\mathcal P,\qquad
 R_2=-{h_i'\mathcal P\over2A^2},                             \tag{I4}
\]
其中 mathcal D=Σ{Q_j,P_j}/2，mathcal P=ΣP_j²。
R0(t) 的零模为原 H_i−B 的零模，非零 pair 只转相位；
其 grade-zero 原态范数不变。共同 source/geometry Gaussian 给
\[
 \|R_0(t)\|_2<e^{60}\epsilon,\quad
 \|R_1\|_2<e^{36}\epsilon,\quad
 \|R_2\|_2<e^{28}\epsilon,
\]
\[
 \|R(t)\|_{L^2(\rho\otimes\mu_t)}
 \le\epsilon\left[e^{60}+{e^{36}\over2\delta_0}
                   +{\sqrt3\,e^{28}\over4\delta_0^2}\right]
 =:\epsilon\,{\cal B}(\delta_0),\quad \epsilon<e^{-1158}.     \tag{I5}
\]
这里使用 W7 的完整源矩与实际 H_i−B 界，
没有把经过门后的 Q/D 范数当原样。

原〈D〉=0、〈mathcal P〉=2A³Ez，故
\[
 \langle R\rangle=-{A h_i'E_z\over4\delta_0^2}.
\]
选同一初始 pointer 均值
\[
 \boxed{\mu={A h_i'E_z\over4h_i\delta_0^2}}                   \tag{I6}
\]
使〈A〉out=0。这个 canonical mean shift 必须记录，
不能同时宣称初始 geometry mean 完全未变。

real Gaussian 振幅给 centered sym cross(P_g,R)=0；
因此在同一个输出态
\[
 {\rm Var}_{out}({\cal A})=\delta_0^2+
          {\rm Var}_{\rho\otimes\mu_t}(R(t))
 \le\delta_0^2+\epsilon^2{\cal B}(\delta_0)^2 .                \tag{I7}
\]
明确取 δ0=10^−6，B(δ0)<e61，便有
\[
 10^{-6}\le{\rm RMS}({\cal A})<1.000001\,10^{-6},
 \qquad \langle{\cal A}\rangle=0.                            \tag{I8}
\]
这些是 toy 约束的模型单位，不是实验精度。若未来用于 ACTION_LIFT 的初始 density 荷，须先证明变量识别并显式乘 2/(3V0A²)；δ0 本身不是无量纲 Einstein 残差或重力读数。
δ0→0 时 I5 的 δ0^−2 项不能忽略，本页不宣称免费精确极限。

## 3. 几何 momentum、完整裸态和零模资源

同一联合态精确给
\[
 \langle P_g\rangle=\mu,\quad
 {\rm Var}(P_g)={\delta_0^2+{\rm Var}(B)\over h_i^2},\quad
 {\rm Cov}_{sym}(P_g,B)=-{{\rm Var}(B)\over h_i},
\]
\[
 {\rm Var}(Q_g)={h_i^2\over4\delta_0^2},\qquad
 {\rm Var}(B)=A^2\sigma_{\rm thin}^2\mu_2 .                   \tag{I9}
\]
因此当前分支 ΔP_g>10^−3/h_i>10^−3 e19980；
这个巨大 canonical 资源与 I8 同时成立。
source H_i 谱不保留；保留的是 B 的全谱和 A_P restriction。
总约束、装置总能量与局域实施并未从 I9 得到。

对每个 zero species，
\[
 \Delta\langle Q_j^2\rangle={E_z\over4A\delta_0^2}>2\,10^{12}
 \quad(\delta_0=10^{-6}).                                   \tag{I10}
\]
这是正常 source 的有限坐标二矩成本，不是已算装置能量。

两支 B 谱同为宽 Aσthin 的平滑 bump。其密度
f_B(b)=varpi(b/(Aσthin))²/(Aσthin)，
Zb≥exp(−8/3) 给 ||f_B||∞<2/(Aσthin)。
rank-two 支撑 overlap 为
\[
 F=\iint e^{-(b-b')^2/(8\delta_0^2)}d\mu_B(b)d\mu_B(b')
 \le {2\sqrt{8\pi}\delta_0\over A\sigma_{\rm thin}}<10^{-3}.
\]
故在同一正常源上
\[
 D_{\rm tr}(\rho_S',\rho_S)\ge1-F>0.999 .                    \tag{I11}
\]
允许改变完整裸态正是此正例的必要条件。
大裸态改变与非选择应力限制完全相同并不矛盾。

## 4. 完全正读数与尚缺的总作用量

校准 toy pointer 读数 z=−h_i(P_g−μ) 得
\[
 K_z=(2\pi\delta_0^2)^{-1/4}
           \exp[-(z-B)^2/(4\delta_0^2)],\quad
 {\cal I}_z(\rho)=K_z\rho K_z,\quad
 \int K_z^\dagger K_z dz=I .
\]
全部记录均计入，非选择 map 就是 I1 的 source 边缘。
没有只选窄带成功记录并删除失败代价。

I3 不等于原 A，U_B 没有证明与封闭总约束对易；
自由 P_g、Qg 是明确增加的 canonical pointer，不自动等于原 P_u/u。
还缺原 ACTION_LIFT 的 constrained phase space、完整几何初态、
局域自主 coupling、controller应力、后续双行演化和重力校准。
本轮两条 source-GNS 弱行与本页 normal toy 不能直接拼接成正常物理解。

下一门应从这个更强的同 source-functional 对照出发：
证明或排除其在原高阶几何初值中的 embedding，完整记录 I6/I9 的资源，
再接真正因果演化与所有局域约束。

若保输入 μ=0，也有非中心均方 〈A²〉=δ0²+E TrρR(t)²，其平方根满足同一I8上界；但其均值为I6之前的明确微小值。只有要求均值严格0时才使用I6。本页没有把非中心RMS与centered方差混为一谈。
