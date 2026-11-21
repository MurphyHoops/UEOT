# 压力弱解之后：剩余密度荷、有限块自由度与独立载体的精确界

本页检验PREPARED_READOUT所选的fullmode R(q)=p(q)−B_i(q)，
明确把有限零模也包含在B_i中。
结论针对这个具体初始规则及保持其原裸source态的独立carrier补救；
不推广为所有真实含源准备或所有约束后物理态的不可能性定理。

## 1. 密度行的合法 transpose 延拓

记L_p=δS、E_U=δE，均指same incoming、零初始geometry/mode变化的graph域。
已证Ward intertwiner为
\[
 E_U G_p=\mathcal J,\quad
 \mathcal J f(t)=2e^{-U(t)}\int_0^t h(s)e^{U(s)}f(s)ds.
\]
对紧支smooth密度测试f，
\[
 \mathcal J^*f(s)=2h(s)e^{U(s)}\int_s^T e^{-U(t)}f(t)dt.
\]
它smooth且末端flat，属于advanced pressure graph域。
在该域定义/识别E_U^*f=L_p^*(J^*f)，所以
G_p^*E_U^*f=J^*f，且H3迹相等。

因此对统一W(F)=R(−a²G_p^*F)，密度响应是合法的
\[
 e_W(f)=R(-a^2\mathcal J^*f).                        \tag{D1}
\]
这没有任意扩张一个无界transpose的定义域，也没有给W普通H4初值样本。

取φ内紧支，J^*(−φ′+hφ)=2hφ；
此测试在初片平坦，R退回原压力。
结合实际source Ward，令d=(2/3)a²ξρ，得到
\[
 e_W'+he_W=-2a^2h\xi_p=d'+hd.
\]
所以D=e_W−d满足(e^UD)′=0，是一份GNS向量值常数分布。

## 2. 残差不是未知常数：有明确的有限全场表示

任取χ∈C∞_c((0,T))、∫χ=1，Ψχ(s)=∫_s^Tχ。
定义
\[
 K_{\rm res}[R]=R(-2a^2he^U\Psi_\chi)
                   -{2\over3}\xi_\rho(a^2e^U\chi).  \tag{D2}
\]
它与χ无关，D(f)=K_res∫e^{-U}f。

finiteK用同一source的
\[
 \delta\rho_K={\delta H_{0,K}-h\delta D_K+h^2\delta Q_K\over V_0a^4}
\]
和source Ward积分。qχ=−2a²he^UΨχ在初端满足
q_i=−2a_i²h_i eUi、q_i′=−2a_i²eUi(h_i′+3h_i²)。
代入同一个B_i，所有D项精确相消，得到
\[
 \boxed{K_{\rm res}[R]=
 -{2e^{U_i}\over3V_0a_i^2}\,\delta H_{V,i},\quad
 H_{V,i}=\lim_{K\to\infty}(H_{0,K}-V_iQ_K)_{\rm centered}.}      \tag{D3}
\]
centered极限包含原低模与零模，局部c-number减项不影响它。
这恰是bulk变量的初始Hamiltonian组合，不是新独立carrier。

该特定sharp组合确实有L²意义：
H0的pair领先项V_i/(4ω)与V_iQ的同项相消，
剩余O(μJ/ω²)，Σ4k²|pair|²可和。
单独sharpρ、Q、H0没有因此被赋予有限二阶矩。
D2提供完全smooth的等价定义。

## 3. 当前正常薄层态下，残差严格非零

用固定incoming零模primitive mathcal I_i，H_V的零模部分为
\[
 H_{V,z}=\alpha\mathsf Q+\beta\mathsf D+\gamma_z\mathsf P,
\]
\[
 \alpha=-a_i^2h_i'/2,\quad
 \beta=h_i-a_i^2h_i'\mathcal I_i,\quad
 \gamma_z={1\over2a_i^2}+h_i\mathcal I_i
                       -{a_i^2h_i'\mathcal I_i^2\over2}.        \tag{D4}
\]
原ρ有权重1−p>0的ψ0⊗全部壳vacuum分支。
如果Var H_V=0，投影回同一壳vacuum分量，
必须有H_V,z ψ0=cψ0。

当h_i′≠0，这是正半径annulus上的非退化二阶径向ODE。
ψ0是C∞ compact环包，在外边界函数及导数都为零，
ODE唯一性迫使其恒零，矛盾。
当h_i′=0、h_i≠0，它成为非退化一阶径向ODE，同样矛盾。
当h_i=h_i′=0，它只是P²/(2a_i²)乘法，
非零正常L²环包不可能支持在单个能量壳上。
因此
\[
 \operatorname{Var}_{\rho_\pm}H_{V,i}>0,\qquad
 \operatorname{Var}K_{\rm res}[R]>0.                 \tag{D5}
\]
其他pair输出处于正交壳，不能抵消这个严格正性。

这直接拒收“P10的pressure弱解已经满足两条齐次Einstein行”的主张。
UV合并闭环和density约束闭环是两项不同验收。

## 4. 再附一个保持完整裸源态的独立记录，能做到什么

设P为原秩二source支撑，u0=ψ0⊗vac，
u2=ψ2⊗A_±；H表示已中心化的H_V。
考虑任意正常source⊗carrier扩张R_SA，其source边缘仍为原ρ，
carrier-only自伴Z有有限二阶矩。
正常扩张的支撑在P⊗1内。
将(H⊗1−1⊗Z)R_SA^{1/2}投影到(1−P)⊗1，
Z及均值项全部消失，因此
\[
 \operatorname{Var}(H-Z)\ge
 {\cal L}:=\operatorname{Tr}\rho H(1-P)H .           \tag{D6}
\]
这里只用H在两个支撑向量上的已证L²作用；
不需要调用未证明的完整谱独立性。

H的两个支撑之间没有矩阵元：zero项不改壳粒子数，
k=2 pair跨支项乘〈ψ0|ψ2〉=0，因原两个energy annuli不相交；
high pair输出也正交。
于是
\[
 {\cal L}=(1-p)\operatorname{Var}_{u_0}H
             +p\operatorname{Var}_{u_2}H>0.         \tag{D7}
\]
它就是PREPARED_READOUT绝对式删除between-branch均值平方后，
保留全部zero、壳内pair及高模pair的和。

该界在这个抽象independent-carrier类中是精确最小值：
取正常classical记录
Σ_j p_j|u_j><u_j|⊗|j><j|，Z|j>=〈u_j,H u_j〉|j>，
达到Var(H−Z)=L。
记录最多删掉两支均值之间的那一块，
不能删掉每个pure source支内的量子涨落。
乘D3的系数平方即为K_res的对应最小残差。

此处两级carrier只是数学扩张，未被认作几何约束荷或真实局域装置。
允许改变裸source、真正含源初始列或不同物理代数，需另行构造。

## 5. 有限块不是由UV条件唯一选出来的

本页R是“包括零模在内的全部模式都减B”的明确选择。
UV发散只强制处理高模；零模本来有限。
例如
\[
 R_\lambda(q)=R(q)+\lambda B_{i,zero}(q)
\]
对任意有限实λ仍有相同高模尾和compact interior压力弱式，
但有限协方差、C混合块及K_res会改变。
λ=1时恢复zero压力仅含P²，所选fullmode R的αQ/D资源成本消失。

因此PREPARED_READOUT的σ⁻²成本及D3是该候选的结果，
不是所有UV合法初始规则的普遍下界。
这份非唯一性说明必须由同一总作用量、初始态和真实准备选择有限块，
不能由“噪声有限”自行决定物理理论。

下一步可以给一个含源有限列尝试修D3，
但必须同时验收它对全部测试的统一性、约束、对易结构、正常性与资源。
当前D6/D7已经排除了保持原裸source的独立carrier替代方案。

算符域补充：carrier 下界中的 H 先作用在原 source 支撑向量 u_j 上，L=Σp_j||(1−P)Hu_j||² 是这些向量上的正二次型。该证明不要求把所有无界算符乘积定义在整个 Hilbert 空间，也没有以有限方差替代自伴性证明。
