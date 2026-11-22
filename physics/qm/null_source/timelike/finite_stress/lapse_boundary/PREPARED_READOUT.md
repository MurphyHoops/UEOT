# 实际伴随读数、同源初片补偿与完整量子预算

本页接合ACTUAL_INVERSE与FINITE_SOURCE_DOMAIN：
对同一实际quiet-U历史构造一族统一的source-GNS弱读数，
给完整绝对方差、源荷混合块及两类截断误差。
这是一份含源边界补偿的候选线性化读数；
尚未证明该边界方案由正常几何联合态或真实准备装置产生。

## 1. 指定一个真正的固有钟读数

固定τ(η)=∫0^ηa(s)ds及同一初片钟原点。
对g∈C∞_c((0,τ(T)))，测量膨胀的线性化测试
\[
 O_g=\delta\int g(\tau)H_{\rm phys}(\tau)d\tau
     =-\int g'(\tau)w_\tau(\tau)d\tau ,
\quad
 w_\tau=w-{h\over a}\int_0^\eta aw .
\]
换回η并交换有界积分，
\[
 O_g=\int_0^T F_g(\eta)w(\eta)d\eta,\quad
 F_g=-a\,g'(\tau)+a\int_\eta^T h(s)g'(\tau(s))ds.     \tag{P1}
\]
F_g在未来端附近为零，但一般不在初片附近为零；
不能误称F_g∈C∞_c((0,T))。它属于本页所需的L²测试类。

压力方程L_Uw=f的物质force为f=−a²ξ_p。
记q_a=Ghat_U^*F，k_F=M_U^*q_a。
真正作用于raw压力的测试是
\[
 \boxed{q_F=-a^2k_F=-a^2M_U^*\widehat G_U^*F.}       \tag{P2}
\]
不能漏掉−a²，也不能将固定共形时间测试当成固有钟测试。

## 2. 已证明的伴随正则性及误差

以Y_-=L²(e^{+2γη}dη)定义反向权重，
||q||H3,-为0…3阶导数Y_-范数的和。
ACTUAL_INVERSE独立advanced证明给q_a∈H4、末端0…3阶迹为零。

当ε≤.1，e^U和e^{2U}的0…3导数≤2，
h e^U的0…3导数≤4ε。Hardy与Leibniz给
||M_U^*q||H3,-≤(12+192ε)||q||H3,-<32||q||H3,-。
a²的乘法范数≤12A²。因此
\[
 \|q_F\|_{H^3,-}\le
 {768A^2M_0\over\gamma(1-q_{\rm inv})}\|F\|_{Y_-},
 \qquad q_F(T)=q_F'(T)=q_F''(T)=0.                 \tag{P3}
\]
初片q_F(0),q_F′(0)一般不为零。

若Ghat的Neumann级数截到m阶，所得q_F^[m]满足相同末端迹，
且P3右侧再乘q_inv^{m+1}即为H3误差上界。
转换成未加权输入范数时必须保留||F||Y_-≤e^{γT}||F||L²；
小q_inv不是小几何波动。

## 3. 合法的同源组合，不要求尖片块单独存在

对任意实q∈H²(I)，q(T)=q′(T)=0，置
\[
 w_q={q\over3V_0a^4},\quad
 r_q=w_q''+3hw_q'+Vw_q.
\]
同一finiteK恒等式给
\[
 R_K(q):=\int q\,\delta p_K-B_{i,K}(q)
       =\int[r_q\,\delta Q_K+w_q\,\delta H_{0,K}],
                                                               \tag{P4}
\]
其中B_i,K为FINITE_SOURCE_DOMAIN U6，i=0。
若不要求末端双零，必须另保留末端边界，不能直接用P4。

ACTUAL_INVERSE的全k Jost界，μJ=Σ0³||V^(j)||L¹≤.1，
给Q和H0的pair envelope
\[
 Q_k^{pair}=e^{-2i\omega\eta}[1/(4\omega)+O(\mu_J/\omega^2)],
\]
\[
 H_{0,k}^{pair}=e^{-2i\omega\eta}[V/(4\omega)+O(\mu_J/\omega^2)] .
\]
两个余项共同可取C_I=10μJ：
Q余项≤1.5μJ/ω²；H0余项≤(4+.5μJ+4μJ/ω)μJ/ω²<4.5μJ/ω²。
所以
\[
 \beta_k[q]={\widehat a_q(2\omega_k)\over4\omega_k}+e_k,
 \quad a_q=r_q+Vw_q,\quad
 |e_k|\le{C_I(\|r_q\|_1+\|w_q\|_1)\over\omega_k^2}.   \tag{P5}
\]

频率Ωk=2√(k²−1)间距>2。中心化I以后，
每个互不重叠的[Ωk−1,Ωk+1]使用
|A(Ωk)|²≤∫|A|²+2∫|A′|²，Plancherel给
\[
 \sum_k|\widehat f(\Omega_k)|^2
 \le2\pi(1+T^2/2)\|f\|_2^2.                        \tag{P6}
\]
于是实际高模真空完整方差满足
\[
 \operatorname{Var}_{high}R(q)\le
 {9\pi\over8}(1+T^2/2)\|a_q\|_2^2
 +8C_I^2(\|r_q\|_1+\|w_q\|_1)^2.                   \tag{P7}
\]
使用了k²/ω²≤9/8及Σk≥3k²/ω⁴<1。

低模是原正常smooth径向包及有限粒子壳，所有Q²,D,P²二阶矩有限；
第7节给完整积分。三角界保留zero–shell相关：
\[
 \operatorname{Var}_{low}R(q)
 \le(M_{Q,low}\|r_q\|_1+M_{H,low}\|w_q\|_1)^2,
\]
其中M_Qlow、M_Hlow为同一态上δQlow、δH0low的区间sup GNS范数。
它们由第7节有限profile积分与实际低mode连续性计算，不被假定很小。

因此P4在真实source-GNS中收敛，定义连续线性映射
R:H²_terminal→L²(ρ_±)。
全过程先在共同K合并，再取极限；Q_i,D_i或B_i不需要单独具有全场二阶矩。

## 4. 模数尾有显式 O(1/K) 方差界

P3使实际q_F∈H³且末端三迹为零，故a_q∈H¹、a_q(T)=0。
一次分部积分与P6给
\[
 \sum_{k>K}|\widehat a_q(\Omega_k)|^2
 \le {|a_q(0)|^2\over2K}
 +{\pi(1+T^2/2)\over\omega_{K+1}^2}\|a_q'\|_2^2 .
\]
这里Σk>K(k²−1)⁻¹=½(K⁻¹+(K+1)⁻¹)<1/K。
以P5拆square，K≥2的实际正尾精确受控：
\[
\boxed{\begin{split}
 {\cal T}_K(q):=\operatorname{Var}(R-R_K)
 \le{}&{9|a_q(0)|^2\over32K}
 +{9\pi(1+T^2/2)\over16\omega_{K+1}^2}\|a_q'\|_2^2\\
 &+{81C_I^2\over8K}(\|r_q\|_1+\|w_q\|_1)^2 .
\end{split}}                                                     \tag{P8}
\]
高壳输出与保留壳正交，所以这是非负variance tail。
H²有界球本身没有被误说成统一小尾；这里用到了实际adjoint的H³控制。

若C_R为P7和低模积分给出的H²→GNS范数，
有限m、K的总误差满足
\[
 \|R(q_F)-R_K(q_F^{[m]})\|_2
 \le C_R\|q_F-q_F^{[m]}\|_{H^2}
       +\sqrt{{\cal T}_K(q_F^{[m]})}.              \tag{P9}
\]
方差误差可由2||R_K||₂ times右侧加右侧平方控制。
这给可验收的解析误差，不声称已经算出了数值几何方差。

## 5. 整族一致的压力弱解与边界候选

定义GNS向量值线性泛函
\[
 {\cal W}(F)=R(-a^2G_U^*F).
\]
它对所有测试F使用同一映射，协方差正性由原source态继承。
对φ∈C∞_c((0,T))，令F=L_U^*φ。
共同graph上的inverse/transpose恒等式给G_U^*F=φ，
q=−a²φ初片双零，故
\[
 {\cal W}(L_U^*\phi)=\xi_p(-a^2\phi).                \tag{P10}
\]
这是实际source Hilbert空间中的齐次压力方程弱解。

它尚不是几何—物质联合量子理论。
特别地，一般解应写w=w_B+G_U(−a²ξp)，而本构造要求
\[
 \langle F,w_B\rangle=-B_i(q_F)
\]
这一个统一的含源边界规则。
不能将初始荷的affine列喂给零初值Ghat后，声称真实非零初始约束已解决。

这个规则可写成对全部F共同的弱列。
定义v0,v1的测试配对
〈F,v0〉=(G_U^*F)(0)，〈F,v1〉=(G_U^*F)′(0)；
P3的trace连续性保证其存在，无需假设点态Green核。
于是
\[
 w_B^{cand}={-v_0\delta D_i+(v_1+h_iv_0)\delta Q_i
                  \over3V_0a_i^2}.                \tag{P11}
\]
finiteK可读作Green初端核及其导数；
全场只验收P4/P10的组合，P11单块仍可能无L²极限。
密度/平滑荷、物理对易关系、正常joint或约束后物理内积仍需独立构造。

## 6. incoming零模相位必须固定

令mathcal I′=a⁻²，积分常数由同一incoming态固定。
原canonical零模满足q_j=a(Q_j+mathcal I P_j)。
不得免费令mathcal I_i=0并继续声称原real packet不变。

记mathsf Q=ΣQ_j²，mathsf D=½Σ{Q_j,P_j}，mathsf P=ΣP_j²。
P4的零模块为中心化的
T0=αQ mathsf Q+αD mathsf D+αP mathsf P，其中
\[
 \alpha_Q=\tfrac12\int[r_qa^2+w_q(ah)^2],
\quad
 \alpha_D=\int[r_qa^2\mathcal I+w_qah(ah\mathcal I+a^{-1})],
\]
\[
 \alpha_P=\tfrac12\int[r_qa^2\mathcal I^2+
                       w_q(ah\mathcal I+a^{-1})^2].
\]
它们等价于实际初端表达
\[
 \alpha_Q=-{q_i'-3h_iq_i\over6V_0a_i^2},\quad
 \alpha_D={q_i-a_i^2\mathcal I_i(q_i'-3h_iq_i)\over3V_0a_i^4},
\]
\[
 \alpha_P=\int{q\over2V_0a^6}
               +\mathcal I_i\alpha_D-\mathcal I_i^2\alpha_Q.    \tag{P12}
\]
这些是给定实际q的系数，不是可自由选择的装置参数。

## 7. 当前正常薄层态上的完整绝对方差

原实、偶、归一profile记varpi(x)，J=∫|varpi′|²，
e=e_N+σx。定义
\[
 d_q=\int[r_q|v_2|^2+w_q(|v_2'|^2+\omega_2^2|v_2|^2)],
\quad
 \beta_k[q]=\tfrac12\int[r_qv_k^2+w_q(v_k'^2+\omega_k^2v_k^2)].
\]
令L_q=αQ J/(A³σ²)+αP A³，μ_N=2e_N L_q，
\[
 {\mathscr R}_N=-{2\alpha_Q\over A^3}
       ({\varpi'\over\sigma}+{e\varpi''\over\sigma^2})
           +2\alpha_PA^3 e\varpi,\qquad
 {\mathscr D}_N=\varpi+2e\varpi'/\sigma,
\]
\[
 {\cal V}_N(q)=\int({\mathscr R}_N-\mu_N\varpi)^2dx
                        +\alpha_D^2\int{\mathscr D}_N^2dx .
\]
完整绝对式为
\[
\boxed{\begin{split}
 \operatorname{Var}_\pm R(q)={}&(1-p){\cal V}_0+p{\cal V}_2
 +4p(1-p)(d_q-2\varepsilon_2L_q)^2\\
 &+[16+(24\pm16)p]|\beta_2[q]|^2
 +\sum_{k\ge3}4k^2|\beta_k[q]|^2 .
\end{split}}                                                     \tag{P13}
\]
zero–shell相关就在between-branch平方中，没有独立化；
pair与number/zero交叉按粒子数grading为零。

所需canonical资源也有直接有限积分：
||mathsf Q ψ_N||²=4/A⁶∫(varpi′/σ+e varpi″/σ²)²，
||mathsf D ψ_N||²=∫mathscr D_N²，
||mathsf P ψ_N||²=4A⁶(e_N²+σ²μ2)。
这验证第3节低模常数的有限性，并保留σ窄化的实际代价。

对两个候选的同一个actual q_F，
\[
 \Delta\operatorname{Var}R(q_F)=32p|\beta_2[q_F]|^2.  \tag{P14}
\]
允许β2为零。尚未用此恒等式声称每个固有钟测试都能区分两态；
严格信号还需一个具体g及非零矩阵元证明。

## 8. 新的源荷混合块及旧不确定性原则的应用

αs=2/(3V0A)，C=αs(H_z+ε2 N−E*)，
VarC=αs²σ²μ2。定义J2=∫x²|varpi′|²。
径向分部积分给当前完整态的精确弱混合块
\[
 \langle C R(q)\rangle
 =\alpha_s\left[
 {\alpha_Q(2J_2-1)\over A^3}
       +2\alpha_PA^3\sigma^2\mu_2
       -i\alpha_D E_z\right].                      \tag{P15}
\]
C和R均已中心化。实部是sym covariance，虚部对应
〈[C,R]〉=−2iαsαD Ez。
该式不同于只含未来derivative stress的旧C混合列。

Cρ^{1/2}与R_Kρ^{1/2}的Hilbert–Schmidt弱极限足够；
没有要求未证明的CR强算符域。
Cauchy–Schwarz给
\[
 \operatorname{Var}R(q)\ge
 {\,\alpha_D^2E_z^2+
 [\alpha_Q(2J_2-1)/A^3+2\alpha_PA^3\sigma^2\mu_2]^2
       \over\sigma^2\mu_2}.                        \tag{P16}
\]
特别地≥αD²Ez²/(σ²μ2)。
不确定性原理及旧BOUNDARY_STATE(79)的资源门是复用；
新增的是它在实际adjoint测试和固定incoming端点系数上的完整应用。
固定q且αD≠0时，缩σ反而增大这一canonical成本。
没有签收任意指定g都满足αD≠0，更不是所有引力装置的普遍下界。

R含Q,D，超出旧free derivative/stress观测代数。
21级记忆后的源态为m_j(C)ψ_N；其旧stress保持不能自动转用于P13/P15。
更换制备必须重算这些canonical初始块，不能删除装置及准备代价。

## 9. 当前关闭与下一门

已关闭：actual pressure inverse的伴随测试、统一source压力弱解、
共同初片组合的GNS正协方差、完整原态绝对预算、
Neumann误差和显式模数尾，以及新的C–readout混合块。

仍未关闭：同一正常物理准备是否产生P11并同时满足
C_geom−C_pre=C_source、全部动量约束和正确几何对易关系；
完整非齐次tensor反馈及固定AE匹配；装置总应力与校准。
本页没有用有限的候选读数替代这些独立条件。

## 明确的有限低模选择

本页 R 使用所有模（包括正常零模）的初端减除。FINITE_SOURCE_DOMAIN 的 UV 存在性只强制非零高模的组合，未唯一决定有限低模完成。可加入 λlow B_i,zero(q) 而保持高模极限和内部 pressure 弱行；λlow=1 会去掉本页 zero Q/D 端点成本，但也改变 C 混合块与 density 荷。见 CONSTRAINT_RESIDUAL §5。因此本页成本不是所有 UV 合法准备的共同下界；MIXED_BOUNDARY 中修复参数 λ 与这里的 λlow 不同。
