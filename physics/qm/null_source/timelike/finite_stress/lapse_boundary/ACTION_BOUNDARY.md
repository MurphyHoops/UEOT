# 保留 lapse 的作用量、初始核与边界约束映射

## 1. 结论与实际范围

在原两场、同一密度与同一几何历史上，已知的 canonical 端点项不提供新的物理约束列。本页先证明有限共同模式截止上的完整恒等式：作用量、初始 cross kernel、末端配对以及它们的一、二阶变分必须一起运输。随后才能使用 ENDPOINT_DOMAIN 的全场平滑极限。单独把一个含源的 canonical 动量称为新几何荷，会改变原问题。

这完成的是端点候选的分类与原齐次 lapse 入口。它没有构造完整协变重整化 tensor CTP、量子几何态或所有 momentum constraints。特别是已有 AE 的完整齐次 mean-RSET，不等于已经给出了全部非齐次 in-in 泛函。

## 2. 同一原作用量和共同截止

取
\[
 ds^2=a^2(-N^2d\eta^2+d\Omega_3^2),\quad
 h=a'/a,\quad \kappa=h/N,\quad D=N^{-1}\partial_\eta .
\]
这里 N 是 conformal lapse；proper lapse 是 aN。N 在两条 CTP 支上分别保留，直到变分完成。V0=2π²。两场的完整实谐波截止集合记为 I_K，ω_k²=k²−1，k=1 为单独正常处理的零模。

有限截止物质作用量为
\[
 S_{m,K}=\frac12\sum_{r\in I_K}\int
 a^2[(\phi_r')^2/N-N\omega_r^2\phi_r^2]d\eta
 -V_0U_0\int Na^4d\eta .
\tag{L1}
\]
在原 G=2T 归一化，EH+GHY 的齐次骨架为
\[
 L_g=\frac{3V_0}{2}(-a'^2/N+Na^2).
\tag{L2}
\]
固定 AE μ=1 与已有有限项不变。以下等式的两边使用同一个几何局部项，因此其相消不依赖擅改重整化系数。L2 不被当作完整 AE 量子 Hamiltonian。

谐波截止保留齐次时间重参数化与完整 SO(4) 壳；没有声称它保留任意空间微分同胚的全部约束代数。

## 3. 精确分部积分与 Hamiltonian

令 q=aφ，X=q′−hq，Q_K=Σq²/2。逐模分部积分给
\[
 S_{\rm raw,K}=\frac12\int\sum_r[X_r^2/N-N\omega_r^2q_r^2]d\eta
 =S_{\rm bulk,K}-[\kappa Q_K]_i^f,
\]
\[
 S_{\rm bulk,K}
 =\frac12\int N\sum_r[(Dq_r)^2-(\omega_r^2-D\kappa-\kappa^2)q_r^2]d\eta .
\tag{L3}
\]
原 U0 项两边相同。raw p=X/N，bulk p_b=q′/N=p+κq。

在共同 Schwartz 核心上，以 Weyl 对称排序记
\[
 H_0=\tfrac12\sum(p^2+\omega^2q^2),\quad
 {\cal D}_K=\tfrac12\sum\{q,p\},
\]
\[
 H_{\rm raw}=NH_0+h{\cal D}_K,\qquad
 H_{\rm bulk}=NH_0-(\kappa'+N\kappa^2)Q_K.
\]
若 W=exp(−iκQ_K)，则 WpW†=p+κq，故
\[
 H_{\rm raw}=WH_{\rm bulk}W^\dagger+iW'W^\dagger .
\tag{L4}
\]
有限 Fock 矩阵截断不满足精确 CCR；本页的算符恒等式不以那种截断作为证明。

## 4. CTP 两支和末端配对

在有限截止，
\[
 U_{{\rm raw},\pm}=W_{f,\pm}U_{{\rm bulk},\pm}W_{i,\pm}^\dagger,\quad
 \rho_{{\rm raw},i}=W_{i,+}\rho_{{\rm bulk},i}W_{i,-}^\dagger .
\tag{L5}
\]
不同几何支上的 ρ_i 是 cross kernel；它通常不是一份单独的正密度。物理对角或实际联合对象才需满足正常性与正性。

让 J_f 显式表示由加支末端空间到减支末端空间的配对。则
\[
 {\cal F}_{\rm raw}
 =\operatorname{Tr}(J_{\rm raw}U_{{\rm raw},+}
           \rho_{{\rm raw},i}U_{{\rm raw},-}^\dagger)
 =\operatorname{Tr}(J_{\rm bulk}U_{{\rm bulk},+}
           \rho_{{\rm bulk},i}U_{{\rm bulk},-}^\dagger),
\]
\[
 J_{\rm bulk}=W_{f,-}^\dagger J_{\rm raw}W_{f,+}.
\tag{L6}
\]
若 raw 配对取 I，则 bulk 配对是 W_f,−†W_f,+。只有共同端点 frame 确实相同时它才是 I；只要求 a_f,+ = a_f,− 不够。也可从固定 bulk 配对出发运输 raw 配对。初始端点相位精确相消，末端剩余由 J 而非任意丢弃决定。

L6 对当前低模光滑包与有限高模真空的所有所需矩成立；在共同矩域内，其一阶、二阶和混合导数相同。不对任意 trace-class 核无条件交换无界微分与迹。

## 5. 不能删掉的 contact 项

固定 a,q 历史，对 lapse 方向 f,g：
\[
 \delta_NS_{\rm raw}[f]
 =-\frac12\int\sum(X^2/N^2+\omega^2q^2)f,
\quad
 \delta_N^2S_{\rm raw}[f,g]
 =\int\sum X^2N^{-3}fg .
\tag{L7}
\]
这是 configuration-path 局部二次项。保持 q 而取 δu=v，还给
\[
 \delta_uS=-\int\sum Xq\,v'/N,\quad
 \delta_N\delta_uS[f,v]=\int\sum Xq\,fv'/N^2,\quad
 \delta_u^2S[v,w]=\int\sum q^2v'w'/N.
\tag{L8}
\]
固定 q 的 u 行不等于固定原 φ 的 metric variation；后者必须加入 q=aφ 的链式导数、测度和端点运输。只有 lapse 行在固定 a 时无此差别。

B=κQ 的相应边界导数是
\[
 B_N=-hQ/N^2,\quad B_{NN}=2hQ/N^3,\quad
 \delta_uB=Qv'/N,\quad \delta_N\delta_uB=-Qfv'/N^2.
\tag{L9}
\]
这些项与 L5、L6 的初始与末端导数一同保留。

phase-space Hamiltonian 对 N 线性，并不允许从 configuration 表达中删去 L7。动量 Gaussian 积分及 equal-time contraction 重新分配接触项。若改用 j=g00，在固定 a 下
\[
 N_j=-1/(2a^2N),\quad N_{jj}=-1/(4a^4N^3),
\]
\[
 \Gamma_{jj}(t,s)=
 \frac{\Gamma_{NN}(t,s)}{4a(t)^2a(s)^2N(t)N(s)}
 -\frac{\Gamma_N(t)}{4a(t)^4N(t)^3}\delta(t-s).
\tag{L10}
\]
即使某一表示的裸 H_NN=0，后一个链式 contact 仍存在；完整总泛函 on-shell 可能另有相消，不能提前把物质项删掉。

一个区分错误实现的精确例子为 q=1+t、h=1+t²、N=1+ε(2+t)、ω²=3、0≤t≤1。端点 [hq²/(2N)] 的 Taylor 系数为 7/2, −11, 34。遗漏端点会造成 raw−bulk 的一阶导数差 11、二阶导数差 −68，而不是可忽略的小误差。

## 6. 真正的初态运输与纯端点连接分开

对参数 α，定义
\[
 \nabla_\alpha\rho_{\rm raw}
 =\partial_\alpha\rho_{\rm raw}
   +i B_{+,\alpha}\rho_{\rm raw}
   -i\rho_{\rm raw}B_{-,\alpha}.
\]
因 Q 不依赖这些 frame 参数且彼此对易，
\[
 \nabla_\alpha\rho_{\rm raw}
 =W_+(\partial_\alpha\rho_{\rm bulk})W_-^\dagger,\quad
 \nabla_\alpha\nabla_\beta\rho_{\rm raw}
 =W_+(\partial_\alpha\partial_\beta\rho_{\rm bulk})W_-^\dagger .
\tag{L11}
\]
连接是 flat 的。展开的二阶式含 B_αβ、Q²ρ 与 QρQ；不能把其中一项另认作新物理初始相关块。

真实准备过去引起的剩余态变化没有消失。例如
\[
 \delta U(i,t_0)
 =-i\int_{t_0}^iU(i,s)\,\delta H(s)\,U(s,t_0)\,ds .
\tag{L12}
\]
二阶有有序双插入与 δ²H contact。它们由同一个实际过去固定。不同的 past metric、interaction 或输入密度属于新物理候选，需要单独验收。

## 7. 动量含源并不自动增加自由度

若几何本身也在配置空间，原正则一形式在 q=aφ 下变为
\[
 \Pi_u^{old}du+\sum\pi_\phi d\phi
   =(\Pi_u^{old}-\sum pq)du+\sum p\,dq.
\]
有限 M_K 个实模式的 Hilbert 映射
\[
 (T_a\Psi)(u,q)=a^{-M_K/2}\Psi(u,q/a)
\]
是酉的，且
\[
 T_a\Pi_u^{old}T_a^\dagger=P_u+{\cal D}_K.
\tag{L13}
\]
因此 EH 骨架的约束写成
\[
 {\cal C}_K=
 -\frac{(P_u+{\cal D}_K)^2}{6V_0a^2}
 -\frac{3V_0a^2}{2}+V_0U_0a^4+H_0,
\tag{L14}
\]
其中排序若由一个已给出的原算符运输，则必须保留该运输排序；L14 的经典式本身不是唯一量子化。原 AE 高阶项也必须同变换，不能省略。

任何已有自伴残差 R 以及正常态 ρ，在共同酉 V 下均满足
\[
 \operatorname{Tr}(V\rho V^\dagger)f(VRV^\dagger)
       =\operatorname{Tr}\rho f(R).
\tag{L15}
\]
完整残差谱、零谱投影及已存在的方差不变。固定薄层源的支撑投影与载体代数也应一起变换；其完整谱独立性因此保持。只改动量表达、不运输态与源/载体代数，不能绕过已有排除。

κ 含几何速度。把 bulk 中的 a″ 和 κ 擅自看作独立装置坐标，会改变相空间及约束，需要另立作用量。

原 scalar momentum row 是 πφ∂iφ。齐次 a 上它成为 p_raw∂iq；剪切后是 p_b∂iq−κ∂i(q²)/2（按所选密度测度写）。Killing/divergence-free shift 的后一项积分为零；一般 shift 仍需保留它。这里不把平均动量为零当作所有量子动量约束已解。

## 8. 有限截止之后的实际出口

ENDPOINT_DOMAIN 证明 Q_K 的中心化方差为 K/4+O(1)，W_K 也无所述 Fock 空间的强极限。正确顺序是 L6 在每个有限 K 先完整组合相消，再对已经合法的平滑应力组合取极限。已有 DYNAMIC_CHARGE 的平滑守恒荷于是保持；它没有凭空增加一个可抵消源荷的物理边界项。

本候选裁决：纯端点 canonical dressing 不补齐 C_geom−C_pre=C_source。真正初始几何荷、实际含源准备过程、完整 tensor response/contact 与正常联合 Einstein-CTP 对象仍需构造。

标准文献只支持所采用的方法和边界：
Anderson–Molina-Paris–Mottola, https://arxiv.org/abs/gr-qc/0209075；
Hollands–Wald, https://arxiv.org/abs/gr-qc/0404074；
Hu–Roura–Verdaguer, https://arxiv.org/abs/gr-qc/0402029。
它们不替本页证明当前具体模型，也不提供本项目缺失的联合态。

## 9. 从作用量还原实际密度／压力约束行

先对 interior 或 compact-support variation 写 bulk 行。保留同一物质演化、U0、局部项与实际态运输，令
\[
 E_N=1+\kappa^2-\frac23a^2\rho,\quad
 S_N=D\kappa+\frac{1+\kappa^2}{2}+a^2p .
\]
有限截止总作用量直接给
\[
 \Gamma_N=\frac{3V_0a^2}{2}E_N,\qquad
 \Gamma_u|_N=3V_0Na^2(S_N+E_N/2).
\tag{L16}
\]
固定 proper lapse ℓ=aN 时，
\[
 \Gamma_u|_\ell=\Gamma_u|_N-N\Gamma_N=3V_0Na^2S_N.
\]
因此不能先把 N 固定为一，再从 pressure 方程猜测独立 density 行。Hamiltonian constraint 的号为 C_K=−Γ_N；这与 L14 一致。

时间微分同胚取 δu=hf、δN=(Nf)′。对 anchored f，完整同态 Ward 的 bulk 部分为
\[
 h\Gamma_u-N(\Gamma_N)'=0
 \quad\Longleftrightarrow\quad
 E_N'+hE_N=2hS_N.
\tag{L17}
\]
on-shell 一阶式为 δΓ_N=(3V0a²/2)e、δΓ_u=3V0Na²(s+e/2)，并有 e′+he=2hs。原 AE 极限的这一齐次 Ward 复用已证同处方结果；没有据此宣布全部 tensor Hessian 已重整化。

若变分触及初片，完整分布导数另有 L5–L12 的 density、embedding 和配对项。分部积分产生的 [NΓ_N f] 也须与这些端点责任一起处理。非 anchored 的时间平移不是免费的新约束荷。

在物理 φ 固定的变量上，还可给一个直接的 finite-K metric 接口。N=1 时令 T_K=Σa²φ′²/2、G_K=Σa²ω²φ²/2、U=V0a⁴U0，則
\[
 S_{NN}=2T_K,\quad S_{Nu}=-2(T_K+G_K)-4U,\quad
 S_{uu}=4(T_K-G_K)-16U .
\tag{L18}
\]
各式乘同一时间 delta。它们不同于固定 q 的 L8。这些裸局部量的全场极限必须与 retarded loop 及同一反项组合，不能用重整化的 ρ,p 随手替换裸量后声称已求得完整 Hessian。
