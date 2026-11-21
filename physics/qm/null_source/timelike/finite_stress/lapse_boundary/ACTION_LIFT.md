# 固定 AE 约定的有限模式 lapse action 代表与真实混合初始列

本页补齐一个明确的齐次作用量代表，保留 lapse 后变分。
它复现原有限 K 平均行、全部已声明 AE 局部项和初始边界势。
它不是由 FLRW 数据唯一恢复任意四维作用量，也没有指定未知的几何初态。

## 1. 不先固定 lapse 的完整代表

设 a=Ae^u，D=N^−1∂η，κ=Du，χ=Dκ，V=χ+κ²，
ell=ell0+2u，ell0=log(A²/4)+2γEuler，C=19+15ell。
用不同字体区分 harmonic number 与源算符：
\[
 {\mathfrak h}_K=\sum_{k=1}^K{1\over k},\qquad
 B_K=-{3\over4}-\sum_{k=2}^K\left({k\over2}+{1\over4k}\right),
\]
\[
 C_{{\rm rad},K}={3\over8}+
 \sum_{k=2}^K\left(k^3-{k\over2}-{1\over8k}\right),\quad
 c_{\rm an}={3\over40}+{\ell_0\over16}.
\]
取
\[
 L_{\rm an}={C\chi^2\over240}
 +{(C-29)\kappa^2\over120}
 +{(3C-59)\kappa^4\over720}+{u\over8}+c_{\rm an},
\]
\[
 L_{{\rm ct},K}=B_K V-{{\mathfrak h}_K V^2\over8}
                     +L_{\rm an}+C_{{\rm rad},K}.              \tag{L1}
\]
同一 homogeneous lapse 代表是
\[
 S_K=\int d\eta\left\{
 {3V_0\over2}\left(-{a'^2\over N}+Na^2\right)
 +{1\over2}\sum_{r\in{\cal I}_K}a^2
       \left({\phi_r'^2\over N}-N\omega_r^2\phi_r^2\right)
 -NV_0U_0a^4+N L_{{\rm ct},K}\right\}.                        \tag{L2}
\]
I_K 含两个场全部 k≤K 模，包括正常零模。
ρz 和 k=2 非 Gaussian 占据来自同一量子 density 的 field expectation，
不能在 L2 外再加一份经典 ρz 以免双算。

CTP 使用 S_K[+]−S_K[−]，两支 lapse 独立保留到变分之后，
初始 density 与末端 gluing 按 ACTION_BOUNDARY 同时运输。
只写 bulk L2 不等于已经给出完整联合初态。

## 2. 同一反项同时复现两行，不能只匹配 pressure

在 N=1 写 h=u'，u_j=u^(j)。原冻结 AE 表达化简为
\[
 t_{\rm an}=-{1\over32}-{Cu_4\over480}
 +{(C-29)u_2\over240}+{(3C-59)h^2u_2\over240}
 +{h^2\over16}-{hu_3\over8}-{3u_2^2\over32}+{3h^4\over32},
\]
\[
 4r_{\rm an}=-{Chu_3\over120}+{Cu_2^2\over240}
 +{(C-29)h^2\over120}+{(3C-59)h^4\over240}
 -{h^2u_2\over4}+{1-C\over240}.                             \tag{L3}
\]
直接 Euler–Lagrange 与 Ostrogradsky 计算给
\[
 {\cal E}_uL_{\rm an}=-4t_{\rm an},\qquad
 {\cal H}_{\rm an}=4r_{\rm an}.
\]
对 L_Q=B_KV−mathfrak h_K V²/8，
\[
 {\cal E}_uL_Q=D_u^\dagger
       (B_K-\mathfrak h_KV/4),\quad
 {\cal H}_Q=B_Kh^2-\mathfrak h_K C_e,
\quad C_e={V^2\over8}+{h^2V\over4}-{hV'\over4}.
\]
常数 L_rad 的 Hamiltonian 是 −C_rad。于是
\[
 \rho_{{\rm ct},K}=
 {B_Kh^2-\mathfrak h_K C_e+4r_{\rm an}-C_{{\rm rad},K}
       \over V_0a^4}.                                       \tag{L4}
\]
L3–L4 同时复现有限 k 减项、k=1 reference 和 AE 行。
脚本检查两条恒等式及所有低阶项，不只检查四阶主系数。

## 3. 边界势及 lapse 导数

对 ∫N L(u,κ,χ)，取
\[
 P_\kappa={\partial L\over\partial\chi},\quad
 P_u={\partial L\over\partial\kappa}-D P_\kappa,\quad
 \Theta=P_u\delta u+P_\kappa\delta\kappa,\quad
 \delta\kappa=N^{-1}\delta u'-\kappa\delta N/N.
\]
同一 variation 的 lapse bulk 列为
Γ_N=−(κP_u+χPκ−L)；端点仍保留 Θ。
在 L1 中
\[
 P_\kappa=B_K-\mathfrak h_KV/4+C\chi/120,
\]
\[
 P_u=2\kappa(B_K-\mathfrak h_KV/4)
 +(C-29)\kappa/60+(3C-59)\kappa^3/180-DP_\kappa.                \tag{L5}
\]
B_K V 含显式端点 [B_Kκ]；换代表时必须同步改变 Θ 和初始 kernel。
对 matter 作 q=aφ 后还保留 −[κQ_K]。
bulk matter 的 Pκ=Q_K 与这个端点相消，不能当作额外几何载体。

## 4. 有限 K lapse 行强制的源混合列

最高局部 Hessian 是
\[
 M_K={C\over120}-{\mathfrak h_K\over4}
       =3V_0a^2\gamma_{4,K}.                                \tag{L6}
\]
在 γ4,K≠0 的有限截断，v0,K=Gp,K(t,i) 的初始 jets 是
(0,0,0,1/γ4,K)，原 incoming mode variation 为零。
密度主系数为 2hγ4,K，故 E_K v0,K(i)=2h_i。
v1,K=∂i Gp,K(t,i) 同理给 E_K v1,K(i)=2V_i；
有限 K Ward defect 在此步乘上 v0,K'(i)=0，不能漏掉后续 defect。

原 fullmode 初端减除产生
\[
 w_{B,K}={-v_{0,K}\delta D_i+
             (v_{1,K}+h_iv_{0,K})\delta Q_i\over3V_0a_i^2},
\]
其初始密度为
2[−h_iδD_i+(V_i+h_i²)δQ_i]/(3V0a_i²)。
原 lapse 源要求
2[δH0,i−h_iδD_i+h_i²δQ_i]/(3V0a_i²)。
差正是
\[
 {2\over3V_0a_i^2}\delta(H_{0,K}-V_iQ_K)_i
 ={2H_{i,K}\over3V_0a_i^2}.                                 \tag{L7}
\]
所以保留同一低阶初值、用 v0,K 修复这一 charge 时，必须加
\[
 {H_{i,K}\over3V_0a_i^2h_i}\,v_{0,K}.                         \tag{L8}
\]
同一 action 的初始动量改变为
δP_u=−M_K δu'''=−H_i,K/h_i，
因此 L8 就是
\[
 \boxed{h_i\delta P_u+H_{i,K}=0}.                            \tag{L9}
\]
这里是真实所需的动量–源相关，不是 q=aφ 引起的 D 坐标重命名。
给定当前边界减除、固定前三 jets 且只用 v0 列时系数唯一；
其他零 charge 齐次初值并未排除。

## 5. 全场和物理状态的严格边界

有限 K 后续仍满足
(e_K−d_K)'+h(e_K−d_K)=w_K'(2S_K−E_K)。
故 L7 的初端匹配不能证明全窗 finite-K constraints，
更不能在没有 uniform w_K 界时宣称 Gp,K→Gp。

MIXED_BOUNDARY 使用已独立构造的 full-field Gp 及同源 H_i 的 L² 极限，
得到两条 full-field transpose 弱行；这是另一条明示的极限路线。
L9 提供作用量初始列来源，却不自动生成正常 geometry–matter 联合态。
固定 AE homogeneous lift、一般四维协变 action、物理约束 Hilbert 空间、
真实 preparation 与局域仪器，仍须分别验收。

## 6. 同一作用量的完整有限 K canonical constraint

写 g_K=C/120−mathfrak h_K/4，A_K=B_K−mathfrak h_Kκ²/4，
L_ct=g_Kχ²/2+A_Kχ+L_ct,0，L_g=3V0a²(1−κ²)/2。
保留 bulk q 变量时 Pκ=g_Kχ+A_K+Q，p=Dq，故
\[
 {\cal C}_K=\kappa P_u+{(P_\kappa-Q-A_K)^2\over2g_K}
 +H_0-\kappa^2Q+V_0a^4U_0-L_g-L_{{\rm ct},0}.
\]
端点 −[κQ] 对应 Pκ,raw=Pκ−Q、p_raw=p−κq。
于是等价 raw 形式的平方项为 (Pκ,raw−A_K)²/(2g_K)，
源项变成 H0,raw+κD_raw。显式 Pκ−Q 是已知 canonical 端点重写，
不能因式子混合就宣称已产生新的物理相关。
此式把下一对象落实成原 action 的约束数据；ordering、domain、物理内积和正常准备尚待指定。
