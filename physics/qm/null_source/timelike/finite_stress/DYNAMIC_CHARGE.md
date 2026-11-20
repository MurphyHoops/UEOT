# 真实非静态平均历史上的密度响应、全场平滑电荷与剩余边界条件

本页直接在 GEOMETRY_MATCHING 的真实非静态 U 上继续。
它是冻结完整 Ward 恒等式在已匹配平均解上的线性推论，并进一步
把原全场绝对源通过实际模式极限接到一个平滑的守恒电荷。
不是重新宣布旧全阶 mean 存在／排除定理。

结论是：h0>0 使密度响应一般非零，但它仍是压力响应的因果像，
没有新增独立的 incoming charge。原源的全场平滑电荷方差严格为正。
若保持 zero-charge 的原 incoming 几何响应域，则完整线性涨落方程
仍缺边界列。这里不否定已经成立的确定性平均解。

## 1. 在同一合法态运输上微分，而非只微分 Einstein 左边

背景 E[U]=S[U]=0、h=U'。对同 incoming 数据、同一重整化泛函
的允许几何变化 v，定义 e=DE_U[v]、s=DS_U[v]。
微分完整 E'+hE=2hS 得

\[
 e'+he=2hs.                                             \tag{119}
\]

背景乘以 delta h 的项因 E=S=0 消失；态运输、contact 与全部
实际 mean-RSET 已在 DE、DS 内。只保留 classical 2h delta h
不能替代 (119)。

对 positive-frequency Wiener incoming 域，积分常数为零，

\[
 e=J_Us,\qquad
 J_Us=2e^{-U}\Theta^{-1}(e^Uh s).                       \tag{120}
\]

在已证 ||U||E4≤rho=10^-25 的双圆盘，

\[
 \|J_U\|_{A\to A}
 \le \frac{2e^{2\rho}\rho}{s_*}<1.34\,10^{-25}.          \tag{121}
\]

这个小范数只适用于指定的正频系数 A 空间，不是实际振荡噪声分布
的范数，更不是 metric variance suppression 或探测器灵敏度界。

密度行并非仍恒零：校正域上 DS_U=L+DN(U) 可由
||T DN(U)||≤q=0.128<1 作 Neumann 逆。h 不恒零，正频解析代数
无零因子，故对非零可实现 s，J_Us 不恒零。
但 ker DS_U 仍包含于 ker DE_U；两行不提供独立的 incoming 电荷。

## 2. 完整绝对源必须服从同一 Ward

在该固定背景，用中心化全局密度／压力 fluctuation
xi_rho、xi_p，定义

\[
 d=\frac23a^2\xi_\rho,\qquad b=-a^2\xi_p.
\]

中心化守恒式 xi_rho'+3h(xi_rho+xi_p)=0 给

\[
 d'+hd=2hb.                                            \tag{122}
\]

声明的线性随机扩张（或相应算符二阶相容性）需要同时
e=d、s=b。若实际压力方程已解，R=d-e 满足

\[
 (e^U R)'=0.                                          \tag{123}
\]

在任意有限开时间窗，(123) 作为分布恒等式意味着 e^U R 是常数
分布。任意 chi in C_c^infinity(I)、integral chi=1 都给同一
Q_R=<e^U R,chi>，没有使用 sharp-slice stress trace。

只在有限窗中指定压力解并不能决定 Q_R；它必须来自实际过去或
新的合法边界数据。下节计算完整原 incoming 源的这一 charge，
并明确其与 zero-charge 几何响应域的比较范围。

## 3. 先共同截断，再对平滑组合取全场极限

沿同一个 U、同一态，只为证明引入共同 harmonic cutoff K。
中心化有限模应力 xi_rho,K、xi_p,K 满足精确逐模 KG 守恒；
重整化 c-number 的选择在中心化中消失。
这不是改变场的最终物理 cutoff，也不运行数值模式 ODE。

对有限 K，

\[
 C_K=e^U d_K
       -2\int_{-\infty}^{\eta}e^U h b_K\,d\eta'
     =\frac{2\,\delta H_{{\rm in},K}}{3V_0A}.          \tag{124}
\]

右边来自同一静态过去。H_in,K 是该有限模静态总场能量，
delta 表示减去该同一态的均值；任何 Casimir c-number 均消去。

取 chi 为当前正窗中的光滑单位积分测试，设
Psi_chi(s)=integral_s^infinity chi(eta)deta。则

\[
 C_K[\chi]
 =d_K(e^U\chi)-2b_K(e^Uh\Psi_\chi).                    \tag{125}
\]

第一测试紧支撑。第二测试及每个固定阶导数在过去指数衰减，
在未来紧支撑；其合法性要在本态实际证明，不能从“Hadamard”
一词直接推成任意非紧支测试均可用。

### 统一模式引理

实际轨道严格处于冻结 U 的原双圆盘内部。精确 Jost 模写作

\[
 v_k=e^{-i\omega_k\eta}F_k/\sqrt{2\omega_k},\qquad
 F_k=1+[\Theta(\Theta-2i\omega_k)]^{-1}(\mathcal VF_k),
 \quad \mathcal V=U''+(U')^2.
\]

所有非恒定频率 lambda≥s*>1.5，并有

\[
 |[\lambda(\lambda-2i\omega_k)]^{-1}|
 \le (2s_*\omega_k)^{-1}.
\]

冻结小球的 V 范数使 Neumann 逆一致有界。
更小但仍包含整条所用轨道的内部双圆盘允许 Cauchy 控制每个固定
阶导数。因此对任意固定 j，存在对 k 统一的有限 C_j，使过去

\[
 |\partial_\eta^j(F_k-1)|
 \le C_j e^{s_*\eta}/\omega_k;                         \tag{126}
\]

j≥1 时即为 F_k 的导数。C_j 依赖所选内域、高阶几何 jets，
不把它们错误设成 rho。

令 D_k=F_k'-hF_k。去掉 e^(-2i omega eta) 和共同光滑 a 因子的
density、pressure 的 aa pair 包络分别为

\[
 B_{\rho,k}=-iF_kD_k+\frac{D_k^2}{2\omega_k},
\qquad
 B_{p,k}=-\frac23\omega_kF_k^2-iF_kD_k
                            +\frac{D_k^2}{2\omega_k}. \tag{127}
\]

density 包络及所需低阶导数为 O(e^(s* eta))，
pressure 包络及每个所需固定阶导数为 O(omega_k)。
将实际测试函数和 a 因子一起纳入包络后，二者三阶导数的 L1
范数不超过 C_chi(1+omega_k)。过去的 h 因子与未来紧支撑使
全部边界项消失。对常相位三次分部积分给 pair 系数

\[
 |\beta_k[\chi]|\le C_\chi/\omega_k^2.                 \tag{128}
\]

这里 beta 是应力测试算符的 pair 系数，不是 FINITE_SLICE_UV 的
Bogoliubov beta。密度紧支测试也可用更好的二次积分界。

两场总简并为 2k²；高模 k>2 的 incoming 态是真空，中心化数目项
在该 GNS 向量上消失。pair 二阶范数尾由

\[
 \sum_{k>K} k^2/\omega_k^4=O(K^{-1})
\]

控制；例如 K≥2 时可用常数 8C_chi²/K 包围两场 pair 尾的平方。
零模与有限 k=2 壳使用已有有限四矩。因此 (125) 两项分别在本态
GNS L² 中收敛。非紧支压力测试由平滑过去 cutoff 的这一极限定义；
这是明示状态上的延拓，不宣称它是一般局域可观测代数中的紧支元素。

### 独立的全紧支测试表述

也可取固定光滑单位积分 g，令 g_T(eta)=g(eta+T)，并设

\[
 \psi_T(\eta)=\int_{-\infty}^{\eta}(g_T-f)\,ds.
\]

对每个有限 T，psi_T 光滑紧支撑。全场分布 Ward 给

\[
 d(e^Uf)-2b(e^Uh\psi_T)=d(e^Ug_T).                    \tag{129}
\]

(126)-(127) 对平移过去的 density 测试作两次分部积分，给高模
pair 系数 O(e^(-s*T)/omega²)；低模有限四矩部分也趋于静态过去。
故右边在 GNS L² 中趋于 2 delta H_in/(3V0 A)。
这提供 (125) 的相同极限，不需要单独定义任何非静态瞬时应力方差。

## 4. 得到的是真实全场电荷，不是新背景的瞬时 N00

原输入仅零模和 k=2 壳有非真空激发。中心化 H_in,K 在该态
GNS L² 中对 K≥2 已经稳定。因此可在 (124)-(125) 取极限，

\[
 \boxed{C[\chi]=C_{\rm in}
       =\frac{2\,\delta H_{\rm in}}{3V_0A}},
\quad
 \operatorname{Var}C_{\rm in}
       =\frac49A^4 N_{00,{\rm in}}>0.                 \tag{130}
\]

C[chi] 与选择的单位积分 chi 无关。这个有限二阶矩保留了两个
同一源测试量的实际交叉协方差：Var(x-y)=Var x+Var y-2Cov_sym(x,y)。
它不能在把 density 和 pressure 另行设为独立噪声后继续成立。
N00,in 仅指冻结静态过去的密度方差；没有把它代入非静态 sharp
N00。本页计算的是一个由整个合法过去和正窗应力构成的平滑组合，
不是完整非静态 tensor noise kernel。

新区间检查把原输入 charge RMS 包围在 0.1007 与 0.1008 之间。
它是无量纲 constraint charge 的标准差，既不是度规百分误差，
也不是实验记录。


### 同一 mean-history 上的薄层源

BOUNDARY_STATE 已证明，在同一 minimal massless incoming 输运中，
应力微分消去零模常量 Q，两个场的总 P² 矩与高模二次矩保持相同，
零／高二次交叉为零。因此新 annulus 两态各自的实际 incoming 输运
也能搭配同一个 U，保持原总 mean-RSET；这不表示保持旧完整裸态。

其高 k>2 仍为真空，低模四矩有限，故上述 L² 证明逐项适用。
静态过去 H_in=constant+sigma X、Var X=mu2>0，给

\[
 \operatorname{Var}C_{\rm thin}
 =\frac{4\sigma^2\mu_2}{9V_0^2A^2}>0
 \quad(\sigma>0).
\]

例子 sigma=sqrt(3)/(100A)、mu2<1/3 时，

\[
 \operatorname{RMS}C_{\rm thin}
 <\frac{1}{150V_0A^2}<5.057\,10^{-14}.
\]

这是此新实际动态源的 conserved charge 上界，仍不为零；
它没有构造 geometry/device 共同初态，也未越过
TOTAL_BOUNDARY_GATE 的原完整装置守能条件。

### 非静态瞬时密度方差确实发散

(126) 给 F_k→1、F'_k=O(omega_k^-1)。在任一 h(eta)≠0 的
固定片，实际 density 的每个实振子 creation 系数为

\[
 {\cal B}_{\rho,k}
 =\frac{e^{-2i\omega_k\eta}}{2V_0a^4}
   \left(ih+O(\omega_k^{-1})\right).
\]

真空每振子贡献 2|B|²，两场共有 2k² 个振子，因此

\[
 \lim_{k\to\infty}
 \frac{\operatorname{Var}_{k}(\bar\rho)}{k^2}
 =\frac{h^2}{V_0^2a^8}>0,\qquad
 \lim_{K\to\infty}
 \frac{\operatorname{Var}(\bar\rho_K)}{K^3}
 =\frac{h^2}{3V_0^2a^8}.                            \tag{130a}
\]

旧原源与新薄层源都具有这个相同的高频真空尾。
匹配初片 h0 严格非零，故该 sharp-time 观测量的二阶矩发散，
即使 h0 极小。c-number RSET 减项无法改变 connected 方差。
这只涉及所声明态及该瞬时空间平均观测量，不否定 Hadamard
mean-RSET 存在，也不否定 (125) 的平滑组合有限。

## 5. 同 incoming 的线性完整约束仍不闭合

对保持 zero-incoming-charge 的几何响应，(125) 的对应组合为零。
若同时要求压力响应在整个声明的过去及正窗上服从 s=b，
则有限模恒等式与本页共同极限给

\[
 d-e=e^{-U}C_{\rm in}.                               \tag{131}
\]

完整密度方程要求右边为零，与 (130) 的严格正方差不相容。
因此“改成 h0>0 就已经修好绝对密度约束”的出口被排除。

任意非负光滑 f 支撑于当前正窗、integral f=1，残差满足

\[
 \operatorname{RMS}[(d-e)(f)]
 =\left(\int f e^{-U}\right)
   \sqrt{\operatorname{Var}C_{\rm in}}
 \ge e^{-\rho}\sqrt{\operatorname{Var}C_{\rm in}}>0.1007.
                                                               \tag{132}
\]

相应物理密度残差为 (3/(2a²))(e-d)=-delta H_in/(V0 a³)，
其平滑方差是 Var H_in/V0² 乘以 [integral f a^(-3)]²。
这是压力匹配之后留下的 charge 残差，不是新源瞬时噪声。
压力方程尚未构造时，只能给联合 residual charge，不可报无条件
的 density-alone floor。

该界以 pressure 方程及上述 incoming charge 条件为前提，
没有用 (121) 给粗糙噪声作范数控制。如果仅在有限片重新开始，
或者实际制备在过去改变完整源／装置／几何边界条件，则应保留
新的 C_boundary；那是需要构造的另一合同，不受“旧charge=0”
假设自动覆盖。

(130)-(132) 是对声明线性涨落扩张的必要二阶相容性检验，
不需要 Gaussian 噪声假定，也不是所有量子引力理论的否定。
已经通过的确定性 mean-SCE 历史保持有效。

## 6. 下一项必须增加的实际对象

新有限初片几何／物质／装置对象应当提供与本态 charge 相匹配的
真实边界列及交叉协方差，并满足自身的量子不确定性、动量约束、
边界 Ward 与正则性。简单指定一个 classical 随机变量等于
C_in，尚未构造合法共同量子态或实际制备。

这一项已经把下一入口从“任意非静态几何”缩到可计算的 conserved
charge。当前全部非静态噪声核、局部空间模式、完整初始 CTP、
几何量子态、共同装置作用量与经验引力校准仍 OPEN。
