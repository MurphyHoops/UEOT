# 同一完整场态的局域仪器反作用

取 A_f=phi(f)，f 为实光滑紧支撑测试，理想 Gaussian 指针耦合
U=exp(-ig A_f Pi)。时间有序线性场耦合的 Magnus 展开只多一个 c-number
乘 Pi^2 的相位，因为自由场交换子为 c-number。该相位必须校准/补偿，
不能省略后仍声称 minimum-resolution instrument。

令 s=g^2 Var Pi=1/(4vm)。非选择场通道是 Gaussian 分布的 coherent shift。
在真正的 out-region，u=E f=E_ret f；相互作用期间须使用 retarded 响应，
不能用 E f 声称修改了过去。

## 1. 平均应力与完整噪声

T[phi+xi u]=T[phi]+xi L+xi^2 C，
L=T[phi+u]-T[phi]-T[u]，C=T[u]。

xi 为均值0、方差 s 的 Gaussian。固定 AE 几何 c-number 项相消，得到

Delta <T_ab>=s T_ab[u]，

N_out=N_in+s <{L,L}/2>+2s^2 C tensor C。

这里 L 的二阶矩**不能**改成中心化 Cov(L,L)，否则会漏掉原态非零一阶场的贡献。
公式适用于分离点的双分布或合法光滑时空涂抹，不把点上噪声当普通有限函数。
两点函数仅增加 s u tensor u，故原 Hadamard 奇性保持；
全部高模与交叉项已包含在完整 u 和 L 中。

若 A_f 的零模部分为 alpha_f Q+beta_f P，则
P_out=P-g alpha_f Pi，Delta<S0>=alpha_f^2/(4C vm)。
alpha_f=0 的局域 derivative test 精确保留源谱，但仍可激发高模。
两独立指针分别作用两个场时，把上述各自的反作用相加，不能重复计算共享指针的关联。

## 2. 为什么 out-field 应力不等于全装置应力

对普通双场局域耦合
L_int=-lambda chi(x) phi psi，mostly-plus 约定给
T_int,ab=-lambda chi phi psi g_ab。使用两场 EOM，

nabla^a(T_phi+T_psi+T_int)_ab=-lambda phi psi partial_b chi。

外指定切换函数 chi 不是免费守恒源；控制器必须提供相反项。
把 chi 改成动力学场时，须同时给其作用量、态、EOM 与重整化应力，
不能只给它取名就认为 Bianchi 闭合。

有限场 instrument 的背景见 Fewster–Verch, arXiv:1810.06512；
Mandrysch–Navascues, arXiv:2411.13605v2 的 Gaussian 仪器实现是渐近结论。
2026 后续 arXiv:2607.12976v2 §II.F、§V.A 同样区分 exact 与 asymptotic
FV，不能把其摘要中的 realizability 改读为免费有限资源的精确重力设备。
本节应力/噪声恒等式独立直接推导，设备门仍须按所选实际作用量结算。
