# 关系时钟候选的主块自伴闭合：有限 K 的正结果与剩余算子

本页继续执行 INPUTS_AND_NEXT_TEST 的最小域任务，
给一个明确的 symmetric ordering 和 finite-K principal reference。
原 classical action 没有唯一指定量子 measure、ordering 或 κ=0 边界。
以下结论全部相对于写明的候选，不称为完整 quantum gravity quantization。

## 1. 选择候选后，constraint 化为明确的 clock 方程

取 L²(du dκ)⊗H_source，κ>0，P_u=−i∂u、Pκ=−i∂κ，
在 compact u 区间 g_K(u)≠0 上使用 ACTION_LIFT 的
\[
 D_K=P_\kappa-A_K-Q_K,\quad
 {\cal C}_K=\kappa P_u+{D_K^2\over2g_K(u)}+H_{{\rm rest},0},
\]
\[
 H_{{\rm rest},0}=H_{0,K}-\kappa^2Q_K
                  +V_0a^4U_0-L_g-L_{{\rm ct},0}.             \tag{R1}
\]
common core 取远离 κ=0、κ紧支撑且对finite-K source坐标为Schwartz的光滑向量函数（u也取compact支撑）。
该联合核容许κ/source混合相位，不声称有限可分张量和本身在W_K下不变。
这里的平方 ordering 是明确选择。半轴上的 Pκ 在本页首先是共同核上的形式微分算符，不宣称它或 D 自伴；闭合的是下面的二阶 principal 算子。

f=κ^−1/2 与 g_K、A_K、Q_K 对易，且 [D,f]=−if'。所以
\[
 f{\cal C}_K f=P_u+H_{\rm rel},\quad
 H_{\rm rel}=f\left({D_K^2\over2g_K}+H_{{\rm rest},0}\right)f,
\]
\[
 fD_K^2f=\kappa^{-1}D_K^2+i\kappa^{-2}D_K-{3\over4\kappa^3}.
                                                                  \tag{R2}
\]
这是 symmetric congruence，不是 unitary conjugation。
χ=κ^1/2Ψ 在形式核上满足 (P_u+Hrel)χ=0；
它不自行定义 physical inner product 或保留 kinematic 谱。

## 2. ordering 差确实存在，不能从 classical action 偷选唯一量子项

若先经典除以 κ 再用平直 Weyl ordering，
符号 κ^−1(pκ−A_K−Q_K)² 产生
\[
 \kappa^{-1}D_K^2+i\kappa^{-2}D_K-{1\over2\kappa^3}.
\]
与 R2 的 principal Hamiltonian 相差
−1/(8g_Kκ³)，恢复 ħ 时为 ħ² 项。
两者均有形式对称表达，故 classical lapse action 本身未选择其中唯一一个。

## 3. 几何 principal reference 可以真正给出自伴实现

先取
\[
 A_0=\kappa^{-1/2}P_\kappa^2\kappa^{-1/2}
 =-\kappa^{-1}\partial_\kappa^2+
   \kappa^{-2}\partial_\kappa-{3\over4\kappa^3}
\]
在 C_c∞(0,∞) 上。
它的正二次型为
\[
 q_0[\psi]=\int_0^\infty
       |\partial_\kappa(\kappa^{-1/2}\psi)|^2d\kappa .
\]
令
\[
 x={2\over3}\kappa^{3/2},\qquad
 \phi(x)=\kappa^{-1/4}\psi(\kappa).
\]
该映射在 L²(dκ)→L²(dx) 上 unitary，直接微分给
\[
 {\cal U}A_0{\cal U}^{-1}
       =-\partial_x^2-{5\over36x^2}.                         \tag{R3}
\]
Hardy 不等式 ∫|φ|²/x²≤4∫|φ'|² 给
\[
 q_0[\psi]=\int\left(|\phi'|^2-
                          {5|\phi|^2\over36x^2}\right)dx
                  \ge {4\over9}\|\phi'\|_2^2 .
\]
等价地，κ形式中的一阶算符
Tψ=∂κ(κ^−1/2ψ) 在该 dense core 可闭，
closed form ||Tbarψ||² 定义非负 selfadjoint Friedrichs realization A0,F。
这是真正的 principal-domain 构造，不只检查形式对称。

κ=0 的两条局部零解是 κ^1/2、κ^3/2，
都在端点附近 L²；因此最小对称算符没有被形式表达唯一闭合。
Friedrichs 边界选择去掉 κ^1/2 分支：
在 maximal-domain 边界系数意义下 κ^−1/2ψ→0。
本页明确选择这一 reference，不断言它就是唯一物理边界。

## 4. 有限 K 的 source connection 可以一并运输

A_K=B_K−mathfrak h_K κ²/4 不依赖 u。
每有限 K 定义正常 unitary
\[
 W_K(\kappa)=\exp i[B_K\kappa-\mathfrak h_K\kappa^3/12+
                                                  \kappa Q_K].
\]
在共同 core 上
\[
 W_K^\dagger D_KW_K=P_\kappa,\quad [W_K,f]=0,\qquad
 fD_K^2f=W_K A_0 W_K^\dagger .                              \tag{R4}
\]
所以该 principal block 的一个明确 selfadjoint extension 是
W_K(A0,F⊗I)W_K†，domain 也由同一 W_K 运输。
固定 u 时乘实非零系数 1/(2g_K(u)) 仍 selfadjoint，
但其符号可能为负，不能因此宣称完整 Hamiltonian 非负。

同时
\[
 W_K^\dagger H_{0,K}W_K=H_{0,K}+\kappa\mathcal D_K+\kappa^2Q_K.
\]
因此完整候选在此 finite-K frame 中的形式为
\[
 W_K^\dagger H_{\rm rel}W_K
 ={A_0\over2g_K(u)}+{H_{0,K}\over\kappa}+\mathcal D_K+
       {V_0a^4U_0-L_g-L_{{\rm ct},0}\over\kappa}.             \tag{R5}
\]
principal reference、source/dilation、κ^−1项与 u-dependence
由此明确分开；没有删掉 source 或边界 datum。

## 5. 本次关闭到哪里，下一步验证什么

已关闭：该 ordering 候选的 congruence / Weyl 差；
裸 principal block 的 selfadjoint Friedrichs 实现；
有限 K source connection 的正常 unitary domain 运输；
完整剩余项的精确表达 R5。

未关闭：R5 全部项的共同 selfadjoint domain、
跨 u 的 unitary propagator、κ=0 的物理边界选择、
同一重整化下的 full-field limit、真实 initial density 和可测 physical algebra。
几个 selfadjoint 项相加不自动 selfadjoint，
principal 的闭合也不证明负 g_K 下的完整稳定性。

QUANTUM_ENDPOINT 已排除把 W_K 单独主动施于固定 normal 输入
再取全场正常极限的具体路线。
有限 K 的被动共同 domain 运输仍合法，
但不能由此偷用一个未存在的全场 Fock unitary。
下一次应从 R5 的完整剩余项与共同态运输开始，
而不是再优化独立指针维数或把一个形式对称表达当完整量子化。

## 6. 已选主块的随clock参数传播也可精确给出

由g_K(u)=g_K(u0)+(u−u0)/4，在不跨g_K=0的clock区间，所选 A_F=A0,F 有共同operator domain。主块 Hprin(u)=A_F/[2g_K(u)] 的精确unitary propagator为
\[ U_{prin}(u,u_0)=\exp\{-2iA_F\log|g_K(u)/g_K(u_0)|\}.\]
finite-K connection W_K不依赖u，故带connection的主块传播只需左右同一W_K运输。这里仅处理已选principal block，没有把R5的source/dilation/κ^-1势加入这个指数；完整unitary propagator仍未构造。
