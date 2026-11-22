# 协变源响应：固定测度、因果两腿与接触项账本

这是将已完成的实际source noise推进到任意smooth metric方向的接口。
同一过去态、方程和重整化约定保持；没有完成任意tensor的全部CTP延拓，
也没有将外部文献的一般公式替代本项目固定AE匹配。

## 1. 同一过去态的协变变化

采用−+++和P_g=□_g。h_ab=δg_ab实、smooth、时空紧支，
支撑在共同初片之后；初片数据及态不变。记H=g^{ab}h_ab。
令rε=dvol_gε/dvol_g，Uε=rε^{1/2}，以固定dvol_g比较算子：
\[
 \widetilde P_\epsilon=U_\epsilon P_{g_\epsilon}U_\epsilon^{-1},
 \quad U_\epsilon=1+\epsilon H/4+O(\epsilon^2).
\]
原标量算子变分为
\[
 \delta\Box=-h^{ab}\nabla_a\nabla_b
 -(\nabla_a h^{ab}-\tfrac12\nabla^bH)\nabla_b.
\]
加入测度交换项后
\[
 V_h:=\delta\widetilde P
 =-\nabla_a(h^{ab}\nabla_b)-\tfrac14\Box H.           \tag{C1}
\]
对紧支测试f,g，
\[
 \langle f,V_hg\rangle
 =\int[h^{ab}\nabla_af^*\nabla_bg
       -(\Box H)f^*g/4]\,dvol_g,
\]
所以V_h形式自伴。Uε只是spacetime测度识别，不是Fock implementer。

W为同一过去Hadamard态的Wightman二点函数。
严谨地，对紧支smooth测试f,g先定义
δWtilde(f,g)=−W(V_h G_A f,g)−W(f,V_h G_A g)。
G_A f光滑而V_h紧支，故两个新测试仍在C∞_c，原双分布W足以定义该式。
这避免未经证明的奇异分布乘积。其核记号为
\[
 \delta\widetilde W=-G_R V_h W-WV_hG_A, \qquad G_R^T=G_A.
                                                               \tag{C2}
\]
恢复physical scalar二点函数必须包含
\[
 \boxed{\delta W=\delta\widetilde W
 -{H(x)+H(y)\over4}W(x,y).}                         \tag{C3}
\]
每个retarded项只在相应外腿位于J⁺(supp h)时响应。
零模及非Gaussian薄层态均包含于实际W；quadratic mean的导数只依赖W，
这不意味着完整高阶影响泛函由W决定。

对更一般的初片态变化，还须加上同一双解方程运输的δW_initial；
本页明确没有将该项包含在C2的“固定态”方向里。

## 2. 纯规范方向的精确检验

令h=L_ξg，ξ紧支且在初片前为零。
Kξ=ξ·∇+(div ξ)/2形式反自伴，H=2div ξ。
自然性给
\[
 V_h=[K_\xi,P],\qquad
 \delta\widetilde W=(K_{\xi,x}+K_{\xi,y})W.
\]
从C3扣掉测度端点后
\[
 \delta W=(L_{\xi,x}+L_{\xi,y})W.                    \tag{C4}
\]
这提供非齐次source Ward与因果检验；不需要把未经延拓的
θ乘应力交换子当作已经定义好的全tensor分布。

## 3. 守恒 point-splitting 接触不能删

Moretti的原文使用同一signature，但P_M=−□+m²+ξR。
其Eq(9)、Theorem2.1(a)/Eq(20)给四维η4=1/3。
翻译到本模型P=□后，
\[
 D^{cons}_{ab}=D^{cl}_{ab}-{g_{ab}\over6}(P_x+P_y).  \tag{C5}
\]
令同一规范化Hadamard reference为mathcal H_g，
A_H=[P_x mathcal H_g]=[P_y mathcal H_g]。
守恒c-number为+g_ab A_H/3；其变分为
\[
 {h_{ab}A_H+g_{ab}\delta A_H\over3}.                \tag{C6}
\]
δA_H=[(δP)mathcal H+Pδmathcal H]须整体取光滑coincidence极限，
不能把两项奇异极限各自验收。该c-number在centered noise中相消，
在response/contact里仍保留。

来源：[Moretti, gr-qc/0109048v2](https://arxiv.org/pdf/gr-qc/0109048)，
Eq(9),(10),(20)及Theorem2.1；本页只翻译其规定，不声称由此完成AE等价。

## 4. 每一类接触项都有明确位置

设B_g=Re(W_g−mathcal H_g)，
S_ab=[∇_(a∇_b′)B_g]，S=g^{ab}S_ab，
Q_ab^{cd}=δ_a^(cδ_b^d)−g_abg^{cd}/2。
每个minimal field的固定处方可组织为
\[
 T_{ab}=S_{ab}-\tfrac12g_{ab}S+g_{ab}A_H/3+C_{ab}^{AE}.
\]
因此
\[
\begin{split}
 \delta T_{ab}={}&Q_{ab}^{cd}[\nabla_c\nabla_{d'}\delta B]
 -\tfrac12h_{ab}S+\tfrac12g_{ab}h^{cd}S_{cd}\\
 &+(h_{ab}A_H+g_{ab}\delta A_H)/3+\delta C_{ab}^{AE}. \tag{C7}
\end{split}
\]
δB=Re(δW_phys−δmathcal H)。
每腿一次的scalar混合导数没有额外connection variation；
对角线上的平行输运恒为identity，变分为零。
两个场逐项相加；旧常量源另给−U0 h_ab。

action insertion还必须变分指标与体积：
\[
 \delta(\sqrt{|g|}T^{ab})=\sqrt{|g|}
 [g^{ac}g^{bd}\delta T_{cd}
 -h^a{}_cT^{cb}-h^b{}_cT^{ac}+(H/2)T^{ab}].          \tag{C8}
\]
原δS=½∫√|g|T^{ab}δg_ab有固定½。
再从g_ab转为lapse/u时，必须加δ²g_ab的chain-rule接触；
ACTION_BOUNDARY已给这一坐标问题的有限K检查。
只写δT或½δ(√gT)都不能声称已得到全部CTP Hessian。

## 5. 固定 AE 匹配是明确剩余工作

本项目的AE μ=1、零额外有限曲率项早已冻结。
KERNELS的ell、H1/H3、ran/pan，以及旧overlap tensor合同都必须保持。
AE原文采用+---和其自身曲率符号，故不得直接挪用H1符号。

这里C_ab^AE表示将所选covariant reference转换到这个既定处方的固定差，
不是可以重新任选的Weyl²/R² coupling。
FLRW看不到某些tensor方向，既不能据此验收任意tensor匹配，
也不能据此重开旧耦合。

尚须完成：具体mathcal H/reference的完整匹配、
retarded stress分布的全部局部延拓、有限初片混合块、
并与同一正常联合geometry/装置态耦合。
C1–C8关闭源侧协变响应和接触账本的符号与因果接口；
完整tensor Einstein–CTP解仍OPEN。

## 6. 直接落到本项目的 lapse/scale 方向

取δlog a=w、δN=ν（线性lapse坐标），N=1。
则H=8w+2ν，记s_w=w+ν，C1成为
\[
 V_{w,\nu}=a^{-2}\{2s_w\partial_\eta^2
 +(4hs_w+2s_w')\partial_\eta-2w\Delta_\Omega
 +2w''+4hw'+\nu''/2+h\nu'\}.                         \tag{C9}
\]
直接变分
P_N=−a⁻²N⁻²[∂²+(2h−N′/N)∂]+a⁻²ΔΩ，
再加[2w+ν/2,P]得到同一式。
spacetime half-density ψ=a²√Nφ与slice变量q=aφ用途不同。

对两个方向，令aε=a exp(ε1w1+ε2w2)，
Nε=1+ε1ν1+ε2ν2。C8以外的二阶metric链项精确是
\[
 {1\over2}\int\sqrt{|g|}\,T^{ab}\delta_{12}g_{ab}
 =V_0\int a^4[
 (-2\rho+6p)w_1w_2
 -2\rho(w_1\nu_2+w_2\nu_1)-\rho\nu_1\nu_2].         \tag{C10}
\]
它接到同一一阶J=V0∫a⁴[−ρ(ν+w)+3pw]。
若改用logN坐标，ν1ν2系数会改变；本页不混用两种参数化。
C9/C10新增了原lapse端口到协变公式的可直接核验映射，
仍不取代第5节的固定AE全tensor匹配。
