# 实际有限模式因果逆：构造、初始运输与不能跳过的全场门

## 1. 固定同一截断、实际mode与AE接触

在同一actual U上截断非零模k≤K，但保持原参考k=1减项、
真实零模、k=2占据和完整AE局部项。
这里γ4,K是保留mode/state变化为独立辅助量时的显式局部系数；
若初态本身随geometry jets变化，消去这些变量会另产生边界响应。

令H_K=Σ_{k=1}^K1/k，ell=log(A²/4)+2γEuler+2U。
冻结ran/tan中H1/T1的共同系数为
\[
 c_T={19+15\ell\over17280}.
\]
压力spatial行的w⁽⁴⁾系数来自4pan和完整减项，精确为
\[
 \boxed{\gamma_{4,K}=
 {19+15\ell-30H_K\over360V_0a^2}.}                 \tag{F1}
\]
density行w‴系数精确为2hγ4,K。
一般lapse的最高组合是γ4,K(w⁽⁴⁾−hν‴)，不是新增独立lapse动力学。
漏参考k=1会把H_K改错；只看局部anomaly也会漏−30H_K。

当前|U|≤10^−25，冻结A给ell<23。
K≥10^6有H_K≥log(K+1)>13.8，所以
\[
 \gamma_{4,K}<0,\qquad
 |\gamma_{4,K}|>
 {13.8-364/30\over12V_0a_{\max}^2}>0.              \tag{F2}
\]
这是方便的充分K，不是最小cutoff，不实际枚举百万mode。
γ4,K随K含logK；不能把单独系数的极限当作全场最高阶系数。

## 2. 一个真正可写出的有限窗因果逆

先固定ν=0 gauge，在I=[i,T]使用同一initial density/过去运输。
取
Y=(w,w′,w″,w‴,{Reδv_k,Imδv_k,Reδv′_k,Imδv′_k}_{2≤k≤K})。
若另允许有限低模初态参数变化，它们必须作为明示初始项加入。
每个mode满足
\[
 \delta v_k''+(\omega_k^2-V)\delta v_k
 =(w''+2hw')v_k .                                  \tag{F3}
\]
压力行除w⁽⁴⁾外只线性含Y及实际mode/local coefficients。
F1不穿零时，精确化为
\[
 Y'=A_K(\eta)Y+e_4 f(\eta)/\gamma_{4,K}(\eta).
\tag{F4}
\]
A_K的每项由F3、RETARDED_RESPONSE R8–R10的有限和与原gravity项给出。
它不是忽略mode反馈的四阶geometry ODE。

定义绝对收敛的Peano–Baker级数
\[
 \Phi_K(t,s)=I+\sum_{n\ge1}
 \int_{s<t_n<\cdots<t_1<t}
 A_K(t_1)\cdots A_K(t_n)dt_1\cdots dt_n ,
\]
||ΦK(t,s)||≤exp∫s^t||AK||。于是
\[
 w(t)=e_1^T\Phi_K(t,i)Y_i+\int_i^tG_K(t,s)f(s)ds,
\]
\[
 G_K(t,s)=e_1^T\Phi_K(t,s)e_4/\gamma_{4,K}(s).
\tag{F5}
\]
这是每个声明K的唯一有限窗pressure因果解。
f∈C∞_c((i,T))、零过去几何/mode变化给平坦初片jets。
没有数值ODE或百万维矩阵执行的声明。

Y_i里的δv_i、δv_i′一般由真实过去积分决定；
不能仅凭四个geometry jets随意重置。
F5完整保留initial transport项，它还不是对actual stress随机分布的施加。

## 3. actual U不是有限K的精确背景，缺陷必须带着走

U严格满足完整E=S=0，但截断E_K、S_K一般非零，尾为O(K^−2)。
完整减项与local AE使每个K仍满足原off-shell Ward。
令e_K=δE_K、s_K=δS_K，在ν=0下真正恒等式是
\[
 e_K'+he_K=2hs_K+w'(2S_K-E_K).                     \tag{F6}
\]
因此若只解s_K=b_K且源d_K′+hd_K=2hb_K，
\[
 (d_K-e_K)'+h(d_K-e_K)=w'(E_K-2S_K).              \tag{F7}
\]
有限K密度残差并非自动为常数。
可在finiteK自己的on-shell背景求解，或保留此已知缺陷到统一极限；
本页采用后者的显式记账，没有删项后宣称fullconstraint已经传播。

## 4. 全场逆还缺的准确条件

已证RSET响应尾(L−L_K):C8→C0为O(K^−2)，
只说明算子在该方向类收敛，不说明逆收敛。
F1的logK与高模memory必须组合；各K的Peano–Baker粗界不自动统一。

一个足够的中间紧性门是：同一prepared域、相同smooth f与initial运输，
有K无关的geometry C9控制及对应初态/高jet界。
则Arzelà、固定有限mode连续依赖和R6尾给C8子序列与全场方程。
要得到整列G_R还需同域的统一resolvent估计/唯一性；
当前没有签收这些K统一界。

CAUSAL_DOMAINS新增static G0:L²γ→H⁴γ。
但原P具有四阶log增长，裸H⁴不是完整L0全域。
若L_U−L0保留U∂⁴log∂，任意非零小U也不能仅用H⁴范数控制。
ACTION_RESPONSE现已给正确action归一化和principal比较的精确恒等式；仍须在L0 graph域估
(L_U−L0)G0的相对范数，再使用Neumann/Volterra。
不能把原正频Wiener小球直接套到振荡量子噪声。

## 5. actual source和物理观测的最后一道门

数学f平滑零过去，不等于真实压力噪声在初片自动平坦。
突然写Θ(η−i)ξp会损坏高jet/初态匹配，并遗漏density与准备的Ward补项。
对实际几何测试F，需证明G_R*F属于源应力的GNS L²域，
保留C_geom−C_pre=C_source及已经算出的C–stress交叉项。

密度局部系数2hγ4,K在当前极小h时很小。
没有真实initialstate/energy兼容条件，不能把非零Csource硬填成“很小”的初始jerk；
也不能拿这个局部系数当消去态变量后的完整constraint Jacobian。

本页关闭finiteK的解析因果构造与准确缺陷恒等式；
完整actual全场causal inverse、量子几何态和总装置仍OPEN。
