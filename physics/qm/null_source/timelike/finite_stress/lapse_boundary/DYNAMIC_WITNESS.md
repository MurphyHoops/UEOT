# 原实际正窗的绝对噪声预算与非静态密度见证

本页始终使用 GEOMETRY_MATCHING 的同一个一次选参历史
a=A exp U(−c exp(sη),w* exp(σFη))，c=10^−55，a(0)=A，
w*∈[0.9c,1.1c]。窗口 I=(0,T)，T=1/σF；固有时约0.087296模型单位。
所有 f 都是 I 内非负、单位积分、C∞紧支时间测试。结论不覆盖任意有符号滤波器。
原平均解、incoming态和旧区间只读取，不重求根、不积分任何ODE。

## 1. 在整个未来窗口重新评价实际级数

记 W(λ)=(1+λ)^4 log(e+λ)，Ws=W(s)，Wf=W(σF)，W2=W(2s)，
Rx=exp(s/σF)，Ry=e。冻结收缩常数为
Kinv=2×10^20，H2=6400，q=0.128，ρ=10^−25，
C0=Kinv H2/[2(1−q)]。同一固定点的系数估计在未来半径 (Rx,Ry) 给
\[
 r_T=W_scR_x+W_f(1.1c)e<\rho/2,
\]
\[
 \|v\|_A\le
 \Delta_T:=C_0(W_scR_x)^2/W_2+C_0r_T^2/W_f,
 \qquad \|U\|_A\le r:=cR_x+1.1ce+\Delta_T.                 \tag{W1}
\]
证明与旧有限片估计相同：m=0的系数由纯慢分支产生，其余m≥1频率至少σF，
两个扇区分别除以W2、Wf。先在新半径使用收缩，再由唯一性认回同一U；
不是把初片半径1的界直接套到未来。

## 2. 小振幅但严格非零的密度差

ω=√3，v=e^−iωη F/√(2ω)，D=F′−hF。
正频率卷积给
\[
 [\Theta(\Theta-2i\omega)]F=(U''+U'^2)F,\quad
 (\Theta-2i\omega)D=-hD+2i\omega hF.
\]
总频率Λ≥每个输入频率；故 λ²/[Λ|Λ−2iω|]≤1，
λ1λ2/[Λ|Λ−2iω|]≤1/4，λ/[|Λ−2iω|]≤1。
这些逐系数不等式允许仅用Wiener A范数，而非错误假定||h||A≤||U||A。
令
\[
 t=r+r^2/4,\quad F_0=(1-t)^{-1},\quad F_1=t/(1-t),
\]
\[
 D_0=2\omega r F_0/(1-r),\qquad
 D_2=rD_0+2\omega rF_1.
\]
则 ||F||≤F0，||F−1||≤F1，||D||≤D0，
||D−2iω Θ(Θ−2iω)^−1U||≤D2。
设 E=−iFD+D²/(2ω)，E1=2ω Θ(Θ−2iω)^−1U，得到
\[
 \|e^{-4U}E-E_1\|
 \le e^{4r}(F_1D_0+D_2+D_0^2/(2\omega))
 +(e^{4r}-1)2\omega r=:\mathcal E.                    \tag{W2}
\]
实际 Bρ2=e^−2iωη e^−4U E/(2V0A⁴)。

写 cλ=ωλ/(λ−2iω)，则
Re cλ=ωλ²/(λ²+4ω²)，Im cλ=2ω²λ/(λ²+4ω²)。
θmax=2ωT。种子虚部由负慢根主导；用
|e^−iθ−1|≤θ、m≥1余项W1、非线性W2，整个窗口有
\[
 -\operatorname{Im}B_{\rho2}(\eta)\ge {b_*\over V_0A^4},
\]
\[
 b_*=
 c\,\operatorname{Im}c_s
 -1.1ce\,\operatorname{Im}c_{\sigma_F}
 -\theta_{\max}\omega(cR_x+1.1ce)
 -\omega\Delta_T-\mathcal E/2>0.7c.                    \tag{W3}
\]
因此所有上述f均有 |Bρ2[f]|>0.7c/(V0A⁴)，并非只存在一个测试。
归一化 bump 放在 (T/4,3T/4) 即是明确实例。
\[
 32p[0.7c/(V_0A^4)]^2
 <\Delta N_{\rho\rho}(f,f)
 \le32p[(\omega r+\mathcal E/2)/(V_0A^4)]^2.          \tag{W4}
\]
这里是源密度二阶矩差；不是可测引力信号或度规误差。

绝对N−中的profile块给
\[
 N^-_{\rho\rho}(f,f)>
 {\sigma^2e^{-12\rho}\over128V_0^2A^6},
 \qquad \sigma={\sqrt3\over100A},
\tag{W5}
\]
因为μ2>1/128。故W4/W5还给相对绝对基线的严格上界。
非静态密度差严格存在与其极其微小可以同时成立。

## 3. 同一短窗的完整绝对压力并不弱

令M=450000。冻结T包围严格给MT<1/2。
对3≤k≤M，ωk=√(k²−1)，把傅里叶相位围绕T/2旋转：
\[
 \operatorname{Re}\!\left[e^{i\omega_kT}
          \int f(\eta)e^{-2i\omega_k\eta}d\eta\right]
 \ge1-(\omega_kT)^2/2>7/8.                            \tag{W6}
\]
静态Bp,k=−ωk e^−2iωkη/(3V0A⁴)。
实际E4包围及TENSOR_NOISE的F−1、G界给
\[
 |B_{p,k}[f]-B^{\rm static}_{p,k}[f]|
 <8\rho\omega_k/(V_0A^4).
\]
由于7/24−8ρ>1/4，
|Bp,k[f]|>ωk/(4V0A⁴)。
每个高模真空pair产生正交向量，有限低模相关不能消去此正项：
\[
 N^\pm_{pp}(f,f)>
 {S_M\over4V_0^2A^8},\qquad
 S_M=\sum_{k=3}^M(k^4-k^2)
 ={M(M-1)(M+1)(M+2)(2M+1)\over10}-12.                 \tag{W7}
\]
只用闭合求和式；没有数值演化45万个模式。

由实际平均方程
p=−[U″+(1+U′²)/2]/a²，
|U|,|U′|,|U″|≤ρ，可得
\[
 |\langle\bar p(f)\rangle|
 \le e^{2\rho}[\rho+(1+\rho^2)/2]/A^2.               \tag{W8}
\]
新向外舍入证书给
\[
 {\sqrt{N^\pm_{pp}(f,f)}\over|\langle\bar p(f)\rangle|}
 >400.                                             \tag{W9}
\]
这是当前短窗上的源应力RMS/平均值预算，不能直接转换成度规误差。
它不推翻已成立的平均解，也不排除不同滤波器或更长窗口；
但它拒绝了“源荷RMS很小，所以此窗完整源噪声很弱”的推论。

k=2实际包围还给|Bp,2[f]|<ω2/(2V0A⁴)，所以
\[
 {\Delta N_{pp}(f,f)\over N^-_{pp}(f,f)}
 <{96p\over S_M}<3\times10^{-27}.                   \tag{W10}
\]
原两态压力差在此短窗被共同真空背景淹没。此结论独立于能带宽σ。
完整retarded传递函数、装置响应和校准仍须另算。

## 4. 验收边界与后续

W3是非静态实际密度正见证，W7是完整绝对压力的下界，W10是差与基线的上界。
三者不能互换。时间均为模型单位；没有把它们写成SI秒、实验灵敏度或
半经典理论普遍无效的定理。新的更长弱噪声窗口若要构造，必须一次重选
一条合法历史、重新作有限片匹配和完整窗口预算，不能把原短窗结论外推。
