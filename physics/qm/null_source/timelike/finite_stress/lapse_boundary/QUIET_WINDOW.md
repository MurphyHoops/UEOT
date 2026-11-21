# 复盘后的一次新选参：安静的齐次源窗口与真实快方向敏感性

原c=10^−55短窗的绝对压力预算很大。不能把这一结论扩大到所有窗口。
本页构造另一条完整mean历史及一个明确时间平滑器，然后检查它仍留下什么几何问题。
原M2、U0、incoming薄层源及σ=√3/(100A)保持；新的是一次选定的几何初始幅度。
这不是逐时换根，也不是把原固定初值历史直接延长。

## 1. 有限片匹配对更小幅度的严格推广

旧初片估计具有Δ(c)=Dc²、Δh(c)=Dhc²。
在c0=10^−55已严格验证的Δ<c/1000和h0正下界，对所有0<c≤c0继续成立。
固定点Lipschitz q/(1−q)<0.147与c无关。
故每个这样的c有唯一b(c)∈[0.9c,1.1c]满足
\[
 U(-c,b(c))=0,\qquad |b(c)-c|\le Dc^2,\qquad h(0)>0.
\tag{Q1}
\]
取精确实数c=exp(−20000)，T=1/50=0.02。
一次固定b(c)，使用
\[
 a_q(\eta)=A\exp U(-c e^{s\eta},b(c)e^{\sigma_F\eta}).
\tag{Q2}
\]
冻结s<2.1、σF<937000使
|z_T|<e^−19999.958，|y_T|<1.1e^−1260，
远在Rz=10^−28、Rw=10^−51内部。所有更早过去同样合法。

Ws<200、Wf<10^26及C0<e^80给未来E4种子rT<e^−1159，
同一收缩余项给
\[
 \|U\|_{E_4,\rm future}\le r_T+C_0r_T^2
 <e^{-1158}<t_q:=e^{-1100}.                         \tag{Q3}
\]
程序在log域认证这些界，避免把下溢浮点零冒充严格静态。
a0=A和S=E=0来自同一解析mean族。薄层W2与该mean输入一致，态沿新Q2合法运输。
固有时在AT exp(±tq)之间，约1634.49模型单位，不是秒。

c的极端精细是数学选择。尚没有装置能实现它的资源证明。
新raw有限片状态不是旧h0历史的同一个raw Fock矩阵；仍需合法运输和尖片UV门槛。

## 2. 一个明确且容易控制的 C∞ 平滑器

ℓ=T/4，bℓ=1_[−ℓ/2,ℓ/2]/ℓ。
任取非负单位C∞ mollifierψ，支持[−T/16,T/16]，
例如缩放归一化的exp[−1/(1−x²)] bump。
\[
 f(\eta)=(b_\ell*b_\ell*b_\ell*\psi)(\eta-T/2).
\tag{Q4}
\]
它支持窗口内部宽7T/8，非负、单位积分。
把j≤3次导数分别落在j个box的signed measure上，
\[
 \|f^{(j)}\|_1\le(2/\ell)^j=(8/T)^j,\qquad
 |\widehat f(2\omega)|\le\min(1,(\omega\ell)^{-3}).
\tag{Q5}
\]
所以S3(f)≤401³，S2(f)≤401²。这个证明不需要旧数值平滑器或新的ODE。

## 3. 完整绝对齐次压力上界

静态高模真空部分的和S=Σk≥3 k²ωk²|fhat(2ωk)|²。
取K=200=1/ℓ。低频用|fhat|≤1，
高频用ω²≥3k²/4和Σk>K k^−2≤1/K，
\[
 S\le{201^5\over5}+{16\over9}{200^6\over200}
 <6.4\times10^{11}.                               \tag{Q6}
\]
静态high pressure RMS因此<(2/3)8×10^5/(V0A⁴)。

实际模式F,G=F′−hF的E4/E3界从TENSOR_NOISE同一Jost方程用tq代替ρ给出。
写
\[
 B_{p,k}={e^{-2i\omega\eta}\over V_0A^4}H_{p,k},\quad
 H_p=e^{-4U}[-\omega F^2/3-iFG/2+G^2/(4\omega)] .
\]
有||H_p+ω/3||E3≤16tq ω。
三次时间分部积分及Q5给
\[
 |\delta B_{p,k}[f]|\le{2t_q S_3(f)\over V_0A^4\omega_k^2}.
\]
Σk≥3 k²/ωk⁴<1，故全部high动态误差RMS≤4tq401³/(V0A⁴)<1/(V0A⁴)。

低模不是只保NOON差。由p<0.08、μ2<1、σ=ω2/(100A)，
\[
 \sigma L_f<{\omega_2\over50V_0A^4},\quad
 |A_{p,f}|<{3\omega_2\over V_0A^4},\quad
 S_\pm<20,\quad |B_{p2,f}|<{\omega_2\over2V_0A^4}.
\]
完整profile+number+pair方差<24/(V0²A⁸)，RMS<5/(V0A⁴)。
按实际平方范数三角不等式合并，
\[
 \operatorname{RMS}(\bar p_f)<{533340\over V_0A^4}.
\tag{Q7}
\]
原精确mean方程又给p_f<0和
|〈p_f〉|≥e^−2tq(1/2−tq)/A²>0.49/A²。
因此
\[
 {\operatorname{RMS}(\bar p_f)\over|\langle\bar p_f\rangle|}
 <{533340\over0.49V_0A^2}<10^{-5}.                  \tag{Q8}
\]

## 4. 同一测试上的完整密度与交叉预算

直接展开Dρ2与εL得
|Aρ,f|≤20ω2 tq/(V0A⁴)。
密度pair envelope
Hρ=e^−4U[−iFG/2+G²/(4ω)]
有E2范数≤4tq，故
|Bρ,k[f]|≤tq S2(f)/(V0A⁴ωk²)。
高模RMS≤2tq401²/(V0A⁴)，低number/pair亦O(tq)；
profile RMS<ω2/(50V0A⁴)。保守合并为
\[
 {\operatorname{RMS}(\bar\rho_f)}<{0.1\over V_0A^4},
 \quad
 {\operatorname{RMS}(\bar\rho_f)\over\langle\bar\rho_f\rangle}
 <{0.1\over1.49V_0A^2}<10^{-12}.                   \tag{Q9}
\]
meanρ=3(1+h²)/(2a²)给分母下界。
ρ−p交叉块由同一T11精确决定并满足Cauchy–Schwarz；不重新指定独立噪声。
Q8/Q9只关于这一个齐次测试，不能称任意局域tensor或所有filters的弱噪声定理。

## 5. 同一真实mean族仍有巨大快方向敏感性

无需把静态pole直接搬到新背景。Q2作为精确两参数族给精确切向
\[
 \zeta_F=e^{\sigma_F\eta}U_y,\quad
 \zeta_S=e^{s\eta}U_z,\quad
 Z=\zeta_F-\frac{U_y(0)}{U_z(0)}\zeta_S.
\tag{Q10}
\]
对同一incoming态运输，DE_U Z=DS_U Z=0，且Z(0)=0。
它保持初片a=A的一阶条件。固定N=1时仅剩常数时间平移；
由于h0>0，非零常数时间平移不可能同时满足Z0=0，所以该方向不是此剩余gauge。

令r=max(c e^sT/Rz,1.1c e^σT/Rw)，
\[
 \delta=\max_{j=z,y}{\rho\over R_j}{2r\over(1-r)^2}.
\]
v没有0、1次项，逐系数与λ/W(λ)≤1给
|v_j|、|∂ηv_j|≤δ。当前参数δ<10^−100。
因此
\[
 Z(T)\ge(1-\delta)e^{\sigma_FT}
       -{(1+\delta)^2\over1-\delta}e^{sT},
\]
\[
 |Z'(0)-(\sigma_F-s)|
 \le(\sigma_F-s)\delta+{2\delta\over1-\delta}.       \tag{Q11}
\]
初始δh归一化的尺度敏感性G=Z(T)/Z′(0)满足
\[
 \log G>18709.
\tag{Q12}
\]
程序以log域认证有限数，不把e^18709输出成浮点infinity当证据。

这是精确平均解族的经典导数敏感性；不是已求出的受噪声强迫metric方差。
有限扰动需另有线性化余项和允许幅度；没有给该切向任意量子初态方差。
proper-time比较也须先处理lapse及端点。

## 6. 复盘后的下一验收目标

Q8/Q9说明完整source噪声可以在一个明确新窗口和测试上较弱。
Q10–Q12同时证明：这个结论没有控制同一真实几何的初值快方向。
实际metric observable需要retarded adjoint测试G_R*F、初始geometry covariance和source–initial cross；
它们不由正单位f的源预算决定。

下一项应从原总作用量/正常联合态实际提供这些块，并证明同一约束与
retarded解的相容性；不能只压低σ、只延长平均窗或把初始相关任意调零。
全场局部约束、真实装置、误差及引力校准继续OPEN。

### 5a. 同一初片起算的固有时比较

在τ=∫0η a(s)ds固定时，切向变为
\[
 Z_\tau(\eta)=Z(\eta)-{h(\eta)\over a(\eta)}
                         \int_0^\eta a(s)Z(s)ds .
\tag{Q13}
\]
用|U|,|h|≤ρ及Q11，
\[
 |Z_\tau(T)-Z(T)|
 \le\rho e^{2\rho}
 [(1+\delta)(e^{\sigma_FT}-1)/\sigma_F
  +(1+\delta)^2(e^{sT}-1)/((1-\delta)s)].
\]
此上界除以快方向下界后极小，程序仍认证
log[Zτ(T)/Z′(0)]>18709。
所以敏感性不只是把不同conformal时刻混同的效果。
这仍是同incoming态、有限片态随几何运输的mean族导数；
没有固定原finite-slice raw密度不动，也没有给定量子几何方差。
