# 完整连续读源仪器、canonical 反作用与时钟信息损失

## 1. 同一个守恒源与完整连续记录

令 C=2pi²M2，S0=(P1²+P2²)/C。测量噪声记 v_m，避免与冻结非中心 chi² 源谱参数 nu 混淆。
引入独立指针 [X,Pi]=i，初态为实的中心最小 Gaussian：
Var(X)=v_X、Var(Pi)=1/(4v_X)。
选择一次固定校准 s_c=mu，使用
\[
U_m=\exp[-ig(S_0-s_c)\otimes\Pi],\quad
Y=s_c+X_{\rm out}/g,\quad v_m=v_X/g^2>0.
\]
位置读出诱导
\[
\boxed{K_y=(2\pi v_m)^{-1/4}
       \exp[-(y-S_0)^2/(4v_m)],\qquad
       \mathcal I_y(\rho)=K_y\rho K_y.}
\]
谱演算给 integral K_y^dagger K_y dy=I。全部 y∈R 保留，包括分布尾部；
\[
Y=S_0+N(0,v_m),\quad
p_Y=p_{S_0}*N(0,v_m),\quad
\operatorname{Var}Y=\operatorname{Var}S_0+v_m.
\]
这构造一个完整连续 CP instrument，没有逐记录改变原 M2 或制备谱。

在 S0 的谱表示中，非选择 channel 为
\[
\rho(s,s')\mapsto e^{-(s-s')^2/(8v_m)}\rho(s,s').
\]
固定 y 的乘子是动量的四次指数，条件零模一般不是 Gaussian；
不能套用前驱二分指数滤波的 Gaussian 协方差。
每个有限 v_m、固定 y 的光滑乘子保持本制备的 Schwartz 零模性质；
有限模变化不修改高模 Hadamard 奇性。

## 2. 完整物质应力不变，不等于没有反作用

在同一固定背景和自由 minimal massless 演化中，常数 Q 不进入物质应力；
完整局部应力包含高模二次、P 乘高模的交叉和 P² 项。
S0 与其允许的有界应力效应强交换，因此
\[
\int K_y^\dagger E K_y\,dy=E
\]
对整个该物质应力代数成立，已定义的非选择多时相关／噪声核亦保持。
没有删掉局部零模—高模交叉项。

canonical 状态却被改变：
\[
P_{i,\rm out}=P_i,\qquad
Q_{i,\rm out}=Q_i+\frac{2g}{C}P_i\Pi.
\]
对上述独立零均值最小 Gaussian 指针，
\[
v_m\sum_i\Delta\operatorname{Var}Q_i=\mu/C.
\]
一般独立零均值指针由不确定度关系给相应≥式。
D=sum_i{Qi,Pi}/2 则满足 Dout=D+2g Pi S0，
\[
\Delta\operatorname{Var}D=\mathbb E(S_0^2)/v_m.
\]
所以反作用进入时钟所需的 Q 信息，即使物质应力的非选择完整律不变。

这项不变性没有包含指针、相互作用、开关或记录存储的总应力；
条件记录下的源均值也一般改变，不能把所有条件态直接接到同一固定几何而声称逐支平均 SCE 已成立。

## 3. 一个指定振子指针的资源界

若指定
\[
H_{\rm ptr}=\Omega(X^2+\Pi^2)/2
\]
且 Omega 固定，耦合后、读出前有
\[
\langle H_{\rm ptr}\rangle_{\rm out}
=\frac\Omega2
[v_X+1/(4v_X)+(v_X/v_m)\mathbb E(S_0-s_c)^2].
\]
最佳固定校准为 s_c=mu；对 v_X 优化得
\[
\boxed{\langle H_{\rm ptr}\rangle_{\rm out}
\ge\frac\Omega2\sqrt{1+\operatorname{Var}(S_0)/v_m}.}
\]
实际 Var(S0)≈.1875；v_m=10^-12 时右侧相对 Omega/2 的倍数超过4.33×10^5。
该界限于所写振子模型，不能称作普适测量能量界；
也未证明可免费降低 Omega、加快耦合或实现整体 S0 的局域读出。

## 4. 精确 MMSE 恒等式

由于 K=pi²M2 S0，K_y 与全部时间编码 U_theta 交换。
给定经典 p 标记，完整源读出分布 p(y|p) 与 theta 无关；
保留 p,y 后每个条件零模态仍纯，QFI 为
4(pi²M2)² Var(S0|p,y)/A⁴。
因此
\[
\boxed{J_{\rm after}
=\frac{(2\pi^2M_2)^2}{A^4}
 \mathbb E_p\operatorname{MMSE}(S_0\mid Y,p).}
\]
这里 MMSE 是这个已构造 instrument 的联合 Born 分布所定义的 Bayesian 量，
不要求把源谱声明为额外隐变量本体。

全方差给精确信息损失
\[
J_{\rm before}-J_{\rm after}
=\frac{(2\pi^2M_2)^2}{A^4}
 \mathbb E_p\operatorname{Var}_{Y|p}
  (\mathbb E[S_0\mid Y,p])\ge0.
\]
直接估计量 Y 的均方误差为 v_m，故
\[
\boxed{J_{\rm after}\le(2\pi^2M_2)^2v_m/A^4.}
\]
对同一既定零模，越来越精确的源读出使剩余时间 QFI 趋向零。
没有使用不可正规化的精确连续谱本征态。

## 5. 有限检验：无需局域无偏

将 [CLOCK.md](CLOCK.md) 的纯态有限差界用于全部条件态，N 次独立相同协议得到
\[
D_{{\rm after},N}(d)\le
\min(1,\ |d|\pi^2M_2\sqrt{Nv_m}/A^2).
\]
d=1/sigma、v_m=10^-12 时，单份 D<.0492，45份 D<.330，
等先验错误率仍>.335。
45份若要错误率≤.05，必要的 v_m 大于约7.46×10^-12；
不是充分可实现性条件。

先读源再计时与先计时再读源有同一关系，来自 K_y 与 U_theta 的交换。
若仍可相干访问整个指针净化并逆转耦合，那不是已经产生经典 y 记录且丢弃相关相干信息的本 instrument；
上述资源合同不能被移植过去。

独立重复次数也不是固定两场源中的免费实体时钟。
额外时钟、参考及编码中主动操作必须另记其态、耦合和总源。

## 6. 从全局 CP 构造到局域引力设备尚差什么

[局域测量的一手框架](https://arxiv.org/abs/1810.06512) 要求有界时空区域中的系统—探针耦合、
相应的因果散射映射、诱导 CP 效应及组合一致性。
本页整体 S0 unitary 尚未提供这些结构，也没有完成装置应力与引力反馈。

因此本轮闭合的是完整连续记录、精度／反作用与原时钟信息的定量关系。
下一步须把一个具体有限支撑探针及其全部总源置于共同几何上，
检验约束传播和可校准的引力记录；不能仅凭一个抽象 CP 公式宣布这一层已经完成。
