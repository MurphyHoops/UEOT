# 实际有限初片：压力紫外边界与含源初始块的共同极限

本页在已匹配的actual U和同一incoming态上工作。
高模k≥3为原真空，低模与零模保持原薄层态；它们不改变下述高模发散。
新增结论不是“任何合法制备必须双零”，而是分别计算单独source项的域，
以及同一finite-K初始块与source合并后的域。

## 1. 真实高频引理

令v_k=e^{-iω_kη}F_k/(2ω_k)^{1/2}，ω_k=√(k²−1)，V=h′+h²。
冻结STATE_MATCHING的严格解析内域给任意固定阶V导数的过去L¹与局部一致界。
RETARDED_RESPONSE明确使用同一严格内域；没有把E4的小范数当成所有阶的相同常数。

由F″−2iωF′=VF、incoming条件和Volterra表达，
F−1=O(ω⁻¹)。对j≥1，
\[
 (\partial_\eta-2i\omega)F^{(j)}=(VF)^{(j-1)}.
\]
一次分部积分、吸收||V||₁||F^{(j)}||∞/(2ω)，再对固定j递推，
给F^{(j)}=O(ω⁻¹)。常数可依赖固定观察区及相应有限阶背景范数，
但独立于k。以下用到j≤4。

故真实压力pair系数满足
\[
 B_{p,k}(\eta)=e^{-2i\omega_k\eta}
 \left[-{\omega_k\over3V_0a(\eta)^4}+R_k(\eta)\right],
 \qquad \|R_k\|_{C^3(I)}\le C_I .                    \tag{U1}
\]
这来自原(r²−ω²v²/3)/(2V0a⁴)，r=v′−hv。
它是实际非静态mode结论，不是将静态真空直接搬到初片。

## 2. 单独突然起始的压力项

取实q∈C∞([i,∞))，向未来紧支并平坦。
测试f=1_[i,∞)q在i可能不光滑。每个K先合法定义有限和p_K(f)。

由U1及分部积分，
\[
 B_{p,k}[f]=e^{-2i\omega_k\eta_i}
 \left[-{q(η_i)\over6iV_0a_i^4}+O(\omega_k^{-1})\right].
\]
这里分母i是虚数单位，η_i是初片坐标，a_i=a(η_i)。
当q(η_i)=0时，
\[
 B_{p,k}[f]=e^{-2i\omega_k\eta_i}
 \left[{q'(\eta_i)\over12V_0a_i^4\omega_k}
                   +O(\omega_k^{-2})\right].
\]
高模绝对方差是Σ4k²|B_k[f]|²。因此
\[
 \boxed{\lim_{K\to\infty}{\operatorname{Var}p_K(f)\over K^3}
 ={q(\eta_i)^2\over27V_0^2a_i^8}}
 \quad(q(\eta_i)\ne0),                              \tag{U2}
\]
\[
 \boxed{\lim_{K\to\infty}{\operatorname{Var}p_K(f)\over K}
 ={q'(\eta_i)^2\over36V_0^2a_i^8}}
 \quad(q(\eta_i)=0,\ q'(\eta_i)\ne0).                \tag{U3}
\]
低模输出与高模pair输出正交，不能用低模协方差删除这两个系数。

若q(η_i)=q′(η_i)=0且q的第三导数可积，三次分部积分给
B_k[f]=O(ω_k⁻²)，Σk²|B_k|²收敛。因此在此函数类，
双零恰好是这个单独pressure smear进入实际态L²的门。
它不是对完整联合几何—物质初值的必要条件。

## 3. 同一截断上的精确初始恒等式

定义非零模式的
\[
 Q_K={1\over2}\sum q_\alpha^2,\quad
 D_K=Q_K'={1\over2}\sum\{q_\alpha,q_\alpha'\},\quad
 H_{0,K}={1\over2}\sum(q_\alpha'^2+\omega_\alpha^2q_\alpha^2).
\]
求和包括两个场及全部简并。δ表示减去同一实际态均值。
局部c-number减项在δ中相消。利用同一KG方程，逐振子精确有
\[
 \delta p_K={\delta Q_K''-3h\delta Q_K'
 +(h^2-2h')\delta Q_K+\delta H_{0,K}\over3V_0a^4}.
                                                               \tag{U4}
\]
实际零模可单独加入有限的同形项，不影响高模极限结论。

令w=q/(3V0a⁴)。两次分部积分得到
\[
 \int_{\eta_i}^\infty q\,\delta p_K
 =B_{i,K}+\int_{\eta_i}^\infty
  \left[(w''+3hw'+Vw)\delta Q_K+w\delta H_{0,K}\right],            \tag{U5}
\]
\[
 \boxed{B_{i,K}=
 { -q_i\delta D_{i,K}+(q_i'-h_iq_i)\delta Q_{i,K}
       \over3V_0a_i^4}.}                                       \tag{U6}
\]
等价的Q权重为
\[
 w''+3hw'+Vw
 ={q''-5hq'+(5h^2-3h')q\over3V_0a^4}.                          \tag{U7}
\]
边界符号来自上端平坦、下端有负号；不能把端点当成独立噪声。

## 4. 先合并，再取共同全场极限

实际incoming态中，Q_K的高模pair envelope为O(ω⁻¹)。
H0,K的pair系数为(v′²+ω²v²)/2；共同领先项相消，
F′=O(ω⁻¹)使其envelope及固定有限阶导数仍为O(ω⁻¹)。
U5右侧积分一次分部积分后pair输出O(ω⁻²)，
故在实际GNS中L²收敛。

因此定义同源初始项X_i,K=−B_i,K后，
\[
 X_{i,K}+\int_{\eta_i}^\infty q\,\delta p_K
 \longrightarrow
 \int_{\eta_i}^\infty
 [(w''+3hw'+Vw)\delta Q+w\delta H_0]
 \quad\hbox{in }L^2 .                                         \tag{U8}
\]
右侧是有限K共同极限的记号，不要求其中每个尖片算符先单独存在。
即使U2/U3发散，U8仍可存在；两边完整保持同一源的交叉项。

这给出真实含源混合块的精确数学示例，而不是新增独立tensor-factor载体。
它没有违反旧BOUNDARY_EXTENSION的独立载体排除，因为X_i,K显式含源。

## 5. 已关闭的门与仍未关闭的门

已关闭：actual-U高频边界系数、单独pressure的域条件、
finite-K含源边界恒等式、完整组合的实际L²极限。
符号、归一化、权重及幂次由新检查器核验，分析域论证在本页。

仍未关闭：X_i,K是否等于原引力初值/真实装置准备所产生的初始项。
本页不能把为一个测试q构造的负B自动当成独立可调的geometry初值，
更不能推出其所有测试同时对应一个正常联合物理态。
下一步必须将同一作用量的初始变分、实际制备密度及约束列与U6逐项配对。
