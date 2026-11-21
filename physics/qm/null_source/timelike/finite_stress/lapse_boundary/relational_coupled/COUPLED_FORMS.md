# 完整 moving-frame 算子的共同型域与传播

前驱只证明principal。此页保留全部源与标量余势；
结论为所选finite-K/ordering/clock patch的完整moving-frame动力学。

## 1. 固定Hilbert与合法time-dependent frame

固定K=65536，J=[-.01,.01]，u0=0。
源Hilbert为有限个实模式的Schrödinger空间，含两个零模。
\[
 H_0={1\over2}\sum_r(p_r^2+\omega_r^2q_r^2)\ge0,\quad
 {\cal D}={1\over2}\sum_r(q_rp_r+p_rq_r),\quad
 R(u)=e^{-i(u-u_0){\cal D}}.
\]
所有算子先在joint compact-κ/Schwartz-source核E上。
有限模式数使R为明确正常unitary；在source坐标上
Rψ(q)=e^{-n(u-u0)/2}ψ(e^{-(u-u0)}q)。
故R†qR=e^(u-u0)q、R†pR=e^-(u-u0)p，
-iR†R'=-D。它不是无限模Fock unitary的证明。

前驱W_K不依赖u。令原χ=W_K R(u)ζ，完整clock方程变成
\[
 i\partial_u\zeta=\widetilde H(u)\zeta,\qquad
 \widetilde H(u)={A_0\over2g_K(u)}
 +{H_s(u)+d_0(u)\over\kappa}+d_1(u)\kappa+d_3(u)\kappa^3,
\]
\[
 H_s(u)=R^\dagger H_0R
 =\tfrac12\sum_r[e^{-2(u-u0)}p_r^2+
                  \omega_r^2e^{2(u-u0)}q_r^2].             \tag{F1}
\]
D项被frame导数精确抵消，未从原作用量删去。

## 2. 固定共同型域

用前驱Liouville unitary x=2κ^(3/2)/3；
\[
 q_F[\psi]=\int(\|\psi'\|^2-5\|\psi\|^2/(36x^2))dx,
 \quad {4\over9}\|\psi'\|^2\le q_F\le\|\psi'\|^2.
\]
对source-valued函数，令
\[
 {\cal Q}=H_0^1(\mathbb R_+;{\cal H}_s)
 \cap D(\kappa^{3/2})\cap D(\kappa^{-1/2}H_0^{1/2}),
\]
\[
 \|\psi\|_{\cal Q}^2=\|\psi\|^2+q_F[\psi]
 +\|\kappa^{3/2}\psi\|^2
 +\int\kappa^{-1}\|H_0^{1/2}\psi\|^2dx.                    \tag{F2}
\]
这是有限个闭算子的graph-form范数之交，完备且稠密。
compact x、source Schwartz光滑核在该域稠密；用x截断、
source H0谱截断/Schwartz逼近及平滑即可，先远离端点再取极限。
零模只要求相应p²型，不擅自加入零模q²势。

e^(-.02)H0≤Hs(u)≤e^(.02)H0（型意义），故源型域不随u改变。
R(u)在Q上有界、强连续且onto；不据此声称D在Q型有界。

## 3. 负标量项的明确控制

令c=(2/3)^(2/3)，1/κ=c x^-2/3。
任意δ>0，逐点
\[
 x^{-2/3}\le\delta x^{-2}+{2\over3\sqrt{3\delta}},
 \quad \int x^{-2}\|\psi\|^2\le9q_F[\psi].                 \tag{F3}
\]
第二条由前驱Hardy界。当前完整d0满足|d0|<e50；
取δ=e^-60，有
\[
 |d_0|\int\kappa^{-1}\|\psi\|^2
 \le9ce^{-10}q_F[\psi]+{2ce^{80}\over3\sqrt3}\|\psi\|^2.
\]
由COEFFICIENT_WINDOW的g,d1,d3界，定义完整对称型t_u为F1各项之和，
可取统一平移Λ=e81使
\[
 {1\over20}\|\psi\|_{\cal Q}^2
 \le t_u[\psi]+\Lambda\|\psi\|^2
 \le e^{90}\|\psi\|_{\cal Q}^2.                            \tag{F4}
\]
上界还用κ≤1+κ³。全部常数虽宽但有限，未把巨大真空常数忽略。

系数为C∞；d0,d1的u导数来自a²=e^(2u)A²，
g'=1/4、d3'=-1/8，Hs各阶导数为±2或4倍的p²/q²型。
相同F3给r=1,2的
\[
 |\partial_u^rt_u(\psi,\varphi)|
 \le e^{90}\|\psi\|_{\cal Q}\|\varphi\|_{\cal Q}.           \tag{F5}
\]
本页只用r≤2；更高的有限导数也连续。
负项是infinitesimal型扰动，因此t_u闭且共同型域正是Q。

## 4. 自伴实现和完整传播

闭型表示定理定义唯一与t_u相应的自伴半有界
\(\widetilde H(u)\)。采用Λ平移后的F4内积，
F2/F4/F5逐项满足Kisyński共同型域C²传播定理。
由REFERENCES中Assumption3.8/Theorem3.10，得到唯一unitary传播
\(\widetilde U(u,v)\)，满足composition、identity、Q不变和Q→Q*弱方程。
对operator-domain初态有strong方程，并把
D(\widetilde H(v))运输到D(\widetilde H(u))；
不声称这些operator domains本来恒定。常数Λ只产生标量相位，移除后仍为F1。
这是标准定理的当前模型应用，不是新发现一般传播定理。

## 5. 搬回原变量的准确结论

\[
 U_{\rm bulk}(u,v)
 =W_KR(u)\widetilde U(u,v)R(v)^\dagger W_K^\dagger.         \tag{F6}
\]
它是完整unitary传播，在共同E的时空测试上满足原完整clock方程，
保留R'、source connection和原所有势项。W_KQ为运输后的form class。
通过反向frame运输，C(W_KQ)中的这份分布弱解唯一。

不能直接由F4宣称原固定frame Hrel半有界：其D零模项不在Q型有界。
原fixed-u formal sum的自伴实现另由SNAPSHOT_DOMAIN证明。
本页不证明原snapshot自伴operator域随实际u的强运输；
不证明全K极限、完整非齐次约束、旧mean-SCE恢复或真实装置。
