# 原固定frame完整snapshot的自伴实现：辅助群构造

本页补一个不能从time-dependent frame自动推出的结论。
固定真实u*=J中的任一点，固定其g,d0,d1,d3。
去W后的原formal snapshot为
\[
 H_*={A_0\over2g_*}+{H_0\over\kappa}+{\cal D}
                     +{d_{0,*}\over\kappa}+d_{1,*}\kappa+d_{3,*}\kappa^3.
                                                               \tag{S1}
\]
E是κ紧支撑远离0、对有限source坐标Schwartz的联合光滑核。
E在COUPLED_FORMS的Q中型稠密，R(t)E=E，t导数仍在E。

## 1. 冻结真实系数，另引辅助参数

令R(t)=e^-itD，仅改变source frame。对任意有限辅助t区间，定义
\[
 \widetilde H_*(t)={A_0\over2g_*}
   +{\tfrac12\sum(e^{-2t}p_r^2+\omega_r^2e^{2t}q_r^2)\over\kappa}
   +{d_{0,*}\over\kappa}+d_{1,*}\kappa+d_{3,*}\kappa^3.
\]
同一Q、同一严格正g*,d3*仍适用；在每个compact t窗只需把有限的
e^±2t系数上下界替换。COUPLED_FORMS的闭型/传播证明因此给
\(\widetilde U_*(t,s)\)，其Q不变、唯一、强连续。
定义V(t)=R(t)\widetilde U_*(t,0)。R在Q上强连续且局部一致有界，
故V为unitary且V(t)Q=Q。

## 2. 为什么V真是群，而不是任意unitary曲线

V(t)ψ在E的光滑时间测试上满足i∂tξ=H_*ξ。
这一步以移动测试R(t)†e(t)作分部积分，D来自R'并准确相消。
反过来，任意C(Q)中的S1分布弱解，经R†运输后满足
tilde型方程：E型稠密、tildeH*:Q→Q*有界，使测试恒等式延拓到Q；
积分方程给C¹(Q*)。由上一页唯一性，它等于tildeU_*作用。

S1是autonomous。同一初态的V(t+s)ψ与V(t)V(s)ψ因此相等；
先对ψ∈Q用唯一性，再用Q在H中稠密扩展到全Hilbert。
负t由任意有限区间的同一构造及唯一性拼接。
所以V是强连续one-parameter unitary group。

## 3. Stone实现及其精确域

Stone定理给自伴A_*，V(t)=e^-itA_*，其域明确为
\[
 D(A_*)=\{\psi:\lim_{t\to0}[V(t)\psi-\psi]/t
                         \text{ exists in }{\cal H}\}.
\]
E⊂D(tildeH_*(0))：在compactκ/Schwartz核上formal微分结果属于H，
并由闭型表示的定义识别其operator action。
对ψ∈E，tildeU_*的strong导数和R'(0)于是给
\[
 A_*\psi=H_*\psi.                                         \tag{S2}
\]
因此这是原完整formal sum的一个真正自伴实现。
搬回固定W_K得原bulk snapshot的自伴实现W_KA_*W_K†。

未证明E是operator core，未证明最小闭包essentially selfadjoint，
未证明所有u的A_*域相同。实际u的F6传播已在其声明弱域成立；
它是否运输这些Stone snapshot domains，是另一命题，不能由S2跳步。

## 4. 原snapshot确实没有下界

这不妨碍Stone构造。固定geometry波包支撑在
κ∈[.9κ0,1.1κ0]，其余源固定，只将一个零模取Schwartz coherent
平移(q,p)=(L,−κ0L)。S1中该模的L²主系数为
\[
 {\kappa_0^2\over2}\langle\kappa^{-1}\rangle-\kappa_0
 \le {\kappa_0\over1.8}-\kappa_0<0.
\]
其他源与几何项相对L至多低阶或不变，所以〈H_*〉→−∞。
正g的geometry紧支撑高频波包又给上方无界。
这排除当前clock generator的半有界真空解释，
不把clock能量符号自动视为所有物理模型的实验不稳定性。
