# 有限clock patch的正常约束后物理态、gluing与源身份

本页使用COUPLED_FORMS的完整U_bulk，不再使用principal-only传播。
这是指定finite-K、measure、ordering、κ>0、边界和clock patch的
solution-space构造，不称为唯一量子化或全局group averaging。

## 1. 原约束与守恒物理内积

Rκ=κ^1/2、f=κ^-1/2，原选定约束为
\[
 C=R_\kappa(P_u+H_{\rm rel})R_\kappa,\qquad P_u=-i\partial_u.
\]
给定slice χ0∈Hslice=L²(dκ)⊗Hs，令
\[
 \chi(u)=U_{\rm bulk}(u,u0)\chi_0,\qquad \Psi(u)=f\chi(u).
\]
在compactκ/source时空测试上CΨ=0。
\[
 \langle\Psi_1,\Psi_2\rangle_{{phys},u}
 =\int\kappa\langle\Psi_1,\Psi_2\rangle_s\,d\kappa
 =\langle\chi_{01},\chi_{02}\rangle                         \tag{P1}
\]
与u无关。这里有正的slice flux及完整传播，不要求history属于flat
kinematic L²，也不宣称其不可能属于有限patch的某L²空间。

任意normal trace-one ρ0给正常physical density
ρphys(u)=Uρ0U†。raw solution kernel
\[
 \Gamma_\Psi(u,v)=fU(u,u0)\rho_0U(v,u0)^\dagger f
\]
只在其自然局部测试/加权意义下使用；正确归一化是
Tr(κΓΨ(u,u))=1，不把可能未定义的flat trace当物理trace。

## 2. 同一端点权重的组合律

令Kraw(u,v)=f U(u,v) f。其gluing必须用κdκ：
\[
 K_{\rm raw}(u,v)\,\kappa\,K_{\rm raw}(v,w)=K_{\rm raw}(u,w). \tag{P2}
\]
fκf=I和U组合律直接证明。漏掉中间κ会产生错误的传播。
同一初始density、端点及gluing在这里同时给出，仍限此有限模型。

另可给正的局部rigging form。对时钟内紧支撑、κ远离0的光滑测试φ，
\[
 T_C\phi=\int_J U(u0,u)f\phi(u)\,du,\qquad
 \eta_C(\phi,\psi)=\langle T_C\phi,T_C\psi\rangle\ge0.
\]
fCφ=(Pu+Hrel)Rκφ，分部积分及∂uU(u0,u)=+iU(u0,u)Hrel给
T_C Cφ=0。此处定义了一个clock-patch正解空间；
没有证明全局C的自伴域、端点时钟边界、跨g=0或RAQ唯一等价。

## 3. 一个保留原source裸边缘的实际正常初态

在原bulk χ-frame选择归一g∈Cc∞(0,∞)，
\[
 \rho_0=|g\rangle\langle g|\otimes\rho_{S,K}.
\]
当前ρS,K是两个Schwartz分支的秩二正常态（K≥2），来自同一有限初片
canonical运输；高模不被替换为另一种裸态。
W†(g⊗source branch)是联合compactκ/Schwartz核向量，因而属于
moving-frame共同域；此初态经完整U产生合法normal physical slice态。

初片source裸边缘恰为ρS,K。Pu在解空间由方程确定，不是独立carrier
上的任意指针。故这一存在性不违反前驱独立carrier谱排除。
它不证明该态的κ/Pu均值匹配旧mean历史，也不证明后续source边缘
保持原自由态；这些要另验。

## 4. 可观测量和原动量的区别

对任意bounded slice A，时钟u*的关系observable用
O_A(u)=U(u,u*) A U(u*,u)定义，raw回拉为f O_A Rκ。
它保持解空间及physical adjoint；一般不能声称与原C强对易。
source observable和κ与f对易，初片source边缘可以直接比较。

原flat Pκ的slice运输是
Rκ Pκ Rκ^-1=Pκ+i/(2κ)，并非自伴物理指针。
反向回拉slice形式Pκ为Pκ−i/(2κ)；半轴的一阶动量仍无由此得到的
自伴实现。原Pu沿解的作用为−Hrel，但相关均值/矩必须在共同域上定义。
本页没有把旧free pointer Pg认作Pu。

## 5. 本页真正新增与仍未完成

新增的是：完整finite-K传播支持的正slice内积、normal物理态、
加权gluing和明确局部正rigging form。一般关系解空间思想来自前驱RELATIONAL，
不是本轮重新发明；本轮把它接到原action完整finite-K算子上。

原mean恢复、同AE全场极限、任意局域约束、真实clock/control应力和
可校准装置仍未给出。有限模下正常physical态存在不提升经验状态。
