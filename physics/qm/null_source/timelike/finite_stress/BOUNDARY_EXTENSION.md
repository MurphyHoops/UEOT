# 薄层源的真实量子边界扩张：完整谱独立性与准备过去条件

DYNAMIC_CHARGE 已把两类实际源接到同一非静态平均几何，并给出
平滑约束荷。本页继续检验一个明确候选：保持已经构造的薄层源的
完整裸边缘态，另加独立 tensor factor 的几何／装置约束荷，是否能
用初始相关消去剩余荷涨落。

答案是否定的，而且对该具体秩二态可直接证明完整能谱独立性。
本页没有把冻结的一般 QFI 界再次计作发现，也没有把强 Dirac
量子化声明为原 mean-SCE 的必要前提。

## 1. 实际秩二源的能量压缩

固定 BOUNDARY_STATE 的一个符号 eta=+ 或 -，记

\[
 \rho_S=(1-p)|u_0\rangle\langle u_0|
          +p|u_2\rangle\langle u_2|,\quad 0<p<1,
\]
\[
 u_0=\psi_0\otimes|0\rangle,\quad
 u_2=\psi_2\otimes|A_\eta\rangle,\quad
 M=\operatorname{span}\{u_0,u_2\}.
\]

两支因壳粒子数 0、2 正交。静态 incoming H 保持该壳数；
两支的完整总能量律均为 Ebar+sigma X，X 具有同一个 w² profile，
mean X=0、Var X=mu2>0、support X⊂[-1,1]。

设 alpha=2/(3V0 A)、C=alpha(H−Ebar)。
不仅有

\[
 P_M C P_M=0,\quad
 P_M C^2P_M=\alpha^2\sigma^2\mu_2P_M,                 \tag{133}
\]

而且对任意有界 Borel f，

\[
 P_M f(C)P_M=m_fP_M,\qquad
 m_f=\int_{-1}^{1}w(x)^2 f(\alpha\sigma x)\,dx.        \tag{134}
\]

对角元相同来自实际完整能量 profile；非对角元为零来自 H 的分壳。
这里 P_M 不与 H 对易，不能把 (133) 错读成 C 在 M 上恒为零：
C u_N 通常离开 M。M 内向量的 H 谱支撑在紧带中，
故 ||C P_M||≤alpha sigma；全部所需域清楚。

## 2. 所有保持该完整边缘的正常联合扩张都受约束

令 R 为任意正常迹一 source⊗G 联合态，Tr_G R=rho_S。
不要求 R 为乘积态，也不预先禁止纠缠。
因 Tr R[(I−P_M)⊗I]=0 及 R≥0，

\[
 R=(P_M\otimes I)R(P_M\otimes I).                    \tag{135}
\]

所以任意 G 侧有界效应 B 都满足

\[
 \operatorname{Tr}R[f(C)\otimes B]
 =m_f\operatorname{Tr}R[I\otimes B].                  \tag{136}
\]

因此 source 能谱 POVM 与任意独立几何／装置侧 POVM 的统计
严格独立。任何成功概率非零的 G-only 条件记录仍保留相同的
source 能量律。G 可以记录壳标签或其他信息，却不能从这个固定裸态
的扩张中得到能量 profile 内的涨落信息。

(136) 是对同一个联合态和 endpoint 的结论。此前有无互动并不重要，只要审查时的完整裸边缘仍相同。
若实施会改变该边缘的源—装置相互作用／联合测量，或引入含
source 的 dressing／观测量，就必须重新
验收新状态和完整总作用量；不在 (136) 的固定边缘合同内。

对 G-only 自伴 Z，(136) 还给完整联合谱律的乘积分解；
C−Z 的谱律是 mu_C 与反射 mu_Z 的卷积。因此任意宽度 l 的
最大区间概率 Q_(C−Z)(l)≤Q_C(l)，不要求有限方差。
连续 w² profile 不能由这个独立载体压成精确零残差。

## 3. 混合约束块不能被任意指定成完全相关

令 Z 为真正只作用 G tensor factor 的自伴几何／装置候选荷，
且在 R 中有有限二阶矩。先用有界谱截断 Z_n，
(133)-(135) 给 Tr R(C⊗Z_n)=0。C P_M 有界，Z_n→Z 于该态 L²，
故 Cauchy–Schwarz 允许取极限，得到

\[
 \operatorname{Cov}_{R,\mathrm{sym}}(C,Z)=0,
\qquad
 \operatorname{Var}_R(C-Z)
 =\operatorname{Var}_{\rho_S}C+\operatorname{Var}_RZ
 \ge\alpha^2\sigma^2\mu_2>0.                         \tag{137}
\]

所以这个具体新源不能在保留完整裸边缘的同时，靠独立几何荷的
初始相关把剩余荷方差进一步降到零。经典指定 Z=C 的 PSD 块
不满足此真实量子态合同。

常量 Z 在任意算符比较类中达到 variance 下界；若同时要求残差
均值为零，Z=0 达到对应 RMS 下界。这不是说真实 Einstein
几何荷可被自由指定为常量。

本页的精确下界是 alpha²sigma²mu2。上轮例子给
sqrt(Var C)<5.057e-14 是其上界，不能误写成 5.057e-14 的数值下界。
本页没有计算 profile mu2 的新数值下界。sigma→0 的非正常极限
同样不能签收为实际精确零荷态。

## 4. 有限正窗的修复应写成平滑的准备过去条件

不能把第 16 项的全过去拒收扩大成所有有限片解。
在同一个实际背景，源 d,b 和几何响应 e,s 都保留完整 Ward。
对 chi∈Cc∞(I)、integral chi=1、Psi_chi(t)=integral_t^infinity chi，
定义存在于明确共同域的平滑组合

\[
 C_{\rm source}=d(e^U\chi)-2b(e^Uh\Psi_\chi),
\]
\[
 C_{\rm geom}=e(e^U\chi)-2s(e^Uh\Psi_\chi),
\]
\[
 C_{\rm pre}[\chi]
 =2(b-s)(e^Uh\Psi_\chi).
\]

则严格恒等

\[
 (d-e)(e^U\chi)
 =C_{\rm source}-C_{\rm geom}+C_{\rm pre}[\chi].        \tag{138}
\]

这里 C_pre 明确定义为 b−s 的加权准备过去项，符号不与另一种
pressure residual 记号混用。如果 s=b 在整个窗 I 上成立，
C_pre 与窗内 chi 的选择无关；只有更早的真实差异可以贡献。
未来完整 density 匹配要求

\[
 \boxed{C_{\rm geom}-C_{\rm pre}=C_{\rm source}.}       \tag{139}
\]

全部过去也 s=b 时 C_pre=0，回到第 16 项的旧 incoming 门槛。
只要求未来匹配时，实际 prehistory 可以供给这项约束荷；
必须给它的来源、全源守恒、状态与装置，不能隐藏在边界常数里。

源端非紧支测试的本态 GNS L² 延拓已经在 DYNAMIC_CHARGE 构造。
新几何／装置及混合项也要证明自己的共同域；(138) 不冒充已经
构造了新量子几何、实际制备或任意 retarded noise 解。
若 Z=C_geom−C_pre 真是独立 G-only 算符且保留上述裸边缘，
它仍受 (137) 阻断；含源的真实准备项则要用新的总作用量审查。

## 5. 继续推进的具体对象

已关闭的候选是：保留这一个实际薄层源的完整秩二边缘，仅添加
独立 tensor factor 荷并指定反相关。排除不依赖 Z 正能量、
联合态可分离或 Gaussian 假定。

下一构造必须明确选择其实际允许变化：改变完整源边缘并计其代价；
或者从真实相互作用／关系 observable 导出非加性约束和准备过去。
无论选择哪条，都需同时给合法量子态、完整动量约束、边界 Ward、
总装置和同一因果正窗。它们是待完成的研究对象，不是这里默认
已经存在的修复。原确定性平均历史仍有效，整体物理统一仍 OPEN。
