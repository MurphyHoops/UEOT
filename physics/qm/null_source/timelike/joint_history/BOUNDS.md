# 全记录静态完成的限度：均值上限、条件方差与选择代价

## 1. 任意正能量静态热分支都有全局均值上限

保持 [HISTORY](HISTORY.md) 的同一 U0、M2 和 AE 处方。对任何实际 \(\mu>0\)，完整静态方程给
\[
G(x)=M_2\mu>0,\quad Jn=N(x)\ge0.
\]
在 G>0 的唯一正区间，
\[
G'=3G/x+3x+2\kappa>0.
\]
同时 G>0 蕴含 \(U_0x>(3+\kappa/x)/4\)。故
\[
N'(x)=3-6U_0x+\frac{\kappa}{2x}
<-\frac32-\frac{\kappa}{x}<0.
\]
已知 \(N(x_0)=0,G(x_0)=M_2\mu_{\rm old}\)。所以所有 n≥0 的正能量静态分支都满足
\[
\boxed{x\le x_0,\qquad \mu\le\mu_{\rm old}=L+2/\nu_0.}
\]
这是整个正支的定理，不限于本次小扰动根窗口。远小半径若 G≤0，不能承担实际正 μ，因此没有漏掉另一条正能量根。

## 2. 无论记录如何细分，原共同径向噪声仍有下界

允许有限、可数或连续的完整记录 i。要求非选择性保留新准备的完整 S0 谱，每支按上一节准备正热占据静态平均历史。记 μ_i、v_i 为条件均值、方差，则
\[
\bar\mu=L+1/\nu_0,\quad
\bar v=3/16+2L/\nu_0+1/\nu_0^2,
\]
\[
\bar v=\mathbb E_i v_i+\operatorname{Var}_i(\mu_i).
\]
由 \(0\le\mu_i\le\mu_{\rm old}\)，
\[
\operatorname{Var}_i(\mu_i)
\le\bar\mu(\mu_{\rm old}-\bar\mu)
=\bar\mu/\nu_0.
\]
因此
\[
\boxed{\mathbb E_i v_i\ge3/16+L/\nu_0>3/16.}
\]
这不要求条件零模态 Gaussian，也不依赖筛选强度或记录数。丢弃失败、换掉输入能量谱或离开指定静态物质模型，都是不同合同。

其物理含义很具体：原高半径 R≈1+d≈1.866 若被充分识别，条件均值会高于允许上限 \(\mu_{\rm old}\approx1.433\)，无法同时保留同一 U0 与非负热占据。热缓冲能容纳弱筛选的两种均值偏差，不能把原来的每个宏观能量支都转换成同 U0 的合法静态几何。

## 3. 全记录相对约束残差 RMS 严格大于10%

定义各支全空间平均密度算符 \(\widehat\rho_i=H_i/V_i\)，其均值是 \(3/(2x_i)\)。零模和高模条件乘积准备给
\[
\operatorname{Var}\widehat\rho_i
=\frac{M_2^2v_i}{4x_i^6}
+\frac{6n_i(1+n_i)}{\pi^4x_i^4}.
\]
故
\[
\mathbb E_i\frac{\operatorname{Var}\widehat\rho_i}
{[3/(2x_i)]^2}
\ge\frac{M_2^2}{9x_0^4}\left(\frac3{16}+\frac L{\nu_0}\right).
\]
原静态根恒等式及 E(x0)<0 给 \(M_2/x_0^2>1/L\)。于是
\[
\boxed{
\mathbb E_i\frac{\operatorname{Var}\widehat\rho_i}
{\langle\widehat\rho_i\rangle^2}
>\frac1{48L^2}>\frac1{100}.
}
\]
严格末端无需浮点：\(L^2=19/16+\sqrt3/2<33/16\)，故48L²<99<100。

这也可解释为条件平均 Hamiltonian 约束残差
\(\widehat{\mathcal C}_i=3/(2x_i)-\widehat\rho_i\)
的相对均方界，因为其均值为零。用 Gnn−2Tnn 记号时，分子与归一化平方都乘4，比例不变。完整记录加权后取平方根大于 \(1/(\sqrt{48}L)\approx0.10072316\)。

**这不是每支必大于10%的普遍定理，不是几何涨落预测，也不否定 mean-SCE。** mean-SCE 只匹配期望值。本结论关闭的是“在本模型中靠任意细分完整记录令额外二阶矩约束残差消失”的出口。若某引力理论要求更强联合约束，需另给能承接该源涨落的几何动力学和初态相关。

## 4. 不依赖静态几何模型的有限记录界

给定径向标签 r，输入 S0 有密度
\[
f(s|r)=\frac\nu2 e^{-\nu(s+r)/2}I_0(\nu\sqrt{sr}),\quad s\ge0.
\]
由 [NIST DLMF 10.32.1](https://dlmf.nist.gov/10.32.E1) 的积分表示及
\(1-\cos\theta\ge2\theta^2/\pi^2\)，
\[
I_0(z)\le e^z\frac{\sqrt\pi}{2\sqrt{2z}},\qquad I_0(z)\le e^z.
\]
当 r≥rmin>0、ν rmin≥16，分 s≥r/4 与 s<r/4 得整个混合谱
\[
f(s)\le F=\frac{\sqrt{\pi\nu}}{4\sqrt{r_{\min}}}.
\]
小 s 比较归结为 \(2\sqrt{x}e^{-x/8}/\sqrt\pi<1\)，x≥16；该函数递减且在16严格小于1。

任何保留非选择性输入 S0 谱的记录分解，都有 \(p_i f_i(s)\le f(s)\)。密度≤M的实随机变量满足
\[
\operatorname{Var}X\ge
\int_0^{1/(2M)}2u(1-2Mu)du=1/(12M^2).
\]
所以 N 个完整记录的最佳经典中心补偿后
\[
\sum_i p_i v_i\ge
\frac{4r_{\min}}{3\pi\nu}\sum_i p_i^3
\ge\frac{4r_{\min}}{3\pi\nu N^2}.
\]
若只保留 N 个成功记录、总概率 p，未归一界为
\(4r_{\min}p^3/(3\pi\nu N^2)\)，条件界为
\(4r_{\min}p^2/(3\pi\nu N^2)\)。

该一般有限 N 界不覆盖未计入记录的额外连续几何相关变量。上一节特殊静态模型的更强界则允许任意记录数，因为其物理方程另给了均值支持上限。

## 5. 保均值的强降噪还受到极小成功率限制

令
\[
I=[L-d/4,L+d/4].
\]
对 r=1 和1+d，I 中的 \(\sqrt s\) 与 \(\sqrt r\) 距离均大于2/25。这可只用43/50<d<7/8证明，并由独立有理检查复核。

表示 \(\sqrt{\nu S_0}=\|\sqrt{\nu r}\,e_1+Z\|\)，Z为标准二维 Gaussian。反三角不等式与二维径向尾给
\[
\Pr(S_0\in I)\le e^{-2\nu/625}.
\]
任何保谱成功筛选若满足
\[
|\mu_{\rm selected}-L|\le d/8,\quad
v_{\rm selected}\le d^2/128,
\]
则 Chebyshev 保证至少一半条件概率落在 I，因而
\[
\boxed{p_{\rm success}\le2e^{-2\nu/625}.}
\]
本次 ν=νprep>3.6×10^11，故
\[
\log p_{\rm success}<\log2-1.152\times10^9.
\]
这是自然对数上界，未把下溢的浮点零当成精确零概率。它覆盖保留实际源均值并达到1%相对 RMS 的目标；主要选择低半径标签虽可降方差，却显著改变源均值，不能作为该目标的实现。

## 6. 后续研究由哪些条件真正决定

新静态 CQ 准备已经解决完整条件平均历史。上述证明表明，在同一准备与物质合同内，仅优化筛选或增加记录精度都不能解决剩余源二阶矩责任。

新的有效工作必须明确改变哪项假设并实际计算后果，例如非静态联合历史、不同而合法的物质压力／准备预算、允许量子或随机几何自由度及其初态相关。改变模型后，本轮静态排除不应外推；但新模型必须重新给出完整态、总源、约束传播与可识别记录，不能只把这个上界从文字中删除。
