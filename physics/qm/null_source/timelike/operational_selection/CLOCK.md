# 同一实际零模制备的时间信息与有限辨别界

## 1. 资源与相位固定

本页使用 [joint_history/HISTORY.md](../joint_history/HISTORY.md) 的 unfiltered 实际制备：
两个中心纯 Gaussian，Var(P)=v=x0/4、Var(Q)=1/x0、Cov(Q,P)=0；
给定经典位移 p，动量律为 N(p,v I2)，Q 均值为零。
旧的另一种 Var(P)=A²/2 准备没有被代入。
令
\[
K=(P_1^2+P_2^2)/2=\pi^2M_2S_0,\quad
\kappa=\langle K\rangle=\pi^2M_2\mu,\quad
\mathbb E|p|^2=2\kappa-2v.
\]
实际自由演化是 U_theta=exp(−iK theta/A²)，其中
theta=eta−eta_ref+Theta^-1(e^-2U−1)；
共同初始剪切必须保留，不能随新几何重置。

为给可读能力一个有利的上界，允许全部 theta 无关经典 p 标记。
不开放其相干 purifying reference，不加入编码期间主动控制或额外时间敏感探针。
遗忘部分标记只会降低辨别能力。

## 2. QFI 与 canonical 校准时钟

给定 p，
\[
\operatorname{Var}_pK=v^2+v|p|^2.
\]
CQ 分块纯态 QFI 因而恰为
\[
J_{\rm flag}=\frac4{A^4}\mathbb E_p\operatorname{Var}_pK
=\frac{4(2v\kappa-v^2)}{A^4}
\in(1.318,1.319)\times10^{11}.
\]
不能将 4Var(K)/A⁴ 中庞大的经典径向方差算作已经可访问的相干时钟资源。
相干净化若额外开放，可以增加这一资源，属于不同合同。

令 D=sum_i{Q_i,P_i}/2，则 [D,K]=2iK，
D(theta)=D(0)+2theta K/A²。
实际去剪切制备有
\[
\operatorname{Var}D(0)=1+\mathbb E|p|^2/x_0
=\frac12+2\kappa/x_0.
\]
校准 Tcal=A²D/(2kappa) 的均值为 theta；
其初始方差 A⁴ Var(D)/(4kappa²) 与 QFI 下界一致。
相关消去后
\[
\operatorname{Var}(T_{\rm cal})J_{\rm flag}
=1+\frac{v(\kappa-v)}{2\kappa^2}>1.
\]
这项恒等式用相关参数计算，不能直接相乘宽区间再判定极小正差。

局域无偏 Cramér–Rao 给单份 SD(theta)>约2.7541×10^-6；
近静态 proper-time 模型单位约0.22508，不是 SI 秒。
CRB 需要相应无偏与正则性条件，下面的有限二元检验不需要这些条件。
标准量子测量统计背景见 [Braunstein–Caves](https://doi.org/10.1103/PhysRevLett.72.3439)。

## 3. 有限二元识别：精确重叠与全部记录

令 d=Delta theta、r=vd/A²。Gaussian 特征积分直接给
\[
F_p(d)=|\langle\psi_p|e^{-iKd/A^2}|\psi_p\rangle|^2
=\frac{\exp[-|p|^2vd^2/(A^4(1+r^2))]}{1+r^2}.
\]
纯态差的支撑最多二维，故其 trace distance 为 sqrt(1−Fp)，该结论适用于这里的无限维 Gaussian 态。
CQ 直和得到
\[
D_{\rm CQ}=\mathbb E_p\sqrt{1-F_p}
\le\sqrt{1-\mathbb E_pF_p}.
\]
指数凸性再给
\[
F_{\rm lo}(d)=\frac{\exp[-(2\kappa-2v)vd^2/(A^4(1+r^2))]}{1+r^2}
\le\mathbb E_pF_p.
\]
注意 CQ 的平方 fidelity 是 (E sqrt(Fp))²，通常不等于 E Fp。
本证明使用直接块 trace norm 与 Jensen，未混淆两者。

等先验最优二元错误率为 (1−D)/2，故任意共同最终读取有
\[
p_{\rm err}\ge[1-\sqrt{1-F_{\rm lo}}]/2.
\]
这些标准识别关系可在 [Fuchs–van de Graaf](https://arxiv.org/pdf/quant-ph/9712042) 核验；
本页的实际态公式与连续标记扩展则由上述直接推导给出。

在 d=1/sigma 这个相位差基准，证书给 Flo 约0.963092、
单份错误率下界约0.40394。这里 d 是校准的相位差，并非任意两条几何自动相差1/sigma。

N 次独立相同编码，保留全部经典标记，有
\[
D_N\le\sqrt{1-F_{\rm lo}^N}.
\]
要达到错误率≤e，必要条件为
\[
N\ge\left\lceil\frac{\log[4e(1-e)]}{\log F_{\rm lo}}\right\rceil.
\]
e=.05 时至少45次。没有证明45次足够，也没有构造最优设备。
独立重复是统计资源计数；在同一固定两场源中增添实体时钟、复制场或控制器，须重新计入总应力。

## 4. 真正跨几何相位的有限读取上界

对于任意有限方差纯态，由 1−cos x≤x²/2，
\[
1-|\langle e^{-iKd/A^2}\rangle|^2
\le d^2\operatorname{Var}(K)/A^4.
\]
平均 CQ 分量后得到不要求无偏的
\[
D_{\rm CQ}\le\min(1,|d|\sqrt{J_{\rm flag}}/2).
\]
接 [GEOMETRY.md](GEOMETRY.md) 的实际 incoming 相位差：

| 对齐方式 | 相位差上界 | 原零模全部经典标记下任意最终读取的 D 上界 |
|---|---:|---:|
| 同 conformal eta、同 epsilon | 2.244e−57 | 4.08e−52 |
| 同 proper time、同 epsilon，两个端点在 D | 3.345e−57 | 6.08e−52 |

实际证书还使用稳定的
L=log(1+r²)+(2kappa−2v)vd²/[A⁴(1+r²)]
而非在低精度中直接减1−exp(−L)。针对这个极小差的5%错误率目标，
同 eta 至少超过9e102次独立编码，同 proper time 至少超过4e102次。
这不是可实现性方案，只量化当前认证域和既定资源的分辨限制。

所有结果允许编码后参数无关辅助态及任意共同 CPTP 最终读取。
编码中的控制、重制备、多次未知参数查询、高模、额外物理探针和相干净化不在本上界内。
当前小数值也不能外推为认证域外快模的普遍不可观测性。

## 5. 下一物理责任

继续加高阶几何 jet 不能自动提供额外读取资源。
若希望通过精确读源选定历史，必须同时核算同一零模时钟的信息变化；
[INSTRUMENT.md](INSTRUMENT.md) 已给这一步的完整连续仪器与定量损失恒等式。
