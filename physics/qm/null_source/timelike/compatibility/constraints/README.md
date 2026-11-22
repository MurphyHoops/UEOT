# 可验证的初片约束相容候选与有限球边界

这里复用上一轮冻结的完整量子密度区间，构造同形背景上的 **Hamiltonian 与动量约束相容候选**。没有改变参考态以取得较小应力，也没有重新积分模式来替换旧核。

已经得到两类结果：

1. 保留原经典二阶动量 \(M_2=27\) 时，存在唯一正尺度根；运输整个场态时，在 \(\lambda\geq1\) 上也有唯一根。两个根族的量子份额仍然很大。
2. 在 \(\lambda=8192\) 上，用同一个 \(Q\) 相关地调整 \(M_2\)，可使初片约束精确成立；相对经典同形源的改变量小于 \(3.310\,10^{-6}\)。另给出明确有理数的 \(M_2\)，其初片 Einstein 约束相对残差小于 \(1.633\,10^{-6}\)。

这里的“相容”限于完全指定的缩放背景和参考态上的初片约束。它不是全半经典演化存在定理，也不是有限球外区量子态的构造。

[代码](constraints.py) · [精确有理端点回执](result.json) · [态与高阶数据责任](../state/) · [缩放及整段应力界](../scaling/)

## 1. 输入与三种不同的物理操作

原完整参考密度记为 \(Q=\rho_q(0)\)。输入来自 [上一轮应力回执](../../evolution/stress/result.json)：下端使用 \(k\leq256\) 加中频正性与无限尾拼接，上端使用已经证明的直接 UV 包围。代码固定该回执的 SHA。

采用同一最小耦合无质量场，固定物理减除尺度 \(\mu=1\)，有限曲率项在应力侧记为 \(+\alpha H^{(1)}\)。数字证书取 \(\alpha=0\)。定义

\[
 a_\lambda(\eta)=\lambda\sqrt{3\cos2\eta},\qquad
 g_\lambda=\lambda^2g,\qquad W_\lambda=\lambda^{-2}W,\qquad
 C=\frac1{96\pi^2}.
\]

运输的是整条辅助制备与完整参考核。在静态制备初刻，零模协方差为

\[
 {\rm Var}(q_0)_\lambda=\frac1{6\lambda^2},\qquad
 {\rm Var}(p_0)_\lambda=\frac{3\lambda^2}{2},\qquad
 {\rm Cov}(q_0,p_0)_\lambda=0.
\]

到了 \(\eta=0\)，原零模已经传播，\(q_0\) 方差和 \(q_0,p_0\) 相关项都必须保留。正确的任意切片运输是

\[
 V_\lambda=S_\lambda V S_\lambda^{T},\qquad
 S_\lambda=\operatorname{diag}(\lambda^{-1},\lambda).
\]

不能在初片重新把位置方差设回 \(1/(6\lambda^2)\)。初片密度只依赖保持正确运输的动量方差，因此本构造没有丢失零模能量。

经典齐性位移的规范动量记为 \(P\)，\(M_2=\mathbb E[P^2]\)，它不是 \((\mathbb E P)^2\)。其密度为

\[
 \rho_{\rm cl}(\eta)=\frac{M_2}{54\lambda^6\cos^3(2\eta)}.
\]

运输量子参考核并不决定经典位移如何运输：

| 合同 | \(M_2(\lambda)\) | 初片经典密度 | 与几何所需密度之比 |
| --- | --- | --- | --- |
| 保留原二阶动量 | \(27\) | \(1/(2\lambda^6)\) | \(\lambda^{-4}\) |
| 整个场态按 \(\Phi_\lambda=\Phi/\lambda\) 运输 | \(27\lambda^2\) | \(1/(2\lambda^4)\) | \(\lambda^{-2}\) |
| 经典 Einstein–标量解的几何同形缩放 | \(27\lambda^4\) | \(1/(2\lambda^2)\) | \(1\) |

第二行来自 \(P_\lambda=a_\lambda^2\Phi_\lambda'=\lambda P\)。第三行保留经典场函数，故 \(P_\lambda=\lambda^2P\)。对于原随机位移族，\(\sqrt{M_2/a_\lambda^6}\) 是 \(\Pi\) 的 RMS，不是每一分支的绝对幅度；回执据此命名 classical_Pi_rms_interval。

## 2. 精确初片约束与两个根族

初片 \(K_{ij}=0\)、\(a_{\lambda,0}^2=3\lambda^2\)，因此

\[
 \rho_{\rm required}=\frac1{2\lambda^2}.
\]

[B 的缩放推导](../scaling/README.md)给出

\[
 \rho_{q,\lambda}(0)
 =\lambda^{-4}[Q+C\log\lambda+6\alpha].
\]

对数项来自局域重整化补项，不能在固定物理方案下省略。齐性、各向同性源满足 \(j_i=0\)，所以动量约束同时成立。

### 固定 \(M_2=27\)：全正轴唯一根

令 \(x=\lambda^2\)，Hamiltonian 约束等价于

\[
 f(x)=x-\frac1x-C\log x=2Q+12\alpha.
\]

有

\[
 f'(x)=\left(\frac1x-\frac C2\right)^2+1-\frac{C^2}{4}>0.
\]

又 \(f(0+)=-\infty\)、\(f(+\infty)=+\infty\)，故对任意固定有限 \(Q,\alpha\)，存在且仅存在一个正根。这是全局单调性证明，不是数值搜索只找到一个根。

在本次 \(\alpha=0\) 与原 \(Q\) 区间下，严格向外简写为

\[
 1.8227907684<\lambda<14.9035735778.
\]

区间较宽来自 \(Q\) 的现有上界，而非求根误差；每个 \(Q\) 端点都执行了 112 次有向区间二分。

根处量子密度占所需总密度的比例为

\[
 \rho_q/\rho_{\rm required}=1-\lambda^{-4}>0.9094157446.
\]

因此这不是一个微小量子反馈的构造。

### 整个场态运输：\(\lambda\geq1\) 分支唯一

当 \(M_2=27\lambda^2\) 时，

\[
 x-C\log x=1+2Q+12\alpha.
\]

在 \(x\geq1\) 上，导数至少为 \(1-C>0\)。本次正 \(Q\)、\(\alpha=0\) 在该域有唯一根：

\[
 2.0054414923<\lambda<14.9369343564.
\]

不声称整个正轴只有一个根；对数项可允许另一个很小的 \(x\) 分支。这里

\[
 \rho_q/\rho_{\rm required}=1-\lambda^{-2}>0.7513548413.
\]

### 经典同形源：仅放大不是精确修复

若 \(M_2=27\lambda^4\)，经典源已精确占满几何所需密度。对每个有限 \(\lambda\geq1\)，\(Q+C\log\lambda>0\)，因此量子项留下严格非零的初片约束残差。相对残差可以变小，但不能把这一点改写为精确解。

## 3. 给定尺度下调节源：保留与同一个 \(Q\) 的相关性

在指定 \(\lambda\) 上取

\[
 M_2(\lambda,Q)=27\lambda^4-54\lambda^2[Q+C\log\lambda+6\alpha].
\]

代回原约束后精确消去。只要 \(M_2>0\)，可相应缩放原随机齐性位移的动量分布；这种光滑位移不改变参考核的短距离奇异结构。

程序在 \(\alpha=0\) 下认证：

| 尺度 | 相对经典同形 \(27\lambda^4\) 的减少比例 | 用途 |
| --- | --- | --- |
| \(\lambda=15\) | 约 \(0.0134491\) 至 \(0.987165\) | 整个旧 \(Q\) 区间均允许正 \(M_2\) |
| \(\lambda=8192\) | \(4.52898\,10^{-8}\) 至 \(3.30993\,10^{-6}\) | 初约束相容且相对源调整很小 |

减少比例为

\[
 \Delta=\frac{27\lambda^4-M_2}{27\lambda^4}
 =\frac{2[Q+C\log\lambda]}{\lambda^2}.
\]

原尺度 \(\lambda=1\) 则要求 \(M_2=27-54Q<0\)。所以没有用一个正经典幅度修复原尺度；这一失败被程序明确检出。

### 精确相关族与可指定有理数是两个合同

\(M_2\) 区间是函数 \(M_2(Q)\) 的像。不能任意配对其上下端与 \(Q\) 的上下端，也不能从该区间随便挑一个数就宣称约束为零。

另令 \(q_{\rm eff}=Q+C\log\lambda\)，以其有理包围中点 \(\widehat q\) 定义

\[
 \widehat M_2=27\lambda^4-54\lambda^2\widehat q.
\]

完整有理数保存在 explicit_rational_approximation 中。这个可明确指定的源满足

\[
 \rho_{\rm cl}(\widehat M_2)+\rho_q-\rho_{\rm required}
 =\lambda^{-4}(q_{\rm eff}-\widehat q),
\]

\[
 \frac{|G_{nn}-8\pi G\rho_{\rm total}|}{|G_{nn}|}
 \leq\frac2{\lambda^2}|q_{\rm eff}-\widehat q|.
\]

在 \(\lambda=8192\) 上，该相对误差小于 \(1.633\,10^{-6}\)；在 \(\lambda=15\) 上只能界到约 \(0.487\)。后者也说明，宽 \(Q\) 区间的中点不能被无代价地叫作精确初值。

## 4. 初约束之后的方程残差

令 \(c=\cos2\eta\)。精确相关的源调整给出

\[
 \rho_{\rm cl}=p_{\rm cl}
 =\frac1{2\lambda^2c^3}-\lambda^{-4}q_{\rm eff}(0)c^{-3}.
\]

于是指定同形背景上，总源与 Einstein 张量所需源的差为

\[
 \Delta\rho=\lambda^{-4}
 [\rho_{q,\rm eff}(\eta)-q_{\rm eff}(0)c^{-3}],\qquad
 \Delta p=\lambda^{-4}
 [p_{q,\rm eff}(\eta)-q_{\rm eff}(0)c^{-3}].
\]

初片 \(\Delta\rho=0\)，但 \(\Delta p\) 一般不为零。[B 的整段证书](../scaling/result.json)在 \(\eta\in[0,3/16]\)、\(\lambda\geq8192\) 上给两分量相对方程残差均小于 \(1\%\)。本目录供应相关源参数与初片恒等式；整段上界由该独立证书和主组装负责。

小方程残差不是到精确解的距离，也没有提供稳定性或存在定理。若用压力方程改变未来几何 jets，不能直接继续使用旧完整参考核。详见 [态与初值审查](../state/)。

## 5. 有限球、外区匹配与无陷界

### 内核中已经证明的部分

初片面积半径约束为

\[
 \mu'(R)=R^2\rho_{\rm total}(R),\qquad
 \gamma=\frac{dR^2}{1-2\mu/R}+R^2d\Omega^2.
\]

相容内核的总密度为 \(1/(2\lambda^2)\)，所以

\[
 \mu(R)=\frac{R^3}{6\lambda^2},\qquad
 2\mu/R=\frac{R^2}{3\lambda^2}.
\]

若核心面积半径同时改为 \(\lambda\)，边界紧致度为 \(1/3\)；若保留原半径 1，则为 \(1/(3\lambda^2)\)。这是局部约束与初片无球形边缘陷获的结论，不认证未来寿命。

### 两种条件性的正总密度延拓

旧 taper \(B(s)\) 在 \(s\leq1\) 等于 1，在 \(1<s<3/2\) 使用原五次多项式，外部等于 0。其导数 \(-30z^2(1-z)^2\) 保证 \(0\leq B\leq1\)。程序独立积分重得 \(7565/26208\)。

如果另有一个**总应力**实现下列轮廓，约束可精确积分：

| 规定的总密度 | 核心／支撑半径 | 条件 ADM \(GM\) | 全初片紧致度上界 |
| --- | --- | --- | --- |
| \(B(R/\lambda)^2/(2\lambda^2)\) | \(\lambda,\ 3\lambda/2\) | \(\lambda\,7565/26208\) | \(3/4\) |
| \(B(R)^2/(2\lambda^2)\) | \(1,\ 3/2\) | \(\lambda^{-2}\,7565/26208\) | \(3/(4\lambda^2)\) |

这是可核验的几何延拓条件，不是已构造的外区量子态。实际自由量子场的外区密度不会因写下 \(B^2\) 就自动等于该轮廓；真空极化、全局正性与中心核匹配仍待处理。原 taper 只有 \(C^2\)，也不能直接当作已经完成的全局光滑 Hadamard 背景。换成 \(C^\infty\) 外 taper 可以保留核心，但须重新计算质量与匹配，不能沿用原 ADM 数值。

### 原仪器与因果合同不会自动保留

所有面积半径和固有时同时按 \(\lambda\) 放大时，同形几何的共形零测地线与 \(\chi\) 边界不变。这保留原协议在**指定几何**中的坐标包含关系，但改变实际尺寸、时长和源参数，没有证明实际装置已经可制备。

若保留核心面积半径 1，齐性核边界变为

\[
 \chi_b(\lambda)=\arcsin[1/(\sqrt3\lambda)].
\]

原中心收齐时刻 \(\eta=3/8\) 仍在该核的几何因果区内，需要

\[
 \lambda<1/[\sqrt3\sin(3/8)].
\]

两个已认证根的下界都超过此门槛。因此原先依靠该齐性核担保的收齐步骤不能直接复用。对末窗 \(\eta=3/16\)，尺度根区间也不足以统一保证原边界保护。

这些比较没有把微因果性升级为量子引力保护，也没有证明新的共同半经典发展域已经存在。

## 6. 验证接口与责任范围

程序使用 80 位有向区间算术。根端点残差严格分离于零；继承的密度回执固定 SHA，源码与来源在执行前后冻结。精确有理端点是权威，终端浮点数仅作摘要。

负控覆盖原尺度负 \(M_2\)、遗漏对数项、混淆三种源合同、把相关区间当独立选择，以及固定旧半径后错误沿用收齐域。

复算：

~~~sh
python -B physics/qm/null_source/timelike/compatibility/constraints/constraints.py --check
~~~

重生：

~~~sh
python -B physics/qm/null_source/timelike/compatibility/constraints/constraints.py --write
~~~

主组装读取 JSON，不必导入本文件的全局精度。主要接口为 fixed_M2_root、entire_state_transport_root，以及 tuned_sources 中 lambda 为字符串 8192 的条目。根记录含 lambda_interval；调源记录含 Q_effective_initial、M2_interval、relative_decrease_from_classical_homothety 和 explicit_rational_approximation。source_sha256 路径相对 null_source 目录。

没有修改旧 evolution 证书、Core、书稿或公共状态，没有新增硬件数据，也没有认证真实制备、读数和驱动成本。

## 原始依据

- [Gourgoulhon, gr-qc/0703035](https://arxiv.org/pdf/gr-qc/0703035)：Einstein 约束与初值问题的 3+1 分解。
- [Anderson–Eaker, gr-qc/9906055](https://arxiv.org/pdf/gr-qc/9906055)：闭空间模式与局部重整化项；同形缩放由本轮 B 独立重推。
- [Juárez-Aubry、Kay、Miramontes、Sudarsky, 2406.01498](https://arxiv.org/abs/2406.01498)：Cauchy 面上重整化应力与离面四阶几何数据。
