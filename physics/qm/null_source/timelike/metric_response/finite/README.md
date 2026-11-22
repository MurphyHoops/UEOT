# 原局部 lapse 家族的有限扰动与完整 Weyl 记录稳定性

本轮直接基线为 `719babd3386b9d9274d5c91dd0b8ad5e71688049`。
前轮 [局部响应](../../stress_kernel/response/README.md)只认证
\(\epsilon=0\) 的概率斜率。本节保留完全相同的局部度规族，
在整个 **\(|\epsilon|\le1\)** 上给出有限概率误差，
并保留同尺度原候选的分类门。没有把零点导数直接积分成有限误差。

方法是把未来场涂抹向共同过去传播，比较两个真实 Klein–Gordon 解，
再用固定过去的完整 Gaussian 协方差与实际相干位移分布计算概率差。
不需要把应力噪声 \(C_0\) 重新估到整条几何路径上，不重跑模式 ODE，
也没有构造完整非线性半经典引力解。

[检查器](check.py) · [精确有理端点](result.json)

## 1. 完全固定本节比较的物理对象

记 \(a(\eta)=\sqrt{3\cos2\eta}\)，
\(F_s=h(\eta)w_s(\chi)\)，其中
\[
h=b(32(\eta-3/32)),\qquad w_s=b(8\chi).
\]
\(b(x)=e^{-1/(1-x^2)}\) 于 \(|x|<1\)，其外为零。
沿用原非归一密度测试的
\(D=\int F_s\rho_f\,d{\rm vol}_g>0\) 和
\(\lambda=32768\)，定义
\[
\alpha=\frac{F_s}{D\lambda^2},\qquad
n_\epsilon=\sqrt{1-2\epsilon\alpha},
\]
\[
g_{\epsilon,\lambda}
=\lambda^2 a^2[-n_\epsilon^2d\eta^2+\gamma_{ij}dx^idx^j].
\tag{1}
\]
扰动时间区间 \(I=[a_I,b_I]=[1/16,1/8]\)，
未来仪器窗口 \([5/32,T]\)，\(T=3/16\)。

原仪器的空间窗保持为
\[
F_p(\chi)=Z_p^{-1}b(\chi/R_p),\qquad R_p=1/100,
\quad \int F_p\,d\Omega_3=1.
\]
时间权 \(w\ge0\) 光滑、支撑在原后续窗口且 \(\int w\,d\eta=1\)。
仪器读取
\[
Q_\epsilon=\int w(\eta)F_p(x)\Phi_\epsilon(\eta,x)\,d\eta d\Omega_3.
\tag{2}
\]
这是原单位归一 \(\widetilde J_\lambda=wF_p/a_\lambda^4\) 的涂抹，
物理增益 \(g_{\rm phys}=5\,{\rm gain}\)，
\({\rm gain}\in[199/200,201/200]\)。

共同过去的完整参考 Cauchy 数据、经典位移数据、候选幅度分布固定。
\(d_\lambda\) 在本轮比较中固定且 \(0<d_\lambda<1\)，不随 \(\epsilon\) 重调。
参考物理场协方差为共同基参考的 \(\lambda^{-2}\) 倍，
经典物理位移为 \(d_\lambda Yf\)，其中 \(a^2f'=\sqrt{27}\)。

未来测试窗口、孔径、增益、校准映射和问询前失败规则固定。
若改成每个度规上从过去开始连续计时、但不补偿累计钟差的固有钟窗口，
则测试也发生变化；那一时钟误差不包含在本节的固定测试证书内。

## 2. 用真实 backward KG 解表示未来观察

去掉常数同形因子 \(\lambda\)，采用基正则变量
\[
q=\phi,\qquad p=\frac{a^2}{n}\phi'.
\]
在单位三球上的真实场方程是
\[
q'=\frac{np}{a^2},\qquad p'=a^2{\rm div}(n\nabla q).
\tag{3}
\]
空间变化的 lapse 保留在散度内部，没有替换成齐次模式频率变化。

令 \(z_\epsilon=(q_\epsilon,p_\epsilon)\) 满足 (3)，
但在第二式加入源 \(+wF_p\)，并取 \(T\) 的终数据为零。
取辛配对
\[
\sigma(z,x)=\int(z_qx_p-z_px_q)\,d\Omega_3.
\]
有 \(\sigma(z_\epsilon,x_\epsilon)'=-wF_p x_q\)。
因此任意早于仪器的 Cauchy 面上，
\[
\sigma(z_\epsilon,x_\epsilon)=Q_\epsilon[x_\epsilon].
\tag{4}
\]
源是 \(wF_p\)，没有多乘或漏掉 \(a\) 或 \(\lambda\)。

扰动以后两个几何一致，所以 \(z_\epsilon(b_I)=z_0(b_I)\)；
扰动以前也一致，故可在同一个 \(\eta=a_I\) 上比较两者的初值，
并在同一固定参考态中评价 (4)。
光滑正 lapse 保持正常双曲性与共同 Cauchy 结构；
标准 Cauchy 存在唯一性只用于确认这些真实解存在，下面的常数由本节独立推导。

## 3. 包含零模的能量范数与梯度项

使用辅助能量范数
\[
N(z)^2=
\|p/a\|_2^2+\|a\nabla q\|_2^2+\|aq\|_2^2.
\tag{5}
\]
最后一项只是范数中的零模控制，不改变无质量场方程。

对无源 (3)，空间分部积分给
\[
\begin{aligned}
\frac{d}{d\eta}N^2={}&
2h_a\!\left[a^2(\|\nabla q\|_2^2+\|q\|_2^2)
-\|p/a\|_2^2\right]\\
&+2\int p\nabla n\cdot\nabla q
+2\int npq,\qquad h_a=a'/a .
\end{aligned}
\tag{6}
\]
因此
\[
\left|\frac{dN}{d\eta}\right|
\le r_n N,\qquad
r_n=|h_a|+\frac{\|n\|_\infty+\|\nabla n\|_\infty}{2}.
\tag{7}
\]
外加正则源 \(S\) 时，右侧再加 \(N(S)\)。
式 (6) 中的空间梯度项确实存在，不能因背景齐性而删除。

未扰动传播还可使用
\[
\begin{aligned}
N_1(z)^2={}&
a^{-2}(\|p\|_2^2+\|\nabla p\|_2^2)\\
&+a^2(\|q\|_2^2+2\|\nabla q\|_2^2+\|\Delta q\|_2^2).
\end{aligned}
\tag{8}
\]
这是 \(N((1-\Delta)^{1/2}z)\) 的准确谱表达。
未扰动算子与 \(1-\Delta\) 交换，所以同一个
\(r_0=|h_a|+1/2\) 控制 \(N_1\)。
不对空间变化的扰动算子假定这一交换关系。

## 4. 有限差方程，不使用一阶截断

令 \(\delta z=z_\epsilon-z_0\)。
在 \(I\) 内，它满足扰动传播算子下的真实受迫方程，
终数据为零，强迫准确为
\[
S_q=(n-1)p_0/a^2,\qquad
S_p=a^2{\rm div}((n-1)\nabla q_0).
\tag{9}
\]
将 \(\nabla n\) 项展开后，三分量范数的三角不等式给
\[
\boxed{
N(S)\le
\|n-1\|_\infty N_1(z_0)
+\|\nabla n\|_\infty N(z_0).
}
\tag{10}
\]
这里没有省略 \(O(\epsilon^2)\)，\(n\) 仍是式 (1) 的完整平方根。

设
\[
a_{\min}=\sqrt{3\cos(3/8)},\quad
E_0=e^{r_0(T-a_I)},\quad
E_I=e^{r_n(b_I-a_I)},\quad
E_F=e^{r_0(T-b_I)},
\]
其中右侧用相应区间的统一上界。
从零终数据及 \(\int w=1\)，
\[
N(z_0)\le E_0\|F_p\|_2/a_{\min},\qquad
N_1(z_0)\le E_0\|F_p\|_{H^1}/a_{\min}.
\]
于是
\[
\boxed{
N(\delta z(a_I))
\le\frac{E_IE_0}{a_{\min}}
\left[
\|F_p\|_{H^1}\int_I\|n-1\|_\infty
+\|F_p\|_2\int_I\|\nabla n\|_\infty
\right].
}
\tag{11}
\]

全部扰动系数都由准确恒等式控制：
\[
n-1=-\frac{2\epsilon\alpha}{1+n},\qquad
\nabla n=-\frac{\epsilon\nabla\alpha}{n}.
\tag{12}
\]
用整个 \(|\epsilon|\le1\) 的正下界 \(n_-\) 后，
式 (11) 右侧可写成 \(|\epsilon|B_N\)。
这是一条有限参数 Lipschitz 估计，并非在零点计算导数后直接积分。

## 5. 固定过去的完整参考协方差

原光滑准备的总对数变差 \(r<1/8\) 已冻结。
检查器还冻结并核对实际 `instrument/instrument.py` 的初值：
在 \(\eta=-1/8\) 以空间本征值零、宽度一取
\(u_0=1/\sqrt6\)、\(p_0=-i\sqrt{3/2}\)。
对每个非零模式 \(\omega_k=\sqrt{k^2-1}\ge\sqrt3\)，
归一正则协方差的最大方向由 \(e^{2r}/2\) 控制。
对 \(\ell_z=\sigma(z,\varphi)\)，有
\[
{\rm Var}_{G,\ne0}\ell_z
\le\frac{e^{1/4}}2
\sum_{k,j}\left[
a^2\omega_k|q_{kj}|^2+\frac{|p_{kj}|^2}{a^2\omega_k}
\right]
\le\frac{e^{1/4}}{2\sqrt3}N(z)^2.
\tag{13}
\]
求和覆盖完整谱和简并度；扰动后的模式混合只是改变 \(z\) 的系数。

零模保留原完整协方差。写
\(q_{\rm field}=q_{\rm seed}+Jp_{\rm seed}\)，
\({\rm Var}q_{\rm seed}=1/6,\ {\rm Var}p_{\rm seed}=3/2\)，
\(J\le25/216\)。这个界覆盖从种子片 \(-1/8\) 到
整个未来终点 \(3/16\)：区间长度 \(5/16\)、
全程 \(a_s^2\ge27/10\)，故 \(J\le(5/16)/(27/10)=25/216\)。
实际协方差比较片是 \(1/16\)，包含在此范围内。对零模配对，
\[
{\rm Var}\ell_z=p^2/6+\frac32(q-Jp)^2.
\]
相对于 \((aq,p/a)\) 的协方差矩阵，其最大特征值不超过迹
\[
\frac{a^2}{6}+\frac3{2a^2}+\frac32J^2a^2
\le\frac12+\frac59+\frac92(25/216)^2<\frac98.
\tag{14}
\]
因此包括所有零模交叉项的统一界为
\[
\boxed{{\rm Var}_G\ell_z\le\frac98 N(z)^2.}
\tag{15}
\]
没有在物理初片重置 \(qp\) 协方差。

令 \(V_\delta={\rm Var}_G(Q_\epsilon-Q_0)\)、
\(V_0={\rm Var}_GQ_0\)，则
\[
\sqrt{V_\delta}\le\sqrt{9/8}\,B_N|\epsilon|,
\quad
|V_\epsilon-V_0|\le
(2\sqrt{V_0}+\sqrt{V_\delta})\sqrt{V_\delta}.
\tag{16}
\]
\(V_0\) 直接消费原未来仪器的全模式上界。

## 6. 均匀位移相位另用精确辛恒等式

用 (11) 和粗能量界直接估相干相位会浪费小孔径的空间分辨率。
实际位移 \(f\) 在未扰动背景空间均匀，
\(p_f=a^2f'=\sqrt{27}\)。
对 \(z_\epsilon\) 与 \(f\) 求辛配对的导数，得到准确恒等式
\[
\boxed{
\mu_\epsilon-\mu_0
=-\int_I\!\int (n-1)f' z_{\epsilon,p}\,d\Omega_3d\eta.
}
\tag{17}
\]
其号对应式 (4) 的固定辛配对；概率误差使用绝对值。

由 (7)，
\[
\|z_{\epsilon,p}\|_2
\le a_{\max}E_IE_F\|F_p\|_2/a_{\min}.
\]
故
\[
|\mu_\epsilon-\mu_0|
\le
\frac{\sqrt{27}}{3\cos(1/4)}
\frac{a_{\max}E_IE_F\|F_p\|_2}{a_{\min}}
\int_I\|n-1\|_2
=:B_\mu|\epsilon|.
\tag{18}
\]
它只需要原扰动空间窗的 \(L^2\) 范数。
没有为经典位移引入小孔径的 \(H^1\) 损失，也没有删除局部空间响应。

## 7. 空间与时间常数的完整解析包围

原测试的 \(D\)、\(\|w_s\|_2\) 及 \(\int h/a\) 由冻结回执提供。
使用 \(a\le\sqrt3\)，
\[
\int h\le\sqrt3\int h/a.
\]
\(w_s\) 的最大值为 \(e^{-1}\)，最大梯度为
\(\max|b'|/R_s\)，\(R_s=1/8\)。
由 \(b''=b(6x^4-2)/(1-x^2)^4\)，
\(\max|b'|\) 位于 \(x_*^4=1/3\)，准确表达进入有向区间。

对原小孔径 \(R_p=1/100\)，由 \(\chi\le R_p/2\) 的内球，
\[
Z_p\ge Z_*=
\frac{\pi R_p^3}{6}e^{-4/3}(1-R_p^2/24)^2.
\]
旧回执给 \(\|F_p\|_2^2\) 的完整上界。
另用整个支撑球体积不超过 \(4\pi R_p^3/3\)，得到
\[
\|\nabla F_p\|_2^2
\le\frac{4\pi R_p^3}{3}
\left(\frac{\max|b'|}{R_pZ_*}\right)^2.
\tag{19}
\]
这是全空间导数范数估计，不是若干采样点的检查。

对整个有限参数区间，(12) 给
\[
\begin{aligned}
\int\|n-1\|_\infty
&\le|\epsilon|\frac{2e^{-1}}{1+n_-}
 \frac{\int h}{D\lambda^2},\\
\int\|\nabla n\|_\infty
&\le|\epsilon|\frac{\max|\nabla w_s|}{n_-}
 \frac{\int h}{D\lambda^2},\\
\int\|n-1\|_2
&\le|\epsilon|\frac{2\|w_s\|_2}{1+n_-}
 \frac{\int h}{D\lambda^2}.
\end{aligned}
\tag{20}
\]
所有值均由 mpmath 有向区间和精确有理输入计算；
结果不依赖模式采样或普通浮点解的误差猜测。

## 8. 完整候选概率和全部启动记录

设 \(t=10\,{\rm gain}\le201/20\)。
同一未来 Weyl 仪器的相干系数准确为
\[
z_\epsilon
=e^{-t^2V_\epsilon/(2\lambda^2)}
\chi_Y(t d_\lambda\mu_\epsilon).
\tag{21}
\]
时间序附加相位对两个 \(Z=\pm1\) 分支相同，不进入该相干系数。

旧制备逐分支有
\(|Y|\le(1+\sqrt3)/2\)，新制备 \(|Y|=1\)。
由 \(|e^{-x}-e^{-y}|\le|x-y|\) 对 \(x,y\ge0\) 成立，
以及特征函数的 Lipschitz 界，
\[
\boxed{
|\Delta p|
\le
\frac{t\,Y_{\max}}2|\Delta\mu|
+\frac{t^2}{4\lambda^2}
(2\sqrt{V_0}+\sqrt{V_\delta})\sqrt{V_\delta}.
}
\tag{22}
\]
这里已用 \(d_\lambda\le1\) 保守化。
也可利用 \(\mathbb E|Y|\le1\) 收紧旧态，当前保留更强的逐分支幅度覆盖。

完整沿用增益比 \([199/200,201/200]\)、相位误差 \([-1/100,1/100]\)、
额外对比 \([99/100,1]\)、概率偏置 \([-1/1000,1/1000]\)，
以及问询前 heralded 失败率 \([0,1/100]\)。
既有相位校准误差乘单位复数、额外对比不超过1，
固定的概率偏置在比较中消去，故 (22) 覆盖原完整校准范围。
问询前 heralded 失败概率固定，完整三标签概率为
\((f,(1-f)p,(1-f)(1-p))\)。
正号与负号变化相反，失败不变，故完整三标签的总变差距离
不超过同一个 (22) 上界。

代码将 (22) 写成
\[
B_P(\epsilon)=
|\epsilon|(B_{\rm coherent}+B_{\rm quantum,linear})
+\epsilon^2B_{\rm quantum,quadratic},
\tag{23}
\]
并在整个 \(|\epsilon|\le1\) 上验收。
实际区间计算得到以下结果；表中小数向保守方向舍入，
完整精确有理端点在 result.json。

| 量 | 整个 \(|\epsilon|\le1\) 上的界 |
|---|---:|
| 新候选全部启动正号概率变化 | \(<0.000057562\) |
| 旧候选全部启动正号概率变化 | \(<0.000077804\) |
| 完整三标签记录统一总变差 | \(<0.000077804\) |
| 旧候选全部启动正号概率 | \([0.463644054,0.486706718]\) |
| 新候选全部启动正号概率 | \([0.000597235,0.018279125]\) |

扩张后的旧概率仍 \(>9/20\)，新概率仍 \(<1/40\)。

所以原阈值 \(19/80\)、128 次独立新启动仍保证
每个候选的误判概率
\[
e^{-2(128)(17/80)^2}=e^{-289/25}<10^{-5}.
\]
该数是保留原门的稳定性证书；更紧统计界可由主审单独给出，
不能归因为新增物理效应或真实硬件性能提升。

## 9. 因果、时钟及未闭合责任

扰动后未来观察的坐标支撑与原来相同。
新 null 速度至多 \(n_+\)，程序核验
\[
R_p+T+(n_+-1)|I|<1/4<\arcsin(1/\sqrt3),
\]
所以需要的物理因果内域未越过原有限内球责任边界。

本节证明的是指定自由场、完整准备、原 finite lapse 家族和固定未来
Weyl 仪器的有限参数概率带。它没有给所有有界效应的统一误差，
没有认证有限路径上的完整应力作用素范数，
没有解完整量子 RSET 的几何反馈或非线性 SCE。

正 lapse 不意味着该度规由同一源自洽产生。
真正共同固有钟、实际读出/驱动漂移和总装置应力须分别处理。
没有真实实验数据、没有新 Lean、没有新增模式 ODE。

检查器还保留一个有界概率负控：
\(\sin^2(\pi\epsilon/2)\) 在零点导数为零，但在 \(\epsilon=1\) 等于1。
因此旧零点斜率本身确实不能充当本节有限概率带的证明。

## 10. 标准分析依据

- Bär–Ginoux–Pfäffle，
  [Wave Equations on Lorentzian Manifolds and Quantization](https://arxiv.org/abs/0806.1036)，第3章：
  正常双曲算子的 Cauchy 问题、因果传播及 Green 算子。
- Fewster–Schenkel，
  [Locally covariant quantum field theory with external sources](https://arxiv.org/abs/1402.2436)，§3、附录A：
  共同过去/未来识别及相对 Cauchy 演化。

文献提供存在与协变框架；本节能量范数、完整零模常数、
原小孔径的有限扰动误差及统计门由上述实际合同独立计算。
