# 同一有限度规上的中心固有钟与完整量子记录

工作基线：`f2b09fb2b8fd2235bde7017b060fc07ecc44b441`。
本节把[前轮有限 lapse 证书](../../metric_response/finite/README.md)的固定未来坐标测试，
推进为**同一个度规族、同一个准备态、实际中心固有钟控制的测量权**。
保留全部场模式、正则零模、原校准与询问前失败标签；没有引入另一套经典分支几何。

另给一个非零的操作预算：未来中央时钟的共同常数原点／同步偏置满足
\(|\beta|\le10^{-5}\)，物理钟读数误差为 \(\lambda\beta\)。
它与各站的差分计时误差、任意钟速漂移不同；后两者不在本证书内。

[可执行检查](check.py) · [精确有理回执](result.json)

## 1. 同一态与同一度规，只改变实际开关的时钟定义

沿用
\[
a(\eta)=\sqrt{3\cos2\eta},\quad \lambda=32768,
\]
\[
g_{\epsilon,\lambda}=\lambda^2a^2
[-n_\epsilon^2d\eta^2+\gamma_{ij}dx^idx^j],\qquad
n_\epsilon=\sqrt{1-2\epsilon F/(D\lambda^2)},\quad|\epsilon|\le1.
\]
原扰动支撑在 \(I=(1/16,1/8)\times\{\chi<1/8\}\)。
公共过去参考 Cauchy 数据、相干位移初值和旧／新幅度律不变。
经典物理位移是 \(d_\lambda Yf_\epsilon\)，\(0<d_\lambda<1\) 固定；
完整参考物理协方差是基参考协方差的 \(\lambda^{-2}\) 倍。

取球心 \(\chi=0\) 的共动世界线为中央时钟。
由于径向 lapse 的空间梯度在中心为零，该世界线保持测地。
以扰动之前的 \(\eta=0\) 同步为共同起点，定义
\[
\tau_0(\eta)=\lambda\int_0^\eta a(s)\,ds,\qquad
\tau_{c,\epsilon}(\eta)=\lambda\int_0^\eta a(s)n_\epsilon(s,0)\,ds.
\]
在扰动结束以后，
\[
\tau_{c,\epsilon}(\eta)=\tau_0(\eta)+\Delta\tau_c,\qquad
\Delta\tau_c=\lambda\int_I a(s)[n_\epsilon(s,0)-1]\,ds .
\tag{1}
\]

允许一个未来共同常数读数偏置：
\[
\widehat\tau_c(\eta)=\tau_{c,\epsilon}(\eta)+\lambda\beta,\qquad
|\beta|\le10^{-5}.
\tag{2}
\]
未来钟速仍是固有钟速；偏置不随未来时间改变。
控制整个小孔径的程序使用同一个已经标定的中央时间。
没有把每站未经校正的本地钟假定为这个共同钟。

## 2. 实际时间权必须带 Jacobian

本节始终使用生成归档名义概率的原时间程序，未选择另一个窗口。误差分析只需要其非负、归一和支撑性质；若实际更换程序，名义概率仍须重新认证。

原窗口程序以名义参数 \(u\) 写为 \(w(u)\ge0\)，
\[
\operatorname{supp}w\Subset(5/32,3/16),\qquad
\int w(u)\,du=1.
\]
空间测试保持
\[
F_p(\chi)=Z_p^{-1}b(\chi/R_p),\quad R_p=1/100,\quad \int F_p\,d\Omega=1.
\]

同一 proper-clock 程序把中央读数换成
\[
u(\eta)=\tau_0^{-1}(\widehat\tau_c(\eta)).
\]
因为未来 \(n_\epsilon=1\)，有
\[
\boxed{\frac{du}{d\eta}=\frac{a(\eta)}{a(u)}.}
\tag{3}
\]
程序密度按每单位中央固有时为 \(w(u)/[\lambda a(u)]\)；
乘实际中央固有时增量 \(d\tau_c=\lambda a(\eta)d\eta\) 后，
真实的正则源为
\[
\boxed{j_{\epsilon,\beta}(\eta,x)=
w(u(\eta))\,\frac{du}{d\eta}\,F_p(x).}
\tag{4}
\]
物理增益仍为原来的 \(5\,{\rm gain}\)，没有新增或漏掉 \(\lambda\) 因子。

换元立即给
\[
\widetilde w_{\epsilon,\beta}(\eta)=w(u(\eta))u'(\eta)\ge0,\qquad
\int\widetilde w_{\epsilon,\beta}\,d\eta=1.
\tag{5}
\]
因此它仍是同一孔径上的正归一时间测试。这个推导不要求 \(w'\) 的数值上界，
也不把一个未知高导数窗口当作平滑常数处理。

**省略 Jacobian 的反控。**
即使对简单时钟 \(\tau_0(\eta)=\eta^2/2\)，若有常偏移 \(c>0\)，
则 \(\eta(u)=\sqrt{u^2-2c}\)。
漏掉 Jacobian 会把归一质量变为
\[
\int w(u)\frac{u}{\sqrt{u^2-2c}}\,du>1
\]
（对任意正归一、支撑在 \([1,2]\) 内的窗口及 \(0<c<1/2\)）。
错误不只是重新命名时间。
检查器还用该区间的常密度计算出错误质量
\(\sqrt{4-2c}-\sqrt{1-2c}\)，在零点的导数为 \(1/2\)；
正确归一质量恒为1。光滑窗口也保留上述严格不等式。

## 3. 先证明新测试没有越出受控区域

定义
\[
L=5/32,\quad T=3/16,\quad \delta_{\rm guard}=10^{-5},\quad
T_g=T+\delta_{\rm guard},
\]
\[
a_{\min}=\sqrt{3\cos2T_g},\qquad a_{\max}=\sqrt3.
\]
使用前轮在原扰动区间 \(I\) 上的完整有限界
\(J_n|\epsilon|\ge\int_I\|n_\epsilon-1\|_\infty\,d\eta\)，得到
\[
|\Delta\tau_c|/\lambda\le a_{\max}J_n|\epsilon|.
\]
先在已知几何区间 \([L-\delta_{\rm guard},T+\delta_{\rm guard}]\)
检查 \(a>0\) 与钟映射严格单调（同一估计也覆盖后述同步事件的
\(u=9/64\)，其两个保护端点都在扰动结束后）。数值严格余量保证
\[
a_{\min}\delta_{\rm guard}>a_{\max}J_n+|\beta| .
\]
因此对每个名义 \(u\in[L,T]\)，两个已知端点 \(u\pm\delta_{\rm guard}\)
的钟读数分别在 \(\tau_0(u)\) 两侧；连续性与单调性先给唯一逆像，
随后正导数反演给
\[
\boxed{|\eta_{\epsilon,\beta}(u)-u|
\le\zeta_{\epsilon,\beta}
=\frac{a_{\max}J_n|\epsilon|+|\beta|}{a_{\min}}.}
\tag{6}
\]
检查器对整个 \(|\epsilon|\le1,|\beta|\le10^{-5}\) 认证
\(\zeta<\delta_{\rm guard}\)。反演的端点夹逼因此自洽：
\[
\operatorname{supp}\widetilde w
\Subset(L-\delta_{\rm guard},T+\delta_{\rm guard}),
\qquad L-\delta_{\rm guard}>1/8.
\]
全部开关仍在度规扰动结束后。

此处没有延长旧平均 RSET、密度噪声或原窗口 \(V_0\) 的有效域。
下面只重新估计新未来测试向共同过去的能量传播。

## 4. 共同过去的协方差与未来的全模式时间导数

基参考态仍在同一个预扰动片 \(\eta_a=1/16\) 上评价。
前轮已经认证并冻结
\[
{\rm Var}_G\,\sigma(z,\varphi)\le\frac98N(z)^2,\quad
N(z)^2=\|p/a\|_2^2+\|a\nabla q\|_2^2+\|aq\|_2^2 .
\tag{7}
\]
它使用实际非零模准备及原零模完整 \(qp\) 协方差。
旧 \(r<1/8\)、\(J\le25/216\) 只用于这个旧片；
不把它们的旧未来终点改成 \(T_g\)。

在新的未来区间上，未扰动 KG 能量增长率重新取
\[
r_0=\tan(2T_g)+\tfrac12,\qquad
E_0=e^{r_0(T_g-\eta_a)}.
\tag{8}
\]
于是任意未来片 \(s\le T_g\) 的测试向过去传播由 \(E_0\) 控制。
记 \(F_0=\|F_p\|_2\)、\(F_1=\|F_p\|_{H^1}\)，其全空间上界沿用同一
空间孔径的冻结证据。

原背景上的空间场平均为 \(Q_0(s)=\int F_p\varphi(s,x)d\Omega\)。
其时间导数由片上正则测试
\[
(q_{\rm test},p_{\rm test})=(F_p/a(s)^2,0)
\]
表示，因为 \(p_{\rm field}=a^2\varphi'\)。
因此
\[
N_{\rm slice}(Q_0'(s))=F_1/a(s)\le F_1/a_{\min}.
\]
结合 (7)–(8)，得到**包含全部空间模式和零模**的统一界
\[
\boxed{
\sqrt{{\rm Var}_G Q_0'(s)}
\le\sqrt{9/8}\,E_0F_1/a_{\min}.
}
\tag{9}
\]
有限 \(H^1\) 损失完整保留；没有用有限模或采样值代替这个界。

## 5. 对真实传播与真实时钟作两个有限比较

用 \(\widetilde w\) 表示式(5)的实际权，精确分解
\[
Q_\epsilon(\widetilde w)-Q_0(w)
=
[Q_\epsilon(\widetilde w)-Q_0(\widetilde w)]
+[Q_0(\widetilde w)-Q_0(w)].
\tag{10}
\]
第一项是同一实际测试的度规传播差；第二项是同一未扰动场的时钟移窗。
两项在同一个过去场代数中比较，所以可以对其协方差范数使用三角不等式。

### 度规传播项

前轮有限传播的完整 KG 系统和空间 lapse 梯度保留。
令 \(E_I=e^{r_n|I|}\)，\(E_F=e^{r_0(T_g-1/8)}\)，其中 \(r_n\) 沿用
原扰动区间上的正 lapse、梯度和背景界。
因为新权仍正归一、同一空间 \(F_p\)，前轮证明直接重算为
\[
N_{\rm prop}\le
\frac{E_IE_0}{a_{\min}}
\left[
 F_1\int_I\|n-1\|_\infty+
 F_0\int_I\|\nabla n\|_\infty
\right].
\tag{11}
\]
相干位移的精确辛恒等式给
\[
|\Delta\mu_{\rm prop}|
\le
\frac{\sqrt{27}}{3\cos(1/4)}
\frac{a_{\max}E_IE_FF_0}{a_{\min}}
\int_I\|n-1\|_2.
\tag{12}
\]
这里是有限比较，不是一阶导数截断。

### 纯时钟项

换元后，第二项准确为
\[
Q_0(\widetilde w)-Q_0(w)
=\int w(u)\int_u^{\eta_{\epsilon,\beta}(u)}Q_0'(s)\,ds\,du .
\]
用 (9)、正归一权和 Minkowski 不等式，
\[
\boxed{
\sqrt{{\rm Var}_G\Delta Q_{\rm clock}}
\le\sqrt{9/8}\frac{E_0F_1}{a_{\min}}\zeta_{\epsilon,\beta}.
}
\tag{13}
\]
基经典齐性位移 \(a^2f'=\sqrt{27}\) 则给
\[
\boxed{
|\Delta\mu_{\rm clock}|
\le\frac{\sqrt{27}}{3\cos(2T_g)}\zeta_{\epsilon,\beta}.
}
\tag{14}
\]
式(13)–(14)的差分界对正归一平滑 \(w\) 一致有效，完全不需要控制 \(w'\)。后面的绝对概率区间仍针对归档的原时间程序；差分界的一致性不授权把旧名义概率搬到另一程序。

合并后令
\[
B_N=N_{\rm prop}+\frac{E_0F_1}{a_{\min}}\zeta,\quad
B_\mu=|\Delta\mu_{\rm prop}|+
\frac{\sqrt{27}}{3\cos2T_g}\zeta,\quad
\sqrt{V_\delta}\le\sqrt{9/8}B_N .
\tag{15}
\]
原 \(V_0\) 仍是归档名义窗口的实际上界，没有被搬到新窗口；
新窗口与它的差由 (15) 控制。

## 6. 完整概率与两种时钟预算

Weyl 特征系数与原证明相同：
\[
e^{-t^2V_{\epsilon,\beta}/(2\lambda^2)}
\chi_Y(t d_\lambda\mu_{\epsilon,\beta}),\qquad t\le201/20.
\]
因此相对归档名义窗口，
\[
\boxed{
|\Delta p|
\le\frac{tY_{\max}}2B_\mu+
\frac{t^2}{4\lambda^2}(2\sqrt{V_0}+\sqrt{V_\delta})\sqrt{V_\delta}.
}
\tag{16}
\]
旧候选 \(Y_{\max}=(1+\sqrt3)/2\)，新候选 \(Y_{\max}=1\)。

沿用原增益、相位、对比、概率偏置及询问前 heralded 失败合同。
比较时同一场增益／相位／对比／偏置校准参数和失败率保持固定；最终区间对允许参数一致成立。含 \(\beta\) 行是相对归档理想名义程序的总误差预算，包含整个共同钟偏置；它不声称相同 \(\beta\) 本身造成两模型间的额外差。
失败标签不丢弃，三标签总变差不超过同一个旧候选概率变化上界。

实际有向计算得到：

| 中央钟合同 | 坐标时移上界 | 旧候选概率差上界 | 新候选概率差上界 |
|---|---:|---:|---:|
| 理想中央固有钟，\(\beta=0\) | \(<9.129097\times10^{-8}\) | \(<8.115450\times10^{-5}\) | \(<6.059996\times10^{-5}\) |
| 共同常数偏置 \(|\beta|\le10^{-5}\) | \(<6.076525\times10^{-6}\) | \(<3.013810\times10^{-4}\) | \(<2.603350\times10^{-4}\) |

相对于原名义程序的完整三标签总变差，分别不超过各行旧候选的概率差上界。
全部启动的实际概率带为：

| 中央钟合同 | 旧候选 plus 概率 | 新候选 plus 概率 |
|---|---:|---:|
| 理想中央固有钟 | \([0.46364070,\ 0.48671007]\) | \([0.00059419,\ 0.01828217]\) |
| 含共同常数偏置预算 | \([0.46342047,\ 0.48693030]\) | \([0.00039446,\ 0.01848190]\) |

表中小数向外放宽，回执保存精确有理端点。
\(\lambda\beta\) 的物理钟读数误差上限为0.32768个本模型的时间单位；
它没有被解释为未经标定的 SI 秒或硬件实现精度。

两个时钟预算下均严格保留
\(p_{\rm old}>9/20,\ p_{\rm new}<1/40\)。
所以[前轮独立64次全记录规则](../../metric_response/README.md)仍适用：
固定64次启动，plus至少11次判旧，其余判新。
每次条件于完整过去必须满足新的中央钟／共同偏置、准备、校准和失败合同。
允许按过去预先选择 \(\epsilon,\beta\) 及原校准参数；
仅有单次边缘概率不足以推出该重复结论。
本节复用原 Chernoff 证明，不把新的单次门当成已经执行的硬件统计实验。

## 7. 同步的因果余量与实施边界

选择以同一中央钟程序 \(u_{\rm sync}=9/64\) 触发的同步发送事件。
其实际坐标时刻位于 \(9/64\pm\delta_{\rm guard}\)，两个端点都晚于扰动结束。
无需假定一个额外的绝对坐标时钟精确触发该事件。
未来背景上径向 null 传播满足 \(\Delta\eta=\chi\)，小孔径半径为 \(1/100\)。
于是
\[
5/32-9/64-1/100-2\times10^{-5}>0 .
\tag{17}
\]
中心消息能在最早可能开关前到达整个孔径。
检查器还保留原内球的因果支撑余量。

式(17)只证明这一同步合同有几何因果余量。
实际控制协议、光学／电子转移误差、中央钟校准以及准备／驱动／装置总应力
仍须设备证据。空间上不同的站钟误差不会被一个共同 \(\beta\) 包含。
本节也没有证明任意钟速漂移、自由落体分布装置或任意有界效应的统一界。

本轮关闭的是同一自由场与同一外加有限 lapse 路径上的
**实际中央固有钟测量权及指定全记录概率出口**。
没有将旧平均 RSET／密度噪声证书延伸到整个有限路径，
没有引入经典逐分支几何，也没有完成非线性 SCE 或完整量子反馈。

程序对旧输入按 f2b09fb2 精确字节身份冻结，并核对计算前后哈希。
新场模式 ODE、几何 ODE、硬件数据和 Lean 定理均为零。
