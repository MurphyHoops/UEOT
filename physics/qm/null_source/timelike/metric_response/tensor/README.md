# 真正局部的张量度规读出与完整应力噪声

直接基线：719babd3386b9d9274d5c91dd0b8ad5e71688049。旧目录保持冻结；本目录新增一个空间非齐次、规范相容的 tensor 通道，接续 [局部约束接口](../../stress_kernel/geometry/README.md)。

**本次出口有三项：**构造非零、真正局部的 TT 度规测试；用完整张量波动方程把该测试接到合法四维应力噪声，并消去所有齐次初值；给原完整参考态的全模式二次应力上界。另得到一个限制此前调源结论的重要反例：**齐性相干位移对这整个空间无迹应力子代数没有作用，旧、新振幅制备在本 tensor 通道的噪声完全相同。**

这里使用经典 Einstein–齐性标量背景上的受迫线性 tensor 方程。完整量子 RSET 的度规反馈尚未纳入，量子平均残差也没有被改写成零。因此本结果不是完整 Einstein–Langevin 解或完整 SCE 解。

[检查程序](check.py) · [实际有向回执](result.json)

## 1. 固定物理合同与真正的空间非齐次算子

单位三球度规记为 \(\gamma\)，其 Ricci 张量为 \(2\gamma\)。沿用
\[
A(\eta)=\sqrt{3\cos2\eta},\quad a_\lambda=\lambda A,\quad
4\pi G=\hbar=1,\quad
g_{ij}=a_\lambda^2(\gamma_{ij}+h_{ij}).
\]
\(h\) 是相对空间应变，不是带有 \(a_\lambda^2\) 的度规分量。先在纯 tensor 部分要求
\[
D^ih_{ij}=0,\qquad \gamma^{ij}h_{ij}=0.
\]

最小、无质量、齐性经典标量满足 \(A^2 f'=\sqrt{27}\)。检查程序独立验证
\[
3(\mathcal H^2+1)=f'^2,\qquad
-(2\mathcal H'+\mathcal H^2+1)=f'^2,\quad
\mathcal H=A'/A=-\tan2\eta .
\]
纯 TT 扰动的体积一阶变分为零，且不改变 lapse，所以 \(\delta f=0\) 满足线性标量方程；该经典标量没有 tensor 各向异性应力。

这里的局部张量算子是
\[
\boxed{\mathcal D_T h=h''+2\mathcal Hh'-\Delta_\gamma h+2h.}
\tag{1}
\]
\(\Delta_\gamma=D^kD_k\) 是作用于协变二阶张量的粗 Laplacian；它不是标量模的替代品。单位三球的常曲率交换恒等式保证它保持 TT 子空间。

在 \(h\) 的上述归一下，受迫方程为
\[
\boxed{\mathcal D_T h=4\,\xi^{\rm TT}_{ij,\rm cov}.}
\tag{2}
\]
右侧是共形坐标中的协变空间应力；若使用正交标架各向异性应力 \(\pi\)，则为 \(4a_\lambda^2\pi\)。这个因子不能与旧密度二次式的 \(1/2\) 混用。[Durrer 的式(30)、(39)、(69)](https://arxiv.org/pdf/astro-ph/0402129)分别给出 \(h_{\rm spatial}=2H^{(T)}\)、tensor 规范不变性和带 \(2K\) 的方程；代入 \(4\pi G=1\) 正好得到式(2)。

约束也有明确归属。纯空间 TT 源配上零的 \(0\mu\) 分量是背景协变守恒的：时间散度仅含其迹，空间散度仅含 \(D^i\xi_{ij}\)，都为零。线性 Hamiltonian、动量约束在这个扇区为零，并由方程保持。一般应力的 tensor 投影可以是空间非局部的；下面的局部 TT 配对会自动选取其 tensor 部分，无需将非局部投影操作冒充为局部测量。

## 2. 任意小球内的显式紧支撑 TT 张量

采用球心附近的 stereographic 坐标 \(x=(x,y,z)\)，
\[
\gamma_{ij}=\Omega^2\delta_{ij},\quad
\Omega=\frac2{1+r^2},\quad \chi=2\arctan r,\quad
r_0=\tan(1/16).
\]
定义标准平坦 bump \(b(s)=e^{-1/(1-s^2)}\)（\(|s|<1\)，外部为0），以及
\[
f(x)=z^3 b(r/r_0),\qquad s_{ij}=\operatorname{diag}(f,-f,0).
\]
平直线性 Ricci 与 Schouten 为
\[
R'_{ij}=\tfrac12(\partial_i\partial^ks_{kj}
+\partial_j\partial^ks_{ki}-\Delta s_{ij}),\qquad
S'_{ij}=R'_{ij}-\tfrac14\delta_{ij}R',
\]
并定义本目录约定的线性 Cotton–York
\[
t_{ij}=\epsilon_i{}^{kl}\partial_kS'_{lj},\qquad
\boxed{\tau_{ij}=\Omega^{-1}t_{ij}/M.}
\tag{3}
\]
这些都是局部微分操作，故支撑留在 \(\chi<1/8\)，边界无限阶平坦。程序对任意光滑 \(f(x,y,z)\) 直接符号验证 \(t\) 对称、无迹、无散度，及其每个分量的三阶导数绝对系数和不超过1。也直接核对三维 conformal 散度恒等式
\[
D_\gamma^i(\Omega^{-1}t)_{ij}=\Omega^{-3}\partial^it_{ij}.
\]
该构造与 [Beig 的紧支撑 TT/Cotton 框架及式(2.13)](https://arxiv.org/pdf/gr-qc/9606055)一致；这里给出了自己的具体 seed、非零点和归一证据。

在球心，
\[
t_{12}=t_{21}=-3/e,\qquad
\tau_{12}(0)=-3/(2eM),\qquad
|\tau(0)|_\gamma=\frac{3\sqrt2}{8eM}>0.
\tag{4}
\]
所以本测试不是零张量。

### 固定归一，防止任意缩小测试冒充降噪

\(M\) 是下面算法确定的唯一正整数，不是为了使方差小而自由调节的参数。令 \(u=x/r_0\)、\(v=(1-|u|^2)^{-1}\)，从 \(P_0=u_z^3\) 出发递推
\[
P_{\alpha+e_i}=\partial_{u_i}P_\alpha
 +2u_i v^2(\partial_vP_\alpha-P_\alpha).
\]
于是
\[
\partial_x^\alpha f=r_0^{3-|\alpha|}
 P_\alpha(u,v)e^{-v}.
\]
若 \(P_\alpha=\sum c_{\beta p}u^\beta v^p\)，取
\[
B_m=\max_{|\alpha|=m}\sum_{\beta,p}|c_{\beta p}|\,\mu_p,\quad
\mu_0=e^{-1},\quad \mu_p=p^pe^{-p}\ (p\ge1).
\]
因为 \(|u_i|\le1,v\ge1\)，这是明确的导数上界。程序用70位有向区间计算它们，并固定
\[
\boxed{M=\left\lceil3\,\overline B_3\right\rceil,\qquad
\|\tau\|_{\gamma,F,\infty}\le3\,\overline B_3/M\le1.}
\tag{5}
\]
实际有向计算固定 \(\boxed{M=7640}\)。回执保存这个整数、所有0至5阶上界以及式(4)的正下界。这里是 Frobenius 范数；只用算子范数会在下一节 Hessian 收缩时漏掉因子。本归一不声称 \(\|\tau\|_\infty=1\)，也不声称测试已达到最优灵敏度。

## 3. 裸度规的局部伴随读出、规范与初值

时间窗口保持原来已经认证的
\[
\psi(\eta)=b(32(\eta-3/32)),\quad
\Psi_{ij}=\psi\tau_{ij},\quad Q=\mathcal D_T\Psi .
\]
它们都支撑在
\((1/16,1/8)\times\{\chi<1/8\}\)。式(7)对应的四维应力测试为 \(F^{ij}=4A^2\psi\tau^{ij}/a_\lambda^4\)、\(F^{0\mu}=0\)，相对于物理体积元 \(a_\lambda^4d\eta d\Omega\) 光滑且紧支撑，因而属于合法测试域。
定义真正只配对度规的线性记录
\[
\boxed{\mathcal O[h]=
\int A^2Q^{ij}h_{ij}\,d\eta\,d\Omega.}
\tag{6}
\]
指标都由 \(\gamma\) 升降。式(6)是一个固定、可以校准的度规加权读出；没有把“应力源”直接定义为几何记录。

\(\mathcal D_T\) 在 \(A^2d\eta d\Omega\) 中形式自伴。程序核对时间 Green 恒等式；空间部分使用 S³ Laplacian 的积分分部。因 \(\Psi\) 紧支撑，所有边界项为零，式(2)给
\[
\boxed{\mathcal O[h]
=4\int A^2\psi\tau^{ij}\xi_{ij,\rm cov}\,d\eta\,d\Omega.}
\tag{7}
\]
因此任何满足齐次 tensor 方程的自由扰动在这个特定读出中都为零。其初值可未知、随机，也可与源相关，不需另加“初始度规噪声为零”的假设。

\(Q\) 非零：否则非零紧支撑 \(\Psi\) 会是零终端 Cauchy 数据的齐次张量波解，与唯一性矛盾。这一论证同时说明本读出有明确限制：它是特别设计来排除自由引力波的源响应记录，不能代表任意局部应变测量。

由于 \(Q\) 是空间 TT，
\[
\delta_\zeta h_{ij}=D_i\zeta_j+D_j\zeta_i
       +2\mathcal H\zeta^0\gamma_{ij}
\]
与它的配对为零，故式(6)在完整一阶坐标变换下不变。背景 tensor 应变为零，时间标签的一阶变动也不产生背景 tensor 项。纯 TT 的 lapse 一阶不变，但这里仍是明确的同形测试合同，不把它提升为未知硬件或有限扰动下的任意时钟结论。

### 响应校准与记录误差增益

定义有限的正量
\[
J=\int A^2|Q|_\gamma^2>0,\quad
q_\infty=\|Q\|_{\gamma,F,\infty}>0,\quad
E_Q=\int A^2|Q|_\gamma.
\]
单位点态 Frobenius 应变 profile \(h_{\rm cal}=Q/q_\infty\) 的响应为
\[
\mathcal O[h_{\rm cal}]=J/q_\infty>0,\qquad
|\mathcal O[\delta h]|\le E_Q\|\delta h\|_{\gamma,F,\infty}.
\tag{8}
\]
这给出非零校准和误差传递。若把输出按单位 profile 归一，方差必须同时乘 \(q_\infty^2/J^2\)。本轮没有数值认证 \(J/q_\infty\)，因此后面的原始读出噪声数字**不被表述为单位应变灵敏度**。

还有直接的源校准：对 \(\xi_{ij}=c\psi\tau_{ij}\)，
\(\mathcal O=4c\int A^2\psi^2|\tau|^2\)，其增益严格为正。

程序给出 \(E_Q\) 的保守数值上界。推导没有采样空间极值：以式(5)的 \(B_3,B_4,B_5\) 控制 \(\tau\) 的0至2阶偏导；用
\[
|\Gamma|\le g_0=6r_0,\quad
|\partial\Gamma|\le g_1=6+12r_0^2
\]
控制协变导数。若其分量上界依次为 \(d_0,d_1,d_2\)，则
\[
\|\Delta_\gamma\tau\|_{F,\infty}
\le9[d_2+15g_0d_1+(6g_1+54g_0^2)d_0]=D_\tau .
\]
因此，记旧窗口的 \(L_j=\|\psi^{(j)}\|_1\)，有
\[
E_Q\le3\,{\rm Vol}(B_{1/8})\{
\|\tau\|_\infty[L_2+2\tan(1/4)L_1+2L_0]+D_\tau L_0\}.
\tag{9}
\]
实际程序给出 \(E_Q<8372.088\)。这个粗界反映高阶差分记录的误差放大；不能只展示小方差而隐去该增益。

## 4. 齐性调源在这个通道严格无效

固定背景上，场分解为
\[
\Phi_\lambda=\lambda^{-1}\varphi+d_\lambda Y f_\star(\eta).
\]
只需 \(f_\star\) 齐性；这里不把它误写为其它“解族导数”。最小标量应力满足
\[
\tau^{ij}T_{ij}[\Phi_\lambda]
=\tau^{ij}\partial_i\Phi_\lambda\partial_j\Phi_\lambda
=\lambda^{-2}\tau^{ij}\partial_i\varphi\partial_j\varphi.
\tag{10}
\]
迹项被 \(\tau\) 消去，齐性位移没有空间梯度。重整化的局部 c 数不影响中心化方差。

这个结论限定在本目录未扰动的齐性背景 \(g_0\) 上。另一条有限 lapse 路线沿空间非齐性的 \(g_\epsilon\) 传播后，\(f_\epsilon\) 一般会获得空间依赖；不能把这里的 \(\partial_i f_\star=0\) 移植到那条路径。

式(10)是场代数上的恒等式，强于一次 Wick 协方差计算：任意齐性相干位移及其任意经典混合，都在这个空间无迹应力子代数上给出同一状态。于是旧、新振幅分布的完整应力统计相同；经典振幅项 \(D_{\mathrm{amp},T}\) 与位移线性项 \(C_{1,T}\) 都严格为零。

参考态齐性、各向同性，所以本 TT 读出的均值为零；不能再以旧正密度均值 \(D\) 作“相对噪声”分母。旧局部密度通道中成功的振幅降噪不能外推成 tensor 降噪。本结果恰好给出这种外推的一个严格边界。

## 5. 完整参考态的全模式二次噪声

仍使用原静态过去准备的纯 quasifree 参考态，包括原正规零模；没有换成有限模 Gaussian 模型。参考场的 Gaussian 性只用于 Wick 公式，**二次应力本身未假定为 Gaussian 随机变量**。

实 S³ 球谐标签为 \(n=(k,j)\)，\(\omega_k=\sqrt{k^2-1}\)，简并度 \(k^2\)。定义
\[
N^\tau_{nm}=\int\tau^{ij}D_iY_nD_jY_m\,d\Omega.
\]
零模式的整行、整列严格为0，从不除以其频率。

### 无空间导数损失的行界

归一化梯度 Bessel 不等式给
\[
\sum_{m\ne0}\frac{|N^\tau_{nm}|^2}{\omega_m^2}
\le\|\tau\nabla Y_n\|_2^2\le\omega_k^2 .
\]
另一方面，\(D_i\tau^{ij}=0\) 使导数不落在 \(\tau\) 上。Parseval、Frobenius 收缩和单位 S³ 的 Bochner 恒等式给
\[
\sum_m|N^\tau_{nm}|^2
=\|\tau^{ij}D_iD_jY_n\|_2^2
\le\|\operatorname{Hess}Y_n\|_2^2
=\omega_k^4-2\omega_k^2\le\omega_k^4.
\]
Cauchy 因而给完整加权行界
\[
\boxed{\sum_{m\ne0}|N^\tau_{nm}|^2/\omega_m\le\omega_k^3.}
\tag{11}
\]
每条先对一个完整空间标签成立，再乘简并度求和，没有丢弃角模。

令
\[
A_\tau=\tfrac12\int A^2\psi\tau^{ij}
               \partial_i\varphi\partial_j\varphi,\qquad
B_{nm}=\int A^2\psi u_nu_mN^\tau_{nm}.
\]
原真空表示的成对产生归一给
\[
{\rm Var}(A_\tau)=\tfrac12\|B\|_{\rm HS}^2.
\]
式(7)与(10)是 \(\mathcal O_\lambda=8\lambda^{-2}A_\tau\) 的中心化版本，所以最终因子是 \(64/2=32\)，而非密度通道的 \(1/2\)。

### 低行、高频正频主项和实际准备余项

取 \(K=256\)，低块包含 \(k\le K\)。直接消费基线 [完整噪声回执](../../stress_kernel/noise/result.json) 中已经证明的 \(H,L_0,E_5,L_{\rm grad}\)。这些分别控制真实模式场列、原时间窗口、原 W2 准备余项及保留两种独立正频率的三次分部积分；不是把平均 RSET 尾当成噪声尾。

式(11)及 \(|Au_k|^2\le H/\omega_k\) 给
\[
N_L=HL_0\sqrt{S_4},\qquad S_4=\sum_{k=1}^K k^4,\qquad
\|B_{L,\mathrm{all}}\|_{\rm HS}\le N_L .
\]
完整低行已经同时包含低—低与低—高，故
\[
\|B_{LL}\|^2+2\|B_{LH}\|^2
=2\|B_{L,\mathrm{all}}\|^2-\|B_{LL}\|^2\le2N_L^2.
\tag{12}
\]
此处没有把低—高重数2漏掉。

对高—高正频主项，旧 \(L_{\rm grad}\) 与式(11)给
\[
N_{\rm main}=\frac{L_{\rm grad}}{2\sqrt K}.
\]
具体谱和是
\[
\sum_{n,m\in H}\frac{|N^\tau_{nm}|^2}{kl(k+l)^6}
\le\sum_{k>K}k^{-2}\le K^{-1}.
\]
这里 \(k,l\) 独立，振荡频率是其正频之和。

原真实准备与正频列的差由 \(\eta_k=E_5/k^5<1\) 控制。场乘积差至多
\(2(\eta_k+\eta_l)/\sqrt{kl}\)，所以
\[
N_{\rm err}\le4L_0E_5
 \sqrt{\sum_{k>K}k^{-6}}
\le\frac{4L_0E_5}{\sqrt{5K^5}}.
\]
这包括交叉频率和双负频率，不只是正频截断。

综上，
\[
\boxed{\begin{aligned}
{\rm Var}(\mathcal O_\lambda)&\le\lambda^{-4}C_T,\\
C_T&\le32\left[
2(HL_0)^2S_4+
\left(\frac{L_{\rm grad}}{2\sqrt K}
 +\frac{4L_0E_5}{\sqrt{5K^5}}\right)^2\right].
\end{aligned}}
\tag{13}
\]
本界对式(5)范数合同下的所有 TT 测试成立，所有模式及简并度都已覆盖。实际有向计算给出
\[
C_T<9.18804\times10^8,\qquad
{\rm Var}(\mathcal O_{32768})<7.96935\times10^{-10},\qquad
{\rm RMS}(\mathcal O_{32768})<2.82301\times10^{-5}.
\]
完整精确有理端点保存在回执。这里报告的是共同 \(\lambda=32768\) 的原始记录，不是未校准的相对应变精度；旧、新制备使用同一个 \(C_T\)。

## 6. 剩余边界与下一项真正需要的输入

完整量子度规反馈恢复后，应使用
\[
\mathcal D_T h-4\mathcal R_T^{\rm cov}[h]=4\xi^{\rm TT}_{\rm cov}.
\]
此时式(7)多出
\(4\int A^2\psi\tau:\mathcal R_T[h]\)。本轮没有证明这个项小，也没有把它删除后继续称完整 SCE。经典背景上量子均值残差虽有旧上界，仍不等于完整量子 on-shell 背景。

本结果关闭的是：**真实局部 tensor 算子、可合法测试的裸度规记录、规范/约束责任、任意齐次初值消去，以及该模型内完整参考态的诱导二次噪声。**尚需量子 retarded tensor response kernel 的可控算子界和相应 resolvent，才能把同一记录推进到完整反馈系统。一般度规读出、自由引力波初值、单位应变的实际灵敏度及硬件误差也不能从式(13)自动推出。

程序运行前后检查所有旧输入及自身文件的字节身份，绑定直接基线719babd3。新增模式 ODE 为0；Core 只读，GI 排除，无新增 Lean、硬件或全 SCE 求解声称。
