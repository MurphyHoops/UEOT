# 闭球面 FLRW 的完整 TT Weyl／Bach 局部反馈算子

[检查器](check.py) · [精确回执](result.json) · [显式局域块推迟逆](../resolvent/README.md) · [共同合同](../CONTRACT.md)

## 结论与约定

在任意光滑正尺度因子 \(a(\eta)\) 的正则区间上，固定
\[
g_\varepsilon=a^2\{-d\eta^2+[\gamma_{ij}+\varepsilon h_{ij}]dx^idx^j\},
\qquad D^ih_{ij}=0,\qquad\gamma^{ij}h_{ij}=0.
\]
\(\gamma\) 为单位三球度量，\(\Delta_\gamma=D^iD_i\) 是粗拉普拉斯，\(h\) 是无量纲共形度量扰动；其指标以 \(\gamma\) 升降。曲率约定使 \(\operatorname{Ric}_\gamma=2\gamma\)，四维号差为 \((-+++)\)。定义
\[
H^C_{ab}=4\nabla^c\nabla^d C_{acbd}+2R^{cd}C_{acbd}.
\]

本证书得到完整线性局部算子
\[
\boxed{\delta H^C_{ij}=-a^{-2}\mathcal W h_{ij}},\qquad
\boxed{\delta H^{C\,i}{}_j=-a^{-4}\mathcal W h^i{}_j},
\quad
\boxed{\mathcal W=(\partial_\eta^2-\Delta_\gamma+2)^2+4\partial_\eta^2}.
\]
其 \(00\)、\(0i\) 变分为零。若输入写成物理协变扰动 \(\delta g_{ij}\)，须先代入 \(h_{ij}=a^{-2}\delta g_{ij}\)，不能直接把同一个 \(\mathcal W\) 作用于 \(\delta g\)。

三球 TT 谱为
\[
-\Delta_\gamma Y^{(l)}_{ij}=[l(l+2)-2]Y^{(l)}_{ij},\quad l\ge2,
\]
故在全部允许模式及其简并度上
\[
\boxed{\mathcal W_l=(\partial_\eta^2+l^2)(\partial_\eta^2+(l+2)^2)}.
\]
最低 \(l=2\) 模式为 \(\partial_\eta^4+20\partial_\eta^2+64\)。

## 1. 在 Einstein cylinder 上直接计算

令 \(\bar g=-d\eta^2+\gamma\)。背景 Weyl 为零，
\(\bar R_{00}=0,\bar R_{ij}=2\gamma_{ij},\bar R=6\)。
因此线性化 \(H^C\) 时，所有 \(\delta\Gamma\)、升指标变分乘背景 \(C\) 的项都为零，留下背景协变导数作用于 \(\delta C\)，以及背景 Ricci 对 \(\delta C\) 的收缩。

TT 变分给出
\[
\delta R_{00}=\delta R_{0i}=\delta R=0,\quad
\delta R_{ij}=\tfrac12(h''_{ij}-\Delta_\gamma h_{ij}+6h_{ij}),
\quad\delta R_{0i0j}=-\tfrac12h''_{ij}.
\]
代入 Weyl 的 Ricci 分解，定义 \(E_{ij}=\delta C_{0i0j}\)，得到
\[
E=-\tfrac14(h''+\Delta_\gamma h-2h). \tag{1}
\]
其混合与空间分量是
\[
\delta C_{i0jl}=\tfrac12(D_jh'_{il}-D_lh'_{ij}),\quad
\delta C_{ikj0}=\tfrac12(D_ih'_{jk}-D_kh'_{ij}), \tag{2}
\]
\[
\delta C_{ikjl}=\gamma_{ij}E_{kl}+\gamma_{kl}E_{ij}
-\gamma_{il}E_{kj}-\gamma_{kj}E_{il}. \tag{3}
\]
\(E\) 仍为 TT；时间导数和常曲率背景上的粗拉普拉斯保持这一子空间。

对任意对称二张量 \(X\)，球曲率给出
\[
[D^k,D_i]X_{kj}=3X_{ij}-\gamma_{ij}\operatorname{tr}X.
\]
对 TT 张量于是有
\[
D^kD_iX_{kj}=3X_{ij}. \tag{4}
\]
检查器从
\(R^e{}_{acd}=\delta^e_c\gamma_{ad}-\delta^e_d\gamma_{ac}\)
逐指标收缩，在完整对称矩阵基上验证该式。曲率项 3 不能按平直偏导数交换删除。

记 \(X_{ij}=\bar\nabla^c\bar\nabla^d\delta C_{icjd}\)。双时间项为 \(E''\)；两个混合项因升时间指标各带负号，由 (2)、(4) 合成 \((\Delta_\gamma-3)h''\)；纯空间项由 (3)、(4) 为 \((\Delta_\gamma-3)E\)。因此
\[
X=E''+(\Delta_\gamma-3)h''+(\Delta_\gamma-3)E.
\]
另一方面
\[
2\bar R^{cd}\delta C_{icjd}=4\gamma^{kl}\delta C_{ikjl}=4E_{ij}.
\]
代入 (1)，直接得到
\[
4X+4E
=-\{\partial_\eta^4+(8-2\Delta_\gamma)\partial_\eta^2
+(\Delta_\gamma-2)^2\}h=-\mathcal W h. \tag{5}
\]
这包含二阶和零阶球曲率项，已经超出只认证主符号的前驱结论。

## 2. 独立的 Weyl 电磁分解与作用量校验

对 TT 张量定义
\((\operatorname{curl}X)_{ij}=\epsilon_i{}^{kl}D_kX_{lj}\)。
在 TT 子空间该表达式已对称并保持 TT。由 epsilon 收缩与 (4)，
\[
\operatorname{curl}^2X=(-\Delta_\gamma+3)X.
\]
令 \(B_{ij}=\tfrac12\epsilon_i{}^{kl}\delta C_{klj0}\)，则
\(B=\tfrac12\operatorname{curl}h'\)。Lorentzian 代数恒等式是
\[
\delta C_{abcd}\delta C^{abcd}=8(E_{ij}E^{ij}-B_{ij}B^{ij}). \tag{6}
\]
检查器在电、磁对称无迹基及两两和上构造四维 Weyl，检查张量对称性、Bianchi 恒等式、无迹性及 (6)。两两和确保二次型交叉项也由极化覆盖。

设 \(A=-\Delta_\gamma+2\)，
\(I_C[g]=\int\sqrt{-g}\,C_{abcd}C^{abcd}\)。背景 \(C=0\)，所以展开的 \(\varepsilon^2\) 项为
\[
I_C^{[2]}[h]=\int d\eta\left\{
\tfrac12\|h''-Ah\|^2-2\langle h',(A+1)h'\rangle\right\}. \tag{7}
\]
内积是三球张量 \(L^2\) 内积。在时间紧支撑扰动上，
\[
I_C^{[2]}[h]=\tfrac12\int d\eta\{
\|h''\|^2-2\langle h',(A+2)h'\rangle+\langle h,A^2h\rangle\}
=\tfrac12\int\langle h,\mathcal W h\rangle\,d\eta. \tag{8}
\]
这里 \(I_C[g_\varepsilon]=\varepsilon^2 I_C^{[2]}+O(\varepsilon^3)\)；
严格二次方向导数是 \(\int\langle h,\mathcal W h\rangle\)，不是其一半。

固定归一
\[
\delta I_C=\int\sqrt{-g}\,H^C_{ab}\,\delta g^{ab}
\]
并用 \(\delta g^{ij}=-h^{ij}\)，即得到 (5) 的负号。
平直 TT 波 \(h_{11}=f(t,z),h_{22}=-f(t,z)\) 因而满足
\(\delta H^C_{11}=-(\partial_t^2-\partial_z^2)^2f\)，与冻结前驱约定一致。

## 3. 共形权重、全谱和错误算子负控

四维 \(I_C\) 的共形不变性及变分归一给出
\[
H^C_{ab}[a^2\bar g]=a^{-2}H^C_{ab}[\bar g].
\]
固定 \(a\) 只变 \(h\)，即把 (5) 转成首页公式。背景 \(H^C=0\)，升一空间指标只再带来 \(a^{-2}\)，不产生背景压力接触项。这也是无量纲 \(h\) 的 \(\mathcal W\) 中没有 Hubble 导数的原因。

令 \(L=l(l+2)\)，
\[
\mathcal W_l=\partial_\eta^4+(2L+4)\partial_\eta^2+L^2
=(\partial_\eta^2+l^2)(\partial_\eta^2+(l+2)^2).
\]
检查器保留任意符号 \(l\)，没有截断谱；也保留一般曲率 \(K\)，检查
\(\mathcal W_K=(\partial_\eta^2-\Delta+2K)^2+4K\partial_\eta^2\)，
\(K=0\) 时恢复平直符号。

负控取 \(l=2,h=\cos2\eta\)：完整 \(\mathcal W h=0\)，错误的平方项
\((\partial_\eta^2-\Delta+2)^2h=16h\)。删除最后的曲率项会被精确检出。
主审还从四维度规、Christoffel、Riemann、Weyl 与双散度独立重算全局光滑 Hopf \(l=2\) 张量，验证同一个 \(1,20,64\) 算子；见[独立主审](../review.py)。

## 4. 继承处方、R² 与显式参数族

项目取 \(4\pi G=1\)，故 \(8\pi G=2\)。继承的原方程是 \(G=2T\)，物理 \(\mu=1\)、源侧有限系数 \(\alpha=0\)，没有额外有限曲率项；见冻结的[兼容合同](../../compatibility/CONTRACT.md)、[动态应力处方](../../evolution/stress/README.md)与[参考态定义](../../continuation/quantum/README.md)。AE 的 \((+---)\) 及相反 Riemann 号满足
\[
g_{\rm AE}=-g,\quad R^{\rm AE}_{ab}=-R_{ab},\quad
R_{\rm AE}=R,\quad\Box_{\rm AE}=-\Box,\quad
\boxed{H^{(1)}_{\rm AE}=-H_R}.
\]
检查器对任意 \(a(\eta)\) 独立核对密度的逐项负号。因此额外有限系数
\[
\boxed{z=1,\qquad b_{\rm extra}=-\alpha=0,\qquad c_{\rm extra}=0}.
\]
最后一个零表示相对于冻结参考处方，本轮不新增独立 \(H_C\) 反项；它不表示参考处方中的四阶局部接触响应为零。

下面 \(b,c,z\) 是 Einstein 块加入显式常系数 \(R^2/C^2\) 变形后的结构参数，供精确条件定理使用，不重新开放原有物理输入。扣除各向同性背景压力后的 mixed TT 方程为
\[
D_T h=4a^2\delta T^i{}_j,\qquad
D_T=\partial_\eta^2+2(a'/a)\partial_\eta-\Delta_\gamma+2.
\]
因此 RSET 的 \(+cH^C\) 在右侧给 \(-4ca^{-2}\mathcal W h\)，移左后为
\(D_T+(4c/a^2)\mathcal W\)。

对
\[
H^R_{ab}=2RR_{ab}-\tfrac12g_{ab}R^2
+2(g_{ab}\Box-\nabla_a\nabla_b)R
\]
有
\[
\delta(H_R)^i{}_j=a^{-2}[R D_T+R'\partial_\eta]h.
\]
其一般 FLRW 分量由主审从四维几何独立重算。
于是显式 \(bH^R+cH^C\) 变形与 Einstein 块组成的完整算子是
\[
\boxed{\mathcal L_{b,c}=(1-4bR)D_T-4bR'\partial_\eta+
\frac{4c}{a^2}\mathcal W}. \tag{9}
\]
令 \(q=1-4bR\)，加权形式是
\[
a^2\mathcal L_{b,c}h=\partial_\eta(a^2q h')
+a^2q(-\Delta_\gamma+2)h+4c\mathcal W h. \tag{10}
\]
它独立检查 \(R'\) 项符号。\(4c/a^2\) 是 \(\mathcal W\) 外的乘法系数，不应凭空再加其导数乘 \(h'''\)。
[推迟逆证书](../resolvent/README.md)另保留一般常数 Einstein 系数 \(z\) 作为代数参数；本项目原 Newton 归一对应 \(z=1\)。

实际工作点 \((z,b_{\rm extra},c_{\rm extra})=(1,0,0)\) 的待解方程仍是
\[
D_T h-4a^2\Pi_{\rm ref}^{TT}[h]=4a^2F.
\]
这里 \(\Pi_{\rm ref}^{TT}\) 包含同一固定参考处方的显式 metric 变分、固定接触项及非局域量子响应。本节没有把这些接触项全部归结为 (9)。FLRW 均值上 \(H_C=0\) 只说明 RW 均值不能辨识 Weyl 方向，不能据此重开有限耦合；若此前只实现了 RW 公式，尚需构造/核对与冻结处方一致的非齐性实现。

下面补偿公式只说明一般记账恒等式，并非授权为原项目增加引力耦合。

若方程为
\[
G_{ab}+\gamma_C H^C_{ab}
=\kappa(T^{\rm rest}_{ab}+c_{\rm mat}H^C_{ab}),
\]
则 \(c=c_{\rm mat}-\gamma_C/\kappa\)。
处方补偿 \(c_{\rm mat}\mapsto c_{\rm mat}+s\),
\(\gamma_C\mapsto\gamma_C+\kappa s\) 保持净 \(c\)。
若作用量约定是
\(S_{\rm grav}=(2\kappa)^{-1}\int\sqrt{-g}R+\alpha_C I_C\)，
则 \(\gamma_C=2\kappa\alpha_C\)，净 \(c=c_{\rm mat}-2\alpha_C\)；
对应补偿为 \(\alpha_C\mapsto\alpha_C+s/2\)。
只改变 RSET 侧、保持引力侧固定，会改变物理净耦合。

## 5. 显式四阶参数族的数据和边界合同

在上述显式参数族中，\(c\ne0\) 且 \(a>0\) 时，每个模式的局部方程是四阶，需要四个 Cauchy 数据或明确等价的分支处方。两个纯 Bach 负控是
\[
v_0=\cos2\eta-\cos4\eta,\qquad
v_1=\tfrac12\sin2\eta-\tfrac14\sin4\eta.
\]
它们满足 \(\mathcal W_2v=0\)，初始 jets 分别为
\[
(v_0,v'_0,v''_0,v'''_0)|_0=(0,0,12,0),\quad
(v_1,v'_1,v''_1,v'''_1)|_0=(0,0,0,12).
\]
所以只给 \(h,h'\) 不足以选定四阶响应。零过去推迟合同指定驱动前 \(h=h'=h''=h'''=0\)；这是该四阶参数族的明确数据条件，不在固定的 \(c_{\rm extra}=0\) 物理工作点擅自增加两项初始数据。

令 \(S=A+2\)，Green 流为
\[
\mathfrak b_{\mathcal W}(u,v)=
\langle u,v'''\rangle-\langle u',v''\rangle+
\langle u'',v'\rangle-\langle u''',v\rangle+
2\langle u,Sv'\rangle-2\langle u',Sv\rangle,
\]
\[
\langle u,\mathcal Wv\rangle-\langle\mathcal Wu,v\rangle
=\partial_\eta\mathfrak b_{\mathcal W}(u,v).
\]
(8) 的变分边界项为
\[
[\langle\delta h',h''\rangle-
\langle\delta h,h'''+2Sh'\rangle]_{\eta_-}^{\eta_+}.
\]
(7) 与 canonical 作用量还差总导数
\(-\partial_\eta\langle h',Ah\rangle\)；有限区间上不能省去而不说明边界合同。
由 (10)，全局部加权 Green 流为
\(a^2q(\langle u,v'\rangle-\langle u',v\rangle)+4c\mathfrak b_{\mathcal W}\)。
纯处方补偿还必须保持初始／边界合同；order reduction 是需要误差与频带控制的另一个近似，不能视为精确四阶方程的恒等变换。

## 6. 验证和边界

本目录验证完整局部 Weyl／Bach 算子、所有 \(l\) 的恒等式、作用量归一、继承处方的符号转换，以及显式四阶参数族的耦合与边界合同。它不单独给出完整重叠 RSET 核或量子反馈逆。

基线为 c57e2f411e58dc1dae60de8f3c97fbd680e46d8b。检查器按 git show 逐字节冻结前驱 operational_response 的合同与主审文件，以及明确固定 μ、α 的三个原处方文件，记录其与本目录源文件的 SHA256。只做精确代数，不执行前驱检查器，不新增模式或几何 ODE，Core 只读，GI 排除。

从仓库根运行：

    /Users/murphyhoops/Documents/ueot-physics-closure-20261111/.physics-venv/bin/python -B physics/qm/null_source/timelike/overlap_response/local/check.py --write --check

## 原始文献

- Beccaria、Bekaert、Tseytlin，[Partition function of free conformal higher spin theory](https://arxiv.org/pdf/1406.3542)，§3.1 式 (3.14)、§3.2 式 (3.17)–(3.18)。Euclidean 算子以 \(\partial_\tau^2\mapsto-\partial_\eta^2\) 延拓后与本独立推导一致，文献的 \(n\) 对应本稿 \(l=n+2\)。
- Anderson、Molina-París、Mottola，[Linear Response, Validity of Semi-Classical Gravity, and the Stability of Flat Space](https://arxiv.org/pdf/gr-qc/0209075)，式 (2.8a,b)、(2.9) 给局部曲率张量与有限耦合的背景；本文未将其平直稳定性结论移到本 FLRW 模型。

- Anderson、Eaker，[Adiabatic regularization in homogeneous and isotropic universes](https://arxiv.org/pdf/gr-qc/9906055)，式 (10a,b) 给出其约定下的 H1 及 FLRW 密度；本节按两项约定变换核对符号，没有改变既定 μ=1、α=0。
