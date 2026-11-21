# 重叠 TT 响应：完整局部几何、因果对数主部与齐性调源盲性

[共同合同](CONTRACT.md) · [四项复核](run_verification.py) · [执行回执](verification.json) · [独立主审](review.py) · [前驱](../operational_response/README.md)

本轮接续 c57e2f411e58dc1dae60de8f3c97fbd680e46d8b，把严格分离窗口后的三个关键责任推进为可复核结果：闭 FLRW 的完整 TT 曲率算子、对数主部的合法因果定义与精确标量逆、重叠窗中的同背景态差响应。完整固定参考量子反馈仍未关闭。

## 1. 先纠正一项继承判断

原项目已经固定物理 μ=1、源侧 α=0、无额外有限曲率项和 G=2T。上一轮的“齐性均值/分离窗不能单独识别 Weyl 系数”是一条数据不可辨识结论，不能将已固定的物理处方重新开放为任意参数选择。

本轮从原始合同和 AE 约定重新核对：
\[
H^{(1)}_{\rm AE}=-H_R,\qquad
\boxed{(z,b_{\rm extra},c_{\rm extra})=(1,0,0)}.
\]
零额外项不表示固定参考 RSET 的局部接触项为零。真正尚待计算的是同一参考处方的非齐性线性化；不是重新选择 α、μ 或一个新引力耦合。

实际反馈方程保持
\[
\boxed{D_T h-4a_\lambda^2\Pi_{\rm ref}^{TT}[h]=4a_\lambda^2F}.
\]
本轮的辅助四阶参数族与标量 log normal form 均明确独立于这项尚未完成的物理反演。

## 2. 已完成的数学结果

| 工作包 | 本轮推进 | 明确边界 |
|---|---|---|
| [局部几何](local/README.md) | 完整 Weyl/Bach TT 算子、全部谱的精确因子分解、作用量和边界合同、R² mixed 变分 | 不是只看最高阶符号；也不是固定参考 RSET 的全部接触项 |
| [量子重叠响应](quantum/README.md) | 定义含局域有限部分的因果 log 分布，证明时间 Sobolev 映射；精确标量逆、正极点与严格质量界；同背景态差完整响应 | normal form 不是完整 prepared FLRW 核；实际 M8 仍待数值认证 |
| [局部因果逆](resolvent/README.md) | 显式 Einstein+R²+C² 参数族在真实时间依赖背景上的全模式唯一因果解及尾界；非零 C² 块的同空间反例 | 非零 c 条件定理不用于 c_extra=0 物理工作点；不证明实际参考态稳定或失稳 |
| [独立主审](review.py) | 从四维坐标几何重算 Hopf TT 的 Bach 和一般 a 的 R² 变分，核对冻结参数、Green 初值和量子常数 | 不导入子检查器，不执行旧模式积分，不把条件证明升级成完整反馈 |

### 2.1 完整闭球面 Weyl/Bach 算子

对 g=a²(−dη²+γ+h)，gamma 为单位三球、h 空间 TT，
\[
\delta H^C_{ij}=-a^{-2}Wh_{ij},\qquad
\delta H^{C\,i}{}_j=-a^{-4}Wh^i{}_j,
\]
\[
\boxed{W=(\partial_\eta^2-\Delta_\gamma+2)^2+4\partial_\eta^2},
\quad
\boxed{W_l=(\partial_\eta^2+l^2)(\partial_\eta^2+(l+2)^2)}.
\]
曲率项 4∂η² 不能省去。最低 l=2 的完整系数是 1、20、64；在频率2时正确多项式为0，错误平方项给16，检查器明确检出这个负控。

推导由 cylinder 双散度和电磁 Weyl 作用量两条路线完成。主审再用全局光滑 Hopf 张量 tau=K⊗K−gamma/3、K 为单位 Hopf Killing 场，直接计算四维联络、曲率及双散度；另验证 tau 无迹、无散、−Δtau=6tau。任意尺度因子 a 的 mixed R² 响应为
\[
\delta(H_R)^i{}_j=a^{-2}(R D_T+R'\partial_\eta)h^i{}_j.
\]

### 2.2 对数奇性已被定义，标量主部有真正的因果逆

自由实标量的 spin-2 UV 系数 beta_T=1/(1920π²)>0。先定义可积原函数
\[
q_{k,\mu}(t)=-2[\gamma_E+\log\mu t+
\int_0^t(\cos kr-1)dr/r],\quad K=D_t(\theta q),
\]
则 Laplace K=log[(p²+k²)/μ²]。有限部分的局域补项、尺度变化和截止误差都被保留，未用未定义的 theta×奇异分布。

令 L_mu 的符号为 log(p/μ)。对 c实、κ>0，
\[
\boxed{(c\delta+\kappa L_\mu)_{\rm ret}^{-1}(t)
=\frac1\kappa\int_0^\infty
\frac{p_*^u t^{u-1}}{\Gamma(u)}du},\qquad p_*=\mu e^{-c/\kappa}.
\]
该核正且局部可积，有限时间质量是 ν(p*T)/κ，有解析上下界和尾界。近零为 1/[κt log²(p*t)]，可纳入主要反演对象。

其谱表示包含正实增长极点 p*e^(p*t)/κ。这里没有删除极点，也没有把“存在因果逆”改称“稳定逆”。仅反演局部四阶块后仍剩 log 高频增长，不能直接假设其为普通 L1 Volterra 小修正。实际非平稳曲背景还须给正确主部和受控余项。

### 2.3 原齐性调源对重叠有效 TT 响应仍严格不可见

对同背景 Hadamard 态差 S=W1−W0、V_h=δP=+div(h grad)、B_h=−V_h，
\[
\delta S=E_RB_hS+\mathrm{transpose},
\]
\[
\Delta\mathcal R_{\rm eff,cov}[h]
=[D_iD_{j'}\delta S]_{\rm diag}^{TT}-\sigma_Sh.
\]
局域态项 −sigma_Sh 来自显式指标变分，不能省掉。若 S 是齐性相干位移或其混合引起的对 x、y 分别空间常数的纯零模核，V_hS=0、sigma_S=0，故
\[
\boxed{\Delta\mathcal R_{\rm eff,cov}[h]=0}
\]
对任意平滑 TT 输入成立，包括时间窗重叠。混合不需 Gaussian。

这一结论扩大了已知盲性范围，也把后续 TT 反馈责任集中到两候选共有的参考态。它不表示共有响应本身为零，更不把原密度噪声优势移植到 TT 通道。raw covariant δTij 可以有 a²Δp hij，升指标后才抵消。

更一般的 SO(4) 不变（齐性各向同性）态差令 J=1−Δ、MS=sup||JSJ||trace、M8=sup||J²SJ²||HS；在 [1/16,3/16]、输入此前为零时，
\[
M_S\le(\pi^2/6)M_8,\qquad
\boxed{\|\Delta\mathcal R_{\rm eff,cov}\|_{L^\infty X\to L^\infty X^*}
\le(\pi^2/6)(C_ET^2+1/3)M_8}.
\]
T=1/8，CE=exp[(1/2+2tan(3/8))/8]。这是带明确数据责任的真 Volterra 界；实际 M8 并未从旧噪声回执凭空补入。

### 2.4 显式局部四阶参数族的全模式反演

对辅助 L_z,b,c h=f、c≠0，真实背景系数
m=(a²/4c)·(z−4bR) 给 W_lh+(mh')'+kappa_l mh=gamma_c f。
四项零过去数据下，准确 Volterra 核是
\[
K_l(t,s)=\frac{\sin((l+1)(t-s))}{l+1}
[-m(s)\cos(t-s)+\tfrac12m'(s)\sin(t-s)].
\]
全模式 |K|≤A(t−s)，迭代范数≤A^nT^(2n)/(2n)!，因此因果解唯一且级数绝对收敛，无需 ||V||<1；给出全部截断余项。

固定 l=2、紧支撑高时间频率 h_n 的精确负控还给
\[
\|D_{T,\rm ret}^{-1}(a^{-2}Wh_n)\|_{CH^s}
\ge(n^2/3-32)/\lambda^2.
\]
它排除非零额外 C² 块经过旧二阶逆后的同空间全频小增益。原物理 c_extra=0 时该额外块为零，不能据此宣布实际参考响应无界或失稳。

## 3. 主审与复现身份

三个原生协作席分别推导局部几何、量子重叠响应和局部因果逆；主审负责交叉核验、唯一落盘与执行。证明文档保留完整分析论证，程序独立核对所述符号、负控、区间和文件身份，并非 Lean 形式化证明。

从仓库根执行：

    python -B physics/qm/null_source/timelike/overlap_response/run_verification.py

环境沿用 Python3.14、numpy2.5.4、scipy1.18.1、sympy1.14.0、mpmath1.3.0。总入口复用34项旧结果、冻结140个旧科学文件，只运行本轮4项。旧证据来自真实执行收据和 c57 准确 head 的 CI，而不是再次执行旧模式积分。

本地预提交 receipt 保留真实旧 HEAD 和工作区状态；新提交的可信身份由远端准确 head CI 绑定。新增模式/几何 ODE0、旧科学入口重跑0；Core只读、GI排除、书稿/Lean/经验状态不升级。

## 4. 下一项具体科学验收

下一步应在原 μ=1、α=0、无额外有限项和原 prepared 态下，构造非齐性 TT 的 Pi_ref 本身，并逐项接入本轮接口：

1. 从同一协变减除定义求显式 metric 变分和固定 contacts，核对 Ward/守恒及指标约定；若只有 RW 实现，补其一致的非齐性实现。
2. 构造 actual closed-FLRW 因果 kernel 的局部 UV 主部与非平稳余项；证明剩余算子所在空间和实际常数。纯时间 normal form 只提供入口，不替代时空核。
3. 将完整主部逆、真实余项、初值和合法噪声测试放入同一空间，再给反馈逆、稳定性及量子噪声传播的可验收界。

这三项是同一剩余责任的顺序接口。非线性 SCE、精确解距离、外区态与匹配、完整装置应力、真实硬件和经验检验仍保留原开放身份；现有有限概率和校准结果继续按前驱各自的明确合同使用。
