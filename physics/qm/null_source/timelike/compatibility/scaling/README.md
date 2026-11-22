# 同形缩放、绝对应力与全时段缺陷

## 本轮实际出口

对原最小耦合无质量场的**整个参考制备背景**作 \(g_\lambda=\lambda^2g\)，并把同一个中心 Hadamard 核作相应运输，可以精确计算完整重整化应力的缩放。固定物理减除尺度 \(\mu\) 时，

\[
 \boxed{\mathcal T_{\mu,\lambda}
 =\lambda^{-4}\left[
 \mathcal T_\mu+\frac{\log\lambda}{576\pi^2}\mathcal H^{(1)}
 \right]},\qquad
 \mathcal T=(\rho,p),\quad
 \mathcal H^{(1)}=(H_\rho^{(1)},H_p^{(1)}).
\]

这里的 \(\lambda^{-4}\) 缩放明确指**对应共动正交标架中的 \(\rho,p\) 分量**；右侧曲率分量在基准背景上计算。固定同一坐标系时，协变张量的两个下标分量满足另一权重：

\[
 \langle T_{ab}\rangle_{\mu,g_\lambda}
 =\lambda^{-2}\left[
 \langle T_{ab}\rangle_{\mu,g}
 +\frac{\log\lambda}{576\pi^2}H^{(1)}_{ab}[g]
 \right].
\]

原因是共动正交标架向量本身按 \(e_{\hat a,\lambda}=\lambda^{-1}e_{\hat a}\) 缩放，两次投影再贡献 \(\lambda^{-2}\)。下文有限系数记账中的 \(T,H^{(1)}\) 若未写坐标下标，均沿用上述共动正交分量约定。这不是单纯的幂次缩放，也没有把改变 \(\mu\) 当作物理修复。

在原冻结齐性因果内核、共同 \(\eta\in[0,3/16]\) 内，不重新积分任何模式，我们用上一轮验证结果得到

\[
 |\rho_{\rm ref}(\eta)|<9507.62151,\qquad
 |p_{\rm ref}(\eta)|<270564.125.
\]

用同一精确初片能量 \(Q=\rho_{\rm ref}(0)\) 调整经典源强、令初片 Hamiltonian 密度约束精确成立后，对所有 \(\lambda\ge8192\)：

\[
 \frac{|\Delta\rho|}{\rho_{\rm bg}}<0.000286660,\qquad
 \frac{|\Delta p|}{\rho_{\rm bg}}<0.008066751,
 \quad
 \rho_{\rm bg}=p_{\rm bg}=\frac1{2\lambda^2\cos^3(2\eta)}.
\]

这是整个共同时间区间上的**平均场方程的应力缺陷**包围，两分量均小于背景对应分量的 \(1\%\)。它没有给出度规误差、稳定性定理或精确半经典演化解。尺度 8192 是当前保守证书给出的充分选择，不是必要尺度或从理论唯一推出的物理常数。

正式程序为 check.py，精确有理端点回执为 result.json。本目录只读取 [上一轮绝对应力证书](../../evolution/stress/README.md)，不修改或重跑旧模式传播。初值和制备仍绑定 [有限源合同](../../../FINITE_WINDOW.md) 与 [共同参考态](../../continuation/SOURCE.md)。

## 1. 什么被同形运输

令 \(a_\lambda(\eta)=\lambda a(\eta)\)，包括 \(\eta<-1/16\) 的完整实际制备插值，而不只是物理段。固定同一无量纲空间坐标和共形时间。于是

\[
 h_\lambda=a_\lambda'/a_\lambda=h,\qquad
 q_\lambda=-1-a_\lambda''/a_\lambda=q.
\]

对最小无质量算子 \(P_g\)，有 \(P_{g_\lambda}=\lambda^{-2}P_g\)。若基准两点核为 \(W\)，则

\[
 W_\lambda(x,x')=\lambda^{-2}W(x,x')
\]

保留正性；对应传播核的缩放保证 CCR；常数正缩放不改变波前集，而同形背景的零锥、时间方向和联络保持对应，因此 Hadamard 条件也保留。

对模式的规范变量，

\[
 u_\lambda=u/\lambda,\qquad p_\lambda=\lambda p,\qquad
 v_\lambda=a_\lambda u_\lambda=v,\qquad
 b_\lambda=p_\lambda/a_\lambda=b.
\]

这保持辛结构，且原模式方程严格对应。因此每个模式的原始二次型 \(e_k,s_k\) 和 AE 的无量纲模式减项不变。共同前因子 \(1/(4\pi^2a^4)\) 提供完整模式差和的 \(\lambda^{-4}\) 因子。

### 正规零模必须一起运输

原最小场 \(k=1\) 模没有普通静态振子真空。使用的正规高斯制备种子是

\[
 \operatorname{Var}q_0=\frac16,\qquad
 \operatorname{Var}p_0=\frac32.
\]

同一核的运输要求

\[
 q_{0,\lambda}=q_0/\lambda,\quad p_{0,\lambda}=\lambda p_0,
\qquad
 \operatorname{Var}q_{0,\lambda}=\frac1{6\lambda^2},\quad
 \operatorname{Var}p_{0,\lambda}=\frac{3\lambda^2}{2}.
\]

以上对角方差描述的是制备种子。传播到物理初片 \(\Sigma_0\) 后，一般已经存在 \(q\)–\(p\) 相关，不能重置为对角高斯。任意切片的完整运输规则是

\[
 V_\lambda=S_\lambda V S_\lambda^{\mathsf T},\qquad
 S_\lambda=\operatorname{diag}(\lambda^{-1},\lambda),\qquad
 V_\lambda=
 \begin{pmatrix}
 V_{qq}/\lambda^2&V_{qp}\\
 V_{qp}&\lambda^2V_{pp}
 \end{pmatrix}.
\]

交叉协方差保持，\(\det V_\lambda=\det V=1/4\)。程序的应力计算只需要守恒的 \(V_{pp}=3/2\)，并没有假设物理初片的交叉项为零。零模能量

\[
 \rho_{0,\lambda}=p_{0,\lambda}^{\rm(stress)}
 =\frac{\operatorname{Var}p_{0,\lambda}}
       {4\pi^2a_\lambda^6}
 =\lambda^{-4}\frac3{8\pi^2a^6}
\]

也正确缩放。

若把两个零模方差都保留为原数值，会得到另一个合法零模态，其动能按 \(\lambda^{-6}\) 缩放，但不是同一核的运输。在原对角制备种子上，若只把位置方差缩小、却不放大动量方差，在 \(\lambda>1\) 时行列式变成 \(1/(4\lambda^2)<1/4\)，连正规量子态的不确定性条件也不满足。

这里运输了整个已知参考几何及其所有导数。这不能推广为“保持同一个初片内禀度规与外曲率，就可把核移到任意更高阶几何 jets 上”。后者需要单独的态兼容审查。

## 2. 固定物理 \(\mu\) 的 log 项

采用 [Anderson–Eaker 的式 (9)–(14)](https://arxiv.org/pdf/gr-qc/9906055)，上一轮已经得到本最小场的完整局部补项。令 \(c=\cos2\eta\)，\(L_\mu=\log(3c\mu^2/4)+2\gamma_E\)：

\[
 \rho_{\rm an}
 =\frac{(168+180L_\mu)c^2-110-135L_\mu}{8640\pi^2c^6},
\]
\[
 p_{\rm an}
 =\frac{(160+300L_\mu)c^2-240-405L_\mu}{8640\pi^2c^6}.
\]

本背景的曲率应力分量为

\[
 H_\rho^{(1)}=\frac{6(4c^2-3)}{c^6},\qquad
 H_p^{(1)}=\frac{40c^2-54}{c^6}.
\]

整体同形缩放使全部局部曲率应力乘 \(\lambda^{-4}\)，同时

\[
 L_\mu\longmapsto L_\mu+2\log\lambda.
\]

逐项代入即得开头的完整缩放式。无限模式差和已在第 1 节严格缩放，不存在未计算的附加态项。特别地，

\[
 Q_\lambda=\lambda^{-4}
 \left[Q+\frac{\log\lambda}{96\pi^2}\right],
\]
\[
 P_\lambda=\lambda^{-4}
 \left[P-\frac{7\log\lambda}{288\pi^2}\right].
\]

初片 \(H_\rho^{(1)}=6,\ H_p^{(1)}=-14\)，所以压力 log 项的符号与能量相反。程序对两个系数分别作符号恒等式核验。

## 3. 物理有限曲率系数的记账

为避免引力侧符号约定的歧义，本目录把有限项定义在源侧：

\[
 T_{\rm physical}=T_\mu+\alpha_\mu H^{(1)}.
\]

平直真空能和 Newton 常数仍沿用原合同；这里的 \(\alpha\) 是剩余有限曲率系数。若把同一项放到场方程左侧，系数符号应相应改变。

固定物理 \(\mu,\alpha_\mu\) 比较两种物理尺寸时，

\[
 T_{{\rm physical},\lambda}
 =\lambda^{-4}\left[
 T_\mu+\left(\alpha_\mu+
       \frac{\log\lambda}{576\pi^2}\right)H^{(1)}
 \right].
\]

括号内的组合是把缩放张量写回基准几何后的记账，不表示物理耦合自行改变。

若仅改变重整化表示 \(\mu\to\mu e^s\)，要描述同一物理总张量，必须同步取

\[
 \alpha_{\mu e^s}
 =\alpha_\mu-\frac{s}{576\pi^2}.
\]

例如取 \(\mu_\lambda=\mu/\lambda\) 会使量子部分的显式 log 项消失，但相应

\[
 \alpha_{\mu/\lambda}
 =\alpha_\mu+\frac{\log\lambda}{576\pi^2}
\]

会把它完整恢复。把 \(\mu\) 换掉而仍令 \(\alpha=0\)，不是同一物理问题的修复。

本次数值证书固定 \(\mu=1,\alpha=0\)。若另有已知界 \(|\alpha|\le A\)，统一能量/压力上界只需分别增加 \(6A\) 与 \(29.83495A\) 后再缩放；若 \(\alpha\) 无界，本证书不能给出对所有物理耦合统一有效的数值尺度。

## 4. 三种不同的经典源合同

设经典齐性源的守恒动量为 \(P_{\rm cl}\)，\(M_2=\mathbb E[P_{\rm cl}^2]\)。在缩放背景上，

\[
 \rho_{\rm cl}=p_{\rm cl}
 =\frac{M_2}{54\lambda^6c^3},\qquad
 \rho_{\rm bg}=p_{\rm bg}=\frac1{2\lambda^2c^3}.
\]

原 \(M_2=27\)。三种制备选择必须区分：

| 合同 | \(M_2(\lambda)\) | 经典密度与背景所需密度之比 |
|---|---:|---:|
| 保持原经典守恒动量二阶矩 | \(27\) | \(\lambda^{-4}\) |
| 连同相干位移一起运输整个量子态 | \(27\lambda^2\) | \(\lambda^{-2}\) |
| 保持原经典同形 Einstein 几何 | \(27\lambda^4\) | \(1\) |

第二行来自相干解 \(f_\lambda=f/\lambda\)，其守恒动量为 \(P_{{\rm cl},\lambda}=\lambda P_{\rm cl}\)。第三行需要 \(P_{{\rm cl},\lambda}=\lambda^2P_{\rm cl}\)，是另行调整了相干制备强度。仅运输中心参考核，并不会强迫采用哪一种经典源强。

第三行已用经典源填满约束；对每个有限 \(\lambda\ge1\)，当前 \(\alpha=0\) 的量子初片能量仍严格为正，所以单纯放大尺度只能使相对失配变小，不能让该未调源的模型精确满足总约束。另两种合同的初片约束根由相邻约束分析独立认证；其存在不自动意味着量子效应是微扰。

## 5. 不重新传播模式的统一动态上界

### 5.1 瞬时 Hamilton 基的准确增长式

对每个 \(k\ge2\)，\(\omega_k=\sqrt{k^2-1}\)。定义

\[
 A_k=\frac{\sqrt{\omega_k}au_k
                +ip_k/(\sqrt{\omega_k}a)}{\sqrt2},
\quad
 B_k=\frac{\sqrt{\omega_k}au_k
                -ip_k/(\sqrt{\omega_k}a)}{\sqrt2}.
\]

由原 canonical 模式方程直接得到

\[
 A_k'=-i\omega_k A_k+hB_k,\qquad
 B_k'=hA_k+i\omega_k B_k,
\quad |A_k|^2-|B_k|^2=1.
\]

这里的 \(B_k\) 是瞬时 Hamilton 基中的系数，与上一轮 UV 证明的 \(W_2\) 基系数不同。

它满足

\[
 \operatorname{arsinh}|B_k(\eta)|
 \le \operatorname{arsinh}|B_k(0)|+r(\eta),
\quad
 r(\eta)=\int_0^\eta|h|d\eta=-\tfrac12\log c.
\]

已验证初片能量给出

\[
 |B_k(0)|^2=\frac12\left(\frac{e_k(0)}{\omega_k}-1\right).
\]

程序用该精确关系的区间上端得到 \(b_{k0}\)，再用

\[
 |B_k(\eta)|
 \le b_{k0}\cosh r_{\max}
       +\sqrt{1+b_{k0}^2}\sinh r_{\max}
\]

覆盖整个物理时间段。这里

\[
 c_{\min}=\cos(3/8)>0.9305076219,\qquad
 r_{\max}<0.03601250587.
\]

对应二次型为

\[
 e_k=\omega_k(1+2|B_k|^2),\qquad
 s_k=\frac{\omega_k}{3}(1+2|B_k|^2)
          -\frac{4\omega_k}{3}\operatorname{Re}(A_kB_k^*).
\]

故压力交叉项可用
\(|A_kB_k^*|\le |B_k|\sqrt{1+|B_k|^2}\) 包围。

### 5.2 先消去真空大项，再作有限和

有限 \(k\le256\) 的模式初值包围来自上一轮 C 的两份回执。我们没有在 \(\eta>0\) 新积分这些高模。为避免真空 \(k^4\) 量级的粗估，使用精确稳定式

\[
 r_s(k)=k^2\omega_k-k^3+\frac k2+\frac1{8k}
       =-\frac{\omega_k+3k}{8k(k+\omega_k)^3}.
\]

若 \(e_k^d=k+E_1/k+E_3/k^3\)，
\(s_k^d=k/3+P_1/k+P_3/k^3\)，则

\[
 k^2(\omega_k-e_k^d)
 =r_s(k)-\frac{h^2k}{2}-\frac{E_3+1/8}{k},
\]
\[
 k^2(\omega_k/3-s_k^d)
 =\frac{r_s(k)}3-(P_1+1/6)k-\frac{P_3+1/24}{k}.
\]

这些恒等式连同每模粒子项先求有限和，再加入一次正规零模及其减项、一次 AE 局部补项。最后接入旧 K256 的整个 \([0,3/16]\) 一致 UV 尾。

所有数值均为有向区间算术，主回执保存精确有理端点：

| 统一上界的组成 | 能量绝对上界 | 压力绝对上界 |
|---|---:|---:|
| 零模、\(k=2,\ldots,256\)、AE 补项 | <9269.39212 | <173438.640 |
| 旧同态一致 UV 尾 \(k>256\) | <238.22940 | <97125.486 |
| 完整参考应力 | **<9507.62151** | **<270564.125** |

有限部分和最终和分别向外取整，因此表列已取整分项之和可以比最终上界略大。正式计算直接使用未舍入的有理包围。

这是真实的时间区间控制；没有把四个时刻插值成一条无证明误差的曲线。界仍很保守，尤其压力的相位信息被丢弃，但它足以认证下面的尺度族。

## 6. 调整源强后的初片相容与全段缺陷

令 \(C=1/(576\pi^2)\)，固定本轮 \(\alpha=0\)，定义同一精确未知量

\[
 Q_{\rm eff,0}=Q+6C\log\lambda.
\]

选择

\[
 M_2^\star=27\lambda^4-54\lambda^2Q_{\rm eff,0}.
\]

当它为正时，该经典源合法，且初片总密度精确满足给定背景的 Hamiltonian 约束。这里 \(M_2^\star\) 和量子初片能量使用的是**同一个 \(Q\)**；不能在不同公式中独立选择两个区间端点来声称实现了相容。该式定义一个数学制备合同，并不声称已经在仪器上精确标定其动量。

在原同形背景上，这个经典源仍解齐性无质量场方程，其整个演化是

\[
 \rho_{\rm cl}^\star=p_{\rm cl}^\star
 =\frac1{2\lambda^2c^3}
  -\lambda^{-4}Q_{\rm eff,0}c^{-3}.
\]

因此总右侧相对给定 Einstein 背景的准确应力缺陷为

\[
 \Delta\rho
 =\lambda^{-4}
 [\rho_{\rm ref}(\eta)+CH_\rho^{(1)}(\eta)\log\lambda
                        -Q_{\rm eff,0}c^{-3}],
\]
\[
 \Delta p
 =\lambda^{-4}
 [p_{\rm ref}(\eta)+CH_p^{(1)}(\eta)\log\lambda
                        -Q_{\rm eff,0}c^{-3}].
\]

在当前时间区间上，

\[
 |H_\rho^{(1)}|\le6,\qquad
 |H_p^{(1)}|<29.83495.
\]

两者作为 \(c\) 的函数都严格递增；前者正、后者负，因而端点给出这些极值。程序同时核验导数公式及区间 \(c^2>3/4\)。

设旧参考初片上界为 \(Q_+\)，第 5 节全段上界为 \(R_+,S_+\)，则

\[
 \frac{|\Delta\rho|}{\rho_{\rm bg}}
 \le \frac2{\lambda^2}
 [R_++Q_++(6+6)C\log\lambda],
\]
\[
 \frac{|\Delta p|}{\rho_{\rm bg}}
 \le \frac2{\lambda^2}
 [S_++Q_++(29.83495+6)C\log\lambda].
\]

程序使用未向小数舍入的 \(H_p\) 区间端点。上述类型
\((B+D\log\lambda)/\lambda^2\) 在 \(\lambda\ge1\) 上严格下降，因为本回执验证了 \(2B>D\)。

在 \(\lambda=8192\)：

| 量 | 认证上界，已向外取整 |
|---|---:|
| 初片量子密度 / 背景所需密度 | \(3.309926\times10^{-6}\) |
| 全段参考量子能量 / 背景密度，绝对值 | 0.000283350 |
| 全段参考量子压力 / 背景压力，绝对值 | 0.008063441 |
| 调源后全段能量方程缺陷，相对值 | **0.000286660** |
| 调源后全段压力方程缺陷，相对值 | **0.008066751** |

\(M_2^\star>0\) 也由区间直接验证。相对原经典同形 \(M_2=27\lambda^4\) 的源强改变不超过 \(3.309926\times10^{-6}\)。随着 \(\lambda\) 继续增加，以上保守相对缺陷界继续下降。

较小尺度展示了初片与动态控制的区别：\(\lambda=15\) 已可保证所需调源为正，但我们的全时段压力缺陷界仍远大于背景；\(\lambda=4097\) 能把**初片**压力绝对界压到背景的 \(1\%\) 内，全时间段压力缺陷界仍约为 \(3.23\%\)。不能把这些不同认证互相替代。

## 7. 证书接口、复算与边界

运行：

~~~sh
/Users/murphyhoops/Documents/ueot-physics-closure-20261111/.physics-venv/bin/python physics/qm/null_source/timelike/compatibility/scaling/check.py --check
~~~

这个命令只重新进行符号恒等式、有限谱和、区间缩放及缺陷计算，不重新积分任何模式。输入旧回执、旧源文件、共同物理合同和本程序均绑定 SHA，并在计算结束再次检查未改变。inherited_input_sha256 只列旧继承文件；新 check.py 在独立 source_sha256 中。python -O 会被拒绝。

便于独立组装的主要 JSON 字段：

- initial_base_density_interval、initial_base_pressure_interval：旧完整初片区间。
- uniform_base_reference.c_interval：全时段 \(c\) 包围。
- uniform_base_reference.full_rho_absolute_upper、full_pressure_absolute_upper：完整参考应力的统一界。
- uniform_base_reference.H1_rho_absolute_upper、H1_pressure_absolute_upper：曲率项极值。
- scales：指定 \(\lambda\) 的初片、量子相对项、调源 \(M_2\) 区间及全段缺陷。
- certified_scale_family：\(\lambda\ge8192\)、\(\alpha=0\)、全段两应力缺陷均小于 \(1/100\) 的合同。
- failure_controls：遗漏 log 项、只换 \(\mu\)、错置零模方差、混用三种 \(M_2\) 合同和把小应力缺陷当度规误差等负控。

主审与 C 已逐项独立核对 Hamilton 基方程、简并度、有限真空消项、零模、曲率项极值和全段缺陷公式。主审还采用总粒子预算和整体 Cauchy 不等式设计不同的统一界复核，避免仅复述本程序的逐模实现。

这项结果把上一轮的初片排除推进到了一个合法的同形参考态族、可认证的正源强调整和整个时间段的小方程缺陷。要进一步变成真实自洽半经典演化，仍需处理允许的高阶几何 jets、重整化耦合、全局初值及演化稳定性。小残差本身不提供这些结论。


## 8. 小均值缺陷没有消除原源的混合涨落

这里认证的是平均应力。若仍使用原分布合同 \(Y=s/2+X\)、\(X\) 对称、\(\mathbb E X^2=3/4\)，则在四阶矩存在时

\[
 \mathbb E Y^2=1,\qquad
 \operatorname{Var}(Y^2)=\mathbb E X^4+\frac3{16}
 \ge\frac34.
\]

原有界候选 \(X=\pm\sqrt3/2\) 达到等号；更一般的允许分布可能没有有限四阶矩。放大空间尺度并不会改变这项相对混合方差。

对于任意固定平滑应力读数，按 \(Y\) 条件化后的均值含 \(Y^2 T_{\rm cl}^{\star}\)。其经典混合协方差项是
\(\operatorname{Var}(Y^2)T_{\rm cl}^{\star}(x)T_{\rm cl}^{\star}(x')\)。在本调源族中，相对背景应力平方的比例至少为

\[
 \frac34\left(1-\frac{2Q_{\rm eff,0}}{\lambda^2}\right)^2,
\]

并随 \(\lambda\to\infty\) 趋向 \(3/4\)。这只是能独立计算的经典混合项，没有把全部量子应力噪声或度规涨落冒算成它。它也不允许把小平均方程缺陷解释为每个分支的引力误差都很小；噪声到几何的响应仍需明确的动力学和观测合同。
