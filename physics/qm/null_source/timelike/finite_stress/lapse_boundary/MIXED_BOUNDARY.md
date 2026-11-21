# 真正含源的初始列：两条齐次弱方程的共同闭合

在CONSTRAINT_RESIDUAL拒收原fullmode R之后，本页继续构造修复，
不把“独立carrier不行”推广成所有mixed项不行。
新增结果是一份来自同一正常source态的连续GNS向量值弱解：
它精确满足已声明的齐次线性化压力、密度两行，并有统一正协方差。
它尚不是独立geometry⊗matter上的正常联合态或原总CTP准备的实现。

## 1. 一个统一初始列，不能逐测试换态

沿用同一actual quiet U，h_i>0且a_i=A。
令
\[
 H_i=\delta(H_0-V_iQ)_i\in L^2(\rho_\pm),\qquad
 \Lambda(q)=-{q_i\over3V_0a_i^4h_i}.
\]
定义对所有q共同的映射
\[
 R_\lambda(q)=R(q)+\lambda\Lambda(q)H_i,\quad
 {\cal W}_\lambda(F)=R_\lambda(-a^2G_p^*F),\qquad\lambda\in\mathbb R.
                                                               \tag{M1}
\]
q_i是H² trace；H_i已由共同source cutoff得到L²。
所以M1是连续映射，不需要单独sharp Q_i、D_i或H0_i的二阶矩。

等价地，以〈F,v_i〉=(G_p^*F)(i)定义同一弱边界列，
\[
 {\cal W}_1(F)={\cal W}(F)
     +{H_i\over3V_0a_i^2h_i}\langle F,v_i\rangle.     \tag{M2}
\]
它明确含源，不是pure canonical变量重命名，也不是独立carrier记录。
该列一般在原zero-initial H4图域之外；
本页验收的是该算子的向量值transpose延拓。

## 2. 压力、密度与有区分力的负对照

对φ∈C∞_c((i,T))，
G_p^*L_p^*φ=φ，q=−a²φ初端为零，所以全部λ都满足
\[
 {\cal W}_\lambda(L_p^*\phi)=-\xi_p(a^2\phi).         \tag{M3}
\]

对密度测试f，使用已经证明的
E_U^*f=L_p^*J^*f及G_p^*E_U^*f=J^*f。
q_E=−a²J^*f的初端是
\[
 q_E(i)=-2a_i^2h_i e^{U_i}\int_i^T e^{-U}f .
\]
因此
\[
 K_{\rm res}[R_\lambda]=(1-\lambda)K_{\rm res}[R].
                                                               \tag{M4}
\]
H_i的方差严格正，故在这个单参数族中，只有λ=1消去density荷。
λ=0与λ=2仍有非零残差，尽管两者pressure通过且Gram为正。

于是对所有compact测试，
\[
 \boxed{
 L_p{\cal W}_1=-a^2\xi_p,\qquad
 E_U{\cal W}_1={2\over3}a^2\xi_\rho
 }\quad\hbox{作为同一source-GNS中的弱恒等式}.        \tag{M5}
\]
这不是仅匹配均值，也没有把密度和压力改成独立噪声。

## 3. 共同 cutoff、正性与因果性

每个K用同一个source态定义
\[
 R_{\lambda,K}(q)=\xi_{p,K}(q)-B_{i,K}(q)
       -{\lambda q_i\over3V_0a_i^4h_i}
               \delta(H_{0,K}-V_iQ_K)_i .
\]
两个已证共同GNS极限使任意有限组测试的全部cross内积收敛。
所以Gram、实对称协方差和弱交换子均由实际态继承，
不是独立填写一个正定矩阵。

这里响应Gp是已经构造的full-field算子；
没有宣称每个K的total-action逆Gp,K同时收敛。
有限cutoff只用于同一source算符组合的极限。

若F的未来上界为t*，advanced q_F在t*之后为零；
R只使用t*之前的源，新增H_i只取共同初片。
因此该候选具有声明的时间因果性，没有使用未来制备状态。

## 4. 完整方差必须重新计算

记c_q=Λ(q)，H_i的zero系数(α_H,β_H,γ_H)见CONSTRAINT_RESIDUAL D4。
设
\[
 d_H=|v_2'(i)|^2+(\omega_2^2-V_i)|v_2(i)|^2,\quad
 b_{H,k}={v_k'(i)^2+(\omega_k^2-V_i)v_k(i)^2\over2}.
\]
M1完整绝对方差由PREPARED_READOUT P13做如下同源替换：
\[
 (\alpha_Q,\alpha_D,\alpha_P)\mapsto
 (\alpha_Q+\lambda c_q\alpha_H,\ 
  \alpha_D+\lambda c_q\beta_H,\
  \alpha_P+\lambda c_q\gamma_H),
\]
\[
 d_q\mapsto d_q+\lambda c_qd_H,\qquad
 \beta_k[q]\mapsto\beta_k[q]+\lambda c_qb_{H,k}.       \tag{M6}
\]
所有平方及cross项一起保留。
C混合块同样以这三个新zero系数代入P15，不能继续沿用旧R的值。

特别地λ=1时，
\[
 \alpha_{Q,corr}={-q_i'+(3h_i+h_i'/h_i)q_i\over6V_0a_i^2},
 \qquad
 \alpha_{D,corr}=2\mathcal I_i\alpha_{Q,corr}.        \tag{M7}
\]
旧αD的q_i/(3Va⁴)主项被精确抵消。
因此原fullmode R的σ⁻²下界不能原封当作修复后预算。

对高模|b_H,k|≤6μJ/ω²，可取
Var(H_i−H_i,K)≤200μJ²/K。
M6的模数尾保守满足
\[
 {\cal T}_{K,corr}(q)\le
 2{\cal T}_K(q)+400c_q^2\mu_J^2/K.                 \tag{M8}
\]
Neumann误差也必须乘上修复映射的额外trace系数
||H_i||₂/(3V0a_i⁴|h_i|)；不能只报告原逆的小q_inv。

## 5. 靠近静态极限的明确限制

该列使用1/h_i。h_i严格非零时它有限，
h_i=0时公式未定义，不允许把tiny h当成0再继续沿用。

固定T、原正常包宽σthin>0，沿一次选参族c→0，
实际inverse和source高频界给q_F,c→q_F,0于H³、
R_c(q_c)在GNS有界，以及H_i(c)→A δH_in于GNS。
若q_F,0(i)≠0，则保留全部cross后
\[
 h_i{\cal W}_{1,c}(F)\longrightarrow
 -{q_{F,0}(i)\over3V_0A^3}\delta H_{\rm in},
\]
\[
 h_i^2\operatorname{Var}{\cal W}_{1,c}(F)
 \longrightarrow {q_{F,0}(i)^2\sigma_{\rm thin}^2\mu_2
                         \over9V_0^2A^6}>0.         \tag{M9}
\]
若F来自同一proper-time g，须同时用P1的F_c→F_0；
本轮明确例子见READOUT_WITNESS。

这是此数学completion的非一致近静态放大，
不能用渐近式替代本轮固定c的误差预算，也不是所有准备的no-go。
不受控的线性读数不能外推成真实非线性度规发散。

## 6. 这项闭环没有偷换物理目标

已完成：同一实际mean历史、同一非Gaussian正常source、
同一因果/伴随响应、同一source cutoff极限及真正含源初始列，
在声明的transpose域上同时满足两条齐次线性化方程。
finite组正协方差与完整原态预算由同一态产生。

ACTION_LIFT 已从保留 lapse 的同一有限 K 作用量推导该初始列，
并保留后续 off-shell Ward defect；这不替代本页 full-field 逆的独立构造。
仍待完成：该初始列是否由同一正常联合有限初片 density 及真实准备过程实现；
其geometry/source可观测代数、Peierls/正则交换结构和正常物理态；
非齐次tensor行、原AE匹配、装置总源及实际校准。

仅有M5和正Gram不等于已获得完整Einstein–CTP物理解。
下一轮应继续审查M2的物理初态与真实准备，
而不是重新尝试已排除的保裸态独立carrier。

## 7. 作用量来源已经补齐到明确的有限截断初始行

ACTION_LIFT L7–L9 给出同一 AE lapse 代表、完整边界势与初始列。原减除留下的 density 差恰为 2H_i,K/(3V0a_i²)，E_K v0,K(i)=2h_i，所以补偿系数必须为 H_i,K/(3V0a_i²h_i)，与 M2 完全一致。对应 δP_u=−H_i,K/h_i。这是给定初值合同下的作用量必要关系，不是正常联合态或全模式 Gp,K 收敛定理。
