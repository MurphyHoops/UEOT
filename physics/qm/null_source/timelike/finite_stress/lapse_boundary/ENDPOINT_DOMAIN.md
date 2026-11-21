# 尖锐端点生成元的全场定义域与先相消后取极限

## 1. 同一个实际态，新的定量尾估计

沿用已匹配非静态历史及其精确 incoming 高模真空。每个实振子的
\[
 \langle q_k^2\rangle=(2\Omega_k)^{-1},\quad
 \Omega_k=\omega_k-\mathcal V/(2\omega_k)+O(\omega_k^{-3}),
 \quad \omega_k=\sqrt{k^2-1}.
\]
两场每壳有 2k² 个实振子。任意有限低模（包括两个不同的正常薄层态）不影响下面的尾。

定义 Q_K=Σq²/2。Gaussian 单振子直接给 Var(q²/2)=1/(8Ω²)，于是
\[
 \operatorname{Var}Q_K
 =\sum_{k=3}^K\frac{k^2}{4\Omega_k^2}+O(1)
 =\frac K4+O(1).
\tag{U1}
\]
后一等号用 k²/Ω²=1+O(k^−2)。因此 Q_K−任何实数序列均没有当前态的 GNS L² 极限。减去均值或 Wick c-number 不改变这个结论。这是尖锐时间、全空间二次生成元；不否定光滑时空测试的 Wick 多项式。

## 2. 端点剪切不存在所声称的强酉极限

令 W_K(κ)=exp(−iκQ_K)。单振子 Gaussian 积分给
\[
 \langle e^{-i\kappa q^2/2}\rangle
 =(1+i\kappa/(2\Omega))^{-1/2}.
\]
对 L>K 且 K 已超过所有被修改的低模，
\[
 |\langle W_K\Psi,W_L\Psi\rangle|^2
 =\prod_{k=K+1}^L
       (1+\kappa^2/(4\Omega_k^2))^{-k^2}.
\tag{U2}
\]
固定 κ≠0，逐项 Taylor 展开及可和余项给
\[
 \log|\langle W_K\Psi,W_L\Psi\rangle|^2
 =-\frac{\kappa^2}{4}(L-K)+O(K^{-1}).
\tag{U3}
\]
取 L=2K 时趋于负无穷。因此对任意 c-number 相位 θ_K，e^{iθ_K}W_KΨ 都不是 Cauchy 序列：两向量距离平方至少为 2−2|重叠|，趋于 2。不存在这个 Fock 空间上的所声称强酉极限。不同 CCR 表示、代数态或经过实际平滑相互作用产生的态不被这项结果一概排除。

U1 与 U3 给已有 Shale 判断的定量端点版本；不是仅凭粒子数期望发散就断言任意非 Gaussian 正常态不可能。

## 3. 主动 kick 与被动坐标运输不同

以下只是固定静态背景、固定同一个 proper-time Hamiltonian 的主动对照。它不移植到动态 Hadamard RSET。

在静态高模真空上实际施加 W_K(κ)，每振子
\[
 \Delta\langle H_{0,k}\rangle=\kappa^2/(4\omega_k),\quad
 \Delta\langle N_k\rangle=\kappa^2/(4\omega_k^2).
\]
所以两场的 proper-time 增量为
\[
 \Delta E_K=\frac{\kappa^2}{2A}\sum_{k=3}^K\frac{k^2}{\omega_k}
 =\frac{\kappa^2 K^2}{4A}+O(K),
\]
\[
 \Delta{\cal N}_K=\frac{\kappa^2}{2}\sum_{k=3}^K\frac{k^2}{\omega_k^2}
 =\frac{\kappa^2K}{2}+O(1).
\tag{U4}
\]
一个瞬时剪切若改读为真实准备门，不能继续享有被动变量变换的“零物理改变”。平滑局域作用量可以改变高频尾，但它是另外的动力学与应力责任。

## 4. 对实际平滑约束荷的结论

ACTION_BOUNDARY 的有限 K CTP 恒等式必须先组合：

- raw 与 bulk 作用量的端点差；
- 同一初始 cross kernel 的两个相位；
- 实际末端配对及全部相关导数。

组合后它们精确相消，或者保留共同 physical endpoint 明确要求的同一个配对。不能分别给 Q_K 或 Q_KρQ_K 赋一个不存在的全场极限，再把它当作新初始混合块。

对已经定义好的应力平滑组合，旧 DYNAMIC_CHARGE 已证明：共同截止的密度和压力测试分别在实际态 GNS L² 中收敛，且
\[
 C_{\rm source}[\chi]
 =\frac{2\,\delta H_{\rm in}}{3V_0A}.
\tag{U5}
\]
因此纯 canonical 端点候选在这个极限中仍不产生额外物理荷。这是从有限恒等式到已接受平滑域的确切传递；没有证明每一个未定义的 tensor Hessian 或任意边界分布极限存在。

完整重整化相位、真实准备过去的变化与量子几何仍是独立问题。尤其不能从“总组合合法”倒推其每一个尖锐分项合法。

## 5. 独立可执行检查的意义

endpoint_domain.py 检查 Gaussian 积分对应的有限式、高频渐近系数与静态主动能量系数，并给可复核有限 K 尾样本。无穷阶与不收敛结论由 U1–U4 的解析证明承担；有限样本不冒充无穷维证明，也没有执行旧模式 ODE。

方法背景：Cortez et al., https://arxiv.org/abs/1101.2397。该文支持 compact S³ 上简并加权的酉可实现性判据，不替代本页实际态的定量推导。
