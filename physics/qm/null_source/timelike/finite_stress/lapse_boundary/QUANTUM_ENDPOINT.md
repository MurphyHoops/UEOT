# 将端点相位当作第二几何 canonical 对的主动准备：正常极限失败

ACTION_LIFT 的完整几何初值还有 κ、Pκ，
不能把 INCOMING_PREPARATION 的一对自由指针直接替代全部几何。
本页审查一个具体、可复核的尝试：
把已知 −[κQ_K] 端点相位主动施加在正常 κ 波包上，
再在固定 incoming tensor 表示中取全场极限。

已有 ENDPOINT_DOMAIN 证明单独 sharp shear 的 Fock 极限阻断。
本页复用该高频数据，新增联合几何边缘 purity 的直接判定；
不是重新计算一个全局 no-go。

## 1. 每个有限 K 的明确正常联合态

取任意固定 g∈L²(R,dκ)，||g||₂=1。
源为同一当前 ρS，低模正常、高模实际 incoming 真空。
定义
\[
 {\cal V}_K=\exp[-i\kappa\otimes Q_K],\quad
 Q_K={1\over2}\sum_{r\in{\cal I}_K}q_r^2,\qquad
 \rho_{gS,K}={\cal V}_K(|g\rangle\langle g|\otimes\rho_S)
                         {\cal V}_K^\dagger .                \tag{E1}
\]
各有限 K 都是正常正 trace-one 态。
它是固定因子代数上的主动状态改变；
若只是 canonical 坐标运输，则不能把 E1 当成新物理制备。

几何边缘有 kernel
\[
 \rho_{g,K}(\kappa,\kappa')=
 g(\kappa)\overline{g(\kappa')}
 \chi_{Q_K}(\kappa-\kappa'),\quad
 \chi_{Q_K}(s)=\operatorname{Tr}\rho_S e^{-isQ_K}.             \tag{E2}
\]

## 2. 当前非静态高模给精确的 offdiagonal 消失

单 real oscillator 的 q 真空分布方差 X_k=|v_k(i)|²，
\[
 \langle e^{-isq^2/2}\rangle=(1+isX_k)^{-1/2}.
\]
两个场、k²重数给
\[
 |\chi_{{\rm high},K}(s)|^2
  =\prod_{k=3}^K(1+s^2X_k^2)^{-k^2}.                        \tag{E3}
\]
实际 Jost 高频式 X_k=1/(2ω_k)+O(ω_k^−3)，ωk²=k²−1，
故对固定 s≠0，
\[
 {1\over K}\log|\chi_{{\rm high},K}(s)|^2
 \longrightarrow -{s^2\over4}<0 .                           \tag{E4}
\]
有限低模 characteristic function 模≤1，不改变消失结论。
中心化 Q_K 或加入任意 κ-dependent c-number 相位也不改变模及下面 purity。

## 3. 正常联合全场极限不存在

由 E2，
\[
 \operatorname{Tr}\rho_{g,K}^2
 =\iint |g(\kappa)|^2|g(\kappa')|^2
              |\chi_{Q_K}(\kappa-\kappa')|^2d\kappa d\kappa'.
\]
integrand 被可积的 |g|²⊗|g|² 控制。
除 κ=κ' 对角零测集外，E4 使 integrand→0。
因此
\[
 \boxed{\operatorname{Tr}\rho_{g,K}^2\to0}.                  \tag{E5}
\]
没有假设 g 有额外光滑性，也没有把 variance divergence 单独当作 E5 的证明。

若 ρg,K 在 trace norm 收敛到正常 trace-one ρg，
则 Hilbert–Schmidt 连续性给 Trρg²=0；
但非零正 trace-one 算符的 purity严格正，矛盾。
partial trace 的 trace-norm contractivity 又排除 ρgS,K 的正常联合 trace-norm 极限。
等价的二阶 Rényi entropy −logTrρg,K² 无界增长。

## 4. 这个拒收怎样影响下一项

拒收对象是：固定正常 g、同一 incoming tensor frame、
把单独端点 shear 当作主动准备，再直接令 K→∞。
它不能提供原 Pκ−Q 初始混合块的正常全场实现。
任何有限 K 都正常并不能替代这个全场门。

未被排除：先在有限 K 合并完整 action、initial density、端点和 gluing 再取极限；
不同 cutoff-dependent 几何准备且另验统一资源；
Hilbert-bundle、约束后 physical inner product 或其他协变量子化。
这页没有把坐标变换当相互作用，也没有否定合法 Hadamard source 本身。

因此下一任务应把 INCOMING_PREPARATION 的同应力近似对照，
放回 ACTION_LIFT 的两对几何初值与完整约束，
先共同处理端点/态/观测运输，再谈正常物理态及实际装置。

## 5. 一般正常几何输入与固定 Gaussian 的定量率

固定一般正常 geometry density 属于 Hilbert–Schmidt，具有 L² kernel。E2中的gκgκ′*可换为该kernel，E5仍由其模平方可积和DCT成立；仍要求原 geometry/source 输入为已声明 product，不擅自扩大到任意K相关初态。

对 |g|²=N(μ,s²)、固定 s>0，difference κ−κ′ 的密度为 exp[−d²/(4s²)]/(2√πs)。令d=x/√K，实际high特征模趋exp(−x²/4)，有限low因子趋1，给
\[\sqrt K\operatorname{Tr}\rho_{g,K}^2\longrightarrow1/s.\]
严格可积控制可取高模块k∈[K/2,K]，|v|⁴≥1/(8k²)，得到scaled bound (1+x²/(8K³))^(−K³/16)。用n log(1+x²/n)的单调性，在固定充分大K0选一个可积幂函数控制即可。这是特定κ单位的purity率，不是度规误差比。

## 6. 主动符号与被动表示必须分开

固定 Pκ=−i∂κ，U−=exp(−iκQ)给 U−†PκU−=Pκ−Q；若试图主动抵消bulk的Pκ−Q，则用U+=exp(+iκQ)，有U+†(Pκ−Q)U+=Pκ。两种符号的全部purity结论相同，所以本页拒收亦包括正确抵消符号的主动方案。
被动raw/bulk变换则是W(Pκ−Q)W†=Pκ，并须同时运输density、action与observables。它不是本页固定因子代数的主动准备。
