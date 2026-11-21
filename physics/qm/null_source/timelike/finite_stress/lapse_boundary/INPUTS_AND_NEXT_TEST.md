# 闭环之后的下一项：实际几何初始块、因果逆与观测预算

## 已验收输入

本轮的完整source N、同一实际态的齐次retarded RSET响应、初始C–future stress混合列、
六个global Killing momentum行及其定义域已明确。
保留完整裸边缘的独立carrier修复已由前驱排除；pure canonical endpoint混合也不能造新物理荷。
21级正常记录允许改变裸态并保留当前非选择源应力限制，但记忆Z不是几何约束荷。

## 必须保留的实际线性约束矩阵

背景E=S=0，ν=δN、w=δlog a、δκ=w′−hν。
以RETARDED_RESPONSE的同态算子Rρ、Rp定义
\[
 {\cal E}=2h\delta\kappa-\tfrac23a^2(2\rho w+R_\rho[w,\nu]),
\]
\[
 {\cal S}=(\delta\kappa)'-\nu h'+h\delta\kappa
                    +a^2(2pw+R_p[w,\nu]).
\]
原action给δΓ_N=(3V0a²/2)E，δΓ_u=3V0a²(S+E/2)。
实际源力η_N=−V0a⁴ξρ、η_u=V0a⁴(−ξρ+3ξp)，
两action方程恰为E=(2/3)a²ξρ、S=−a²ξp。
噪声必须取同一源力的完整绝对协方差；不把两个分量独立化。
bulk CTP二次式为qΔ L_R qc+(i/2)qΔ Nη qΔ，另保留真实initial mixed functional。
这只到二阶cumulant层，非Gaussian源不能由它自动变成完整Gaussian物理过程。

正常kinematic强约束与原mean/CTP的层次区别见[合同复盘](CONTRACT_LAYERS.md)。下列强约束验收只对已明确选择的候选适用，不提升为原mean-SCE的普遍公理。

## 本轮继续关闭的定义域与作用量接口

CAUSAL_DOMAINS已证明：完整静态G对实际平稳source的全过去卷积没有GNS L²极限。
因此第4项的无限过去分支已在声明合同下拒收，不继续把它当未检查候选。
有限K实际pressure因果逆和off-shell Ward缺陷现已明确。
FINITE_SOURCE_DOMAIN给实际U上的源起始UV系数与含源Q/D初始块的精确取消；
该block还没有被证明来自正常geometry/装置准备。
ACTION_RESPONSE已将同AE总action行重写到Q响应核与完整局部项；
COVARIANT_RESPONSE给严格紧支测试上的协变两腿及contact账本，固定AE tensor转换仍待完成。

## 下一首要交付及拒收条件

1. 从同一总作用量和一次真实准备过程给出有限初片joint density或约束后物理态与内积。
   必须明确“正常”是原运动学source⊗carrier代数还是由原约束构造的物理代数。
2. 实际满足C_geom−C_pre=C_source，保留已知C–stress关联及局域动量约束。
   若C_geom−C_pre仍是独立carrier-only自伴量，应用旧TOTAL_BOUNDARY_GATE §4（及QUANTUM_FLOOR）的连续谱强约束阻断：
   当前C无点谱，C⊗1−1⊗Z也无点谱，故原普通tensor Hilbert中的正常态不可能精确强匹配。
   这是前驱一般论证的当前应用，不新增定理；没有统一正残差下界。
3. 若有真正含源的mixed/preparation列，明确它的action来源、域、正性和正常联合态。
   不能从可写出的有限协方差直接推定Hilbert态或局域装置存在。
4. 在声明的有限准备片、gauge和边界合同B下构造G_R^B。
   从−∞作用于静态过去不衰减的压力涨落，需要单独的过去加权GNS L²证明；
   几何的正频Wiener逆不能自动作用于平稳噪声。
5. 首个物理几何测试取同一初片起算的proper-time expansion：
   O_g=δ∫g(τ)Hphys(τ)dτ=−∫g′(τ)w_τ(τ)dτ，g为明确compact测试。
   先把它经实际G_R^B的adjoint拉回source域，再计算完整初始+源+交叉方差和截断误差。

若w=w_B+G_R^B b，b=−a²ξp，F为上述几何测试，K_F=(G_R^B)*F，则必须实际验收
\[
 \operatorname{Var}O_F
 =\operatorname{Var}O_B+N_{bb}(K_F,K_F)
 +2\operatorname{Cov}_{sym}(O_B,b(K_F)).
\]
已知Cov(C,b(K))=−ασ²μ2∫a²LK，不能随手设为零。
正交投影检验为
\[
 \min_z\operatorname{Var}(\xi_p(f)-zC)
 =N_{pp}(f,f)-\sigma^2\mu_2L_f^2\ge0,\quad z=L_f/\alpha .
\]
它只去掉profile块，number/pair/highvac部分仍在。
这是GNS二阶投影，不是声称已实现条件测量。

## 本轮复盘已改变的选择

短窗绝对pressure很大，新长窗指定source测试可以较弱，两结论并不矛盾。
但同一新mean族的anchored proper-time快方向log增益>18709；
源的正单位f预算不能控制未知G_R^*F的预算。
因此下一步优先真正的准备/边界/因果逆与观测，停止重复缩窄σ、重复固定裸态carrier或把端点相位当物理修复。

后续任何新interaction都必须重算total stress及其renormalization。
上述工作完成前，完整几何—物质—装置闭环与物理统一均OPEN。
