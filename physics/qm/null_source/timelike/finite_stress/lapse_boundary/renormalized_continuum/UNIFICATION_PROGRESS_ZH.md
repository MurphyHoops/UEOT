# 重整化连续统自主装置、Parseval 四极消除与亚临界反弹闭合宇宙推进报告（PR #468 接续）

## 一、本轮定位与总体裁决

本轮工作从 `joint_constraints` 的已验封提交 `3cd6f7ead5743782173e44ab3344b8129c01c899`（草稿 [PR #468](https://github.com/MurphyHoops/UEOT/pull/468)）直接接续，原样复用全部 `319` 项已接受前驱检查（`294 + 25`），原字节冻结全部 `1,178` 个前驱科学文件（`1090 + 87 + 1`），零前驱科学模块导入或重跑，零模式或几何数值 ODE 积分（全部采用 100 位有效数字 `mpmath.iv` 外扩区间与精确代数证明）。

**核心结论**：针对 `joint_constraints/NEXT_GATE.md` 与前轮报告第八节留下的四道顺序关卡，本轮在明确声明的模型与输入边界内完成了 **12 项新科学证明与证书（`RC01`–`RC12`）及 1 项范围/审计绑定检查（`review`）**。**整体物理统一的核心目标仍未完成（`"physical_unification": "OPEN"`）**；`PR #468` 保持开放草稿（Draft）状态、不提前合并闭环。

- 成果总览索引：[README.md](README.md)
- 研究边界合同：[CONTRACT.md](CONTRACT.md)
- 下一阶段验收门：[NEXT_GATE.md](NEXT_GATE.md)
- 独立计时与三代理不可变源码审计：[SESSION.md](SESSION.md) · [AUDIT.md](AUDIT.md)

---

## 二、逐项闭环的四大科学进展与保留边界

### 1. 有限测地帽传感器核 $\kappa_{\rho_0}$ 与 Glimm–Jaffe 连续统 Friedrichs 下界（`RC01`–`RC03`）
- **解决的前轮障碍**：在点状截断下，固定耦合 $g>0$ 时点时钟方差按 $K^2$ 发散导致开关坍缩（`CLOCK_UV`），裸零点能 $E_{\mathrm{zp},K}\sim K^4$ 发散，且四粒子体场图范数发散（`WICK_CLOCK_GRAPH`）。
- **本轮精确构造**：
  1. 在单位 $S^3$ 上引入非负 $SO(4)$ 不变 $C^7$ 测地帽传感器核 $\kappa_{\rho_0}(x,y)=C_{\rho_0}^{-1}(x\cdot y-\cos\rho_0)_+^8$（$\rho_0=1/20\text{ rad}$）。九次分部积分给出严格上界 $|\hat\kappa_{\rho_0}(k)|\le \overline B_{\rho_0} k^{-10}$（平方后 $O(k^{-20})$），且等时涂抹场在测地距离 $d_{S^3}(x_1,x_2)>2\rho_0=1/10\text{ rad}$ 外严格对易（[GEODESIC_CAP_KERNEL.md](GEODESIC_CAP_KERNEL.md)）。
  2. 采用正规序自由生成元 $H_{0,\mathrm{ren},K}(a)\ge 0$ 消除 $K^4$ 裸零点能，证明对所有 $K\in\mathbb{N}\cup\{\infty\}$ 与 $a\in(0,\sqrt{3/2}]$ 成立一致有界下界 $H_{\mathrm{ren},K}^{\rho_0}(a)+C_{\mathrm{shift},\rho_0}\ge \frac{1}{4}H_{0,\mathrm{ren},K}(a)\ge 0$（$C_{\mathrm{shift},\rho_0}<2.5\times 10^7$ 与 $K$ 无关），由 Friedrichs 定理给出 $K=\infty$ 自伴实现；四粒子 Wick 方差尾按 $O(K^{-18})\to 0$ 收敛，截止投影对易子 $\|[P_K,\mathcal{K}_{\rho_0}Z_a]\|$ 按 $O(K^{-10})\to 0$ 消失（[CONTINUUM_CLOCK_COMPOSITE.md](CONTINUUM_CLOCK_COMPOSITE.md)）。
  3. 纳入共形无质量控制器（$\xi=1/6,M=0$）的完整改进应力张量 $\Delta T_{\mu\nu}^{(Y,\mathrm{imp})}$ 后，内行列式下界由 $>4.5$ 显著加强至 $\det M_{\mathrm{ctrl}}^{\rho_0,\mathrm{conf}}>10.0$，连续统极限/参变近似总源八投影逆范数满足 $\|(J_{\mathrm{total}}^{\rho_0,\infty})^{-1}\|<0.0056$，且未减除正平方复合与真空蝌蚪减除（$v_{\mathrm{eff}}=0$）两种重整化处方在 $K=\infty$ 均可逆；同时明确最小耦合时钟锐切片电荷由 $\mathcal{Q}(H_{0,3}(X))$ 控制（[CONTINUUM_TADPOLE_COLUMNS.md](CONTINUUM_TADPOLE_COLUMNS.md)）。
- **保留边界**：该连续统模型显式依赖有限传感器尺度 $\rho_0=1/20>0$（在 $d_{S^3}<2\rho_0$ 内为有限程相互作用，未宣称 $\rho_0\to 0$ 点状 Wightman 极限），且未声称非微扰 Friedrichs 酉群保持 $\mathcal{Q}(H_{0,3}(X))$。

### 2. 六通道共形耦合 Parseval 标架：全时段精确消除空间四极 $-Q_2/g^2$（`RC04`）
- **解决的前轮障碍**：`POST_CLOSURE` 证明双通道偶极控制器必留非零二阶空间谐波 $-Q_2(\mathbf u)/g^2\neq 0$（因为秩 $\le 2$ 矩阵无法构成 $I_4$ 的非零倍数）。
- **本轮精确构造**：将控制器扇区扩充为 **6 通道共形耦合无质量（$\xi=1/6,M=0$）偶极标架** $(Y_0,Y_1,W_1,W_2,W_3,W_4)$，其中 4 个与体场解耦的旁观通道携带实解析正定矩阵平方根 $\mathbf W(\mathbf u)=(\lambda_0 I_4-\boldsymbol\epsilon\boldsymbol\epsilon^T-\boldsymbol\zeta\boldsymbol\zeta^T)^{1/2}$（$\lambda_0=2\times 10^{-32}$，$\|\mathbf u\|\le 10^{-16}$），使 $S_{\mathrm{frame}}(\mathbf u)\equiv \lambda_0 I_4$ 恒成立。在**任意**闭合 FRW 度规 $ds^2=a(\tau)^2(-d\tau^2+d\Omega_3^2)$ 上，改进共形应力张量中的空间梯度、$a'(\tau)/a''(\tau)$ 导数与 $\cos(2\tau)/\sin(2\tau)$ 振荡**恒等相消**，给出全时空严格 $SO(4)$ 齐次辐射流体：
  \[
   \rho_{\mathrm{frame}}(\tau,x)\equiv \frac{2\lambda_0}{\hat\kappa_{\rho_0}(2)^2 g^2 a(\tau)^4},\qquad j_{i,\mathrm{frame}}\equiv 0,\qquad T^i{}_{j,\mathrm{frame}}\equiv \frac{2\lambda_0}{3\hat\kappa_{\rho_0}(2)^2 g^2 a(\tau)^4}\,\delta^i_j,
  \]
  从而全时段精确消去 $-Q_2/g^2$ 及全部 $\ell\ge 1$ 控制器背景应力行，且背景几何与控制向量 $\mathbf u$ 完全独立（[PARSEVAL_ISOTROPIC_FRAME.md](PARSEVAL_ISOTROPIC_FRAME.md)）。

### 3. 刚性时钟大挤压视界定理、亚临界反弹 FRW 共同历史与 Hadamard 运输（`RC05`–`RC08`）
- **严格区分坍缩区与反弹窗口（`RC05`）**：证明在 $\Lambda\le 0$ 时，任意非零最小无质量时钟（$w_X=+1$）加共形辐射的闭合 FRW 宇宙总共形寿命严格满足 $\Delta\tau_{\mathrm{universe}}<\pi<\pi+4$（纯时钟 $\le \pi/2$），在到达编码/读出前即坍缩为大挤压；而在 $\Lambda>0$ 与正辐射 $\beta_r>0$ 下，光滑转折反弹 $a(0)=1,a'(0)=0,a''(0)>0$ 存在的**充要条件**是亚临界引力紧致度 $\frac{4\pi G}{g^2}<1$（$\alpha_G=\frac{4\pi G}{3g^2}<\frac{1}{3}$，[CRUNCH_VS_SUBCRITICAL_GRAVITY.md](CRUNCH_VS_SUBCRITICAL_GRAVITY.md)）。
- **零 ODE 220 阶 Taylor–Picard 区间包络与弯曲演化重推（`RC06`–`RC08`）**：
  1. 在 $(\alpha_G,\lambda_\Lambda,\beta_r)=(\frac{1}{10},\frac{550001}{1000000},\frac{349999}{1000000})$ 上用带权 Banach 不动点（$\gamma=3,L_{\mathrm{lin}}<0.31$）认证全窗口 $\tau\in[-1,\pi+3]$ 解误差 $R_u<2\times 10^{-30}$，严格满足非静态性与弯曲正平方阈值 $1\le u(\tau)<1.016<\frac{3}{2}$，并重推出非匀速物理时钟 $\theta(\tau)=\int_0^\tau u(s)^{-1}\,ds\neq\tau$（[DYNAMICAL_FRW_CLOCK_PROGRAM.md](DYNAMICAL_FRW_CLOCK_PROGRAM.md)）。
  2. 证明非转折面未重标静态真空移植违反 Shale–Stinespring 条件（$\|\beta^{\mathrm{naive}}\|_{\mathrm{HS}}=\infty$），而在转折面 $\tau=0$ 按 Weyl 共形重标初始化后，全体体场与时钟非零模在整个 $[-1,\pi+3]$ 上保持 $|\beta_k(\tau)|=O(k^{-2})$（绝热基 $O(k^{-3})$），在 $K=\infty$ 单一重标 Fock 空间上酉可实现且逐片保持正常 Hadamard 正则性（[HADAMARD_CAUCHY_TRANSPORT.md](HADAMARD_CAUCHY_TRANSPORT.md)）。
  3. 在该动态闭合 FRW 历史上完成连续统总源八投影逆包络 $\|(J_{\mathrm{total,FRW}}^{\rho_0,\infty})^{-1}\|<0.0057$（[CURVED_CONTINUUM_INVERSE.md](CURVED_CONTINUUM_INVERSE.md)）。

### 4. 四维局域自主指针、涂抹应力方差、联合两支 CTP 核与物理标定边界（`RC09`–`RC12`）
- **四维局域自主指针（`RC09`）**：引入无坐标/无程序依赖的共形指针场 $\Psi_{\mathrm{ptr}}$ 与对跖对称 $r_b/g$ 标度共形信标场 $B_{\mathrm{rec}}$（$\tilde\lambda_{\mathrm{ptr}}=10^{-28}$ 压低量子信标涨落至 $<2\times 10^{-25}$，对跖偶对称使全部奇 $\ell$ 信标矩恒零而不扰动 `RC08` 的 $\ell=1$ 平衡），通过严格相对论光锥帽包含 $\frac{31}{80}+\frac{1}{80}+2\rho_0=\frac{1}{2}$ 与正核窗口内的时钟门 $[5.90,5.92]\subset(\theta(\pi+\frac{5}{2}),\theta(\pi+3))$，证明保留全部分支的 $k=1$ 正交分量连续统自主指针概率差 $>4.5\times 10^{-23}$（[LOCAL_AUTONOMOUS_POINTER.md](LOCAL_AUTONOMOUS_POINTER.md)）。
- **时空涂抹连续统应力方差与联合 CTP 核（`RC10`–`RC11`）**：对比锐切片最小耦合时钟空间压力方差的精确 $\frac{2}{9}\sum_{k=2}^K k^2(k^2-1)\asymp \frac{2}{45}K^5$ 发散与时空涂抹总应力方差在 $K\le\infty$ 的一致有界性（[CONTINUUM_STRESS_VARIANCE.md](CONTINUUM_STRESS_VARIANCE.md)），并建立围绕动态反弹背景的标量 lapse、$k_V=3$ 非 Killing 矢量 shift 与 $k_T=3$ $(2,0)\oplus(0,2)$ 横无迹张量联合两支 CTP 二次核（含 $R^2+\mathrm{Weyl}^2$ 抵消项、经 $S^3$ 符号积分精确核验的三扇区严格正定 Keldysh 噪声与 $O(K^{-10})$ 截止 Bianchi 残差衰减，[COUPLED_CTP_TENSOR_KERNEL.md](COUPLED_CTP_TENSOR_KERNEL.md)）。
- **SI / Planck 标定与诚实开放门（`RC12`）**：恢复物理单位 $G_{\mathrm{model}}=(\ell_{\mathrm{Pl}}/R_{S^3})^2$ 后，$\frac{4\pi G_{\mathrm{model}}}{g^2}=\frac{3}{10}$ 在 $g=10^{-40}$ 对应宏观闭合三维球半径 $R_{S^3}\approx 1046.1\text{ km}$、传感器帽半径 $L_{\mathrm{sensor}}\approx 52.30\text{ km}$ 及致密天体量级闭合能量密度 $\rho_{X,\mathrm{SI}}\approx 1.32\times 10^{30}\text{ J m}^{-3}$，且二元读出样本下界 $N_{\mathrm{trials}}>8\times 10^{41}$ 明确表明当前正概率差属于模型内部数学可区分性而非桌面引力实验；点状 $\rho_0\to 0$ 极限、编码二次项与对跖信标的偶 $\ell\ge 2$ 高阶谐波、非微扰算符量子 Einstein 方程与从 `Core v3` 导出场内容仍保持 **OPEN**（[CALIBRATION_AND_OPEN_GATES.md](CALIBRATION_AND_OPEN_GATES.md)）。
