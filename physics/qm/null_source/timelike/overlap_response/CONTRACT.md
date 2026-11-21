# 重叠响应增量的物理与证据合同

主审日期：2026-11-20（Asia/Shanghai）。直接基线 c57e2f411e58dc1dae60de8f3c97fbd680e46d8b。接续[上一轮操作合同](../operational_response/CONTRACT.md)，全部旧科学输入按字节冻结。

## 1. 物理模型沿用，不重开已固定参数

真实目标仍是同一有限源、同一最小耦合无质量实自由场、同一光滑制备、同一共同过去态和物理单位。4πG=1、ħ=1，
\[
a_\lambda(\eta)=\lambda\sqrt{3\cos2\eta},\quad
\lambda=32768,\quad0\le\eta\le3/16.
\]
已声明的几何是平均方程有受控缺陷的研究背景，不在本轮改称精确非线性半经典解。

[兼容合同](../compatibility/CONTRACT.md)已固定物理 μ=1、源侧 α=0；[动态 RSET](../evolution/stress/README.md)及[参考量子态](../continuation/quantum/README.md)明确采用 AE、无额外有限曲率项和既定 Newton 归一。三者均绑定基线 SHA256，不重新选择。

本稿采用 −+++ 和 Ric_gamma=2gamma。与 AE 的 +---、相反 Riemann 约定转换后 H1_AE=−HR，故
\[
\boxed{z=1,\quad b_{\rm extra}=-\alpha=0,\quad c_{\rm extra}=0}.
\]
c_extra=0 表示本轮相对于固定参考处方不增加独立 Weyl² 反项，不表示参考处方的全部四阶局域接触项为零。FLRW 均值上的 HC=0 不能把已固定处方改写成未知自由耦合。

若原实现只给出 RW 公式，需构造或核对与该冻结处方一致的非齐性实现；不能新增物理 c 代替缺少的计算。已有完整协变定义若已指定这一延拓，应直接继承。

## 2. 度规、应力与实际反馈方程

输入是无量纲空间 TT 相对应变 h：
\[
g_\epsilon=a_\lambda^2[-d\eta^2+(\gamma+\epsilon h)_{ij}dx^idx^j],
\quad D^ih_{ij}=0,\quad\gamma^{ij}h_{ij}=0.
\]
物理协变扰动是 delta g_ij=a_lambda²h_ij；不能混用两者。

定义参考响应
\[
\Pi_{\rm ref}^{TT}[h]^i{}_j
=\delta\langle T^i{}_j\rangle_{\rm ref}^{TT},\qquad
\mathcal R_{\rm eff,cov}=a_\lambda^2\gamma_{ik}\Pi_{\rm ref}^{TT\,k}{}_j.
\]
升指标所需的背景压力接触项已经计入。raw covariant delta Tij 与 R_eff,cov 不同。

外加 mixed TT 应力 F 对应 f=4a_lambda²F，实际方程为
\[
\boxed{(D_T-4a_\lambda^2\Pi_{\rm ref}^{TT})h=f},\quad
D_T=\partial_\eta^2+2(a_\lambda'/a_\lambda)\partial_\eta-\Delta_\gamma+2.
\]
本轮尚未反演这一完整物理算子。

## 3. 四个对象的区别

| 对象 | 已固定输入 | 本轮结果 | 不可据此升级的主张 |
|---|---|---|---|
| 原物理参考响应 | μ=1、α=0、z=1、无额外有限项、原 prepared 态 | 保留准确的非齐性响应责任，齐性调源的有效 TT 一阶响应差为零 | 尚非完整 Pi_ref 或非线性 SCE |
| 显式局部参数族 L_z,b,c | 任意有限 z,b 与非零 c；同一给定几何 | 完整 R²/C² 算子、全模式因果逆、明确尾界 | 非零额外 c 的结果不适用于 c_extra=0 工作点；未收齐参考接触项 |
| 标量对数 normal form | c实、κ>0、μ>0，平直/冻结纯时间主符号 | 正的局部可积因果逆与质量界，保留增长极点 | 不等于 actual closed-FLRW 逆，不证明稳定 |
| 同背景 Hadamard 态差 S | 两态各自过去数据固定，S 光滑，标量 contact 要求空间核 SO(4) 不变 | 精确 Duhamel、contact 和 MS/M8 条件 Volterra 界 | MS/M8 的 actual prepared-reference 数值尚未认证，共同 UV 主部未被消去 |

局域参数族
\[
L_{z,b,c}=(z-4bR)D_T-4bR'\partial_\eta+(4c/a_\lambda^2)W
\]
只用于明确的结构定理或后续真实导出块的接口。其四阶零过去合同 h=h'=h''=h'''=0 仅适用于 c≠0 的辅助问题，不为原固定工作点擅自增加两项初始数据。c=0,q=z−4bR≠0 的已知几何子问题为二阶，仍不删除 Pi_ref。

## 4. 时间、空间与范数合同

局域参数族在 I0=[0,3/16] 上作全模式 C(I0;H^s_TT(S3)) 分析。全场解为 mild，模式解经典四阶，完整场方程按分布成立；不声称四阶时间导数仍在同一 H^s。

Hadamard 态差界在 I1=[1/16,3/16] 上取 T=1/8，输入 h 在 I1 之前为零，两态分别保持自己的共同过去数据。若已有更早输入，应从其真实最早支撑开始积分，重新取时间长度和背景常数，不能遗漏过去 forcing。

X 为光滑 TT 测试张量的空间 sup 范数完备化，点态范数取 Hilbert–Schmidt；输出 X* 用积分配对定义，不把 X* 的界未经证明改称 H^s 同空间界。
\[
M_S=\sup_{s,t\in I1}\|JS(s,t)J\|_1,\quad
M_8=\sup_{s,t\in I1}\|J^2S(s,t)J^2\|_{HS},\quad J=1-\Delta_\gamma.
\]
SO(4) 不变保证局域 contact 系数在空间上为常数。精确零响应特例额外要求 S 对 x、y 分别空间常数（纯空间零模差），不是任意 SO(4) 不变态差。

M8 包含同背景精确平滑态差的全部导数；有限阶 WKB 近似和旧分离窗噪声界不是它的替代。

辅助闭三球用于继承的 Cauchy 表示及谱估计。应用回物理有限球时，输入、输出及相关因果域须保持在原共同内域。全局齐性公式不取消外区态与匹配责任，也不改变物理拓扑。

k≥0 的平直 Fourier normal form、l≥2 的三球 TT 谱及 k≥1 的标量 J 谱分别定义，不互相替换。normal-form μ 的数值与物理 μ=1 在共形时间缩放后需配套局域位移。

## 5. 核验、归档与主张

三个工作包各含 check.py、README.md、result.json；[主审](review.py)独立从四维 Hopf 度规计算 Christoffel、曲率、Weyl 双散度和一般 a 的 R² mixed 变分，并交叉核对原处方、核的初值及量子系数。

[总执行器](run_verification.py)复用34项已有结果、逐字节冻结140个旧科学文件，只运行本轮4个入口。基线 CI 的准确 head、通过步骤和实际日志证据存于[baseline_ci.json](baseline_ci.json)。本地 verification 保留真实执行时 HEAD 和脏工作区，不把预提交执行伪装成新提交已测；远端 CI 再绑定推送后的准确 SHA。

新增模式积分0、几何 ODE0、旧科学入口重跑0。Core 只读，GI 排除；正式书稿、Lean、经验状态不升级。证明文档中的连续函数空间定理不是 Lean 定理；符号检查与有向区间检查支持所列恒等式和常数，但不声称计算机已形式化全部分析证明。

完整 Pi_ref、实际余项范数、完整反馈逆和稳定性、量子噪声到几何、非线性 SCE、外区态、准备/驱动/测量总应力、真实器件及匹配数据仍开放。
