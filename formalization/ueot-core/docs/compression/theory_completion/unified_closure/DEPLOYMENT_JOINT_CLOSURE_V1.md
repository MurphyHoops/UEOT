# Deployment Joint Closure V1：UEOT 有限训练与部署风险的连续数学审计

**验证状态：四个最终模块的独立数学审读、模块构建、完整 UEOT 构建与两次一致的原生 Lean 验证均已通过。以下证据只认证这组冻结源码的本地结果；本轮外层发布和远端 CI 另有集成记录。**

本稿承接既有统计风险增量，解释两个数学任务及其最小组合。数学实现分为 `DeploymentCoverage`、`DeploymentCoverageWitness`、`TrainingDeploymentJoint`、`CalibratedDeploymentJoint`；最后一项直接连接注册实验、实际覆盖和联合概率，并包含旧实际采样实验的固定部署联合推论。本轮沿用既有研究范围与账本定义。

## 1. 源与本轮交付边界

此前五模块增量将实际源行采样连接到共同校准事件、经验参考过程与微观失效风险。本轮进一步解决两个有区别的问题：训练之后实际部署的联合概率，以及未采源行在部署过程中造成的覆盖代价。

此前增量的来源与验证保存在 [Statistical Risk Closure V1](STATISTICAL_RISK_CLOSURE_V1.md)。它的工程记录与定理计数只适用于该增量；以下四模块使用独立的本轮验证记录。

| 本轮源快照 | SHA256 | 已独立核对的内容 |
| --- | --- | --- |
| [DeploymentCoverage.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DeploymentCoverage.lean) | `5869824d0b059abcdf7e211d330cc944d0e5448275732bfad60f5728d1819585` | 实际部署行分布、有限路径加法界、覆盖拆分和受限行采样。 |
| [DeploymentCoverageWitness.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/DeploymentCoverageWitness.lean) | `19db0904c2d856c6efa3830555bb75572d670da607b97a8dcd6e4e120397288b` | 实际覆盖质量、两步风险与证书、未覆盖部署反例，以及真实一次采样的经验损失反例。 |
| [TrainingDeploymentJoint.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/TrainingDeploymentJoint.lean) | `7ebce1bcbc1b6a73810ce0138721daf80494e0717caee4dd46fe4002ef103b2b` | 联合 PMF、两个边缘、塔式与积分、数据依赖预算、同源统计适配和正反例。 |
| [CalibratedDeploymentJoint.lean](../../../../UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/CalibratedDeploymentJoint.lean) | `9b3345f5132f7f952e81cc2d37801269e3e22b0d130d455ebf22cc74fd83d941` | 同一注册实验、好事件、实际覆盖与公共微观事件的终端；旧固定部署联合风险保留 \(143/256\)。 |

理论范围依据为 Core 数学 §7.3、§16.1–16.9、§20.4–20.5、§31.2，及给定任务书 `03-CORE_V3_OPEN_PORT_MATRIX.md` 的 C2-02、C7-01–03、`04-CORE_V3_POST_CORE_SCIENTIFIC_CLOSURE.md` 的 §§1、2、6、9、`05-THEORY_COMPLETION_ROADMAP_V2.md` 的 §§1、2、7。任务书中的日期和旧进度属于规划与历史，不能代替当前提交状态。

### 1.1 已观察到的编译与原生证据

2026-10-20，Lean **4.33.1** 完成四模块的目标构建（**8,767 build jobs**）与完整 `lake build UEOT`（**9,356 build jobs**），两条实际命令均返回退出码零。五路径源清单同时固定四份模块和仅增加 import 的 `TheoryCompletion.lean`；构建后再次核对，源文件未变。这些 job 数包含依赖构建任务，不是新增定理数。

随后分别执行原生导出与固定验证器，两条 `lake env lean` 命令也实际返回零。两份完整 JSON 的对象和原始字节均相同，覆盖所有编译器定理的类型、存储的宇宙参数、模块归属、直接证明常量、直接定理常量与传递公理。四模块共 **93 个 native theorem constants**，其中 **54 个已确认公开源定理、12 个 private、27 个其他非 private 原生常量**。这 27 个名称不能未经检查就计为人工书写的公开声明。全部 93 个定理的传递公理仅包含 `propext`、`Classical.choice` 和 `Quot.sound`。[原生证据](../knowledge/reuse/DEPLOYMENT_JOINT_NATIVE_V1.json)与[固定验证器](../knowledge/reuse/VERIFY_DEPLOYMENT_JOINT_OVERLAY_TYPES.lean)记录这一范围。

已注册直接定理依赖共 **98 条**，包括组合终端对注册校准、覆盖微观风险与联合概率界的真实复用，以及固定策略见证对旧好事件存在性和旧风险界的复用。对 **3,938 个此前已注册公开源定理**进行了 **212,652** 次跨集合类型比较，新集合内部进行了 **1,431** 次比较；按照当前原始存储类型的 `Meta.isDefEq` 协议均无匹配。宇宙参数仍保留其存储名称，故该观察不等于穷尽数学等价或所有可实例化复用。此前已注册集合也不声称覆盖每一历史公开声明。[本轮复用证据层](../knowledge/reuse/DEPLOYMENT_JOINT_REUSE_OVERLAY_V1.json)保留具体统计与方法。

独立的源代码与编译类型审阅还检查了全部 **13 组词法提示 / 26 个候选**，并核实 **22 条核心原生复用路径与 6 条 private 见证路径**，结论为 `PASS_NO_BLOCKING_REUSE_OMISSION`。这项判断依赖实际输入、类型和证明常量，不以零类型匹配代替语义审阅。源绑定报告 `typed-reuse-review.json` 的 SHA256 为 `83fc4e149dc79f918d8bba7024de230af7bafe850a65da994e931923e1a502c7`；它要求提交后再核对不可变候选中的源字节、54 个声明及 13/26 提示集，未虚构提交号。

| 实际证据 | SHA256 |
| --- | --- |
| 五路径构建源清单 | `2919716f5ab97829ef51913c347a5308e7302d770e3daf8046635a8defe7268c` |
| 四模块完整构建日志 | `5d9cda522de479543ee6b381d1f2222a1c2f3d446a15ce1c03557df64a7e35d8` |
| 完整 UEOT 构建日志 | `87761016ce311a0b0b3ff0b26d16e32dbc0df0ea8163a806122770eb0cd23bcf` |
| 两次一致的完整原生 JSON | `04058c199ae439fbafb0a659ed78228b3c5e5ab2a4e2444efa6e60d1df588725` |
| 实际执行的固定验证器 | `48e310eb767413092a0e02fff53bc00b22c87808b4abc838be1ec2279c35b873` |
| 绑定上述观察的复用证据层 | `72fd346f3ab3adca4cb29de1f5c19cc6742555e3003fc32efa345eabbda850f2` |

这些本地结果确认了下文组合终端和 \(143/256\) 固定部署联合推论的编译状态。语义复用判断、不可变 Git 对象上的发布检查及远端 CI 有各自的证据范围，不能从原生计数或编译成功自动推出。这里不宣称本轮研究发布已经完成。

## 2. 同一个声明的生成实验

取有限微观状态集 \(X\)、观察状态集 \(Y\)、动作集 \(A\) 与有限时域 \(T\)。固定真实微观转移 PMF \(P_t(x,a)\)。训练空间 \(\Omega\) 在联合概率端点中有限，训练概率测度为 \(\mu\)，并具有可测单点。注册采样定理本身允许一般可测训练空间；把它接入当前联合构造时采用有限训练空间。

一个候选 \(c\) 指定观察映射 \(q_c:X\to Y\)、实际初态 PMF \(p_0^c\)、读取观察历史的策略 \(\pi_c\) 和归一化参考转移 PMF \(Q_c\)。所有候选使用同一个 \(P\)，且参考初态为 \(q_{c\#}p_0^c\)。选择器 \(s:\Omega\to C\) 可依赖训练数据；有限训练空间使其可测。候选空间本身无需有限。

真实部署路径 PMF 是

\[
D_T^c=\operatorname{causalLaw}
 \bigl(p_0^c,\operatorname{riskMicroControlKernel}(q_c,P,\pi_c),T\bigr).
\]

它与参考过程使用同一个观察历史策略，包括过去动作。微观路径投影可以依赖完整历史，当前结论不需要它在 \(Y\) 上成为状态马尔可夫过程。

共同微观失效事件 \(E\) 固定在 \(X\) 的历史空间。候选的观察包络 \(F_c\) 必须显式满足

\[
E\subseteq q_{c,\mathrm{hist}}^{-1}(F_c).
\]

选择候选可以改变观察包络，但不会改变这个终端中的微观失效定义。若选择的初态有误差，必须另外建立相应初态适配；本端点指定的实际初态与参考投影初态是精确的。

## 3. 任务一：把训练置信接到真实联合概率

构造联合 PMF：先从 \(\mu\) 抽取训练结果 \(\omega\)，再从 \(D_T^{s(\omega)}\) 抽取部署历史，保留两个坐标。实现使用 \(\mu.\mathrm{toPMF}\) 和既有 `pmfExtend`。`Measure.toPMF_toMeasure` 证明转换后训练测度仍是原来的 \(\mu\)。

质量公式、训练边缘、部署边缘以及塔式公式均由构造推导：

\[
\mathcal J(\omega,h)=\mu(\{\omega\})D_T^{s(\omega)}(h),
\qquad
\mathcal J(\Omega\times E)=
\sum_\omega\mu(\{\omega\})D_T^{s(\omega)}(E).
\]

若同一个训练好事件 \(G\) 上有 \(D_T^{s(\omega)}(E)\le b(\omega)\)，则

\[
\mathcal J(\Omega\times E)
\le\mu(G^c)+\sum_{\omega\in G}\mu(\{\omega\})b(\omega).
\]

如果还有 \(b(\omega)\le\beta\in[0,1]\)、\(\mu(G^c)\le\alpha\)，则

\[
\boxed{\quad
\mathcal J(\Omega\times E)
\le\min\{1,\alpha+(1-\alpha)\beta\}.
\quad}
\]

这里训练与部署可以因选择器而相关；并未额外假设它们独立。若并界给出的 \(\alpha>1\)，结果会被截为平凡上界一，不产生负置信或更强保证。

实际声明包括 `selectedTrainingDeployment_failure_tower`、`selectedTrainingDeployment_failure_integral`、`selectedTrainingDeployment_data_dependent_bound`、`selectedTrainingDeployment_failure_le`。全源行版本 `statistical_selected_empirical_deployment_risk` 已直接消费此前 `statistical_empirical_reference_certificate`，不把所求风险界装入输入记录。

**生成实验的适用边界：** 联合构造指定了训练之后如何产生未来路径，因此其条件部署律来自构造。训练样本的实际边缘律条件 `hlaw` 本身不能识别任意外部部署过程的条件律。现实应用仍需证据说明部署确实服从声明的源过程与控制方式。

## 4. 任务二：只在注册行采样，并付出真实部署覆盖代价

### 4.1 样本域真正缩小

固定注册行集合

\[
J=\{(t,a,x):t<T,\ \mathrm{certified}(t,x,a)\}.
\]

Lean 样本类型是 `CoverageRegisteredRow certified T → Fin N → Ω → X`，其中注册行是有限完整行索引的子类型。未注册行没有样本字段、样本边缘律或独立性前提。

每一注册行的 \(N>0\) 个样本可测、行内独立，且分别服从该行的实际 \(P_t(x,a)\)。不要求不同行实验独立。对固定的全部微观事件指示测试，既有 `measure_finite_row_calibration_bad_le` 给出一次置信预算

\[
\alpha_{\mathrm{reg}}
=\sum_{j\in J}2\,2^{|X|}\exp(-2N\rho_{t(j)}^2),
\]

以及可测 \(G\)，使 \(\mu(G^c)\le\alpha_{\mathrm{reg}}\)，并且在 \(G\) 上每一注册行满足

\[
\operatorname{TV}(P_j,\widehat P_j(\omega))\le\rho_{t(j)}.
\]

`coverage_registered_row_calibration` 与 `coverage_registered_source_calibration` 直接复用既有采样集中、经验 PMF、事件期望和有限事件 TV 引理。这里未重证 Hoeffding，也未要求给不可观察行伪造完整数据表。全事件库的 \(2^{|X|}\) 代价仍显式保留，当前结果没有解决大型状态空间的统计复杂度。

### 4.2 数据后经验拟合只检查注册行

在同一个 \(G\) 上，若所选参考 PMF 与每一注册经验行满足

\[
\operatorname{TV}\bigl(q_{s(\omega)\#}\widehat P_j(\omega),
Q_{s(\omega),t(j)}(q_{s(\omega)}x_j,a_j)\bigr)
\le\eta_{\omega,t(j)},
\]

则数据处理与三角不等式给出注册行的真实粗误差

\[
e_{\omega,t}(x,a)
:=\operatorname{TV}\bigl(q_{s(\omega)\#}P_t(x,a),
Q_{s(\omega),t}(q_{s(\omega)}x,a)\bigr)
\le\epsilon_{\omega,t}:=\min\{1,\rho_t+\eta_{\omega,t}\}.
\]

这一路线只需要一次统计误差，因为比较终点是实际给出的参考 PMF，经验拟合已经连接到它。正常误差半径解释取非负 \(\rho,\eta\)，因此 \(\epsilon\in[0,1]\)。较底层的线性拆分只依赖实际点态上界，允许更一般实参数。

### 4.3 覆盖概率来自实际部署

以所选真实微观前缀 \(D_t^c\) 和同一策略构造

\[
\nu_t^c=(\operatorname{lastState},\mathrm{id})_\#
\operatorname{pmfExtend}\bigl(D_t^c,
 h\mapsto\pi_{c,t}(q_{c,\mathrm{hist}}h)\bigr).
\]

`coverageDeploymentRowLaw` 实现这个 PMF，`coverage_rowLaw_expectation` 推导其有限求和公式。它不是训练行分配，也不是参考过程的占据概率。

路径误差的单步证明先比较真实前缀下的两个扩展，再以同一参考核推进已有前缀误差。保留动作坐标使条件动作 TV 成为精确加权和。递推结果是

\[
\operatorname{TV}(q_{c,\mathrm{hist}\#}D_T^c,Q_T^{\pi_c})
\le\sum_{t<T}\mathbb E_{\nu_t^c}e_{c,t}.
\]

注册行误差不超过 \(\epsilon_t\)，其余 PMF 行误差不超过一，因此

\[
\mathbb E_{\nu_t^c}e_{c,t}
\le\epsilon_t\nu_t^c(C_t)+\nu_t^c(C_t^c)
=\epsilon_t+(1-\epsilon_t)\nu_t^c(C_t^c).
\]

令这些项的和为 \(B_{\mathrm{cov}}(c)\)，原有微观包络与 TV 事件运输得出

\[
D_T^c(E)\le\min\{1,Q_T^{\pi_c}(F_c)+B_{\mathrm{cov}}(c)\}.
\]

实际端点是 `coverage_same_policy_microscopic_failure_risk`，接入注册行经验校准后是 `coverage_empirical_registered_microscopic_failure_risk`。这是有限历史的加法预算；现有逐行统一误差下的更锐乘积界仍保留自己的前提。

## 5. 注册样本、实际覆盖和联合概率的统一终端

组合声明名为 `coverage_statistical_selected_joint_failure_risk`。其证明明确执行三次复用：

1. 从注册行实际源实验取得同一个 \(G\)、\(\alpha_{\mathrm{reg}}\) 和所有注册行校准。
2. 对每个 \(\omega\in G\)，把已选 \(q,Q,p_0,\pi\)、经验拟合、公共 \(E\) 的包络交给微观覆盖端点，得到真实条件风险上界 \(b(\omega)\)。
3. 用实际联合 PMF 的好坏事件拆分，得到公共微观失效事件的无条件联合界。

`hchecked` 显式要求总选择器在每个训练结果上满足

\[
b(\omega)=\min\left\{1,
Q_T^{\pi_{s(\omega)}}(F_{s(\omega)})+
\sum_{t<T}\left[\epsilon_{\omega,t}+
(1-\epsilon_{\omega,t})\nu_t^{s(\omega)}(C_t^c)\right]\right\}
\le\beta.
\]

因此整个有限生成实验的结论为

\[
\boxed{\quad
\mathcal J(\Omega\times E)
\le\min\{1,\alpha_{\mathrm{reg}}+
(1-\alpha_{\mathrm{reg}})\beta\}.
\quad}
\]

这里没有叠加两份相同校准事件的 \(\alpha\)。`hchecked` 含有实际部署覆盖项；受限样本不会自动给出它。该输入也是存在性的真实边界：当前定理证明通过这些检查的选择器具有相应风险保证，没有证明总能找到可行选择器。

## 6. 同一有限 PMF 构造中的正反例

| 问题 | 真实构造及精确结果 | 解释范围 |
| --- | --- | --- |
| 联合好坏事件界可否达到？ | 坏训练质量 \(1/4\)，好部署风险 \(1/2\)，坏部署风险一；两候选有正选择质量，真实联合风险 \(5/8\)。 | 精确达到 \(\alpha+(1-\alpha)\beta\)，不是常量策略的重复平均。 |
| 旧真实源实验能否接入联合律？ | 原好事件非空，旧固定部署风险 \(143/256\) 与训练结果无关；新联合律仍不超过 \(143/256<1\)。 | 直接复用实际训练概率测度和旧真实路径 PMF；是固定部署接口实例，不是策略发现结果。 |
| 允许未注册部署仍能得到有用界吗？ | 同一 Bool 源的注册动作失败率 \(1/8\)，未注册动作失败率一；策略每步以 \(1/4\) 选未注册动作。 | 两步实际 ever-failure 为 \(583/1024\)，通用覆盖定理给 \(11/16<1\)。 |
| 训练真误差均值能否替代部署覆盖？ | 同一源和参考，训练行集中于注册动作，真 TV 均值 \(1/8\)；部署始终选未注册动作。 | 实际一步风险一，参考风险零，所提替换界为假。 |
| 零经验损失能否单独认证未覆盖部署？ | 从上述注册源行真实抽一次样本，经验点质量与参考的 TV 为零的概率 \(7/8\)。 | 同一未覆盖部署风险仍为一；\(7/8\) 与真行误差 \(1/8\) 是不同量。 |
| 可否换成另一条件部署律？ | 相同训练与选择，一族实际 joint 永不失败，替换后的另一族实际 joint 必然失败。 | 样本或名义证书不能认证未匹配的外部部署律。 |

覆盖正例允许后续恢复，事件采用 `riskEverFailure`，因此不是只计算最终状态为坏的概率。其两步存活概率是 \(((3/4)(7/8))^2=(21/32)^2\)，故失效为 \(583/1024\)。初态为安全点质量；一般定理仍把初态失效保留在事件中。

上述数字来自有限 PMF 源构造。它们不是外部真实系统的测得失败率。当前负例也没有断言已观察行的真实转移分布与参考完全相同，其真 TV 明确为 \(1/8\)。

旧实际实验的 `statistical_fixed_policy_training_deployment_witness` 使用 `good_sample_exists` 和 `microscopic_two_step_risk_on_good`：任意一份好记录就为同一个固定路径律给出 \(143/256\)；再对联合好事件取全集、\(\alpha=0\)，无需增加训练失败成本。机械套用原 \(\alpha=1/4\) 会得到较松的 \(685/1024\)，本轮已改用更强结论。一般数据依赖部署不能作此消去，非恒定 \(5/8\) 例说明了区别。

## 7. 本轮减少了哪些前提，哪些问题仍存在

| 接口 | 本轮实际推进 | 仍须给出的信息 |
| --- | --- | --- |
| 训练与未来路径的关系 | PMF 构造、边缘与塔式已在真实源代码中给出。 | 现实部署是否服从这个生成实验。 |
| 全源行访问 | 样本类型已经缩为固定注册子类型，未观察行没有假样本。 | 注册行能否按声明规律采样；相关/自适应数据的另行预算。 |
| 覆盖对路径风险的影响 | 实际源占据权重、加法路径 TV 与微观风险已连接。 | 未观察部署质量的可计算上界或独立证据。 |
| 训练后选择 | 同一校准事件下，实际所选模型与策略进入联合风险。 | 可行候选的构造或发现算法，以及参考风险的计算。 |
| 哲学叙述 | 预测不足、行动分布与有限失效在一个明确过程中约束彼此。 | 独立目的机制、Π/Φ 计量锚、长期存在、物理实现与现实检验。 |

本轮复用并落实 Core §16.9 已指出的覆盖问题。既有 P-STAT-09 的密度比/TV 运输和 P-QUO-04/05 的折扣占据结论不被重新计为新成果；新增的是有限实际因果历史的覆盖推导、受限注册实验和实际联合终端。路径证明复用既有有限因果路径与 PMF overlap 引理，并未把平均行误差当作 P-DYN-03 统一逐行端点的输入。

三个不同概率对象应始终保留其类型：训练实验为 \(\mu\) 在 \(\Omega\) 上的测度；如果另行给出训练行分配 \(\lambda\)，它才是在 \(X\times A\) 上对各行加权的测度；实际部署 \(\nu_t\) 是由真实路径与策略导出的 \(X\times A\) 上的 PMF。注册行的响应校准不提供 \(\nu_t\ll\lambda\)、密度比上界或 \(\operatorname{TV}(\nu_t,\lambda)\) 上界，因此不能自动解除 P-STAT-09 的运输前提。

最直接的后继任务是在明确的可观察策略限制下，推导可用的 \(\widehat u_t\ge\nu_t(C_t^c)\)，并将它代入现有覆盖与联合端点。一份具体可检验的合同是：给出观察状态和动作上的许可关系 \(\Gamma_t(y,a)\)，证明它对整个观察纤维保证注册性，即 \(q(x)=y\) 且 \(\Gamma_t(y,a)\) 蕴含 \(C_t(x,a)\)；再由每份观察历史上对不许可动作概率的策略上界，推导实际未覆盖质量的上界。若隐藏状态使同一观察纤维内的注册性不同，应给出保守许可关系或不可识别反例。这个后继合同尚未作为本轮四模块的已证结果。

全局 `scientific_closure = NOT_ESTABLISHED`、冻结 106/4 及 11/89/6 的原有意义均不因本轮结果改变。连续哲学修订见 [UEOT Core Philosophy V2](UEOT_CORE_PHILOSOPHY_REVISED_V2.md)，原句和页码的反馈对照见 [Philosophy–Mathematics Feedback V2](PHILOSOPHY_MATHEMATICS_FEEDBACK_V2.md)。
