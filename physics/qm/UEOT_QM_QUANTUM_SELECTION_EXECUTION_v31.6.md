# UEOT→QM 下一轮唯一首要任务：同源经典操作模型的纯化分离证书

**状态：下一轮执行合同／待形式化，非本轮新增证明。** 采用基线为 v31.5 源提交 57283f4efdac02584a36713ae419dc9d439b1686；其合入主线为 be90695c53d337574470b454e3f74479ee934e38。 本说明依据 v31.5 工作树中的正式总著第 0–3 章、第 47 章、ROADMAP 的 QMU-10／A1，以及下列实际 Core 源码制定。本合同制定阶段只做源码阅读和逻辑审查；下述新名称、定义和定理均为下一轮提案，尚未实现或编译，不能计入 v31.5 的定理数或 PASS。

## 1. 决策与所能得到的科学进展

将宽泛的 A1 收紧为一个可交付任务：**使用现有有限受控随机核，构造一个明确观察两个状态位的 Core 模型；证明它通过实际终端稳定商、精确控制与非空安全路径接口，同时其同一核产生的实际商态在完整有限经典状态空间中没有纯化。**

任务代号暂用 `QSEL-A1-CLASSICAL`。它把总著已有的经典反模型论证落实到实际 frozen Core 源码，而不是再增加一条预先输入复 Hilbert／Density／Kraus 后成立的量子内部定理。它优先解决“已核对的 Core 接口是否足以排除经典理论”这一具体障碍；成功后才有依据挑选能排除该反例的独立领域原则。

准确的预期结论是：**本文列出的有限受控 Core 接口组，与一个明确声明的有限经典操作解释相容；该解释中，一个来自同一源核、在实际终端商上仍为混合的可达态违反纯化存在性。** 这只否定该接口组足以推出普遍纯化的主张。它不是全部 106 条及其全部物理解释的模型，不是“整个 UEOT 不可能重构 QM”的机器定理，也不证明自然界最终选择经典理论。总著的 P-QBR-01、P-QSEL-01 不能因此整项升级为完成了所有背景前提的 Lean 证明。[S1–S3]

## 2. 一个必须先修正的反例：微观混合会被实际商压成纯态

现有源核为：

\[
X=\mathrm{Bool}\times\mathrm{Bool},\quad A=\mathrm{Bool},\qquad
K(x,a,z)=\begin{cases}\tfrac12,&z_1=a,\\0,&z_1\ne a.\end{cases}
\]

对应实际定义 `survivalMicroKernel`；它有非负性与归一化证明。取 \(x_0=(\mathrm{true},\mathrm{false})\)、\(x_1=(\mathrm{true},\mathrm{true})\)，动作 `true` 的实际一行是

\[
p_*=K(x_0,\mathrm{true},\cdot)
=\tfrac12\delta_{x_0}+\tfrac12\delta_{x_1}.
\]

但现有 `registeredSurvivalModel` 只注册第一位，`registered_survival_two_hidden_states_merge` 明确证明这两个支持点在真实终端商上合并。因此该模型的商态是一个 Dirac 态；不能一面使用其 4→2 商作为操作对象，一面把未取商的第二位混合当作操作混态。现有 `registered_survival_nonempty_infinite_law` 只给出存在一个安全策略，也不能直接冒充显式常真策略的首时刻分布证书。[S4–S6]

**主反例改为以下待实现实例**，保留完全同一 `survivalMicroKernel`：

```lean
-- 接口草图，尚未实现或编译。
fullyObservedSurvivalModel :=
  modelWithRegisteredOrganization survivalMicroKernel
    (fun x => x)            -- 显式注册两位读出
    (fun x => x.1)
    (fun _ => ())
    (fun _ => ())
    (fun x => x.1)
    (fun _ _ => 0)
```

其输出类型为 `X × Bool × Unit × Unit × Bool`。由已有 `registered_organizational_attributes_preserved` 的第一项，任何终端等价的两点必须有同一完整读出，故下一轮应证明

\[
(\mathrm{terminalSetoid}\ M_*).r(x,y)\iff x=y.
\]

实际终端商因此保留四个单点类。**这个主反例不再有严格 4→2 压缩**，但仍使用同一算法及其稳定商接口。现有 `hiddenProgramProtectedModel`／`protected_hidden_program_prevents_merge` 可作“不合并”的代码对照；它保护 program 标签的事实不自动证明该标签是可实施测量，所以不选它作为主反例的观测依据。[S5、S7]

令 \(S=\mathrm{terminalSetoid}(M_*)\)，\(q=\mathrm{setoidRepresentation}(S)\)，\(Y=\mathrm{ReachableState}(q)\)。必须使用实际构造出的控制商映射 \(f=Q.f:X\to Y\)，定义 \(\bar p=f_*p_*\)，并证明

\[
f(x_0)\ne f(x_1),\qquad
\bar p=\tfrac12\delta_{f(x_0)}+\tfrac12\delta_{f(x_1)}.
\]

最终纯化反例应以 **实际商上的 \(\bar p\)** 为对象，而不只停在微观分布 \(p_*\)。

## 3. 明确列出所检验的 Core 前提与额外操作解释

### 3.1 唯一的有限 Core 接口组 `H_fin`

下一轮若引入 `CoreInterfaceSlice` 之类的打包命题，其内容仅能是下表；每项由实际对象及已有定理实例化，不能把所需结论直接当作结构字段输入。

| 项 | 确切对象与责任 | 已有来源／新任务 |
|---|---|---|
| H1 有限正规化受控过程 | `X=Bool×Bool`、`A=Bool`、`K=survivalMicroKernel`；对每个源态和动作，真实转移行非负且和为 1 | 现有 `FiniteControlledStochasticKernel` 及具体 K；不新造第二张转移表 [S4、S11] |
| H2 注册当前接口 | `M_*` 的 transition 定义为 `K.mass`，完整观察 `id`，安全位第一位，奖励恒 0 | 现有 `modelWithRegisteredOrganization`；新实例 [S7] |
| H3 实际终端商 | 使用 `terminalSetoid M_*` 及实际注册输出下降／稳定性接口；新证终端等价 iff 源态相等 | 复用冻结算法与注册保持定理，不能用手写 identity 商替代算法结果 [S5、S7] |
| H4 实际精确控制 | `Q := organizationalTerminalControl M_* 0 (1/2) ...`；真实 micro 转移和奖励等于源，Bellman 最优值经 `Q.f` 运输 | `unified_finite_core_control_and_viability`；零奖励上界及折扣条件具体消解 [S7] |
| H5 非空安全内核 | `Safe x := x.1 = true`；`x0` 在每个有限时域的实际 viability 集内，`PMF.pure x0` 满足相应支持前提 | 现有注册模型的证明是参考；必须对 `M_*`／`Q` 重新实例化，不能直接改名借用 [S6、S8] |
| H6 同一源的真实路径 | `P x a := Q.micro.transitionPMF x a`；构造 `piStar := fun _ => true`，证明其真实无限路径所有离散时刻安全，且第 1 时刻的商边际为 `barP` | 用实际 PMF／轨迹接口，明确源等式；一般存在策略定理不足以指定这条策略 [S8–S10] |

恒零奖励仍是合法的精确控制实例，但最优值运输在该奖励上不承载非平凡偏好选择。动作 `false` 把第一位置为 `false`，提供非空安全与失败动作之间的真实区分；全时刻安全只表示注册谓词的概率一保持，不等于物质修复、自然界持续、谱系、自生产或内生目的。[S4、S6–S8]

### 3.2 明确声明的经典操作解释 `D_cl`，不冒称由 Core 推出

| 解释 | 具体内容 | 责任分类 |
|---|---|---|
| 状态 | 任一所用有限载体 \(Z\) 的**完整**概率单纯形：所有非负、总质量 1 的实函数；包含各 Dirac 制备及其凸组合 | B：选定的有限经典模型解释 |
| 效应 | 所有 \(e:Z\to[0,1]\)，配对 \(\sum_z p(z)e(z)\)；在主模型上由显式完整读出实现形式上的区分 | B：允许的响应／制备接口；不是自然界可实施性的实验证明 |
| 动力学 | 源核真实地作用为 \((K_a p)(z)=\sum_xp(x)K(x,a,z)\)，并与 Core 的 PMF 行对应 | B→C 接口等式，必须证明 |
| 复合与丢弃 | 辅助载体 B 为任意有限类型；联合状态为 \(\Delta(Z\times B)\)，丢弃为通常求和边际 | B：完整经典乘积规则；Core 当前接口没有选择此规则，也没有排除它 |
| 纯性 | **整个允许状态空间**的凸极点 | 数学定义；不能改成固定初态／固定策略的可达集合之极点 |

`D_cl` 是构造反模型时公开给定的解释。不得在它的定义中藏入“无纯化”，也不得将“parent／record 存在”直接定义为“存在一个纯联合态”。经典态总能有普通联合扩展；缺失的是纯扩展。

首轮交付是这个具体解释下的同源分离证书。如果另加 Lean 命题 `¬ ∀ I, H_fin I → UniversalPurification I`，必须先给出 `I` 的候选解释类型、组合规则及量化范围。一个固定实例的 theorem 名称不能替代整个 UEOT／所有 OPT 的元理论形式化。

## 4. 可直接实施的类型、定义和待证陈述

### 4.1 共享标量接口先冻结

建议复用现有 `UEOTQM.Mixture.Weights Z` 作为 `ClassicalState Z`：它只有 `weight : Z → ℝ`、逐项非负及 `sum_one` 三项，没有 Density、Hilbert、Kraus、Born 前提。它所在模块确实导入量子模块，因此必须分别记录导入闭包与新定理实际引用；“导入了某模块”不等于“该模块中的量子结构成为定理假设”。本轮不为改名而重构冻结源码。[S12]

需增加的定义及最小等式如下；这是类型合同，尚未编译。

| 名称 | 类型／数学内容 |
|---|---|
| `dirac x` | `ClassicalState Z`，权重为点质量 |
| `mix t ht0 ht1 p q` | `ClassicalState Z`，权重 \(tp+(1-t)q\)，构造时证明非负与归一 |
| `pushforward f p` | `ClassicalState W`，权重 \(\sum_{z:f(z)=w}p(z)\) |
| `marginalLeft omega` | `ClassicalState Z`，权重 \(\sum_b\omega(z,b)\)，应与相应 `pushforward` 一致 |
| `rowState K x a` | `ClassicalState X`，直接使用 `K.mass x a`、`K.nonneg x a`、`K.normalized x a` |
| `stepState K p a` | 真实有限和核作用；证明 `stepState K (dirac x) a = rowState K x a` |
| `toPMF p` | 调用现有 `FiniteProbabilityRow.ofRealRow p.weight p.nonneg p.sum_one`，不重新开发概率测度 [S10] |
| `IsPure p` | 对所有 `q r : ClassicalState Z` 及 `0<t<1`，逐坐标 \(p=tq+(1-t)r\) 蕴涵 `q=p ∧ r=p` |

不能直接定义 `IsPure p := ∃ x, p = dirac x`，然后把“经典纯态都是 Dirac”当成推导成果；该等价可以在极点定义之后作为标准数学定理证明，但不是本轮必须扩大到的分类目标。

### 4.2 必须完成的一个分离证书

先证明通用有限经典引理：任意有限 Z、不同点 \(z_0\ne z_1\)，令 \(p=\frac12\delta_{z_0}+\frac12\delta_{z_1}\)。对任意有限辅助载体 B，

\[
\neg\exists\omega\in\Delta(Z\times B),\quad
\mathrm{IsPure}(\omega)\;\land\;\mathrm{marginalLeft}(\omega)=p.
\tag{N-CL}
\]

Lean 接口应对任意 `B : Type u`、`[Fintype B]` 量化，不固定一个辅助维数；不需要 `[Nonempty B]` 才能证明否定结论。禁止只在一个预选辅助空间中找不到解便宣称 ESP 失败。

随后令 Z 为实际 `Y = ReachableState q`，实例化 `N-CL` 到 `f x0`、`f x1` 和 `barP := pushforward Q.f (rowState survivalMicroKernel x0 true)`。最终报告同一个明确模型上的联合结论：

\[
H_{\rm fin}(M_*,K,Q)\quad\land\quad
\mathrm{ActualFirstMarginal}(K,Q,\pi_*,\delta_{x_0},\bar p)
\quad\land\quad
\forall B\text{ finite},\;\neg\exists\omega\in\Delta(Y\times B),
\;\mathrm{IsPure}(\omega)\land\omega_Y=\bar p.
\]

其中 `ActualFirstMarginal` 必须是实际测度等式，不是构造器输入。例如采用双方的离散可测结构，证明

\[
\bigl(\mathrm{stationaryTrajMeasure}\ P\ \pi_*\ (\mathrm{PMF.pure}\ x_0)\bigr)
 .\mathrm{map}\bigl(\omega\mapsto Q.f(\omega(1))\bigr)
=\bigl(\mathrm{toPMF}\ \bar p\bigr).\mathrm{toMeasure}.
\]

`Model.transitionPMF_apply_toReal`、`stationaryTrajMeasure_coordinate` 提供现有源核到真实坐标边际的接口；`all_times_safe_of_coordinate_one` 提供逐时安全到所有时刻安全的实际测度结论。应使用它们而非新写一个仅具有目标字段的“路径证书”。[S9–S10]

### 4.3 `N-CL` 的最短严格证明路线

设联合态 \(\omega\) 的左边际为上述二点混合。非负性及边际为零推出其他左行全为零。定义

\[
\omega_i(z,b)=2\,\mathbf 1_{z=z_i}\omega(z,b),\qquad i=0,1.
\]

两态的归一化分别来自边际质量 \(1/2\)，且
\(\omega=\frac12\omega_0+\frac12\omega_1\)。两者的左边际分别为 \(\delta_{z_0}\)、\(\delta_{z_1}\)，故均不等于 \(\omega\)。这违反极点定义。整个论证针对任意有限 B，已经否定纯化的存在部分，因此不需要先形式化“纯化的可逆唯一性”。

## 5. 必需的正例、删除见证与实量子责任

| 检查 | 必须得到的结论 | 防止的误判 |
|---|---|---|
| 保留完整读出 | 实际终端商的两支持点不同，`barP` 仍为二点混合 | 微观混合与操作混合混淆 |
| 删除第二位读出 | 回到已有 `registeredSurvivalModel`；其实际商推送的 `pStar` 等于 Dirac | 必須接受该特定反例在此商上失效；这不证明该受限理论普遍可纯化 |
| 删除 `IsPure` | 对给定 `b : B`，`p ⊗ dirac b` 是合法普通扩展 | 边际存在与纯化存在混淆 |
| 删除非平凡混合 | `dirac z` 有纯联合扩展 `dirac (z,b)`，并由极点定义证其纯 | 归一态／所有扩展都被错误排除 |
| 失败动作 | 同一 K 的动作 `false` 从安全源产生不安全第一位 | 将全时刻安全做成与动作无关的空泛结论 |
| 整体状态空间 | 两个 Dirac 制备及凸组合都在允许态空间，极点定义对整个单纯形量化 | 固定可达集合过窄而把混态误判为纯 |

实量子反模型 **留待下一项**。总著的实量子例子针对标准实对称局部效应与标准实联合系统的局部层析：两个联合态可有相同的全部局部乘积统计，但被联合效应区分。这是排除实量子理论所需前提的另一种责任，不由本轮经典纯化反例自动覆盖。[S2]

下一项可以精确形式化 \(\rho_\pm=\tfrac14(I\otimes I\pm Y\otimes Y)\)，核对它们是不同的实联合密度矩阵、对**全部**实对称局部效应的乘积测试响应相等，以及一个合法联合效应能够区分。这里单个 Pauli Y 不在实对称局部效应空间，而 \(Y\otimes Y\) 是实对称联合矩阵。这只是有限局部层析删除见证的拟定陈述；本次没有运行或完成相关证明。

不能仅从复矩阵 Lean 环境中选取实矩阵子集，就声称已经形式化了整个实 OPT 的系统、通道、组合或 ESP；也不能声称该实量子见证已经实例化 H1–H6 或全部 UEOT 物理前提。外部重构论文及总著采用的完整 OPT 背景仍是独立数学输入；当前任务不复现整套重构证明。[S2、P1]

## 6. 循环假设检查及成功／失败边界

必须禁止的捷径有：把 Density、复 Hilbert、Born 或 Kraus 放入新模型字段后宣称这些结构由 Core 导出；把操作等价预先定义为单系统层析相等再声称证明 CIT；用一个模型的安全路径、另一个模型的奖励或读出拼成“同源”证书；用任意父载体／记录扩展代替纯化；忽略实际商造成的态识别；把历史响应等价直接当成随机类转移良定义而省去强可聚合条件；把总著第 3 章的 Fisher 系数、复相位和动量算符输入当成已经由 Core 选择。[S1–S3、S11]

**成功标准：** 新模型、真实终端商、源核／PMF／路径边际及任意有限辅助空间的纯化否定全部实际编译；必要正例与删除见证同样编译；所有新公开证明和证明型构造均完成公理审计，依赖仅为仓库现行允许的基础公理集合，无 `sorry`、`admit`、新增物理 axiom 或 `native_decide` 捷径；实际递归 Core 导入闭包逐项绑定源身份。本轮要用到的 Core 文件不应假定已属于 v31.5 原有 13 个递归导入，不能借旧 PASS。[S3]

正式正文应分别记录：已形式化的有限接口分离、使用的经典 B 解释、尚待论证的量子 S 前提、经验上未检验的可实施性。它可以收紧量子选择责任，但不能把“最小独立领域原则”宣称为已经找到，更不能把它转换成三代、现实谱、数值常数或终极真理的结论。

**失败／停止标准：** 若实际终端商仍合并支持点，则当前操作混态反例失败，应修正读出桥或登记失败；若纯性定义只在可达态子集中成立，先修正状态空间，不绕过问题；若原 Core 接口不能按提案类型实例化，可交付已证的纯经典 `N-CL`，但 Core 同源分离保持未完成；若候选新原则仍被该反模型满足，登记该原则不能完成此排除。没有可复核的新反例／新定理，不继续扩张宏大重构宣称。

## 7. 资源分配与一次可评审交付

这一轮围绕**同一个**分离证书使用主智能体和三个子智能体，暂不同时启动 A2、B1/B2 三条新研究线：

| 角色 | 独占产出与审查责任 |
|---|---|
| 子 A：有限经典数学 | 拟新增 `UEOTQM/ClassicalSector.lean`：共享标量接口、状态／效应／边际、极点定义、`N-CL`。不依赖 QMB 的量子状态结论 |
| 子 B：实际 Core 接合 | 拟新增 `UEOTQM/CorePurificationBoundary.lean`：`fullyObservedSurvivalModel`、实际终端商不合并、同源 `Q`、显式常真策略、安全路径与真实第 1 时刻商边际；依赖冻结后的子 A 接口 |
| 子 C：独立前提审查与删除见证 | 先审 H_fin／D_cl／状态空间及商映射，不与作者共享未审结论；后新增 `scripts/witnesses/ClassicalPurificationExamples.lean` 的正例及删除见证，并交换审查 A/B 文件 |
| 主智能体 | 冻结接口、统一公共导出与公理审计、汇总一次全库验证及受影响运行门、更新总著与来源／状态档案、完成一个源码 PR 及其实际主线 CI 身份登记 |

上述文件名仅为提案，没有创建。先定义接口并独立审查，再让 A 与 B 的无依赖部分并行；依赖合并、集成运行和发布保持顺序。共享已有官方工具链与缓存，不重复构建未改模块；不得提前预测新增定理数或因旧 CI 成功而宣称新源通过。

本任务结束后的下一决策应是：是否把一个独立、可检验的纯化原则引入为 S，并继续用实量子局部层析反模型约束第二个原则；或者发现更弱、具有真实 UEOT 物理解释的候选，并先要求它排除已固定的经典见证。选择由本次证明和反例决定。

## 来源与复核边界

下列均为本次只读核对的仓库来源；路径以 `/workspace/scratch/474cf6b1f047/qm_v315_work` 为根。`U/` 表示 `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`。源码中已有声明只表示当前读取到的既有成果，本说明本身不代替新的导入、编译或运行回执。

| 标签 | 来源 |
|---|---|
| S1 | `physics/interfaces/CORE_PHYSICS_CONTRACT.md`：C／B／S／P／E／O／X 责任及不得静默修改 frozen Core |
| S2 | `physics/qm/book/UEOT_PHYSICS.md` 第 0–3 章、第 47 章：经典／实量子反模型、完整重构背景、Fisher／相位独立输入及下一轮责任 |
| S3 | `physics/qm/ROADMAP.md`：QMU-10、A1、统一验收与版本责任 |
| S4 | `U/ViabilityNonvacuityWitness.lean`：`survivalMicroKernel`、`survivalKernel_nonDirac`、`survivalRead_strongLumpable`、`survival_false_action_is_destructive` |
| S5 | `U/OrganizationalSufficiencyWitness.lean`：`registeredSurvivalModel`、终端合并／区分、`hiddenProgramProtectedModel`、`protected_hidden_program_prevents_merge` |
| S6 | `U/CoreNonvacuousAllTimesWitness.lean`：实际 `registeredSurvivalTerminalControl`、全时域 viability 及 `registered_survival_nonempty_infinite_law` |
| S7 | `U/UnifiedCoreClosureCertificate.lean`：`modelWithRegisteredOrganization`、`registered_organizational_attributes_preserved`、`unified_finite_core_control_and_viability` |
| S8 | `U/CoreInfinitePathClosure.lean` 及 `U/CoreSourceAllTimesAssembly.lean`：源 PMF viability 接合、`exists_source_micro_all_times_viable_path_law`、`single_source_terminal_object_viability_all_times` |
| S9 | `formalization/ueot-core/UEOT/V3/ViabilityTrajectory.lean`：`stationaryTrajMeasure_coordinate`、`all_times_safe_of_coordinate_one`、`exists_stationary_policy_all_times_of_fixed` |
| S10 | `formalization/ueot-core/UEOT/V3/FiniteDiscountedApproxQuotient.lean`：`FiniteProbabilityRow.ofRealRow`、`ofRealRow_apply_toReal`、`Model.transitionPMF_apply_toReal` |
| S11 | `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCFiniteStochasticQuotient.lean`：实际有限受控核、`StrongLumpability` 及唯一类核条件 |
| S12 | `formalization/ueot-qm/UEOTQM/Mixture.lean`：纯标量 `Weights` 结构；后续 Density 构造不进入本任务假设 |
| P1 | Kenji Nakahira, [Two Operational Principles Single Out Quantum Theory, arXiv:2605.23217v1](https://arxiv.org/html/2605.23217v1)：仅用于核准总著已引用的外部重构背景；本文不把该外部结果算作新的 UEOT 推导 |

本方案的商态／纯性范围已另由一个只读子智能体独立复核；该复核也未运行 Lean。最终可执行建议是完整观察的同源模型，受限观察的原模型保留为删除见证。
