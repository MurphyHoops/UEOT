# UEOT-QM v31.4 / Kernel 1.4

## 实际效应、量子稳定性与《UEOT物理学》正式 3.0

日期：2026-10-19 UTC。状态：**LOCAL_VERIFIED_CI_PENDING**。

本轮把已有精确量子内核推进到可组合的实际误差合同：从正半定效应和真实 Born 配对，推出完整 Kraus 通道的全效应响应收缩、实际通道缺陷的一步扰动界、严格正事件的后验界，再以这些已经证明的量子前提调用 Core M-TC。**QMU-04 完成的是有限共同载体完整 Kraus 通道及正事件后验切片**；通道缺陷的数值求界、含标签／历史的自适应模型与 ancilla 稳定范数仍有独立义务。[数学范围与完整声明名单](audits/EFFECT_STABILITY_REVIEW_v31.4.md)

官方 Lean 4.33.1 已实际完成统一构建：**15 个通用模块、256 个显式定理，287 项唯一命名公理审计 PASS**。87 个运行方法、3 个演示、6 份具体证书的重新生成与编译均通过；四种数据篡改同时满足原通过证明被拒绝和同数据 `check = false` 内核证明成功。本轮远端 CI 与合入后的主线验收尚未完成。[统一证明回执](kernel/evidence/v31.4/lean-verification.json)、[实例验收](kernel/evidence/v31.4/lean-exports/verification.json)

## 1. 总著、内核与证据入口

正式理论总入口固定为 [《UEOT物理学》3.0](book/UEOT_PHYSICS.md)，连续正文为第 0–50 章与附录 A–F；[PDF](book/UEOT_PHYSICS.pdf) 与正文同目录。第 49 章解释有限证书如何接入全词响应及闭合更新，第 50 章展开本轮实际效应、通道误差和后选择的论证。总著版本 3.0 与内核版本 31.4 属于不同版本序列。

总著承担完整理论的论证、假设和研究接口组织。通用数学声明由 [Lean 包](../../formalization/ueot-qm/README.md) 与具体源码认证；数值证书由各自真实内核检查认证；物理输入、模型匹配与经验有效性继续需要领域证据。书中的标准数学证明和正文范围没有因为内核构建成功而全部晋升为 Lean 已证。

| 入口 | 负责的内容 |
|---|---|
| [正式总著](book/UEOT_PHYSICS.md) | 操作语义、量子重构输入、各物理扇区、证明论述与工作包 |
| [Effects.lean](../../formalization/ueot-qm/UEOTQM/Effects.lean) | 实际效应、Born 界、完整／选择分支拉回和记录词 |
| [Stability.lean](../../formalization/ueot-qm/UEOTQM/Stability.lean) | 全效应伪距离、通道缺陷、收缩、后验和实际 M-TC 组合 |
| [范围审查](audits/EFFECT_STABILITY_REVIEW_v31.4.md) | 作者范围检查、独立语义复核、全部 74 个新增审计名字和聚焦日志身份 |
| [主张台账](status/CLAIM_LEDGER_v31.4.json) | 每项主张的假设、证明、运行与物理边界 |
| [实际本地回执](kernel/evidence/v31.4/lean-verification.json) | 统一编译、公理、源身份与具体实例验收 |
| [CURRENT](status/CURRENT.json) | 发布阶段、远端 CI 与主线集成状态 |

## 2. 新增范围和准确计数

v31.3 的 13 模块继续提供合法密度态／仪器、全词商、闭合后验、实际效应张成与坐标、完整自适应树、条件谱桥、加权／补零／精确数域以及可靠有限证书。本轮新增两个模块，原有数值样例也针对新包重新验证。[继承合同](UEOT_QM_KERNEL_v31.3.md)

| 范围 | 显式 theorem | 另列定义／构造 | 命名公理目标 |
|---|---:|---:|---:|
| 原 13 模块 | 196 | 17 | 213 |
| Effects | 30 | 10 | 40 |
| Stability | 30 | 4 | 34 |
| 本轮通用包合计 | **256** | **31** | **287** |

新增 14 个公开定义中，9 个构造返回携带证明的 `Effect` 或 `Density`，5 个定义概率、完整通道或上确界数据。它们全部列入审计，但不把这 14 个名字全称为证明构造，也不把 74 个新审计目标当作 74 个新定理。287 不是编译器全部内部常量的普查。六实例的 42 个审计目标与四个假值见证的 4 个目标单独计数。[聚焦审计](kernel/evidence/v31.4/metric-focused-audit.json)、[统一公理检查](kernel/evidence/v31.4/proof-axioms.json)

## 3. Effect：把概率界落实到实际矩阵

共同载体是有限指标类型 $\iota$；`Operator ι` 是有限复矩阵，`Density ι` 仍要求矩阵正半定且迹为 1。新结构 `Effect ι` 只含实际矩阵及两个局部正性证明：

$$
E\succeq0,\qquad I-E\succeq0.
$$

`Effect.zero`、`Effect.one`、`Effect.complement` 都是已经证明合法的构造。概率使用原有配对

$$
P_E(\rho)=\operatorname{Re}\operatorname{tr}(E\rho).
$$

`pairing_nonneg` 从完整 PSD 条件得到 $E=B^\dagger B$，再用迹循环性转到 $B\rho B^\dagger$ 的正迹。证明没有假设非交换乘积 $E\rho$ 本身正半定。对任意 PSD 矩阵 $X$，补效应进一步给出

$$
0\le\operatorname{Re}\operatorname{tr}(EX)
\le\operatorname{Re}\operatorname{tr}(X).
$$

取 $X=\rho$ 即得 `Effect.probability_nonneg`、`Effect.probability_le_one`，以及补概率等式 $P_{I-E}(\rho)=1-P_E(\rho)$。这是输入量子扇区中的实际 Born 配对性质；没有从 generic Core 推导 Born 规则的唯一物理形式。[Effects 源码](../../formalization/ueot-qm/UEOTQM/Effects.lean)

## 4. 完整仪器、分支与每个有限记录

已有 Instrument 的输入是有限 Kraus 表和完整性恒等式

$$
\sum_o\sum_k K_{o,k}^{\dagger}K_{o,k}=I.
$$

`Instrument.pullbackEffects` 接受一族结果依赖效应 $E_o$，构造

$$
\sum_o\sum_k K_{o,k}^{\dagger}E_oK_{o,k}.
$$

正性逐项推出；完整性把其补矩阵写成 $\sum_{o,k}K_{o,k}^{\dagger}(I-E_o)K_{o,k}$，因此补正性也是证明输出。`channelState` 将全部结果相加，由已证 PSD 保持和迹保持构造真实输出 Density；`probability_channelState` 给出实际 Heisenberg 对偶。单结果的 `branchEffect` 则把其他结果的测试设为零，保留所选分支的语义，未将它改称为迹保持通道。

`recordTest` 按已有 chronological word 递归生成效应；`recordTest_matrix` 证明其矩阵等于旧 `recordEffect`。因此每个有限记录都有 $0\preceq E_w\preceq I$，其实际响应为 $P_{E_w}(\rho)$ 并且至多为 1。该结论对任意有限词成立，不以样例的见证词长代替未来记录范围。[对应定理](../../formalization/ueot-qm/UEOTQM/Effects.lean)

## 5. 全效应响应伪距离与共同后续记录

`effectDistance` 的定义为

$$
d_{\mathrm{eff}}(\rho,\sigma)
=\sup\{|P_E(\rho)-P_E(\sigma)|:E\text{ 为 Effect}\}.
$$

零效应保证集合非空，Born 界保证它有上界 1；这些条件均有实际 Lean 证明。随后得到非负、上界 1、对称性、自身为零和三角不等式。`effectDistance_le_iff` 表明，一个实数控制该伪距离，当且仅当它控制全部效应概率差。

本轮的零值结论准确为

$$
d_{\mathrm{eff}}(\rho,\sigma)=0
\iff \forall E,\ P_E(\rho)=P_E(\sigma).
$$

`effectDistance_eq_zero_iff` 没有进一步证明 Density 相等，也没有构造 `MetricSpace` 实例。它与迹范数／通常 trace distance 的识别，以及与带任意辅助系统的通道范数之间的关系，本轮均未作为新增 Lean 成果登记。

由于每个实际词效应属于 Effect，对同一个后续操作库 $Q$ 的任意有限词 $w$，`response_sub_le_effectDistance` 证明

$$
|R_{\rho}^{Q}(w)-R_{\sigma}^{Q}(w)|
\le d_{\mathrm{eff}}(\rho,\sigma).
$$

这里的上确界覆盖全部效应；受限库的响应等价可能更粗，不能混淆这两个对象。[Stability 源码](../../formalization/ueot-qm/UEOTQM/Stability.lean)

## 6. 实际完整通道的收缩与缺陷

完整通道 $\Phi$ 的任一输出效应都能拉回为合法输入效应，所以 `channelState_effectDistance_le` 证明

$$
d_{\mathrm{eff}}(\Phi(\rho),\Phi(\sigma))
\le d_{\mathrm{eff}}(\rho,\sigma).
$$

对同一有限载体上的态映射 $F,G$，定义

$$
\delta(F,G)=\sup\left(\{0\}\cup
\{d_{\mathrm{eff}}(F(\tau),G(\tau)):\tau\text{ 为 Density}\}\right).
$$

插入零使空 Density 类型时的集合也非空；已证明 $0\le\delta\le1$ 及其逐态上界。对两个完整 Kraus 通道，收缩、三角不等式及实际缺陷的定义给出

$$
d_{\mathrm{eff}}(\Phi(\rho),\Psi(\sigma))
\le d_{\mathrm{eff}}(\rho,\sigma)+\delta(\Phi,\Psi).
$$

这是 `channelState_perturbation_bound` 的实际结论。一步量子误差性质没有作为 Instrument 或抽象证书的最终等价字段输入。

`channelDefect` 仍是非计算上确界，不是已经完成的通用数值上界算法。调用方提供一个数 $\widehat\delta$ 时，仍须证明 $\delta\le\widehat\delta$；有限状态抽样得到的最大差通常只给这个上确界的下界。这里比较的完整通道会丢弃结果，因此它不自动控制两个不同仪器的标签分布或历史联合律。[证明与边界](audits/EFFECT_STABILITY_REVIEW_v31.4.md)

## 7. 由真实量子递推接入 Core M-TC

`channelTrajectory` 递归定义两条真实通道轨迹

$$
\rho_{n+1}=\Phi_n(\rho_n),\qquad
\sigma_{n+1}=\Psi_n(\sigma_n).
$$

两条序列作用于共同有限载体。两序列之间可使用不同的结果／Kraus 指标类型；每条序列内部类型固定，实际矩阵可随时间改变。逐步不同的有限表示若需套入此接口，必须先提供明确的共同有限索引及语义保持的嵌入，不能省略这一输入义务。

令 $e_n=d_{\mathrm{eff}}(\rho_n,\sigma_n)$ 和 $\delta_n=\delta(\Phi_n,\Psi_n)$。上一节已经证明 $e_{n+1}\le e_n+\delta_n$。`channelTrajectory_transport_certificate` 把这条实际量子递推交给现有 `Transport.scalar_transport_certificate`，后者实际复用 Core 的 `weighted_chain_bound`。取 $L_n=1$ 并证明递归预算的求和形式，得到

$$
d_{\mathrm{eff}}(\rho_n,\sigma_n)
\le d_{\mathrm{eff}}(\rho_0,\sigma_0)+\sum_{j<n}\delta_j.
$$

`channelTrajectory_response_sub_le_sum` 进一步交付同一后续操作库的每个有限词响应界。量子一步合同在本轮已经闭合；Core 的一般组合定理保持原样。这个结果没有证明 Python 轨迹程序对所有输入细化该 Lean 递归，也没有覆盖未经扩大建模的自适应历史误差。[Stability](../../formalization/ueot-qm/UEOTQM/Stability.lean)、[实际 Core 桥](../../formalization/ueot-qm/UEOTQM/Transport.lean)

## 8. 正事件后验与稀有分支

对同一 Instrument 的同一结果 $o$，设 $p=p_o(\rho)>0$、$q=p_o(\sigma)>0$。分支效应和实际归一化矩阵给出

$$
|p-q|\le d_{\mathrm{eff}}(\rho,\sigma),\qquad
P_E(\rho_{\mid o})=P_{\Phi_o^*(E)}(\rho)/p.
$$

`posterior_effectDistance_le` 逐效应控制归一化比值，证明

$$
d_{\mathrm{eff}}(\rho_{\mid o},\sigma_{\mid o})
\le \frac{2d_{\mathrm{eff}}(\rho,\sigma)}{p}.
$$

下界版本还要求 $\eta>0$ 与 $\eta\le p$，把分母替换为 $\eta$。两个后验的严格正概率见证继续保留。`probability_pos_of_effectDistance_lt` 另证明 $d_{\mathrm{eff}}(\rho,\sigma)<p$ 足以推出 $q>0$。条件化可以放大误差，常数二未被宣称最优；零概率事件不产生后验。[已证合同](../../formalization/ueot-qm/UEOTQM/Stability.lean)

例如，若已核验初始误差至多 $10^{-3}$，二十步的实际缺陷各有经证明的上界 $2\times10^{-4}$，则终态误差至多 $0.005$。若第一态的后续事件概率至少 $0.2$，该误差也能证明第二态事件为正，后验差至多 $0.05$。若只知第一态事件概率至少 $0.001$，则 $0.005$ 的误差不足以保证第二态事件为正；只有另行给出两个正概率见证，才能代入后验定理，而此时得到的上界超过一。这个例子演示合同的适用条件，不是设备或实验性能数据。

## 9. 本轮实际验证和源码身份

| 验收对象 | 本轮实际结果 | 回执 |
|---|---|---|
| 固定依赖 | 9 个 Git 依赖的实际 checkout 匹配固定版本 | [依赖身份](kernel/evidence/v31.4/dependency-identity.json) |
| 统一 Lean 构建 | `lake build UEOTQM` exit 0，8735 个构建任务；15 模块、256 theorem | [证明回执](kernel/evidence/v31.4/lean-verification.json)、[原始日志](kernel/evidence/v31.4/lean-build.log) |
| 通用命名公理 | 287 个唯一目标，无缺项、重复或未审查公理；仅三项标准基础 | [审计检查](kernel/evidence/v31.4/proof-axioms.json)、[原始报告](kernel/evidence/v31.4/axiom-audit.log) |
| 新模块聚焦验证 | 60 theorem + 14 定义共 74 项；实际编译和审计 PASS | [聚焦回执](kernel/evidence/v31.4/metric-focused-audit.json) |
| 运行回归 | 87 个方法 PASS | [运行回执](kernel/evidence/v31.4/runtime-verification.json) |
| 演示 | demo、demo_v312、demo_v313 全部 PASS | [演示回执](kernel/evidence/v31.4/demos-verification.json) |
| 正数值实例 | 6 份实际源码重新编译，42 项实例审计 | [逐实例验收](kernel/evidence/v31.4/lean-exports/verification.json) |
| 严格负控 | 4 个坏数据的原通过证明拒绝；4 个同数据假值证明成功，另计 4 项审计 | 同上 |
| 远端 CI／主线 | 尚待本轮实际源码身份的验收 | [CURRENT](status/CURRENT.json) |

固定工具链为 `leanprover/lean4:v4.33.1`，实际编译器提交 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`；Mathlib 保持 `0df444a360eaa60ab8c11dca51a86af692955474`。新增模块最终聚焦编译无警告，整包保留旧模块已有 linter 警告；两者不混称。实际公理集合仅为 `propext`、`Classical.choice`、`Quot.sound`，并非无基础公理的逻辑体系。

本轮 [source-manifest.json](kernel/evidence/v31.4/source-manifest.json) 记录 **55 项**源码及其字节散列，集合 SHA256 为 `048a2c3c907ee639d39ec18ed2bf48791dcbd15c5c78d728dc4d6e24411ffc08`。本地观察到的 checkout `0c093e9fae990d6ef8d670163b84ec93bd6fb025` 是上一已验收主线；新候选由各文件哈希标识，不声称这个旧提交已包含新数学。远端发布与集成必须记录其各自实际提交、树和运行身份。

本轮数学修改属于 QM 侧；Core 源码、冻结定义、106 项覆盖表和四个计数生成器未改。作者范围核对与另一审阅者的独立语义复核各自记录，不把只读语义检查冒充编译。

## 10. 继承成果与严格未完成项

可靠 `ExactCertificate.check` 继续检查五项有限条件：非负权重、完整 Kraus 和、单位空词、实际词生成和全部局部闭包。由这些局部条件构造 presentation 后，全部有限词充分性和闭合坐标更新是定理输出。全词等价没有作为最终结论字段输入。v31.4 重新编译六份旧固定实例，只证明这些具体数值模型和公共数学接口；没有由此证明所有 Python／JSON 输入的生成器正确性。[精确证书审查](audits/EXACT_CERTIFICATE_REVIEW_v31.3.md)

当前保留以下独立义务：

- **稳定性扩大。** 密度态分离和传统范数识别；可执行的 $\delta$ 上界证书；显式标签／历史／记忆模型；不同自适应仪器与辅助量子系统的比较。
- **程序细化。** W_n 搜索终止、Hermitian d² 维数、消元／Gram／PSD 判定、JSON 和标签到 Fin 的全输入正确性、Python 树解释与轨迹程序。
- **长期与大扇区。** QMB-05 的 CPTP Cesàro 残差／平稳极限点，QMB-06 的对角 CP 存活桥，以及 CV 的能量／尾部／无界定义域和模型特定 QFT/RG 匹配。
- **物理适用。** QDRR 原始实验记录与可失败控制；G3/HGP 的表示、完整谱、补偿、有效窗口、全局异常、真空、质量及可观测量。三代结论继续是指定谱和窗口下的条件结论。

下一轮优先把实际缺陷接到可核验数值上界；需要控制仪器结果时先扩大实际对象。完整任务序列见 [ROADMAP](ROADMAP.md)。正式总著、通用证明、逐实例检查和领域实证同步维护各自范围，使后续推进能够复用已经闭合的接口。
