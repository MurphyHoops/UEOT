# 同源无限状态前缀桥：独立合同与完整源码静态审查

**结论：STATIC_MATHEMATICS_AND_INTERFACE_CLEAR — LEAN_EXECUTION_PENDING。**

审查者 `/root/audit_resume` 完整读取冻结合同与私有 Lean 草稿，核对真实 Core/Mathlib 定义及已通过的动作擦除接口。没有发现来源等式被放进假设、初态被替换、旧状态坐标被丢弃、或一般历史策略被偷偷变成齐次状态 Markov 策略的问题。数学目标和证明路线可进入 root 统一安排的聚焦编译窗口。

本次没有运行 Lean、lake、native、测试或 Git，没有编辑作者文件、生产或书稿。下述 CLEAR 是数学与接口静态审查；不是该文件已通过 Lean，也不是其公理闭包或生产集成收据。

## 1. 绑定对象

| 文件 | SHA256 | 字节 |
|---|---|---:|
| `SameSourceInfinitePrefix.lean` | `7773377037056384b194d09e63623d3a65c127e7d9cd22681430bd89648b54e0` | 9988 |
| `CONTRACT.md` | `153e8e85bed5caffd1e0ae3c9cab98242c1040339e70a3b6ac272dc0f31dadcc` | 12969 |
| `STATUS.json` | `e0928a635c7447274dfce02d35801a6e98a88cc9f3f2ffec1a80c6f6c0b33875` | 1857 |
| `API_INPUTS.json` | `c005698afa81caf206e4e41c702e6d381ee35f4665a7fe92ea24227d55aec0ec` | 6445 |

作者 API 快照的 23 个输入逐一按当前真实字节核对一致；另外读取 PMF 原子测度、Measure map 合成、kernel comap 的三个实际源文件。完整身份列表在 `REVIEW_INPUTS.json`。这是所读接口的快照，不是全库依赖环境或未来执行复用授权。

原先已过的 `SourcePolicyPathBridge` 源 SHA 为 `108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`，其真实 attempt002 二进制 SHA 为 `0ef1132fbfb24b0e571693de99e2729f9a8ede4aa41203fb4b3be67d46915748`。本审查复用其已经完成的数学审查与实际执行身份，不重审该旧证明。未来执行仍须核对完整环境和实际导入路径，不能仅凭二进制文件存在就认定缓存匹配。

## 2. G1 的真实量词与完整前缀

G1 的数据只有有限 X、可测单点、原始 `p0 : PMF X`、固定 `J : X → PMF X` 及任意 n。核 `pmfRowKernel J` 的每一行按定义就是 `(J x).toMeasure`；Markov 性来自实际 PMF 归一性。没有另给一个核、前缀测度或证书后再假设它与真实来源相等。

递归历史类型满足 `H₀=X`、`Hₙ₊₁=Hₙ×X`。`stateHistoryEquiv` 在 n=0 使用 `piUnique.symm`，所以时刻 0 保留的是原始 p0。后继用 `prodCongr` 和 `piSingleton n` 把新状态放入区间 `(n,n+1]`，再由 `IicProdIoc (n≤n+1)` 拼接。该 API 的逆映射分别限制到旧 `Iic n` 与新增区间，因此这是真正保留全部旧坐标的可测等价，不是仅保留末态的函数。

`Iic n` 有 0,…,n 共 n+1 个坐标。`stateHistoryEquiv_succ` 对齐实际 `appendHistory n`，`stateHistoryEquiv_last` 对齐 `currentState`；二者分别负责完整历史保留和下一步读到正确 J 行。完整前缀身份的数学内容为

\[
(e_n)_*\lambda_n.toMeasure
=(\operatorname{frestrictLe}_n)_*\operatorname{homTrajMeasure}(p_0.toMeasure,R_J),
\]

其中 `lambda_n` 确实由 `causalLaw p0 (fun k h => J (currentState k h)) n` 构造。独立地按有限原子展开，两侧在状态串 \((x_0,\ldots,x_n)\) 上均有质量

\[
p_0(x_0)\prod_{k<n}J(x_k)(x_{k+1}).
\]

这说明结论包含整个联合分布和时间相关性；并非所有单时刻边缘相等的弱命题。该乘积式是本审查的数学核对，不冒充草稿新增了一个已执行 Lean 端点。

无需正概率历史、正存活、QSD、不可约性或观察 lumpability，因为此处比较的是未条件化的完整概率律。p0 作为输入已经排除了空 X 上不存在概率分布的情况；无需添加 `Nonempty X` 或默认初态，也不能据此声称构造了空状态类型的 PMF。

## 3. G1 证明体确实推导来源身份

私有 `pmfExtend_toMeasure_compProd` 从真实 `pmfExtend = bind (map (Prod.mk h))` 出发，对可测 E 展开 bind，得到

\[
\sum_h p(h)J(h)(\{z:(h,z)\in E\}).
\]

`Measure.compProd_apply` 与 `lintegral_countable'` 展开右侧后得到相同和式，仅交换两个非负扩展实数因子的顺序。H 有限且单点可测，因而此积分计算成立；Z 不需被额外假定有限。这个辅理不是来源相等的外部前提。

`historyRowKernel_eq_comap` 由构造及 `stateHistoryEquiv_last` 逐行识别旧历史上的下一状态核。`compProd_comap_map_left` 直接按真实 map/compProd/lintegral-map 定义计算左历史推前，保留新状态。G1 随后按 n 归纳：n=0 使用现有 `homTrajMeasure_prefix_zero` 的对称式，后继使用现有 `homTrajMeasure_prefix_succ` 的原方向。源码中没有以归纳假设之外的路径身份完成桥接。

这只是接入现成 Ionescu–Tulcea 轨迹；既有 `homTrajMeasure` 没有被替换，也没有重建第二个无限概率过程。当前不需调用无限概率律唯一性，因为只比较已构造无限律的前缀；`pathMeasure_eq_of_prefix_eq` 是以后比较两个无限律时可复用的端点。

## 4. G2/G3 的同源性与事件范围

G2 仍固定同一个模型 M、观察 q、时间齐次当前观察反馈 `sigma` 和原始 p0。真实行动—状态律使用 `riskMicroControlKernel q (fun _ => M.transitionPMF) (observationMarkovPolicy sigma)`；诱导状态行只通过 `policyTransitionPMF M (liftedStationaryPolicy q sigma)` 构造。

证明先将复合 PMF map 拆开，调用已经通过的 `actual_state_path_eq_stationary_path` 擦除动作，再实例化 G1。因此全部原状态记录被保留；没有独立提供可任意替换的状态核、策略或初态。q 可任意，Y 不要求有限或可测。有限 X/A 与显式 `Nonempty A` 与旧动作擦除接口一致；没有因这次泛化 J 而放宽策略范围。

G2 左侧采用“先 PMF.map，再 toMeasure”，故不需要给原行动记录载体预设可测结构。G3 才为 A 增加可测结构和可测单点，并在实际原行动记录的 `nu_n.toMeasure` 上取事件。有限前缀空间上的任意 B 都可测，映射也因有限域和可测单点而可测；两次实际 map 语义把 G2 转成

\[
\nu_n((e_n\circ a_n)^{-1}B)
=\nu_\infty(\operatorname{frestrictLe}_n^{-1}B).
\]

这个结论限于原行动记录上能通过完整状态前缀因子化的事件。不能据此转移任意依赖动作的事件，也没有构造或宣称一个完整无限行动记录律。源码 G3 的类型准确保留了这项限制。

一般因果策略仍可能依赖旧历史和时间。当前 `sigma` 的固定来源不证明 `viableFamilyPolicy` 满足该表示；若要接某个实际已部署策略，必须证明其逐时间、逐历史的平稳当前观察反馈身份，或另作状态扩充。这里没有把另一策略的安全性质代换过来。

## 5. 实际 API 核对与未执行的 elaboration 风险

| 已读实际 API | 本草稿用法核对 |
|---|---|
| `MeasurableEquiv.piUnique` | 方向为函数空间到唯一坐标，草稿取逆，准确得到时间零前缀。 |
| `MeasurableEquiv.piSingleton n` | 从 X(n+1) 到 `Ioc n (n+1)` 函数空间；恒定族 X 的新状态类型正确。 |
| `MeasurableEquiv.IicProdIoc` | `n≤n+1` 下由旧前缀×新增区间到新前缀，可逆且可测。 |
| `PMF.toMeasure_map` | 实际方向是 `p.toMeasure.map f = (p.map f).toMeasure`；草稿反向 rewrite 正确。 |
| `PMF.map_comp` | 实际方向是两次 map 等于复合 map；G2 反向拆复合正确。 |
| `Measure.map_map` | 参数顺序为后映射可测性、前映射可测性；草稿 append/Prod.map 顺序正确。 |
| `PMF.toMeasure_bind_apply`、`toMeasure_map_apply`、`toMeasure_apply_singleton` | 草稿提供实际可测事件/单点，所用参数与计算目标相容。 |
| `Kernel.ofFunOfCountable` | 有限 H 给 countable，单点可测给任意行函数可测；核值就是实际 PMF 测度。 |
| `homTrajMeasure_prefix_zero/succ` | 前者需要对称，后者与归纳后继目标同方向；同一 p0/R 未换源。 |
| `homHistory_compProd_naturality` 的既有证明模式 | 草稿只复用其左坐标 comap/map 的积分计算，没有错误引入或丢弃 lumpability 假设。 |

未发现一个可仅凭读到的真实签名判定为确定错误的 API 调用。但以下仍须由实际聚焦编译解决，不能以静审宣称已经通过：递归 `CausalHistory` 可测实例与等价的类型归约；`stateHistoryEquiv_succ` 的 `rfl` 和 last-index 的 cast/simp；comap 的核实例及有限测度实例推断；归纳后续 `rw` 的具体匹配与依赖类型归约。API 的实际存在和数学适用性并不保证这一整份 proof script 已 elaborated。

草稿三个 `#print axioms` 尚未执行。没有新增公理或 `sorry` 的文本不等于有公理闭包收据。编译修复可采用显式参数、类型变换或证明体调整；不应新增来源等式假设或弱化三个终端目标。

## 6. 边界、反例与后续组合

合同列出的反例及边界均正确：保持一次公平位与每步独立公平位具有相同一维边缘而不同两时刻联合律；依赖 X0 的策略能在同一当前状态下给出不同下一步律；动作擦除不能保留纯动作事件；原始初态不全在 K 时 `s0=p0(K)`；每个有限窗正存活不保证无限存活为正。它们是数学说明，没有冒充 Lean 见证。

未来取状态安全前缀事件 Bn(K) 时，仍须实际证明其在行动记录上的拉回等于 `¬ riskEverFailure`。这个逐记录事件对齐尚未由本文件形式化；随后才能结合已过 K1，把相同 p0 与同一受限矩阵 Q 的 `eta0 Q^n 1` 接到无限圆柱质量。初始限制 eta0 不应归一化；n=0 和空 K 必须保留，且 K1 的 real 质量与 G3 的 ENNReal 质量要显式转换。

合同对已有尾极限接口的指向准确：`survivalProb_eq_homTrajMeasure_apply` 的集合参数是命中/失败目标，因此传 K 的补集；`homTrajMeasure_apply_eq_lintegral_initial` 对同一实际核进行原初态混合；`neverHitSet_eq_iInter_survivalSet` 与 `survivalProb_tendsto_neverHitProb` 提供既有递减事件极限。初态混合版本以及 K1 的具体事件组合仍需要适配，不能仅列 API 名字就称新目标已完成。

已有 `exists_stationary_policy_all_times_of_fixed`、`exists_source_micro_all_times_viable_path_law`、`single_source_terminal_object_viability_all_times` 确实已提供其明示假设下的同源概率一全时域安全。当前候选没有把这些已有结论说成项目空白，也没有将它们的存在性控制器等同于当前任意 sigma。

## 7. 最小下一步与复用范围

可以按原三个 G1–G3 目标进入一次私有聚焦编译；不需新增数学假设，不需全库回归或 native。root 应绑定实际源码、私有 SourcePolicyPathBridge 及完整执行环境，保留失败与最终成功源码、日志和三个真实公理输出，随后只审编译差异。

本次静态 CLEAR 只绑定上列冻结版本与其明示范围。安全事件对齐、K1/real 组合、无限存活极限、最大不动点、有限窗 Doob，以及任意历史策略的状态扩充均没有因这次静审变成已编译结果。生产化和书稿声称应分别等待各自真实实现与验收。
