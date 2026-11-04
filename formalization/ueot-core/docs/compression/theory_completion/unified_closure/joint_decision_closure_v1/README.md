# UEOT：有限钱包下的全流程联合决策

本包执行 2026-11-04 新合同。原 2026-10-29 整个 Core 条件数学合同与八项总验收保持完成；本包不重开原历史 OPEN，不重抽旧样本，也不改变禁用的 Core 云工作流。

## 实际问题与结果

θ 只初始化抽取一次；同一有限钱包、允许的动作—收据历史和固定时钟贯穿整个过程。选择器联合选择原交易中的修复、idle、合法地址请求与停止付费干预，评价实际出生减实际收费的有限折扣和。公开目标、正固定写费、零终端、无收入、地址 0/1 和新逐步收据权限均见 [冻结合同](CONTRACT.md)。完整世界记录与允许观察严格分开。

交付不是符号 Bellman 或单个候选：可计算算法返回完整有限表，原生 Store 解释这同一张表；其实际 J 等于最优值，所有正概率前缀都能执行前预付。最优性比较包括只在实际支持历史合法的任意实数随机完整历史策略。

### 源特定的一般有限时域结论

总期限 H+1，钱包 B=c，价格化写费 p=λc。设 S_H=Σ(t<H)d^t，且 p≥S_H。原 source 的两健康对象免费余程值满足

```
U1(0) = U2(0) = 0
U1(n+1) = r(1+d U1(n))
U2(n+1) = r(1+d U2(n)) + (1-r)d U1(n)
```

则 **原生 THIS 返回表**的最优实际净值为

```
V*(H+1) = max(0, E[r(1-p+d U2(H))]).
```

这是实际 source 的上界与达到定理。正确首写成功时产生真实 root 和 child1、耗尽唯一钱包，随后仅根据收据派发；故障仍保留损坏人口与未花钱包，但剩余期限的高价格 no-go 排除有利重试。首次收费前没有出生；首次收费在 t 时，后续全部折扣出生不超过 d^t S_(H−t)，所以 no-go 正确计入了费用的同一折扣。

令 μ1=E[r]>0，M_H=E[r U2(H)]。在同一参数区间，V*>0 **当且仅当** p<1+d M_H/μ1。另对任意期限和非负价格，若初始正支持人口全损坏且 B<c，则最优值严格等于零。

### 同信息、同钱包、同全部费用的精确对照

| 实际实例 | 完整期限最优净值 | 合法对照与解释 |
|---|---:|---|
| 等权 r=1/4,3/4；H=2，d=1/2，p=13/10 | 1/160 | 同菜单最佳固定流程同值；重抽 θ 的错误平均核修复值 −1/40 |
| 同源；H=3，d=3/4，p=7/4 | 9/256 | 固定“写 root、idle root、idle child1”已最优；无适应性增益 |
| 同源；H=3，d=1/2，p=13/10 | 27/320 | 保持旧先验而在首次故障后重试得 51/640，损失 3/640 |
| 等权 r=3/4,7/8；H=4，d=3/4，p=37/16 | 39525/524288 | 同菜单最佳固定流程 2325/65536；反馈差 20925/524288 |

所有行钱包 B=c=1。短视策略在这些 p>1 的损坏初态取零值动作。前三个“固定”值不宣称超过精确全历史参考；与该参考一致是正确性检查。

首次正确写的未收费故障收据 (0,0) 给后验矩 μ′k=(μk−μ(k+1))/(1−μ1)。非退化二点先验且 d>0 时，剩余两步修复阈值从 1+d μ2/μ1 严格降到 1+d(μ2−μ3)/(μ1−μ2)。上述后验诊断中阈值为 21/16 与 5/4，失败后低 r 权重为 3/4，重试值为 −3/160。该三步诊断不满足 p≥1+d，由实际通用算法及 THIS 重放认证，不能套用高价子族的闭式作为证据。

四步反馈差 d³E[r³(1−r)] 非负，在 d>0 且源对 0<r<1 有正质量时严格为正；取 max(0,·) 后的最终增益还要看两候选是否为正。它来自身体状态反馈。成功后无写余程的收据策略对每个 r 同时达到全知上界，额外免费揭示 θ 在这个余程类中价值为零。未声明的父标记读数不能免费加入菜单。

### 原生人口与三个不同主张

原 Store 的真实轨迹保留 child/None、全局地址、父关系、owner 与 newborn 零钟。例如 root 首次产生 child1，root 故障追加 None，随后派发 child1 产生地址 3 的孙代；缺失 child1 时原 lookup 返回 None。选择器仍只读取 (birth,paid) 收据。地址 2 以后保留在人口世界中，本菜单不自动获得其派发权。

两步、三步的至少一次出生概率均为 1/2，四步为 13/16。事件概率、净收益最优和逐前缀资金安全分别承担证据。最优期望为正不保证每条路径净收益非负，也不表示单独最大化出生概率。

## 证明与实际返回入口

以下源均位于 `UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`，由现有公共 `TheoryCompletion.lean` 导入。

| 模块 | 实际证明责任 |
|---|---|
| FiniteJointDecisionBelief | 一个联合 primitive 的质量、后验、总期望；分母缓存与原整个 posterior 的定义性等价 |
| FiniteJointDecisionSolver / SolverExecution | 可计算有理返回表、解释期望、行查找、全部前缀账本 |
| FiniteJointDecisionFilteredModel | 原 primitive 的完整迹测试函数、期望与实际支持路径桥 |
| FiniteJointDecisionSupportedPolicy | 仅要求实际支持历史合法的完整历史实数随机比较类 |
| RegisterJointDecisionSource / Execution / NativeLaw | 原交易、真实 mode/label law、完整 Store 执行、收据/费用/身份投影 |
| RegisterJointDecisionConsumer | 公共 Family、单钱包预付菜单、真正由后验构造的模型与 returned |
| RegisterJointDecisionValueBounds / ExpectedBounds | 全损坏人口的逐路径及实际期望 no-go |
| RegisterJointDecisionFreeTail / FixedTail | 一般期限免费余程上界与达到、三次固定地址的最优对照 |
| RegisterJointDecisionBoundary / Optimality | 持久参数矩、后验阈值、一般期限精确最优、价格及预算反向边界 |
| RegisterJointDecisionNativeConsumer | THIS 表实际原生 J、原生预付、随机竞争者最优、人口、原 founder 和参数式的终端组合 |
| FiniteJointDecisionFastSolver | 严格有限缓存返回的值和整张表等于原 solve，保留平局及不可能收据分支 |

主要终端为 `returned_native_value`、`returned_native_payment`、`returned_native_optimal`、`returned_native_population`、`initial_returned_native_value`、`initial_returned_native_boundary`。

实际可执行入口为 [RETURN_POLICY_CACHED.lean](native_protocol/RETURN_POLICY_CACHED.lean)，参数 `two`、`three`、`posterior`、`four`。它输出实际 Lean 表，不导入 Python 候选。`cachedResult_sound` 与整个表的相等定理将打印的值及完整 rows 绑定到原 returned。原入口 [RETURN_POLICY.lean](native_protocol/RETURN_POLICY.lean) 与初次执行全部保留。

独立 [检查器](native_protocol/verify_lean_output.py) 只按输入 Lean rows 执行动作；[参考源](native_protocol/exact_reference.py) 的 planner 只用于逐行最优值比较。原始模式、独立公平标签、故障、收费与 None 全部精确枚举。检查器另外核查全部序列化行的预付菜单；实际路径余额从原交易字面费用扣减，不依靠 clamp。

## 验证、工程记录与接续

最终输入、返回表、同源完整 traces、源与输出身份、旧表字节比较及实测耗时见 `actual-execution/lean-final-02/`、`actual-execution/THIS-final-02/` 和 `checks/`。最终编译、公共导入及公理审查分别记录；作者实现与非作者语义审核分列于 `independent/`。

原四步 solve 实际完成，耗时 1713.890130 秒，返回 85 行和值 39525/524288。随后仅物化子表的缓存尝试前三例仍约同速，其四步在 293.329843 秒人工终止；这不是数学无解。`actual-execution/pre-normalizer-cache/` 保存实际源快照和运行记录。定位到后验权重反复计算同一分母后，使用整个 posterior 的 rfl 等价修正；最终性能以新运行回执为准，不仅凭 noinline 宣称提速。

独立参考结果中的 `persistent_two_step_formula` 是 B≥c 时的候选公式。零钱包／不足预付实例的真实 `optimal.value` 为零；该辅助字段不能解释成这些实例可实现正值。历史输出保持原样。

两书新增数学 §39.75—39.81、哲学第十章与附录 C；旧主文、原 −3/40 反例与已完成合同保留。发布后，原 `memory.py` 使用原个体、原流及 predecessor CAS 写入真实结果，独立 fresh recall 以唯一 `CONTINUE.md` 记录完成状态。GI 实施及数据库没有修改。

本包不证明未知程序识别、额外父标记协议、无限无供给维持、全人口同时老化、内生认知成本或现实普适性。形式模型的经验支持仍为 **UNVERIFIED**。验收范围见 [FINAL_ACCEPTANCE.md](FINAL_ACCEPTANCE.md)。

### Final execution identity and retained timing attempts

The final 17-module rebuild and 18 public-endpoint axiom checks passed. The final source closure contains 282 exact files, unchanged before/after execution. The final two/three/posterior JSON outputs are byte-identical to the successful original runs. The original four-step solve completed exit0 in 1713.890130 seconds and its 85-row actual JSON (SHA256 9ace921a626a4658a1e0dbb98f78706da69b52917026851480b61c7987604f7b) passed all 512 positive original-noise paths and every reachable action optimum. The duplicate final cached four-step timing run was stopped after 791.953935 seconds once all four actual original outputs had passed verification; it is not reported as a successful new four-step run. Whole-posterior definitional equality and whole-returned-table equality justify reuse of the preserved actual output. No measured speedup is claimed. The independent verifier checks the same complete source and exact returned rows, and the before/after source bindings are preserved.
