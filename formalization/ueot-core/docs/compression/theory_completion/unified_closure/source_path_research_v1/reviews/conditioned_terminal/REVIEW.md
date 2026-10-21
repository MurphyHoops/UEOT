# 一般 K2：独立静态审查

## 结论

**MATHEMATICAL_AND_API_STATIC_CLEAR_NOT_COMPILED。** 对冻结候选的数学命题、实际实验身份、量词及边界未发现阻断问题；所用当前 API 的名称与参数方向已按源码检查。本审查没有执行 Lean、lake、native 或测试，没有修改作者文件、生产、书稿或 Git。K2 编译、公理闭包与集成仍未完成。

| 输入 | SHA256 |
|---|---|
| `SameSourceConditionedTerminal.lean` | `7ab97381798440497a3a60fac5ee2dd405deb1f7100438e06b1a1b6a2e21d95c` |
| `CONTRACT_K2.md` 最终版 | `5f040a5ce6ce27e35f09c83a68a21504975540d9ac56039c6f49208410571920` |
| 作者冻结 `STATUS.json` | `43660f0be421d0d152deb846035687ad1d5bfcaf224890548ee95180d3a97afa` |

作者状态仍是 `DRAFT_NOT_COMPILED`。最后两处合同变动已分别核对：修正模块名与命名空间引用，并明确七模块的一般因果策略不能自动识别为这里的平稳反馈策略。源码没有随这些文字变更改变。

## 1. 同一实际实验与量词

固定同一个 `M,q,sigma,p0,K,n`。实际分布是

```lean
causalLaw p0
  (riskMicroControlKernel q (fun _ => M.transitionPMF)
    (observationMarkovPolicy sigma)) n
```

其中 `p0` 任意，安全集外初始质量被保留；存活事件检查 `X₀,…,Xₙ` 全部安全。`Q` 是同一个 lifted stationary policy 的闭环矩阵在 `K` 上的限制，`eta0` 是原 `p0` 在 `K` 上的未归一化限制。K1 两个实际来源等式直接被调用，没有重新作为假设。

额外前提仅是当前窗口的实际存活质量 `s_n > 0`。代码未要求所有未来窗口正存活、初态在安全集内、初态全支撑、`[Nonempty K]` 或 QSD/Perron 数据。观察类型 `Y` 无有限性或可测性要求。矩阵幂表达式仍明确要求时间不变的当前观察随机策略；这不是任意历史策略的 Markov 化。

最终合同新增的策略边界正确：若接七模块实际 `viableFamilyPolicy`，必须证明该同一策略确实满足 `∀ n hY, π n hY = sigma (riskLastState n hY)`，或建立状态扩充来源桥。不能用另一策略的平稳性替代。

## 2. 条件化、归一化和 PMF 相等

`positive_event_mass_iff_support` 使用真实 PMF 测度与支撑不交等价式，由正质量内部推出 Mathlib filter 所需见证。有限概率测度排除了 `ENNReal.toReal` 在无限质量上的退化。

`actualConditionedTerminal` 直接过滤该实际完整历史，再沿实际末态函数推前。私有过滤—推前原子引理给出联合质量除以同一事件总质量；K1 随后将分子替换为 `(eta0 Q^n)(v)`。未更换初始分布、模型或策略。

`normalizedKilledTerminal` 的非负性由同源联合事件质量非负推出，总和为一由同源总质量等式及 `s_n ≠ 0` 推出。两 PMF 的相等通过内部原子比值、外部零支撑及 PMF 原子非顶性证明。**来源相等是结论而非输入**，归一化目标也未被藏入证书假设。

## 3. 边界

| 边界 | 审查结果 |
|---|---|
| `n=0` | 总存活为 `p0(K)`，正质量时条件原子为 `p0(v)/p0(K)`。 |
| `K=∅` | 空子类型求和给所有窗口质量零，包括零时刻；正存活推出非空而非预设非空。 |
| `s_n=0` | 明确无 filter 支撑见证，不任意赋予 null event 条件 PMF。 |
| 当前正、未来零 | 合同 `a→d` 例子正确；K2 不外推全窗口正存活。 |
| 末态安全、初态失败 | 合同 `d→a` 例子正确；过滤全路径事件不能换成末态事件。 |
| QSD 特化 | 必须在真正使用 `r.map Subtype.val` 初态的实验中代入；不是本接口前提。 |

合同有限反例由所述确定转移直接可算，未声称已有 Lean 数值见证。没有无限存活、条件路径齐次性或条件律收敛结论。

## 4. `filter_map_apply_real` 专门核对

当前 mathlib 源码中的 `PMF.map_apply f p z` 给 `∑' h, if z = f h then p h else 0`；`PMF.filter_apply hs h` 给 `S.indicator p h * (∑' a, S.indicator p a)⁻¹`；`PMF.toMeasure_apply_fintype p S` 给有限指示函数和。所需有限性、可测单点和 Classical 实例在该上下文中具备。

有限和展开与分配后，逐项目标正是：左边在 `z=f h` 时取 `I_S(h)p(h)·D⁻¹`，否则为零；右边取 `I_{S∩{f=z}}(h)p(h)·D⁻¹`，其中 `D=Σ_h I_S(h)p(h)`。按 `h∈S` 与 `f h=z` 的四种情形成立。代码的 `eq_comm` 处理 map 中反向等式。

支撑 API 的顺序也正确：map 见证给 `f h = z`，filter 见证给 `h∈S ∧ h∈p.support`。`ENNReal.toReal_div` 本身无额外条件；条件分布合法性仍来自真实 `hs`。`FiniteProbabilityRow.ofRealRow` 已由真实 import 链进入环境。

未发现可静态断言的错误签名。以下是未运行的 elaboration 检查点，**不是已观察失败**：

1. map/filter 展开后的 `tsum_fintype`、`Finset.sum_mul` 与 `Finset.sum_congr rfl` 的匹配顺序；内层 filter 分母应在展开 filter 后归约。
2. 定义内与局部 `let hs` 的证明无关性是否足以直接 `change`。
3. 安全子类型有限实例、`ofRealRow` 隐式参数与零时刻 `rowApply` 单位矩阵有限和的 `simp`。

`rw [← Finset.sum_div]` 的方向正确：逆向把商之和合并成和除以常数。`ENNReal.toReal_eq_toReal_iff'` 的 `.1` 方向正确，且已给 PMF 原子非顶性。若聚焦编译在上述局部匹配处报错，应修展开或显式实例，保留现有量词和实际构造；不应加入来源等式假设。

## 5. 既有依赖与下一门槛

已只读核对来源桥第 2 次、K1 第 10 次的实际收据、源码、olean 和日志哈希。两收据都记录 exit 0；实际日志打印的关键端点公理仅为 `propext`、`Classical.choice`、`Quot.sound`。

K1 当前源码 SHA256 为 `fa4f5ce017d6bfa4d9f3fe77805ad629f1c04f34a7ac3495c9114c432bc6c826`；实际日志 SHA256 为 `cb1c77ddde8702fae626aad9b7ac6de6a079cf3e6cf71e21287c6c48430f5862`。本审查仅复用这些私有依赖证据，没有重跑它们，也没有因此把 K2 标为通过。

下一必要步骤由根安排：用两个已通过私有模块的正确 olean 搜索路径，对此精确 K2 源码做独立聚焦编译并保留新日志与实际公理输出。本静态审查不替代 canonical 发布门槛，不要求重跑全库 build，且发布/native 继续优先。
