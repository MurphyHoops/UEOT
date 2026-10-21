# 有限首次退出草稿独立静态审查

结论：**STATIC_MATHEMATICAL_SCOPE_CLEAR — NOT_COMPILED**。审查限于真实前缀、同一记录中的首次退出、初始失败、空安全域、任意初态与矩阵方向。没有运行 Lean，没有修改候选、生产或书稿，也没有审读或代替另一工作者负责的无限存活推导。

## 身份

- 冻结源码 `SameSourceKilledExitFlux.lean`：`8f88617f06f793492b04b875d38dbc097b7043bbe9ef12567b8492cb1eaf3c8c`。
- `BINDING.md`：`1a10f3505cbd5519be0c9f075c8df06d6d3ec00adf6e490a3f4c26c6679b95ad`。
- `DRAFT_MANIFEST.json`：`dc57437056e1bd3245c2a8435bd98ac4e24dbfebeed8efdccd1e1716b9ecf8a7`。

上述文件完整读取并另存快照。清单所列 11 项输入的当前 SHA 和字节数全部匹配；实际使用的 K1 总质量端点签名与其固定文本相同。K1 现有独立聚焦通过收据可以绑定该依赖，但不能证明本文件已经编译。

## 逐项审查

| 检查项 | 判断 |
|---|---|
| 实际前缀来源 | 原 `pmfExtend p L` 定义为先按 p 取 h，再按 L(h) 取 z，并保留 (h,z)。草稿依次使用实际 `map_bind`、`map_comp`、`map_const`、`bind_pure`，从构造内部推出 `map Prod.fst = p`。没有以目标前缀等式为假设。 |
| 有限路径一致性 | `causalLaw_map_prefix` 使用同一 p0、同一完整 L 的递归一步。实际事件质量版本再通过 `PMF.toMeasure_map_apply` 推出，有限单点可测条件充分。一般前缀引理允许历史依赖 L，固定 Q 公式仍保留 K1 的平稳当前观察范围。 |
| 同一 n+1 记录 | `riskFirstExitAfter K n` 定义在原含行动记录的 `CausalHistory X (A × X) (n+1)`，要求整个 n 步前缀从时刻 0 起安全，且新增状态在 K 外。它不是跨样本事件，也不把以前退出后返回的路径重新计作首次退出。 |
| 概率分割 | 在同一 `nu (n+1)` 上，安全前缀事件等于下一步仍安全与首次退出的不交并。草稿内部证明集合身份及不交性，使用概率测度的有限实质量可加性，再用已经推出的前缀身份，得到首次退出质量为 s_n−s_(n+1)。 |
| 行列方向 | 已有 `rowApply eta Q v = Σu eta(u)Q(u,v)`。Q(u,v) 的行 u 是出发状态，缺口使用 `1−Σv Q(u,v)`；`pow_succ` 与 `rowApply_mul` 给出 `(eta0 Q^n)Q`。双和换序及缺口加权方向正确，没有转置或使用列缺口。 |
| 代数与实际事件 | 有限实行/矩阵的质量差恒等式本身不要求概率条件；实际接口由 K1 把同源 s_n 连接到 eta0 Q^n，再与真实首次退出事件相等。非负性从这份事件概率推出，不是另加 flux≥0 前提。 |
| 任意初态与时刻 0 | p0 始终为同一任意原初态，eta0 是未归一化安全限制。s_0=p0(K) 从真实定义推出。最终分解保留 p0(Kᶜ)，不先条件化初态；n=0 的首次退出只计初态安全而第一步离开的路径。 |
| T=0 | 有限和为空，原风险的失败质量就是 p0(Kᶜ)，与包含初态的 `riskEverFailure` 一致。 |
| 空 K 与零存活 | 未要求 `[Nonempty K]`。空安全子类型的行和及 flux 均为零，K1 的 s_n 也为零，失败质量为一；零存活时公式继续有意义，没有除法或正概率前提。 |
| 固定来源与有限窗 | 所有 n 共用同一 M、q、sigma、p0。不同长度历史上的求和通过实际前缀构造连接，没有逐时域重选策略。源码没有无穷路径、无限存活、QSD 或 Perron 结论。 |

## 复用核对

实际读取了生产 `PathError.pmfExtend` / `causalLaw`、`QSDPerron.rowApply` / `rowApply_mul`、`MicroscopicFailureRisk.riskEverFailure` 的定义，以及已钉住 mathlib 中 PMF 映射与绑定、`measureReal_union`、`probReal_compl_eq_one_sub` 的声明。有限望远镜使用的 `sum_range_sub'` 对应同一文件中 `prod_range_div'` 的 `to_additive` 生成声明；方向确实是首项减末项。没有另造路径概率实验或重建一般极限理论。

## 验收边界

无必须修正的数学命题或假设。拟议证明路线与现有接口一致，实际 elaboration、内核检查及公理闭包仍为 **NOT_COMPILED / NOT_EXECUTED**。后续若只修局部重写或实例推导，应保持已审声明、原 p0、真实 prefix 证明和初始失败项。任何命题或来源前提变化须重新报告；本收据不能替代真实聚焦执行。
