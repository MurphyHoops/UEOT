# 有限首次退出质量：同源接口与静态证明草稿

状态：**完整静态草稿，未编译；独立审查待根智能体与 C 完成。** 没有修改 K1、K2、生产、书稿或 Git，没有运行 Lean、build、native 或数值试验。此批不进入当前冻结七模块的发布范围。

## 1. 精确对象与结论

沿用 K1 的有限状态 X、有限非空行动 A、任意观察类型 Y，固定实际模型 M、观察映射 q、当前观察平稳随机策略 sigma，以及**任意**原初态 PMF p0。安全集 K 可以为空。所有历史法则使用同一个

```lean
L := riskMicroControlKernel q (fun _ => M.transitionPMF)
  (observationMarkovPolicy sigma)
nu n := causalLaw p0 L n
Q := killedMatrix M (liftedStationaryPolicy q sigma) K
eta0 := safeInitialRow p0 K
eta n := rowApply eta0 (Q ^ n)
```

这里 eta0 是原 p0 对安全子类型的未归一化限制；没有条件化初态，也没有用另一份矩阵代替真实 Q。记

\[
S_n=\{X_0,\ldots,X_n\in K\},\quad
s_n=\nu_n(S_n),\quad
d(u)=1-\sum_{v:K}Q(u,v).
\]

拟议接口给出

\[
s_n-s_{n+1}
=\sum_{u:K}\eta_n(u)d(u)
=\nu_{n+1}\bigl(S_n\text{ 的前缀}\;\cap\;\{X_{n+1}\notin K\}\bigr).
\]

右端是**第 n+1 步同一原始含行动记录**上的首次退出事件。由于 S_n 包含从时刻零到 n 的全部安全，不会把较早失败、后来返回 K 的路径再计作首次退出。

最后对每个 `T : ℕ`：

\[
1-s_T=(1-p_0(K))+
\sum_{n<T}\sum_{u:K}\eta_n(u)
  \left(1-\sum_{v:K}Q(u,v)\right).
\]

同时给出实际事件形式

\[
\nu_T(\text{截至 T 已失败})
=p_0(K^c)+\sum_{n<T}\nu_{n+1}(\text{此步首次退出}).
\]

各项的记录空间随 n 变化，但它们来自同一个递归路径法则，真实前缀一致性在草稿内推出；不是把不同源或每个时域另选策略的概率拼接求和。

## 2. 前缀一致性不是假设

新增的最小通用接口是

```lean
theorem pmfExtend_map_fst
    {H Z : Type*} (p : PMF H) (L : H → PMF Z) :
    (pmfExtend p L).map Prod.fst = p
```

直接展开已有 `pmfExtend`，依次复用 `PMF.map_bind`、`PMF.map_comp`、`PMF.map_const`、`PMF.bind_pure`。不需要有限性、平稳性、可测结构或额外来源相等前提；没有重写大型路径归纳。

再由 `causalLaw` 的一步递归直接得到

```lean
(causalLaw p0 L (n + 1)).map
  (fun h : CausalHistory H Z (n + 1) => h.1)
  = causalLaw p0 L n
```

有限历史上的实概率版本复用 `PMF.toMeasure_map_apply` 与 `ENNReal.toReal`，把任意前缀事件 E 的质量从 n+1 步法则推回 n 步法则。可测性由有限历史和可测单点实例给出，没有更改原测度结构。

这个通用前缀引理允许一般历史依赖的 L；后续固定矩阵 Q 的质量公式仍按 K1 要求使用时间齐次当前观察策略。不能把前缀引理的较宽范围传播成未经证明的任意历史策略固定矩阵接口。

## 3. 两条短证明路线在实际事件处汇合

| 草稿端点 | 复用与作用 |
|---|---|
| `row_mass_sub_next_eq_killedExitFlux` | 任意有限实数行/矩阵的双重求和换序及分配律，证明行质量减下一步质量等于行缺口加权和；本身没有概率语义 |
| `killed_pow_mass_drop` | 复用既有 `QSDPerron.rowApply_mul` 与 `pow_succ`，不需要 QSD 或特征关系 |
| `actual_survival_drop_eq_killedExitFlux` | 对 n 与 n+1 各调用 K1 公开 `actual_survival_mass_eq_killed_pow_sum`，连接真实 s_n 与代数质量差 |
| `actual_first_exit_mass_eq_survival_drop` | 在同一 n+1 步记录空间中，前缀安全事件不交分成继续安全与首次退出；复用实际前缀恒等式和 `measureReal_union` |
| `actual_first_exit_mass_eq_killedExitFlux` | 合并前两条路线，得到实际首次退出质量的精确矩阵公式 |
| `actual_killedExitFlux_nonneg` | 从已识别的真实事件概率非负性推出，无需假设 η_n 非负或直接把 flux≥0 放进前提 |
| `actual_survival_zero` | 由 `causalLaw` 与 `riskEverFailure` 在零时刻的定义得到 `s_0=p0(K)` |
| `actual_failure_mass_telescope` | 复用已有 `Finset.sum_range_sub'`，保留 `1-p0(K)`；没有再做一份望远镜归纳 |
| `actual_failure_eq_initial_failure_add_first_exits` | 复用 `probReal_compl_eq_one_sub`，给出原失败事件的初始失败＋首次退出分解 |

事件分割利用的精确集合恒等式为

\[
\{h:S_n(h.1)\}
=S_{n+1}\;\dot\cup\;
\{h:S_n(h.1)\land X_{n+1}(h)\notin K\}.
\]

没有把“当前在 K”与“从初态起一直在 K”混同，没有要求退出后吸收，没有把返回路径从真实模型删去。

## 4. 边界与量词

- **T=0：** 求和为空，右端仅为初始失败 `1-p0(K)`，与原风险事件的时刻零定义一致。
- **n=0：** 第一项 flux 是初态在 K 且第一步离开 K 的概率；初态已在 K 外的质量不进入该项。
- **K 为空：** η 的有限和和全部 flux 均为零，s_n 均为零，失败概率为一。没有 `[Nonempty K]`。
- **初始失败存在：** η0 可能总质量小于一；全程保留原 p0，不能通过先条件化到 K 消去失败质量。
- **零存活：** 质量公式、事件身份和望远镜分解全部可用，没有除法、正生存前提或 QSD 输入。
- **观察类型：** 不要求 `[Fintype Y]`；有限状态/行动要求与 K1 保持一致。
- **真实来源：** M、q、sigma、p0 在所有 n 中相同；没有每个时域各取一份策略再接成路径的量词交换。
- **有限窗：** 当前结果不声明真实无限路径的存在、极限事件身份或无限存活。C 已找到的 `survivalProb_tendsto_neverHitProb`、`homTrajMeasure` 前缀与初始混合接口留给下一条实际来源适配，不重建这些成熟理论。

## 5. 下一步执行门槛

本文件与 `SameSourceKilledExitFlux.lean` 一起冻结供根智能体和 C 审查。K1 的执行状态由根智能体的实际收据决定；本批没有借用 K1 或 K2 的任何编译状态来宣称新草稿已通过。

静态草稿所有拟议声明都有证明体，且未加入公理或占位证明。实际编译仍可能暴露局部记号、递归历史类型、可测实例或 `rw` 的 elaboration 问题；修复只能保持这里的原始来源、事件、量词与初始失败项，不得添加“前缀身份”等本应内部推出的假设。
