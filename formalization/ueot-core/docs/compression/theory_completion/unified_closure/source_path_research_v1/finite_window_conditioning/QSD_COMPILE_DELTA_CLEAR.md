# 同源 QSD：实际编译与 K2 复用增量独审

**状态：QSD_COMPILE_DELTA_CLEAR_PRIVATE_FOCUSED_PASS_NOT_INTEGRATED。** 当前作者冻结的源码与实际第 004 轮执行一致，原 10 个公开端点全部保留，新增三个边界命题正确地复用一般 K2。未发现需要阻塞本私有研究结果的数学或证据问题。

原 V1 的独立静态审查来自 `/root/books_resume`；本报告由 `/root/audit_resume` 对 `/root/math_resume` 的后续实现、精确差异和真实执行增量作审查。它保留原静态收据，不重写原稿、原失败或旧清单。

## 身份与实际执行

| 对象 | SHA256 |
|---|---|
| 原 V1 源码 | `7eaf7716d0b16ee69e27d73b074b335136506deee44c27809ae2e27056d6e933` |
| 实际通过源码 | `be6c14557d455e8e4c6d752bb9255388a4dc5a561a85bf96112fbfba604f66ed` |
| 实际 `.olean` | `bb6a4eca21084acc86989ebf9cd509291cd72feb7f8480eecc7a6fe41258a67d` |
| 第 004 轮日志 | `a735c829497b4a5be6a1099dde7157d2695adfad48ca2550d814a06bab08884b` |
| 第 004 轮状态 | `a777b710788de5eaea4b4af40e82b90989746083891c3559b2941b2a03d23d09` |
| 作者完整执行收据 | `d20752b052559201871284168aeb4bf9279d71d279f0032008f301888191c8be` |
| 当前增量合同 | `470b071f0115c4543996466ef17872ebbb28f853c4c836f23e1f6bb28c8d8e86` |

实际第 004 轮退出码为 0、耗时 6.526 秒，未超时。当前源与该轮输入快照相同。来源桥、K1、一般 K2 的三个源码和三个 `.olean` 共六项 pin 都与执行收据相符；已通过的一般 K2 独审绑定为 `92e4403a15a04d0b0b9bb8137d2e203d605278b4267c187214e4ff2821704084`。

10 个关键端点的实际传递公理闭包都仅包含 `propext`、`Classical.choice`、`Quot.sound`。此处不把十次实际 `#print axioms` 说成全量 native 声明审计。日志中的四组风格/未用变量警告不影响结果，也不需要追加编译。

前三轮分别保留实际 FAIL、退出码 1、源快照和原日志，耗时 6.390、6.436、6.132 秒；中间尝试的透明度选项和语法失败没有被藏掉，最终源码不含该选项。旧 `BINDING_MANIFEST.json` 中的历史 K1 pin 不被偷偷改写，当前六项真实依赖 pin 另由本次执行收据绑定。

## 端点和证明增量

独立提取并比较所有公开声明头：原稿的 10 个公开定理逐字保留；第 001 轮至第 004 轮的全部 13 个公开定理头也逐字相同。两个本地记号只将 dot notation 改为同一函数的显式应用。原稿未成功编译，故本报告不声称比较了原稿的 kernel 类型。

两条质量公式仍调用 K1 的真实事件质量等式和生产 `QSDPerron.leftPerron_pow` / `qsd_survival_mass_pow`。最终 `convert` / `congr!` 处理相同矩阵幂的可判定相等实例差异，没有增加数学假设。一般条件终态证明先调用 K2 的归一化行公式，再用实际联合质量与总质量消去同一个非零因子。

旧重复的 `filter_map_apply_real` 和 `survives_last_mem` 已从当前候选移除。实际过滤支撑由一般 K2 的 `actual_survival_pos_iff_support` 得到；完整条件终态 PMF 等式复用 `actual_conditioned_terminal_eq_normalized_killed_map`。原正特征值接口现在只是更一般当前正存活接口的适配，过滤事件及概率源没有变。

新增的三个实际端点分别为：

| 新端点 | 核验结果 |
|---|---|
| `actual_qsd_survival_pos_iff` | 先从同源次随机核及概率左行推出 `rho ≥ 0`，再证明实际正存活恰为 `n = 0 ∨ rho > 0`。 |
| `actual_qsd_conditioned_terminal_law_of_survival_pos` | 只要求当前真实生存质量正；结论是一般 K2 的实际过滤终态 PMF 等于真实初态 `r.map Subtype.val`。 |
| `actual_qsd_zero_root_no_filter_witness` | `rho = 0` 且 `n ≠ 0` 时，利用同源实际零质量和一般 K2 证明没有过滤支撑见证。 |

## 保留的数学边界

唯一 killed 核是 `killedMatrix M (liftedStationaryPolicy q sigma) K`，真实初态明确是 `r.map Subtype.val`。`safeInitialRow_map_subtype` 证明初始限制行身份；没有输入另一来源相等作为假设。给定左特征关系后，真实联合质量和总质量分别为 `rho^n*r(v)` 与 `rho^n`，且无需先要求 `rho > 0`。

`n = 0` 时总生存质量为 1，包含 `rho = 0`；正时间零特征值则不能条件化。`r : PMF K` 或归一化实数行本身不能在空安全集中提供，不能据此给一般 K1/K2 添上非空安全集限制。对于任意其他既定初态，应继续用一般 K2 的 `eta0 Q^n/s_n`，不能为了分析把真实初态换成 QSD。若将来接入候选初态族，必须确实部署所选 `r_c.map`。

策略始终是同一个时间齐次当前观察随机 `sigma`。一般因果策略和 `viableFamilyPolicy` 没有被自动 Markov 化；需要的策略等式或状态扩充来源桥仍是独立义务。没有证明 QSD 存在、唯一、吸引，也没有把条件终态不变提升成完整有限窗条件路径等于齐次 Doob 路径或无限存活。

## 验收范围

本收据关闭本私有 QSD 特化的实际编译增量审查。没有执行新的 Lean、build、native、测试或远端操作，未修改生产、消费者、书稿或 Git。当前七模块发布与其 92 项 native 范围不变；私有研究的生产集成、公开声明注册及 canonical/resulting-main 验证以后由根分别安排。
