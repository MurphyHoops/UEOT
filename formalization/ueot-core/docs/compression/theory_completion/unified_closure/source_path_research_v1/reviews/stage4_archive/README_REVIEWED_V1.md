# 同源风险路径、killed 矩阵与后续条件生存研究

本目录接续已发布的接口研究，维护下一批数学来源桥。这里的 Lean 文件是独立研究候选，没有加入 UEOT 生产 import 根，不计入 #357 已合并的 666 个生产模块或其 native census。文档进入 main 与其中的私有 Lean 文件进入生产是不同的集成范围。

## 已完成的实质连接

固定同一个有限控制模型、原始初态、任意观察映射和时间齐次当前观察随机策略。动作擦除桥先证明：原风险实验的完整动作—状态记录，擦除动作后等于同一闭环生成的完整状态记录。随后 K1 从该闭环内部构造安全限制矩阵 \(Q\) 与不归一化的初始安全行 \(\eta_0\)，证明

\[
\Pr(X_0,\ldots,X_n\in K,\ X_n=v)=(\eta_0Q^n)(v),
\qquad
\Pr(X_0,\ldots,X_n\in K)=\eta_0Q^n\mathbf1.
\]

核、策略和初态的身份由定义与证明给出。K1 没有外加所需路径等式、初始安全支撑、正存活、QSD、不可约性或安全集非空前提；空安全集、时刻零、初始失败以及退出后返回均按原事件语义处理。

## 实际成熟度

| 项目 | 当前证据 | 仍未声称 |
|---|---|---|
| [动作擦除来源桥](source_bridge/SourcePolicyPathBridge.lean) | 私有 Lean 第 2 轮实际 PASS；两个终点标准三公理；独立执行绑定审查完成 | 任意历史策略的状态 Markov 化；动作相关事件自动因子化 |
| [K1 同源 killed 路径](killed_path/SameSourceKilledPath.lean) | 私有 Lean 第 10 轮实际 PASS，exit 0，81.381 秒；三个终点标准三公理；独立增量审查 CLEAR | 已进入生产、全量 native 比较、canonical 合并或无限路径身份 |
| [一般 K2 条件终态](conditioned_terminal/SameSourceConditionedTerminal.lean) | 私有 Lean 第 4 轮实际 PASS，7.238 秒；五个指定端点标准公理；独立增量审查 CLEAR | 任意初态下条件律不变、完整条件路径或生产集成 |
| [同源 QSD 特化](qsd_binding/SameSourceQSDBinding.lean) | 私有 Lean 第 4 轮实际 PASS，6.526 秒；十个指定端点标准公理；独立增量审查 CLEAR | QSD/Perron 数据存在性、完整有限窗 Doob 路径恒等式 |
| [实际首次退出](exit_flux/SameSourceKilledExitFlux.lean) | 私有 Lean 第 3 轮实际 PASS，7.091 秒；十个指定端点标准公理；独立增量审查 CLEAR | 已进入生产、无限时间或任意历史策略的齐次矩阵公式 |
| [无限存活的有限支撑判据](infinite_survival/FINITE_SUPPORT_AND_INFINITE_SURVIVAL.md) | 完整数学推导与有限性反例，独立数学审查 CLEAR；尚未形式化 | 新 Lean API、已连接当前有限记录与无限轨迹 |
| [有限窗条件路径与 Doob 边界](finite_window_conditioning/FINITE_WINDOW_DOOB.md) | 同源三状态反例、完整时变条件核及精确有理数核对；数学审查 CLEAR | Lean 已证明完整条件路径分解或一般 Q-process 极限 |

QSD 草稿早期任务名中的“K2”是工作标签。按已审 [CONTRACT_KILLED v2](source_bridge/CONTRACT_KILLED.md) 的编号，它对应 K3，以及 K2 在 QSD 初态下的特化。现在一般 K2 已对任意实际初态、当前 \(s_n>0\) 证明：先过滤原实际生存事件再取终态的 PMF，等于归一化 killed 行 \(\eta_0Q^n/s_n\) 的包含映射推前。QSD 直接复用该接口，证明正存活当且仅当 \(n=0\) 或 \(\rho>0\)，并保留 \(n=0,\rho=0\) 的合法条件化情形。原未编译稿及当时的静态收据仍在 `qsd_binding_draft/` 与 `exit_flux_draft/`，不改写为后来通过的执行。

这些来源桥固定同一时间齐次当前观察随机策略。它们没有把一般因果策略或支持生存定理选择的 `viableFamilyPolicy` 自动识别为该策略；后续组合仍需实际反馈身份或适当的状态扩充。

## K1 的执行与审查

最终 K1 源 SHA256：

    fa4f5ce017d6bfa4d9f3fe77805ad629f1c04f34a7ac3495c9114c432bc6c826

三个终点的数学声明从初稿到最终稿逐字一致：

- state_terminal_mass_eq_killed_pow；
- actual_survival_terminal_mass_eq_killed_pow；
- actual_survival_mass_eq_killed_pow_sum。

独立审查还逐一确认了 4 个定义的全文和全部 13 个 theorem 声明不变。修复只涉及证明展开、私有 successor 引理的局部 elaboration 选项及实际公理打印。完整的通过收据、差异、日志和失败历史分别见：

- [COMPILE_PASS.md](killed_path/COMPILE_PASS.md) 与 [COMPILE_PASS.json](killed_path/COMPILE_PASS.json)；
- [原始证明差异](killed_path/PROOF_ELABORATION_DELTA.patch)；
- [第 10 轮实际日志](killed_path/lean-attempt-010/lean.log)；
- [独立增量审查](reviews/killed_implementation/COMPILE_DELTA_REVIEW.md) 与 [机器可读收据](reviews/killed_implementation/COMPILE_DELTA_REVIEW.json)。

第 1–9 轮失败日志、每轮源快照、初始 DRAFT 状态和原稿都保留。失败运行输出中的 sorryAx 仍按原日志保存，不冒充通过的公理闭包。最后一次成功运行输出中没有 sorryAx。

执行绑定还包括已通过的 SourcePolicyPathBridge 源与 olean、工具链、依赖锁文件、准确命令和当时的 full/native 执行门槛。本目录没有重新执行这些检查。

## 下一步证明工作的顺序

一般正存活条件律、QSD 特化和首次退出已经完成私有编译及独审。首次退出现在把

\[
s_n-s_{n+1}
=\sum_u(\eta_0Q^n)(u)\left(1-\sum_vQ(u,v)\right)
\]

识别为同一 \(n+1\) 步实际记录的首次退出事件质量，继而证明

\[
1-s_T=(1-p_0(K))+\sum_{n<T}\mathrm{flux}_n.
\]

该结论保留初始失败、空安全集、零时域及零存活；真实前缀一致性从 `pmfExtend` / `causalLaw` 构造推出。它不把退出后返回的终态分布当作首次退出事件。

下一步优先补当前完整记录与同源无限路径的来源连接，再接已有尾极限、初态混合和首次命中接口；详见 [API 映射](exit_flux_reuse_mapping/API_MAPPING.md) 与 [精确任务排序](next_steps/NEXT_MATHEMATICAL_TASKS.md)。这些无限路径理论已经存在，待补的是当前随机闭环的来源适配。不能以单个时刻边缘相等替代整段前缀身份，也不能把有限时域各自选择的策略当成一个固定无限策略。

完整有限窗条件路径可以独立推进。其条件初态为 \(\eta_0(i)H_T(i)/s_T\)，正条件前缀上的转移为 \(Q_{ij}H_{T-t-1}(j)/H_{T-t}(i)\)，其中 \(H_m=Q^m\mathbf1\)。已审反例证明：左 QSD 和正右特征向量同时存在，仍不能推出有限窗条件路径等于齐次 Doob 路径；本例的路径 TV 精确为 \(1/4\)。行动边缘也会被未来生存条件重加权，零分母不能解释成条件概率。上述完整有限窗公式目前是数学推导。

有限支撑推导进一步区分固定策略的概率一安全、严格正概率存活、受控可行核和观察反馈可实现性。它服务于已有全时域安全理论的统一，不把成熟生产结果重新列作空缺。

## 归档与集成范围

[STAGE1_ARCHIVE.json](STAGE1_ARCHIVE.json)、[STAGE2_ARCHIVE.json](STAGE2_ARCHIVE.json) 与 [STAGE3_ARCHIVE.json](STAGE3_ARCHIVE.json) 保留此前来源桥、K1 和静态研究的归档身份。[STAGE4_ARCHIVE.json](STAGE4_ARCHIVE.json) 另行绑定一般 K2、QSD、首次退出的实际源码与失败/通过日志、独立审查及有限窗数学推导。所有复制均按字节核对；原始执行文件仍在当次临时目录。olean 不作为生产源码提交，其实际哈希保留在通过收据中。

首次退出作者声明比较的三条记录曾在命名实参 `:=` 处提前截断。原记录保留；[新的完整声明增量审查](reviews/exit_flux_actual/COMPILE_DELTA_CLEAR.md) 独立核对了全部 15 个完整公开头与两个定义正文均不变。[窄范围后续核对](reviews/exit_flux_actual/RELATED_HEADER_COMPLETENESS_FOLLOWUP.md) 同时确认一般 K2/QSD 的旧比较记录完整。此证据补充没有改变源码或重跑 Lean。关键端点公理打印不代替将来生产集成所需的全量 native 审查。

原清单保持历史身份。特别是 QSD 草稿的原清单记录了 K1 的一个执行修复中间版本；独立审查已明示这一差异，最终 K1 的定义和接口不变由后续增量收据确认。没有修改原清单使其伪装成后来版本。

最初研究检查点的父基线为实际 main `e9b61ca9c35955028c4bfa425dfa278fd1864029`；后续文档重放到已验收的 #357 Core main `90cd0366b2120656dffbee025b5dc0c00d49b5a6`。完整生产源码、环境和依赖保持与这些私有执行的输入身份一致。本研究没有编辑 QM/physics；两部书稿仍由独立出版分支维护。此目录不替代生产注册、canonical 授权或 resulting-main 门槛。

整体理论与哲学反馈见 [共同结构、同一来源及下一阶段问题](philosophical_feedback/CORE_UNIFICATION_AND_PHILOSOPHICAL_QUESTIONS_2026-10-21.md)。它回顾 MINCORE、H0、冻结 P-ID 与 TheoryCompletion 的不同职责，保留已有全时域安全及同源 GOA，并将条件稳定、历史修复和意义的论证分别展开。

独立后续收据：[首次退出静态审查](reviews/exit_flux/REVIEW.md)、[无限存活数学审查](reviews/infinite_survival/REVIEW.md)。原始数学草稿中的待审措辞作为当时状态保留，以这些另写收据记录审查完成。无限存活审查补充了精确的观察纤维共同安全动作条件：要求存在共同反馈，不要求某个任意选出的反馈恰好因子化；闭合须对完整原核 L 检查，安全可达须限制在 killed 子类型 Q 中。
