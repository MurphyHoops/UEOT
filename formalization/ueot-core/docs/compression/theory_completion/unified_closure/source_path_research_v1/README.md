# 同源风险路径、killed 矩阵与后续条件生存研究

本目录接续已发布的接口研究，维护下一批数学来源桥。这里的 Lean 文件是独立研究候选，没有加入 UEOT 生产 import 根，不计入当前七模块候选的 666 个生产模块或 native census。

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
| [QSD 绑定草稿](qsd_binding_draft/SameSourceQSDBinding.lean) | 数学与来源静态审查 CLEAR；未编译 | 一般初态条件律、Perron 数据存在性、任意初态正存活 |
| [首次退出草稿](exit_flux_draft/SameSourceKilledExitFlux.lean) | 真实前缀、事件分解与有限望远镜的独立静态审查 CLEAR；未编译 | 已取得 Lean PASS 或无限时间结论 |
| [无限存活的有限支撑判据](infinite_survival/FINITE_SUPPORT_AND_INFINITE_SURVIVAL.md) | 完整数学推导与有限性反例，独立数学审查 CLEAR；尚未形式化 | 新 Lean API、已连接当前有限记录与无限轨迹 |

QSD 草稿早期任务名中的“K2”是工作标签。按已审 [CONTRACT_KILLED v2](source_bridge/CONTRACT_KILLED.md) 的编号，它对应 K3，以及 K2 在 QSD 初态下的特化。任意初态、仅假定当前生存质量 \(s_n>0\) 的一般 K2 仍待形式化。其统一的 \(\rho>0\) 条件也没有覆盖 \(n=0,\rho=0\) 的合法条件化特例。

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

先完成一般正存活条件律，再验证 QSD 特化和首次退出草稿。首次退出目标是把

\[
s_n-s_{n+1}
=\sum_u(\eta_0Q^n)(u)\left(1-\sum_vQ(u,v)\right)
\]

识别为同一 \(n+1\) 步实际记录的首次退出事件质量，继而得到

\[
1-s_T=(1-p_0(K))+\sum_{n<T}\mathrm{flux}_n.
\]

真实无限路径已有可复用的尾极限、初态混合和首次命中接口；详见 [API 映射](exit_flux_reuse_mapping/API_MAPPING.md)。需补当前完整记录与同源无限路径的来源连接。不能以单个时刻边缘相等替代整段前缀身份，也不能把有限时域各自选择的策略当成一个固定无限策略。

有限支撑推导进一步区分固定策略的概率一安全、严格正概率存活、受控可行核和观察反馈可实现性。它服务于已有全时域安全理论的统一，不把成熟生产结果重新列作空缺。

## 归档与集成范围

[STAGE1_ARCHIVE.json](STAGE1_ARCHIVE.json) 和 [STAGE2_ARCHIVE.json](STAGE2_ARCHIVE.json) 绑定实际复制的源文件及收据；复制均按字节核对。原始执行文件仍在当次临时目录。olean 不作为生产源码提交，其实际哈希保留在通过收据中。

原清单保持历史身份。特别是 QSD 草稿的原清单记录了 K1 的一个执行修复中间版本；独立审查已明示这一差异，最终 K1 的定义和接口不变由后续增量收据确认。没有修改原清单使其伪装成后来版本。

本研究分支以实际 main e9b61ca9c35955028c4bfa425dfa278fd1864029 为当前本地父基线。它包含并保留其他工作者已经合并的 QM 内容，本研究没有编辑该范围。Core 七模块、消费者授权和两部书稿的发布仍由各自独立分支完成；此目录不替代那些发布门槛。

独立后续收据：[首次退出静态审查](reviews/exit_flux/REVIEW.md)、[无限存活数学审查](reviews/infinite_survival/REVIEW.md)。原始数学草稿中的待审措辞作为当时状态保留，以这些另写收据记录审查完成。无限存活审查补充了精确的观察纤维共同安全动作条件：要求存在共同反馈，不要求某个任意选出的反馈恰好因子化；闭合须对完整原核 L 检查，安全可达须限制在 killed 子类型 Q 中。
