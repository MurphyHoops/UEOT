# 全局数学回顾与同源存活尾

本包在真实 `main@2051db2d6322e2cf5e131ab4f9b07591f2cabe6e` 之后新增，不覆盖既有 Stage1–7。任务沿用 #146 / #302。

## 从这里阅读

1. [全局数学回顾与接下来的证明任务](GLOBAL_MATHEMATICAL_REVIEW.md)：完整 Core 六大块、MINCORE/H0/P-ID/TheoryCompletion、C1–C7 的现行缺口与准确优先级。
2. [同源尾的实际 Lean 收据](tail-proof-v1/COMPILE_PASS.md) 与 [独立执行审查](independent/TAIL_EXECUTION_CLEAR.md)：一个新端点第 1 轮实际 PASS，8.895 秒，标准三公理。
3. [所有有限时域到同一个无限策略的合同](independent/FINITE_BELIEF_INFINITE_POLICY_CONTRACT.md)：固定非自治来源的无限一致选择、支持齐次下的有限记忆、固定点稳定界及必要反例。数学论证完成，新 Lean API 尚未实现。
4. [精确 PMF 记忆见证](root/belief_memory_witness.py) 与 [实际输出](root/BELIEF_MEMORY_WITNESS.json)：两状态恒定观察模型中，有限支持记忆可全时认证，固定当前观察随机反馈不可能同时认证第 0、1 步。
5. [两部书的整体回顾](books-global/GLOBAL_REVIEW.md)、[完整来源映射](books-global/SOURCE_MAPPING.md) 与 [具体书稿修订](books-global/NEXT_TASKS_AND_PASSAGES.md)。逐探针数学合同以 [第二版](books-global/SISC_PROBE_CONTRACT_V2.md) 为准；它替代前一文档 §2 的初稿，保留初稿及 `sisc-contract-review/INITIAL_FINDINGS.json`，补齐源均值、现有风险定义、非空探针及竞争者量词的 API 绑定。该适配仍待实现。
6. [交接](HANDOFF_2026-10-21_GLOBAL_REVIEW.md) 与 `chain-integration/`：已存在的源码桥、下一组生产接口及实际策略扩张的证明义务。

## 新证明及范围

对同一有限模型 M、观察 q、时间齐次当前观察随机反馈 σ、原始 p₀ 和安全集 K，从同一实际闭环构造 killed 矩阵 Q 与未归一化安全初始行 η₀。新端点证明

\[
\eta_0Q^n\mathbf1\longrightarrow
\Pr_{p_0,M,q,\sigma}(\forall n, X_n\in K).
\]

时刻 0、初始失败、空 K、零存活均保留。无额外来源等式、正存活、QSD 或初始全安全假设。实际编译与审查绑定完整生产输入、旧私有链及实际导入，不将本包的归档视为生产 import。

当前生产仍为 666=655+11，冻结 P-ID 分类仍为 11/89/6。全局统一闭合仍未建立；#302 保持 OPEN。两部已出版著作仍为哲学 82 页、数学 168 页，没有为研究状态变化重编。

## 证据的使用方法

`ARCHIVE_MANIFEST.json` 逐项记录原执行位置、归档相对路径、大小与 SHA256，所有归档输入逐字复制。原 STATUS/PENDING、准备阶段元数据失败及实际编译日志保持原样；后续 PASS/CLEAR 是单独收据。复用 [先前 Stage7](../source_path_research_v1/README_STAGE7.md) 和生产接口证据，不复制或重做它们。

作者 runner 中的绝对路径是实际执行现场。私有模块依赖的已编译 olean 由收据绑定，但编译二进制不提交。复现时须按记录重建相应依赖和搜索路径；不能在缺少旧私有链的环境中直接将本目录解释成独立生产模块。

本包只新增研究文档、源码快照、精确例子和审查。生产、既有文档、消费者、工作流、冻结账本、书稿与 QM/physics 不在本次修改范围。实际 canonical 授权、Git 对象检查、PR 和 resulting-main 验收由本包之后的发布收据记录，不用私有 Lean PASS 代替。
