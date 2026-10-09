# UEOT–UMC V4 | 同源跨层可行性固定点与组织充分态研究

日期：2026-10-09。Track TC / Issue #302。本地分支 compression/theory-completion-unified-local。继承 main@6fa4c39d2a41f1563ba75c277b7112b61b2799db。研究仅本地，不 push，不改冻结 106 Core 与四个 counted generators。

## 核心判断
V2 找到有限随机核的未来响应零空间和可辨识条件；V3 从同一 K 构造精确预测/控制商，传递最优值，并证明给定维持策略的安全有限路径。本轮精确消除了「先给定维持策略」的前提：从真实精确控制商的动作/转移核及预注册安全域，反向推导有限时域最大生存可行域、有限步固定点、维持行动与微观路径不变性。这是条件数学结果，不是自创生或物理生命发现。

## 数学主链
同一微观源 K + 已注册 read/probe + 未来类指标线性可重构
→ SISC 强可合并、唯一归一预测商 Kbar（V2）
→ 已证明的精确 P-QUO 控制商，微/宏最优值保持（V3，reward 仍需可下降）
→ V_Y(0)=safe，V_Y(n+1) = safe ∩ {c: 存在行动 a，使所有正概率后继属于 V_Y(n)}
→ 对所有 n,x，V_X(n,x) 当且仅当 V_Y(n,q(x))（本轮 Lean）
→ Y 有限，至多 card(Y) 次迭代稳定；稳定集为 safe 内最大的受控不变子集（本轮 Lean）
→ 可从稳定集构造 sigma:Y→A，而不再将 sigma 作为外给输入
→ 按此 sigma 采取的每条真实微观正概率有限路径留在最大稳定集的 q-逆像。

新增 Lean：ViabilityKernelIntertwining.lean；所有定理、固定点和策略构造已单文件编译；TheoryCompletion 公共根新增 import。
非空正例与负对照：ViabilityNonvacuityWitness.lean。真实四微状态 Bool×Bool、两动作 Bool、行动固定可见后继，隐藏后继两个值各 1/2，因此非 Dirac；可见商两个态。safe=visible true，true 行动永久可维持，false 行动会导致 unsafe。Lean 已单文件编译；不是单动作或空安全集玩具。

## 用 UEOT 研究 UEOT 的结构启发
- 对象：需要区分每项表示是否真正保存组织、预测、目标、材料/程序和身份信息；不是一个能预测未来的单字段 token。
- 跨层：只有带源同步、接口保真与真正商闭合的映射才允许携带证书；X→Y→Z 控制塔不能冒充任意物理 RG。
- 动力学与组织维持：加入维持行动的存在性与最大可行域，不再仅验证给定政策后的被动安全，但 safe 的物理来源仍外加。
- Π/Φ 与 GOD/GOA：低秩不识别两种独立机制；硬可行性不同于最优折扣回报、GOA/QSD 和自主目标来源。
- Omega：冻结对象的失效集/超图、修复和资源流程需要合法的组成机制。形式依赖图的循环不是物理 Omega-loop。

## 全库复用与审核边界
前期全库 618 源文件结构扫描属于 import/定理元数据全覆盖，不是逐行人工复核。重点阅读家族：RecursiveSufficientState、SISC Future/Quotient/Nullspace/NoGo、FiniteDiscountedExactQuotient、PredictiveOptimalControlLift、SameObjectViableGOA、Objecthood/JointHomeostasis/RepairLawSelfReconstruction/OntogeneticConstruction、P12 Autopoiesis、CrossTrack/Scale、SISC 采样和 C5/C6 机制 no-go。已有的强组织模块不可被一阶 viability 集合替代。

## 原创性与未闭合的边界
有限概率双模拟、分割细化和有限 MDP 的最大受控不变核是先前数学和验证领域常见结构；本轮不能声称发明这些基础定理。新贡献是同一个 UEOT 实际 K 的 SISC→P-QUO→最大可维持核的严格类型化连接及旧前提减少。没有从 K/read 推出完整 Omega 物理材料、自主 repair 程序、provenance、目的生成或普适双驱动；自创生 P12 保持 PARTIAL，外部实证 UNVERIFIED，独立评审 PENDING。

## 下轮唯一优先难题：最小组织充分态（Constitutive Closure）
给定 K 和受保护的输出、奖励、资源、安全、程序及来源接口，从它们生成初始分割；对每个动作检查进入当前各类的真实概率；若类内转移质量不同，则细分并迭代到稳定。证明该分割算法有限终止、各接口保真、强可合并、并且是最粗的合法稳定精化。identity 极限不等于成功发现非平凡对象。物理 provenance 若不是 x 的函数，须先历史增广或证明不能识别，不可将来源标签偷偷写入当前态。

将该稳定组织商与本轮最大维持核组合，研究两个闭包/固定点算子何时相容；负例使用同源隐藏记忆奖励失真和六态混合别名。具体源模型和统计采样须保留独立来源与置信误差预算。

## 验收状态
单文件 Lean 编译：ViabilityKernelIntertwining 和 ViabilityNonvacuityWitness 均 PASS。全库 build 在本轮先对第一个导入版成功完成 9325 jobs；新正例也应随最终公共导入重新执行全库和标准公理检查。没有远程推送、PR、Issue 更新。本地报告为版本化新证据，不更改 UMC V1-V3 历史回执。
