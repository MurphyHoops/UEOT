# A：Core 到 SQLite 的有限映射

日期：2026-11-13。版本：A1；认证前独立审查。固定源 main `d30dae2a87150acddd67a3039ceccc4fe96d2b21`。**本次选用两项原则，不凑足三个；没有声称完成 SQLite 的 Lean 实例化。** C7 预注册与失败分类是方法规则，单列而不冒充第三项数学结果。

## 1. 两项确实使用的原则

### P1：声明观察相同不足以决定更强身份／历史谓词

**准确源。** `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCIdentityNoGo.lean`，`ObservationallyEquivalent` 行13—16，`equal_response_does_not_force_token_identity` 行18—24；`response_cannot_identify_sameObject_semantics` 行26—39。后者不作为本试验现实同一性定理。当前 successor §2.1 行25—37及范围决议 §1 行36—51要求对象角色及解释桥分开。[C1,C2]

**真实数学强度。** 第一个 Lean 命题是存在 `response : Bool → PUnit` 及不相等的两个 Bool，而响应相同的见证。它既不量化 SQLite 文件，也不证明任意观察均不可识别，更未证明旧备份已经产生。本次不以其标题代替领域证据。

**应用中的前提与反例责任。** 在同一完整业务合同 H 下，构造当前已确认数据库 D_new 与较旧但结构合法的 D_old；实际记录双方弱观察 O=(能打开、完整 integrity_check 输出)。只有测到 O(D_new)=O(D_old) 而 H(D_new)≠H(D_old)，才获得此任务的具体观察不足见证。两文件的内容区别、承诺历史及干预来源必须独立于最终标签记录；如果旧副本损坏导致弱观察不同，本次见证未实现，不能仍宣布成功。

**简短推导。** 若只依 O 的确定性判定器 f 能在两状态上精确给 H，则同一 O 要同时给不同结果，矛盾。因此同一弱观察不足以决定 H。随机化亦不能在同一输入分布上使两个相反真值都零误差。这个一般函数论推理不需要新增 Lean；实际两个 SQLite 状态是否满足前提由本轮数据检验。

**得失。** 支持更强观察的必要性；不证明候选优于拥有同样历史信息的标准基线，不支持普遍不可识别、所有未来不可预测或形而上学 token 身份结论。

### P2：同一源、权限、历史与实际费用的合同纪律

**准确源。** `constitution/UEOT_METHOD.md` 的 Shared-Source and Identity Discipline 行112—140；current successor §2.2 行39—45；范围决议 §6 行104—123。[C2,C3] 这是当前理论的消费者义务，不是一个由字段同名就成立的数据库定理。

**在本次完整履行的条件。**

| 所需条件 | SQLite 对应输入 | 当前证据身份 |
|---|---|---|
| 同一初态与转移机制 | 相同注册 schema／请求；真实 vendor SQLite、VFS、连接和事务控制；无其他写者 | 需运行日志及库／配置读回，不由版本名推出 |
| 同一故障源 | 进程门控、kill 接收与退出；独立登记旧备份替换 | 外加工程约定＋待检验；不冒充断电或WAL |
| 观察与历史权限 | 请求、实际收到 ACK、许可查询、完整／缺失标记 | 策略公共输入与 oracle 私有事件分离 |
| 同一允许动作 | 打开时自动恢复、读取、关闭、注册恢复／重试 | 自动恢复需双方共同计入；各用原始产物独立克隆 |
| 费用与到账 | 同一计数器、逐步允许条件、无隐含免费扫描、无事后充值 | 逻辑预算可做；硬件 I/O 严格界尚未建立 |
| 时钟与执行关系 | 事件序号、单调时钟、父实际接收、目标退出后复制 | 因果事件优先于单纯时间戳相近 |
| 身份与评价 | run／db／txn／payload／代次；明确已确认历史与允许状态集 | 研究者约定的任务身份；非本体数值同一 |
| 比较量词 | 固定场景与留出负载，同信息强基线 | 有限情形，不推出任意未来故障和所有算法最优 |

**被反驳的方式。** 额外 oracle、不同数据库克隆、先执行者的免费恢复、成本未记、丢失事件、目标判据事后改变，均可使源桥不成立。此时应撤回该比较结论；不能把不符合原假设的应用反例归于 Core 定理。

**明确排除。** 不借用再生人口的 `ValidIdentity` 来证明 SQLite 请求 ID 唯一，也不把 `ProgramPopulation` 当数据库程序内部性的证明。SQL 主键、域标签和请求内容的绑定是应用自己的输入条件与检查责任。

## 2. 两张真正的接口表

### 实际事实 → 分析输入

| 事实 | 输入 | 不能漏掉 |
|---|---|---|
| 源程序发出请求 | request=(run,db,txn,payload,effects) | schema与初态版本、所有注册请求 |
| 控制器收到成功 ACK | K+ 历史 | 接收与发送不同；成功须在COMMIT成功后 |
| 回滚／提交前门控 | K− 或仅oracle私有证据 | 暴露给策略的权限预先固定 |
| 未收到完整确认 | U | 不自动变成“未提交” |
| 已保存故障文件集合 | 每策略独立输入副本 | hot journal、退出顺序及打开前哈希 |
| SQL结果与错误 | 观察向量和完整性标志 | 错误／超时不能作为正常空表 |
| 计数器与动作 | 费用序列、剩余预算 | 覆盖范围、粒度、自动恢复开销 |

### 模型／策略判断 → 可核输出

| 判断 | 必须出现的证据 | 仍不能声称 |
|---|---|---|
| 业务合同 ACCEPT | 有效配置；完整观察；状态在许可集合；预算记录 | 每一个过去提交事件已唯一重建 |
| REJECT | 具体缺失ACK事务、错误内容、部分效果等见证 | 自动归因SQLite bug或Core错误 |
| UNRESOLVED | 指出哪一观测／预算／事件不足 | 用全部弃权冒充充分验证 |
| 与强基线等价 | 规则对应＋同输入判定／成本记录 | 本理论拥有新增控制能力 |
| 具体增益 | 同信息、同预算、同产物；预注册差异达到 | 普适UEOT定理或新数据库原理 |

## 3. 已检查但不采用的形式端点

| 端点／分支 | 不直接采用的理由 |
|---|---|
| P-PRED 最小充分表示 | 未给SQLite全未来协议核及共同可测因子化；完整查询向量不是自动证明的预测最小统计量 |
| P-QUO 精确控制商 | 没有建立完整SQLite状态、每个允许动作转移的商闭合；相同SQL输出不等于最优控制商 |
| CSX-30 真实资源、修复检查与全价格目的 | 当前规范行3036—3140是 literal Register 源、真实费用、故障概率及价格／折扣条件；SQLite进程试验没有这些类型和完整路径律，不能调用健康占据、长期破产或GOD阈值定理 |
| 人口／程序继承、二维瓶颈、连续Itô、C4定量运输 | 当前任务没有相应对象、概率／尺度、误差和运输前提，不引入这些结构 |

CSX-30 对“恢复、最优、可支付分别证明”的警示与本次方法一致；这属于原则解释，不是把该具体 Lean 结果实例化到 SQLite。所有本轮结果仍为应用推理与工程检验；新增 Lean 为零。

## 4. C7 方法责任与证据级别

当前 `C7_EXTERNAL_VALIDITY_REGISTRATION_TEMPLATE_V1.md` 行8—25要求先固定来源、观察、覆盖与缺失；行54—57区分干预失败、领域桥拒绝、统计歧义和支持；行59—76保留有效性阶梯及 UNVERIFIED。[C4] 本次采用这套方法责任，C2—C6未被使用的校准字段应填“不适用＋理由”，不能填虚构 eps、L 或 M。

本文件的分层：**源码／合同已读；运行版本由主审回执报告；配置、费用、留出和领域结果待实验。** A 未执行 Lean、未运行认证、未读 B/C 方案；不能在此提前写 DOMAIN_CONDITIONAL 或独立复现通过。

## 固定源引用

- [C1 SISCIdentityNoGo.lean](https://github.com/MurphyHoops/UEOT/blob/d30dae2a87150acddd67a3039ceccc4fe96d2b21/formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/ScientificClosure/SISCIdentityNoGo.lean)。
- [C2 successor specification](https://github.com/MurphyHoops/UEOT/blob/d30dae2a87150acddd67a3039ceccc4fe96d2b21/core/specifications/successor/UEOT_Core_Successor_Specification.md)，§§2.1—2.2、CSX-30；[范围决议](https://github.com/MurphyHoops/UEOT/blob/d30dae2a87150acddd67a3039ceccc4fe96d2b21/council/resolutions/20261113-core-claim-scope-reconciliation.md)，§§1、6。
- [C3 UEOT Method](https://github.com/MurphyHoops/UEOT/blob/d30dae2a87150acddd67a3039ceccc4fe96d2b21/constitution/UEOT_METHOD.md)，Shared-Source and Identity Discipline、Evidence Discipline。
- [C4 C7 external template](https://github.com/MurphyHoops/UEOT/blob/d30dae2a87150acddd67a3039ceccc4fe96d2b21/formalization/ueot-core/docs/compression/theory_completion/scientific_closure/C7_EXTERNAL_VALIDITY_REGISTRATION_TEMPLATE_V1.md)。
