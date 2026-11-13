# A：最终预注册的科学语义验收

日期：2026-11-13。结论：**ACCEPTED_FOR_PREREGISTRATION_COMMIT**。

A 支持将下列文本与配套源提交为实际预注册；这不是认证已执行、结果已支持或远端冻结已完成的声明。认证继续遵守预注册本身的真实commit读回和匹配授权入口，不另设用户批准门槛。

## 精确版本

| 对象 | 实际核对的SHA-256 |
|---|---|
| PREREGISTRATION.md | `73cb2d621c9012207db24c74edb4087232d1cff1f4375f511de6061e2562d349` |
| runner/sqlite_study.py | `bdbe87252da0b107602f7e30509b4b094f53d97a647ac9dc34cb378195dd92d9` |
| runner/protocol.json | `f68c5e9b643738563eebdce032bf13126e63036b2b473f889840355af5e00566` |

A 全文读过前一最终候选 `1b1868f2…447aa`，随后核对其唯一文字变化及当前hash：S0改为“最后一笔受登记干预的事务执行之前的参考状态”，使NORMAL／ACKED场景也有明确指称；与代码prior_state／after_state一致。变动在 `adjudication/PREREGISTRATION_TEXT_CHANGE_RECORD.md` 留痕，不改样本、规则、数据或实现。

## 接受理由

1. **可反驳且不靠弃权通过。** 有效错误接受、错误拒绝或无理由弃权可反驳主要主张；20个足额格与8个预算格分开，低预算按实际中断证据判断。28项主认证和7项C重现身份分离。
2. **知识与状态分开。** UNKNOWN保持原标签，完整{S0,S1}成员可以获得当前状态证书；公开未提交证书双方同享，私有COMMIT_RETURNED不缩小策略允许集。
3. **实施前提已按B→A质询收窄。** 没有独立db-domain表或故障前关闭后独立核验S0；实际使用参考初始化、可信请求／ACK和完整事务状态。C逐值重建检验该领域桥，不倒填未做的前态量测。
4. **资源和恢复未被放大。** 硬阈值仅为登记callback维度；外部预处理、逻辑复制字节、connect及native／内核成本分层。每个认证PRECOMMIT逐格报告实际hot证据，不把W0校准推广到W1/W2或断电／WAL。
5. **比较公平且允许无增益。** 独立同源克隆、共同信息与动作、强参考模型、结构弱投影及历史消融角色清楚。等价结果可以结案，未测认知便利不替代算法增益。
6. **Core与应用边界准确。** 仅使用两项原则；没有SQLite的Lean实例化，不调用CSX-30等缺少类型前提的端点，不重开D1—D4或改变全局UNVERIFIED。

## 校准证据与审查独立性

A亲自阅读并程序抽取了v1小回执，形成 `A_CALIBRATION_V1_EVIDENCE_REVIEW.md`：七格校准、v1无hot恢复证据、32在首PRAGMA中断均保留。

v2机制证据来自**C的实际独立执行**。A已读 `agents/C/PRE_CERTIFICATION_ACCEPTANCE.md` §3并收到C本人确认：95文件重哈希、2项原始请求／ACK重建和完整SQL逐值比较；另在C独立克隆直接查询hot快照及同H的D_new／D_old。其v2复算报告hash为 `d59ff0a408a8e3004ab1c730aa0ae611d5a3b5d3ca5aeed2851086d2dbe954be`；直接查询原始记录hash为 `3e37c8f73bfd99bdde9e48bde8c993a5252d21d44bb6d58fa4301f9f0944e27b`。A没有亲跑Mac、逐文件重算v2或把C的执行写成自己的执行。

C所报告的有效magic、恢复副本DB变化／journal消失、S0逐值匹配，以及同H新旧状态结构投影相同而业务满足关系不同，支持本轮有限机制和语义见证。它们不证明全部可访问信息不可识别、所有崩溃恢复或一般客体身份。9项校准不计入未来28项认证。

## 后续责任

当前无科学语义阻断。真正commit、认证全尝试、C原始独立复算及七格重现、最终结果与归因仍必须实际发生，不能由本次接受预填。A1独立首审及原交叉意见保持原字节；采用的收窄与问答已在 `A_CROSS_EXAMINATION_SQLITE.md` §8记录。
