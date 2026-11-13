# C：结果后的交叉质询与独立裁决

日期：2026-11-13。实际依据：主认证28项、C新运行7项，均已执行；主源码与协议没有改动。主审负责最终采用，本文件不冒称PR已合并。

## 1. C→A：标准等价和弱投影的解释

C 问：是否同意本结果仅支持标准规则等价和已披露来源条件下的工程适用性，不能由“UEOT来源”另推出新解释或认知增益；no-go是否严格只对O=(opened,integrity响应,foreign_key响应)，不包含callback、时序与全部可访问信息？

A 原义回复：

> 同意两点。runner185–216和实际28条目都只支持本合同判据与强标准方法等价；未测解释/认知效率，不能从UEOT来源标签额外推出增益。no-go只对冻结O=(opened,integrity响应,foreign_key响应)成立；callback/时序/文件元数据及全部可访问信息不在该投影，消融读完全值却忽略历史也不是信息本身不足。A稿§5/7已明确。已核你关键认证包SHA56ddfc…9b47b4/5,109,111B，现在亲读raw H＋完整值；结案会分科学验收与Git采用。

A 随后实际亲读并自写计算器重建8个决定性case，未导入B/C：核初态公式、请求、UUID/hash、raw child与父接收、ACK/门控及完整值，4对同H新旧和4个PRECOMMIT通过。A将其称为对取回数据的重算；C的Mac独立查询仍归C。C的裁定依据是两种规则的实际相同分支及独立数据，不以A同意作为证明。无剩余解释分歧。

## 2. C→B：分母、费用与分析器修正

C 问：28主认证与7个新replication是否分列；callback是否明确不覆盖父预处理、摘要、复制、连接/恢复和物理I/O；compact v1对weak适用域的误读是否保留且仅重做后处理，没有重新采样或改原试验？

B 原义回复：

> 28认证与C的7新replication必须分列35，不把你的复现/后置SQL计入我28或互当概率样本；callback硬计数不包括你列的全部预处理/摘要/克隆/connect/部分恢复/内核IO，copy bytes仅应用逻辑文件量，0预算仍启动/复制等成本；compact v1域错完整保留exports/B-certification和collect_certification_v1.py，v2只读取同一manifest/hash绑定原日志，weak全值成员改null，未重跑或修改原runner/protocol/trial。无额外反证或缺失trial。

C独立检查了两版collect_certification差额：只变后处理输出目录、完整值比较适用条件和说明。冻结observer对weak本来就没有SELECT业务/事务表，因此历史成员字段是None，不应被当作错误完整值。C的独立计算器从v1校准起就只对非weak作完整状态比较。这个修正恢复既定语义，没有改变科学判准。B的35项分列和费用说明与原始回执一致。

## 3. A→C：独立性、冷热覆盖与外部地位

A问：C是否真的从原始请求/ACK/公开门控重建，还是复用B摘要；W1冷journal是否只能缩小hot覆盖而不构成主张失败；七次是否仍属同机同vendor同runner同模型团队，不能当外部operator或业务服务恢复？

C原义答复：

> 实际35全复算完成：认证1261文件、28/28；独立7项315文件、7/7。参考逐值数组由raw initial＋父实际TRANSACTION请求＋raw child/父接收逐条对齐＋实际ACK/门控重建；不以B allowed_states/摘要/verdict为真值，反向检查它们。共同信任仍有父日志、初态输入、固定驱动/SQLite与文件读取栈；初态不是独立物理ground truth，root另按预注册公式复算。C还自写SQLite查询真实clone：主4对同H新旧＋4pre，共12份；replica旧新＋pre三份。同意W1冷2格只缩恢复覆盖；当前完整状态=S0符合登记义务，无SQL-CONTRACT错误；W2主2＋rep1实际hot。准确说同机同vendor同runner同AI团队的分离工程复核，非外部操作者/跨设备/业务服务恢复。

A接受以上分层，并随后对取回的决定性原始数据亲自重算。没有另加试验或扩张Core。

## 4. 主审分析器v1误报的独立判断

C查看了主审v1失败JSON的四个run-id，恰为四个COMMIT_NO_ACK_KILL：1116bb42、7ca6f088、70315ce6、c1446fc3开头的登记ID。C从原始日志逐项确认：最终TRANSACTION的pause_precommit=false、pause_preack=true；有普通PRECOMMIT_READY进度和COMMIT_RETURNED，但无ACK，worker退出-9。因此应是UNKNOWN。

主审v1把任意PRECOMMIT_READY当作暂停屏障。实际worker每笔都发该进度消息，只有pause_precommit=true才等待GO_COMMIT。C已实读v1→v2差额：仅增加匹配最终txn的实际发送命令和该暂停布尔值。C自己的计算器原本就要求这个条件，四项没有报错。主审保留v1脚本/失败JSON后只读同一28项重算，属于分析错误修正，不是SQLite失败、修改实验判准或重新试到成功。

## 5. C最终裁定与尚未发生的采用

科学责任已经履行：预注册先行、28主格齐全、7个新ID的分离重现、独立全值重建、同H成对读取、真实冷热机制边界、强标准比较和上述实质质询。支持限定软件合同内的SUPPORTED_SCOPED，并同时为EQUIVALENT_NO_ADDED_DECISION_GAIN。结论不依赖多数票，不包含新普遍定理、性能/认知增益或外部人类认可。

Git最终tree、PR合并、main读回与分支退休由主审实际执行后另记。本文件编制时不把这些后继动作写成已经完成。原Core冻结、旧SQLite pilot和全局自然经验/外部operator状态不变。
