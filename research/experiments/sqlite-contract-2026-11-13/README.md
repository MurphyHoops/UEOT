# SQLite 事务合同、进程中断与强基线检验

状态：**PREREGISTRATION — 认证尚未运行。** 本文件的首次独立提交冻结方案与源；后继结果必须有明确时间和字节身份，不回填成预注册前已知。

本研究检验 UEOT 的显式来源、观察、事务身份及资源纪律在独立维护的 SQLite 运行时中的具体作用。强标准基线得到相同信息、动作、预算和原始故障产物；候选与其规则等价／没有额外决策增益是允许的结果。试验不改 SQLite、生产 Core、Lean、两书或冻结数学。

## 预注册与源

- [完整预注册](PREREGISTRATION.md)：主张、反例、允许状态集合、28项主认证、7项分离复现、停止规则及解释边界。
- [冻结分配](RUN_ALLOCATION.json)：全部35个预定ID和顺序；认证与复现分开。
- [驱动及重放](runner/README.md)、[协议](runner/protocol.json)、[实现](runner/sqlite_study.py)。
- [源清单](REGISTRATION_SOURCE_MANIFEST.json)：首次预注册的文档和代码字节；不要求清单包含自己的哈希。
- [现场恢复](evidence/SITE_RESTORATION.md)与[当前理论源身份](evidence/SOURCE_IDENTITY.json)。

基准 main 是 d30dae2a87150acddd67a3039ceccc4fe96d2b21。#461—#463 的有限闭环不重开；原多数worker及20261008 SQLite copy/inode方法pilot不是本轮新结果。固定目标为 Apple vendor SQLite 3.51.0；实际source_id、解释器/扩展hash、编译选项和PRAGMA见协议及原始运行环境。它不是未经修改的上游SQLite源码身份声明。

## 分离审查与主审责任

恰好三个原生AI研究子智能体先独立形成意见，再交叉质询；主审另读源码与一手文献并裁定信息和当前状态的桥。它们不是人类同行、外部操作者或跨设备复现。

- A：[应用主张](reviews/A/CLAIM_AND_DOMAIN_CONTRACT.md)、[两项Core原则及不适用端点](reviews/A/CORE_TO_SYSTEM_MAP.md)、[解释边界](reviews/A/INTERPRETATION_AND_LIMITS.md)。A1保留认证前建议身份，实际采用的收窄以最终预注册及后继质询为准。
- B：[独立实现提案](reviews/B/IMPLEMENTATION_PLAN.md)、[最终驱动源身份](reviews/B/FINAL_RUNNER_MANIFEST.json)。首提案的42项和UNKNOWN一律未决是已被讨论修订的设计历史，不是最终协议。
- C：[独立对抗标准](reviews/C/ADVERSARIAL_METHOD_REVIEW.md)与[预实现质询](reviews/C/PRE_IMPLEMENTATION_CROSS_EXAMINATION.md)。
- [主审预注册前裁决](adjudication/PRE_REGISTRATION_DECISIONS.md)：副本公平、UNKNOWN集合语义、有限样本和费用口径。

## 必须保留的边界

结构检查正常不等于已确认业务历史完整。接收ACK、数据库当前包含事务效果、唯一过去事件与进程身份分别判断。自动回滚来自SQLite已有机制；预算计实际回调阈值及其他已披露逻辑量，不保证全部物理I/O或端到端硬实时。零预算仍有共同实验准备费用。

本阶段的有限软件结果不会把全局自然经验 UNVERIFIED、旧SI-5外部操作者门槛或人类学术认可改成完成。原始请求、完整返回行、失败、快照及执行记录将在后继结果包中保留；结果可为支持、拒绝、无增益或不可判定。

## 权利与来源

本目录新写研究文字按仓库持续开放研究规则适用 CC BY 4.0。驱动为本任务新写的AI辅助研究实现，未复制SQLite、Knossos或第三方算法代码；只调用系统Python标准库和已安装SQLite。数据全部为本任务生成的有限测试值，无用户数据库或个人记录。

依本任务明确授权，代码和数据作为研究证据提交和采用；不据此新增Apache、MIT、CC0等一般再利用许可，也不修改根LICENSE_SCOPE既存权利。SQLite运行库、解释器和第三方论文不随包分发。查看与引用来源不等于对第三方内容重新许可。
