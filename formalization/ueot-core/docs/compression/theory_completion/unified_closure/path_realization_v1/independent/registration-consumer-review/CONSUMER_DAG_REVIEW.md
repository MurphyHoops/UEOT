# 六消费者、模块 DAG 与实际本地门槛独立审查

**结论：`CLEAR_SIX_CONSUMERS_DAG_OLD_TEN_PRESERVATION_AND_ACTUAL_LOCAL_GATES`。**

本审查针对 C3 作者提交的六路径候选、已经实际登记的第十一层，以及现存实际门槛日志。独立检查共 **237 项通过**。机器收据为 [CONSUMER_DAG_REVIEW.json](CONSUMER_DAG_REVIEW.json)，审查实现为 [verify_consumers.py](verify_consumers.py)。登记本身的 81 项独立检查另见 [REGISTRATION_REVIEW.md](REGISTRATION_REVIEW.md) 与 [REGISTRATION_REVIEW.json](REGISTRATION_REVIEW.json)。

审查人未编辑这六个消费者、未生成被验收的 DAG、未运行作者的本地测试套件，也未执行登记。审查人此前编写过本批 native 适配器和三个有限记忆模块；这些数学源码及协议的独立审查由其他审查人承担。本收据只认证这里实际检查的登记消费、旧证据保留、图和执行日志，不用自己的源码作者身份代替独立数学或执行审查。

## 一、绑定对象

| 对象 | 精确身份 |
|---|---|
| 已接受的 operations 基线 | `d503586107974c56e0773b4ea106b41a7d144b43` |
| 当前 691 模块源码指纹 | `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379` |
| 六路径候选清单 | `fb8546ac7f6005e3b683986028f568d774294acbc89cd460f3a87693bbedfe03` |
| 当前已登记 overlay | `8e72781498acf49496733ace5dfbf80257830ff3a6d85e1b02e66474f936ec3b` |
| 当前 native 原始导出 | `61dabee5113b7fd2e640971c55ef6d2dba91e257744f587b57235f94a73b3308` |
| 六路径独立审查 JSON | `dfe672373566a701811bf65047fed95e48ba15856ab330120d7b60bd55a809d1` |
| 六路径独立审查程序 | `ddc93fde2c6ca30cd8d2cf71d0e1fae3a125bcd2b5ec1d9fac8bebd556204ae3` |

六个路径为 `UMC_GLOBAL_MODULE_DAG_V4.json`、`knowledge/reuse/fkrg_reuse.py`、`knowledge/reuse/test_fkrg_reuse.py`、`knowledge/reuse/REBUILD_CLONE_CANDIDATES.py`、`knowledge/reuse/README.md` 与 `knowledge/README.md`。完整 before/after 哈希列在独立 JSON；逐个与 Git 基线对象、作者的 [APPLIED_SIX_PATHS_01.json](../../consumer-plan/APPLIED_SIX_PATHS_01.json) 以及当前原始字节交叉核对。作者清单生成时的 `LOCAL_GATES_PENDING` 保持原样，后续实际结果由新收据承接。

## 二、旧十层及消费语义完整保留

`fkrg_reuse.py` 的四个登记数组各追加一个新层记录。独立移除这四个追加项后，整个 Python 可执行 AST 与 Git 基线一致；这不是只核对函数名或若干行。旧十层的 overlay、固定验证器及其保留的 native 与证据字节，逐个仍与基线和原 pin 相符。不可变基础 CSV、历史类型证据和原 68 行 clone 表也逐字节保留。

clone 扫描器除模块说明文字以外，可执行 AST 与基线相同。原来 50 个测试方法全部保留：三个现有方法仅调整当前 census 数值，规范化这些明确数值后，剩余原测试 AST 完全相同。新增四个方法检查：

1. 新层的编译器所有者、真实类型证据与已登记直接边；
2. 同源端点和既有 canonical 声明的实际复用；
3. 新公开物理安全见证实际依赖全部五个私有质量计算；
4. 登记只增加许可的元数据，并保留原执行档案。

新增故障注入测试中的 `verify_source=False` 只用于刻意篡改 native 内容的负例，以检验对应拒绝分支。实际消费者初始化和本审查调用的 `reuse.load()` 均保留默认源码新鲜性检查。本审查没有借此跳过源码身份验证。

## 三、独立重建实际注册图

从不可变基础声明表、十一个 overlay 对象和唯一既有旧节点依赖修复，独立重建完整图，再与正常 `reuse.load()` 的实际输出比较。原来的 **4,272 个节点、5,614 条边**完整保留；本批增加 **73 个公开节点、114 条直接注册边**，结果为 **4,345 个节点、5,728 条边**。

新 114 条边逐声明取自实际 native 的 `direct_constants` 与完整注册节点集合的交集，排除自身边。未把依赖图中不存在的期望关系手工写成边。私有常量不伪装成公开注册节点；公开见证对五项私有质量事实的真实引用，另由 native 常量记录和新增消费测试验证。

最终正常消费者报告为：11 层 overlay、552 个 overlay 公开节点、841 条 overlay 出边、133 个词法候选组。历史的 37 个已验证同型组、77 个对应名字、15 个近型候选对和 68 行 clone 候选均保持。唯一旧公开修复与唯一旧节点入边修复没有新增或删除。

这份注册图表示已登记公开声明之间的直接证明依赖。私有及编译器生成常量的完整所有者、公理和直接常量检查由已经独立签署的 actual native 收据承担，不从公开图的节点数反推全部编译常量数。

## 四、691 模块 DAG 的源级独立核对

`build_umc_global_map.py` 与基线 Git 对象逐字节相同。本审查没有调用它重新覆盖验收文件，而是独立从全部源文件重新提取模块名、行数、声明词法计数、导入、分类和标题，逐项比较 691 个 DAG 条目及聚合数据。

旧模块条目全部保留，公共 `TheoryCompletion` 根条目的变化仅来自新增七个正式导入；恰好增加七个新模块条目。独立计算得到：

| 项目 | 实际结果 |
|---|---:|
| 模块总数 | 691 |
| 维护模块 / 改编上游模块 | 680 / 11 |
| 从公共根可达的模块 | 691 |
| 缺失的内部导入 | 0 |
| 导入环 | 0 |
| 源码行数 | 126,169 |
| theorem/lemma 词法计数 | 4,606 |

各分类计数、跨分类边数、最高入度列表和整树指纹也全部独立核对。词法声明计数属于源码统计，不与 4,345 个已登记公开证明节点混用。

## 五、实际本地门槛原日志核验

本审查读取作者已经执行的完整命令、stdout/stderr 和收据；逐字节核对日志哈希、exit code、测试个数、零 skip、输入前后身份和当前源码身份。没有重跑这些套件。

| 已实际执行的门槛 | 实际结果 | 收据 SHA-256 |
|---|---|---|
| reuse 全套 | 54/54、零 skip，2.345 秒 | `eab49e8dfe1ce6eabb61dae048e766f3a474a74adae4c26c4b7a067ce94eb234` |
| FKRG 全套 | 30/30、零 skip，3.457 秒 | `51d9e76473d89286b8dd6ebbd9a07f6785c41c2514da3d756c0f2f08c8d03d2b` |
| 完整 clone 扫描 | 691 模块，精确等于原 68 行，1.740 秒 | `518569eb6345554b04818fe3d98fb59a82a35e5b8fc7a0d9aecebc2348b04c13` |

FKRG 原日志确含真实 fast-audit 测试及其审计输出，没有以 mock 成功代替实际运行。clone 结果是标准化源码片段匹配，不据此宣称数学定理等价。

原 89 项 parser 套件的实际 PASS 收据、原 stderr 和相关输入身份仍在，已读取并核对，**本轮没有重复执行**。三个当前门槛的输入 before/after 均一致，也与审查时的候选文件一致；全部审查读入文件在结束时再次核对为未变。

## 六、范围与保留的边界

本结论支持当前六路径候选及已登记第十一层进入后续 canonical 与发布检查。canonical、Git 对象预检、PR/主分支 CI、合并后树身份与双端对齐各由后续实际收据负责；本审查没有把它们预填为通过。已有 build/native 的独立执行审查见 [ACTUAL_EXECUTION_REVIEW.json](../ACTUAL_EXECUTION_REVIEW.json)。

原始失败、原候选的 PENDING 字段、第一次未完成的 native 尝试及其诊断均不改写。当前 73 个公开比较项来自经过审查的 API 修订；本收据不声称旧 77 项 native 比较已经完成。当前 native 对完整私有及生成常量的检验、以及公开见证对五个私有事实的实际依赖，保留其各自真实证据。

冻结的 106 项仍为 **11 generated / 89 adapters / 6 boundaries**，计数生成元仍为 **4**。本批为未计数的同源路径实现扩展。强意义的全局数学闭合继续为 **`NOT_ESTABLISHED`**；统计外部校准责任、物理解释和经验验证边界未因登记、图或测试通过而改变。
