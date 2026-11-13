# D3 runner v2：C 有限只读复核

**裁决：READY_FOR_SCOPED_EXECUTION。可在主审已核实的隔离 Mac 路径执行；此裁决不是 D3 PASS。**

目标 main：`6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4`。本次不操作 Mac，不运行 Lean，不重放数学反模型，也不重跑 B 的文件系统测试。

## 1. 固定版本身份

- runner：`31b1671dba48e01386c1afb95f2aaa038c6e9ae96e6339e970f31da31a9412d1`。
- ZIP：`d63db0f9d45abd025eaf1915a84151b0c0f07a82ebb8d80a635a70e257c68d00`，67,760 bytes。
- 实际两版脚本差异与提交的 diff 完全一致；准备清单所有文件及保全 v1 哈希匹配；ZIP 10 项与磁盘文件字节一致。
- 旧 v1 runner、旧 ZIP、计划、probe 的身份没有被 v2 静默重写。

完整逐文件身份见 `RUNNER_V2_READONLY_REVIEW.json`。

## 2. 实际 v1 记录

C 直接读取了主审取回的 `D3_RECEIPT_V1.json` 和 `D3_PROCESS_EXIT_V1.json`。09:21:04 的唯一步骤是 `PredictionDependent --deps`，退出码 0；其后缺少 overlay 中的 `PredictionAE.olean`，runner 记 `FAILED_OR_BLOCKED`、进程退出 1、`fresh_lean_execution=false`。没有生产源码编译步骤。该分类准确：依赖解析阻塞，不是定理失败，也不是 fresh PASS。

runner 的源身份清单实际比较 1,055 文件；如果引导阶段另检查 1,057 文件，两者属于各自集合，不合并为同一覆盖计数。

## 3. 修复的实质复核

| 风险 | 代码中的实际约束 | C 判定 |
|---|---|---|
| 顶层 namespace 选择 overlay 后缺少复用依赖 | 镜像唯一真实项目缓存根，目录实体化，非目标文件逐文件链接 | 修复方向与 v1 阻塞相符；实际 Lean 解析仍由运行日志确认 |
| 目标输出穿透到旧缓存 | 15 目标及 probe 的同 stem 全部扩展排除；目录不链接；新输出槽拒绝已存在文件、断裂链接和链接父目录 | 没有以覆盖旧产物的方式制造新编译 |
| overlay 前缀误标 fresh | 相对/绝对 deps 路径均严格 resolve；保存报告路径与真实路径，仅真实路径位于 overlay 才算新产物 | 缓存链接不会因外观路径被标 fresh |
| probe 偷用旧目标 | 所有 15 目标须为真实普通文件，且显式导入解析到其真实新路径 | 保留实际目标消费义务 |
| 旧缓存遭输出副作用 | overlay 创建前保存目标全部 stem 的真实路径、大小、SHA；完成与异常时核查；增删或变化均阻止成功 | 有明确前后证据，不仅依赖代码意图 |
| 放宽旧成功门槛 | HEAD、源 blob、工具链、依赖、退出码、未完成证明、公理逐项要求保留 | 无放宽 |
| 把脚本准备／测试当 Lean 成功 | 自动结果仍为 `PASS_TARGETED_EXECUTION_REVIEW_REQUIRED`；测试标 `PASS_FILESYSTEM_REGRESSION_ONLY` | 范围清楚 |

B 的 112 个模拟旧产物测试报告已只读查看，C 未重复执行。它是针对文件系统修复的证据，不能代替真实 Lean 执行。

## 4. 后续实际验收责任

主审可以启动这个固定版本。取得新回执后仍须核对实际退出码、完整日志及哈希、15 个新模块产物、全部选定导入的真实路径、旧缓存目标 `UNCHANGED`、44 个类型／公理端点和保留前提。若失败，保留该 run 并按真实失败点分类；不通过放宽 PASS、改换工具链或声称全库已完成来绕过故障。

本轮 runner 审查不改变 Core 的有限 A 裁决，也不新增经验、原创性或哲学全覆盖结论。
