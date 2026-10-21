# 实际首次退出通量：私有聚焦 Lean 通过收据

状态：**PRIVATE_FOCUSED_LEAN_PASS_NOT_INTEGRATED**。本文件记录真实编译，不代替独立增量审查、生产集成或 canonical 验证。

## 实际结果

第 **003** 轮真实 exit code 为 `0`，耗时 **7.091 秒**，没有超时。当前源码与该轮输入快照逐字相同，实际 `.olean` 已保存。每次仅运行一个 `LEAN_NUM_THREADS=1` 的私有 Lean 进程，使用绝对 Lake/Lean 和受钉住的缓存，没有运行 `lake build`、native 或全库检查。

- 最终源码 SHA256：`4ae9df91e5808f7294bb3c141bfe2e038f252adb2267e7e36380e0ba9b1aac18`。
- 原始草稿 SHA256：`8f88617f06f793492b04b875d38dbc097b7043bbe9ef12567b8492cb1eaf3c8c`。
- 实际 `.olean` SHA256：`edcea2cf0b4bedb70c93c39ab809e1c9b70c35690053cefff1b64b8a8d672cdd`。
- 实际状态收据 SHA256：`4919776a00308bb4edfb3035d1b3478fa1a9473cc90f9bac282fa54e87d444e6`。
- 实际 stdout/stderr 日志 SHA256：`dd5f21163a01a920bf459e257b40185bc5b5c14451fa1cc086cc6bafb2a7badd`。

**10 个关键端点**的实际 `#print axioms` 传递闭包均仅含 `propext`、`Classical.choice`、`Quot.sound`；名称和闭包逐项保存在 `COMPILE_PASS.json`。其中包含通用真实前缀、实际首次退出事件、矩阵通量、零时刻生存、有限望远镜和最终实际失败分解。没有把失败轮的错误恢复输出当作公理 PASS。

## 数学结论保持原样

原稿 **13 个定理和 2 个定义的全部 15 个公开声明头逐字相同**，两个定义的完整正文也保持原字节；没有新增端点。首轮实际编译输入到最终通过版的所有声明头亦逐字相同。原稿从未通过编译，故这里明确是源码级比较，不虚构旧 kernel 类型导出。

对于同一实际模型、当前观察平稳随机策略、任意原始初态 `p0`、安全集 `K` 和每个 n，已证明实际 `n+1` 步动作/状态记录中的首次退出事件质量为生存质量差，并等于同一 killed 矩阵的行缺口加权和。前缀身份从实际 PMF bind/map 构造推出；未放进假设。

最后的实际失败事件分解保留 `p0(Kᶜ)`，随后才累加正时间首次退出。`n=0`、最终窗口 `T=0`、空 K、初态安全质量小于一，以及后续零存活均在原量词范围内；没有条件化初态、没有新增正存活或 QSD 假设。退出后返回不会被重新计作首次退出。一般前缀引理可允许历史依赖，但固定矩阵接口仍保留 K1 的平稳策略范围。

## 实际尝试与纯证明修复

| 轮次 | 状态 | exit | 秒 | 源码 SHA256 |
|---|---|---|---|---|
| 001 | FAIL | 1 | 6.434 | fa21abff0548e3cd122ec541a54b10e05f8d9e35d71f9be2b4c0d2732cf24414 |
| 002 | FAIL | 1 | 7.745 | 090d42053ff2f1aee36ed0e7a653d267723fa1457f1edfcba264925ebf987af9 |
| 003 | PASS | 0 | 7.091 | 4ae9df91e5808f7294bb3c141bfe2e038f252adb2267e7e36380e0ba9b1aac18 |

首轮暴露局部记号 lambda 未先化简，以及 `prefix` 被解析为 Lean 保留语法的错误。第二轮的真实事件分割已经完成，剩余为 K1 与局部矩阵幂可判定相等实例匹配。第三轮通过 `convert` / `congr!` 解决该差异。最终源没有全局或局部透明度选项，没有占位证明，也未弱化声明。

第一次请求启动第三轮时，工具报告 exec-server transport disconnected。随后用只读命令确认没有第三轮状态目录，才重新启动；该次工具启动中断单独写在 `LAUNCH_INTERRUPTION.json`，不算作一次 Lean 运行，也不虚构 Lean exit code。

三组未使用 section-variable 警告被保留；它们不妨碍内核通过，也不值得为去除风格警告重跑验证。

## 旧证据保留与输入身份

原稿保存为 `SameSourceKilledExitFlux_v1.lean`；原 `BINDING.md`、`DRAFT_MANIFEST.json`、`K1_MASS_ENDPOINT.txt` 和 books_resume 的独立静态审查保持原始字节。原清单 11 个输入已按实际字节和 SHA 重新核对。旧文件中的 NOT_COMPILED/PENDING 是历史字段，本文件和后续独立增量收据记录新状态，不覆盖它们。

每轮实际编译都核对 SourcePolicyPathBridge 与 K1 的源码和已通过 `.olean` 共四个身份。完整生产 666 个源码路径和每文件 SHA、三个环境文件与 Lean/Lake 程序 SHA 已与完成构建的输入记录一致；生产 source-tree SHA256 为 `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。完整依赖版本及导入环境沿用已钉住的构建证据，不另做重型导出。

精确原/最终差异在 `SOURCE_DELTA.patch`；实际首轮到通过版的差异在 `COMPILE_ELABORATION_DELTA.patch`；完整公开声明比较在 `DECLARATION_COMPARISON.json`。当前包交 audit_resume 做窄编译增量独审，原数学静态审查继续单独保留。

此次没有修改生产、消费者、书稿、Git refs 或远端。该结果只完成私有有限窗来源桥，不宣称无限路径桥已经实现，也不扩大正在发布的七模块范围。
