# 同源 QSD：私有聚焦 Lean 实际通过收据

状态：**PRIVATE_FOCUSED_LEAN_PASS_NOT_INTEGRATED**。实际编译状态与独立增量审查分别保存；本文件不是生产集成或 canonical 授权收据。

## 实际结果

第 004 轮真实 exit code 为 `0`，耗时 `6.526` 秒，没有超时。当前源码与该轮输入快照逐字相同；生成的 `.olean` 已保存。每轮只启动一个 Lean 进程，`LEAN_NUM_THREADS=1`，使用绝对 Lake/Lean 路径和已有生产缓存，没有运行 `lake build` 或 native。

- 当前源码 SHA256：`be6c14557d455e8e4c6d752bb9255388a4dc5a561a85bf96112fbfba604f66ed`。
- 实际 `.olean` SHA256：`bb6a4eca21084acc86989ebf9cd509291cd72feb7f8480eecc7a6fe41258a67d`。
- 实际日志 SHA256：`a735c829497b4a5be6a1099dde7157d2695adfad48ca2550d814a06bab08884b`。
- 实际状态收据 SHA256：`a777b710788de5eaea4b4af40e82b90989746083891c3559b2941b2a03d23d09`。
- 原草稿 SHA256：`7eaf7716d0b16ee69e27d73b074b335136506deee44c27809ae2e27056d6e933`。

10 个实际 `#print axioms` 端点均仅含 `propext`、`Classical.choice`、`Quot.sound`。完整名字和每个闭包见 `COMPILE_PASS.json`。这是实际执行所得的传递闭包，不是全量 native 声明计数。

## 数学范围与增量

原 10 个公开定理的声明文本逐字保留；第 001 轮到最终第 004 轮的 13 个公开声明文本也全部逐字相同。原稿没有编译结果，故只声明源码级头部比较，不编造旧 kernel 类型比较。

新增 3 个已编译端点分别证明：当前真实生存质量为正当且仅当 `n = 0 ∨ rho > 0`；仅凭当前正存活即可得到实际过滤终态律等于 `r.map Subtype.val`；`rho = 0` 且 `n ≠ 0` 时不存在实际生存事件的过滤支持见证。二者输入始终为同一实际模型/策略所定义的 killed 核及真实初态 `r.map`，左特征关系是明确输入。

一般 K2 已通过编译和独立增量审查，本次直接复用它的实际过滤与归一化行推前身份；旧重复 `filter_map_apply_real` 与 `survives_last_mem` 已从当前候选移除，保留在原版副本。已有 `KilledQSDGOA` 的适配直接使用同一核，没有新增并列证书。

实际 elaboration 修复是两条质量公式中 `QSDPerron` 与 K1 的矩阵幂可判定相等实例差异：使用 `convert` / `congr!` 明确处理。当前正存活端点中的行公式先回写到实际事件质量再应用已证 QSD 质量公式。最终源没有额外透明度选项，也没有新结论性假设。通过后只整理收据，没有为风格警告重跑 Lean。

## 原始尝试保留

| 轮次 | 实际状态 | exit | 秒 | 输入源码 SHA256 |
|---|---|---|---|---|
| 001 | FAIL | 1 | 6.39 | 27460f97c82239a4f4ee8d121bff129431c626644efc2c99939aa04ef3048fa7 |
| 002 | FAIL | 1 | 6.436 | d17a358bf0fd719ffd39dfd3b7d5b3b2bcba9bd436e0c1e2d2bc62c0113d10cc |
| 003 | FAIL | 1 | 6.132 | 6e742f9338f10df05eeef9a208c06f2bb6283b46811ef493cd1957c9f060d630 |
| 004 | PASS | 0 | 6.526 | be6c14557d455e8e4c6d752bb9255388a4dc5a561a85bf96112fbfba604f66ed |

第 001 轮是两个质量公式和一个行公式的实例匹配失败。第 002 轮额外记录局部选项位置的真实语法错误；第 003 轮表明该选项没有解决实例差异。最终删除选项，显式证明实例对应后通过。失败日志中的 Lean 错误恢复 `sorryAx` 保持原样，绝不作为最终公理收据。

## 输入与范围

三个私有前序模块的源码及实际 `.olean` 共 6 个身份每轮都重新核对；固定为已 PASS 的 SourcePolicyPathBridge、SameSourceKilledPath 和一般 SameSourceConditionedTerminal。完整生产 666 个源码路径及每文件哈希、3 个环境文件和 Lean/Lake 程序哈希已与完成构建的输入记录核对，生产 source-tree SHA256 为 `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。依赖版本和导入环境沿用完整构建的受钉住证据；本次未重新构建依赖。

更准确的当前合同见 `BINDING_CURRENT.md`；原 `BINDING.md` / `BINDING_MANIFEST.json` / 原版源码均保持原始字节。`SOURCE_DELTA.patch` 记录原稿到最终版，`COMPILE_ELABORATION_DELTA.patch` 记录首轮实际编译输入到通过版的纯证明增量。`DECLARATION_COMPARISON.json` 给出全部头部比较。

本批仅为私有研究证明闭环，不更改当前冻结七模块、消费者、书稿、Git 或远端；不声称 QSD 存在、完整条件路径是齐次 Doob、任意因果策略已经 Markov 化，或无限路径桥已经完成。生产集成及 canonical 验证由根智能体安排。
