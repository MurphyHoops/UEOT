# K1 最终证明差异与实际执行身份增量验收

结论：**CLEAR — PRIVATE FOCUSED COMPILE PASS VERIFIED**。本次复用此前独立静态语义审查，只检查最终差异和实际执行证据；没有再次运行 Lean，没有扩大为生产、原生导出或 canonical 集成验收。

## 声明与定义保持

基线采用本审查者保存的 `input-snapshot-v1/SameSourceKilledPath.lean`，SHA `383eded19936623d3745d06d0f58e193f4f2682e73123b90a8cbc7733739b7f5`。最终源码 SHA 为 `fa4f5ce017d6bfa4d9f3fe77805ad629f1c04f34a7ac3495c9114c432bc6c826`。从这两份实际文本独立重算的完整 diff，与作者 `PROOF_ELABORATION_DELTA.patch`（`bb3d5739deb95d65bec678982cbeb48ed4e4e1b5ce1705c532bdb2757f89f9c4`）完全一致。

4 个定义的完整文本和 13 个 theorem 的声明均未改变。此前已核对的同一实际 p0/M/q/sigma、Q 的安全限制定义、初始限制行、时刻 0、安全域为空及无正存活前提等语义结论继续成立；没有把目标等式、非空 K 或初始安全加入假设。

## 实际差异

| 差异 | 增量判断 |
|---|---|
| 初稿状态注释改为从独立收据读取状态 | 与现在的真实执行阶段一致，不修改数学内容。 |
| `stateTerminalMass_succ` 局部 `backward.isDefEq.respectTransparency false in` | 范围仅为该私有递推证明的 elaboration；声明和四个定义未变，实际终点公理输出仍仅标准三公理。没有加入新公理或放宽结论。 |
| 将 PMF 单步展开改为显式有限双和及逐项 `if_congr`、`pmfExtend_apply` | 展开原来的同一 `causalLaw` / `pmfExtend`；没有更换路径律或事件。 |
| 幂递推末尾增加 `rfl` | 完成原定义性等式，声明不变。 |
| 时刻 0 的擦除事件证明改为 `change` 与 `tauto` | 仍证明初态属于 K 当且仅当不属于其补集；时刻 0 没有删除。 |
| 实际事件质量改为显式 `finite_event_mass` 后逐项判定 | 原实际推前路径、事件与终态质量定义不变。 |
| 新增状态质量端点的第三条 `#print axioms` | 只增加真实公理闭包输出；原两条实际风险端点输出仍保留。 |

## 实际执行与输入绑定

逐项核对 `COMPILE_PASS.json`（`2784c9b2b6eaa11c27ef485e4eb83dc8437295b3f25ef3777ed7727854c11676`）、attempt-010 原始 STATUS、原始日志、当次源码快照及 olean。状态内容相等，源码执行前后、当前源码和执行快照均为同一 SHA。

- attempt-010：实际 exit code 0，未超时，81.381 秒。
- 实际日志 SHA：`cb1c77ddde8702fae626aad9b7ac6de6a079cf3e6cf71e21287c6c48430f5862`。
- 输出 olean SHA：`91c3d26034d72d7abeb140d057c78b55296d4e4e7450cf5b291ccc3ad748d1e5`。
- 实际日志中的三个端点分别为 `state_terminal_mass_eq_killed_pow`、`actual_survival_terminal_mass_eq_killed_pow`、`actual_survival_mass_eq_killed_pow_sum`；逐项读取的依赖公理均恰为 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或报错。
- 日志只有两条 `Set.mem_setOf_eq` 弃用提醒。此次不为清理提醒改动已通过的候选。

编译命令把已通过来源桥的 `lean-attempt-002` 放在 LEAN_PATH 前端。实际输入 `SourcePolicyPathBridge.lean` SHA 为 `108500fc13229b8faffc9829d886313167142075112bc3f6c023a086c074ae91`，被引用 olean SHA 为 `0ef1132fbfb24b0e571693de99e2729f9a8ede4aa41203fb4b3be67d46915748`；二者与来源桥已有真实 PASS 收据和 K1 当次状态吻合。来源桥日志、状态、工具链文件及依赖清单的字节身份也保持原收据所记录值。本次没有重审来源桥的旧证明。

attempt-001 至 009 的状态仍为 FAIL，原源码快照与原日志均在且 SHA 与完成收据吻合；attempt-010 作为后续独立 PASS 保留。初始 `STATUS.json` 的历史 DRAFT/PENDING 内容未改写。

## 剩余范围

此结论完成 K1 的私有聚焦源码与实际执行绑定，覆盖上述三个端点的实际公理输出。没有声称一般条件律 K2、QSD 绑定 K3、无限路径、native 全量审计或 canonical 集成已通过。QSD 草稿的独立收据仍为 NOT_COMPILED；其旧清单记录的活动 K1 身份由本增量收据连接到最终已通过版本，不覆盖原记录。
