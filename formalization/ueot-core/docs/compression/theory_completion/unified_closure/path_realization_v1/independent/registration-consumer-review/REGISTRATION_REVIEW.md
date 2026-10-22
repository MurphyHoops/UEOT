# 实际注册独立复核

**结论：`CLEAR_METADATA_ONLY_REGISTRATION_AND_EXACT_BYTE_PRESERVATION`。**

审查者：`/root/finite_memory_realization`。注册执行者为 `/root`，六消费者修改作者为 `/root/c3_executable_search`。本审查者曾编写冻结 adapter 和三个 Lean 模块；这里独立审查实际注册结果及字节保留，不将其作为独立协议静审或本人数学源码的自我验收。协议另有 C3 独审，构建/native 原档另有 `/root/finite_window_source` 的签署执行审查。

## 精确绑定

| 对象 | SHA-256 或身份 |
|---|---|
| 已接受 operations 基线 | `d503586107974c56e0773b4ea106b41a7d144b43` |
| 本批完整源码 | `de7c7e287bd1b351ed3f790de58bfd71edf18df4013f7e5aaf2af55a6b3f6379` |
| 已签署实际执行审查 | `89697625b9aa110791da53332ba02714191c30b5accf239f5380242076529fbf` |
| 原 raw overlay | `e87a8b9a921e4f9014d59f761ed73c8432c869f354e3b498542d99133a84239a` |
| 注册 overlay | `8e72781498acf49496733ace5dfbf80257830ff3a6d85e1b02e66474f936ec3b` |
| 原 `REGISTRATION_RECEIPT.json` | `1f72a7a063bab710241b7ea11fe643835019da7e06aad155ffbd9439c26c5d51` |
| 本次 [REGISTRATION_REVIEW.json](REGISTRATION_REVIEW.json) | `b18292550f6d2719c792aa67d21a7305b97287a36f63ad1919307bb996463013` |
| 本次 [verify_registration.py](verify_registration.py) | `bfbffe4cd21871dad0f4639ab0a5a35fce8e018e646bb72d5ca1f6814badac58` |

## 实际核对结果

本次独立只读核对通过 81 项断言；只写本审查目录内的新报告。未执行 Mac、Lean、Git 写操作或重复的 89 项 parser 测试。

注册对象仅增加 `lexical_pr_preflight` 和 `registration_provenance` 两个顶层键。剥离这两个键后，完整 JSON 对象与原 raw overlay 相等。原 raw overlay 自身仍以原字节保存在实际归档中；这里没有把“对象相等”误写成注册前后完整文件字节相等。

live 注册 overlay 与归档 `REGISTERED_OVERLAY.json` 逐字节一致。live native JSON 和固定 Lean verifier 分别与实际 native 归档逐字节一致。注册收据中的 39 条来源记录全部核对目标哈希与实际输入字节，包括：16 条实际 native 输出、8 条实际 full-build 输入、2 条执行入口、4 条不可变辅助代码、前层 overlay、Git 基线 consumer、注册入口，以及 6 条实际适配执行源记录。

执行内存来源不是由任意描述字符串替代：冻结 manifest、adapter 和 wrapper 分别绑定已审字节；不可变注册驱动与精确基线的 Git blob 相同；按归档记录的 11 个唯一字面替换锚点重新构造后，与实际归档的执行驱动逐字节一致。静态 diff 仅包含范围/计数/来源身份替换和增加完整执行源归档，不删除原身份或比较检查。

新增 lexical 元数据与原 `SOURCE_PREFLIGHT.json` 和逐声明提示表相符：684→691 个模块，4272 个前置注册公开声明，本批 73 个公开声明，候选注册总数 4345，25 个具有候选的源码提示组。这里不把提示组当成证明依赖，也不把候选注册总数当成六消费者已经完成验收的 live 图计数。

实际注册命令的原 CLI 收据退出码为 `0`，模式是 `REGISTER_METADATA`，用时 `0.4170193119934993` 秒；命令不含 `--check-only`。其日志 JSON、收据输出哈希和注册 overlay 身份相互一致。原 CLI 收据 SHA-256 为 `5d63c7e5d23370ba570fbd8e4aad91eae85daf4362055539d691c3e8ceadd4f4`，原日志 SHA-256 为 `33aca5aa12e680b3a900bc398e0534b37b84ae1a67ec1c0bbdebffc630dbaad5`。

重新读取全部 691 个 Lean 模块后，完整模块清单、逐文件字节与 full-build02 的来源记录完全相同，完整指纹仍为 `de7c7e…`。实际执行独审所绑定的关键原档也均未变化；审查期间读取的所有输入在结束时仍保持相同字节。

## 原状态与后续门

原 preflight 继续保留 `PENDING_ACTUAL_NATIVE_EXECUTION`，原 native 状态继续保留 `PASS_PENDING_INDEPENDENT_REVIEW_AND_REGISTRATION`；本次新审查不回写这些历史快照。注册 provenance 中的独审、Git-object preflight 和消费者状态也保持原记录含义。

**本次 CLEAR 只验收元数据注册与字节保留。** 六消费者和 DAG 的独立审查、实际 consumer/clone/canonical 门、Git-object preflight、发布和 resulting-main 树身份仍由对应新证据验收。冻结 106 个 P-ID、四项 counted 结果及全局 `NOT_ESTABLISHED` 不变。
