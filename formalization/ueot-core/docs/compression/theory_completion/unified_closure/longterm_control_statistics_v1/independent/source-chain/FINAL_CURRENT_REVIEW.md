# 当前候选独立审查：CLEAR

本报告汇总最终生产源码、实际完整构建、两次原生导出、元数据登记及全局 UMC 执行收据的独立审查。它不代表 PR 已合并或 resulting-main 已验收。审查员只读了 cloud 源码和原始执行材料，运行了本地只读核对脚本；实际 Lean 构建和原生执行由主执行者在 Mac 上完成。

## 当前身份与历史审查的适用顺序

- 治理基线：`ff71e63256c88ad2bb527fdd3004d55c77894ab7`。
- 最终完整 Lean 源指纹：`60cd5f8ab161c5b51394463c466947a4c6a6c1742ecdcd9c2bbfc41c0c06bd31`。
- 完整生产来源：678 个模块；本批新增 12 个模块、90 个公共 theorem/lemma 候选。
- 新原生范围：199 个 compiler-owned theorem constants，包含 90 个公共候选、30 个私有常量、79 个其余非私有常量。其余常量不被推断成新增源级公共声明。

原 `FINAL_REVIEW.md`、`FINAL_SOURCE_STATIC_REVIEW.json` 等报告保存了先前 91 候选的审查状态，字节没有被覆盖。当前结论按下列顺序组合：原总体数学审查；`COLLISION_REUSE_DELTA_STATIC_REVIEW.json` 中删除冗余 time-zero 端点、复用已有端点；`TIME_ZERO_APPLICATION_FIX_STATIC_REVIEW.json` 中以局部 `have hzero` 消除实际 Lean 重写失败；`ACTUAL_EXECUTION_REVIEW.json` 中最终 full04/native02 原始证据审查；最后应用本轮登记及 UMC 补充。`CURRENT_REVIEW_INDEX.json` 给出各文件哈希。

## 最终数学与来源结论

同源长期链的最初八个归档主源已经过逐声明及证明的提升审查。production 中仍保持同一个原始初态、观察反馈、闭环源核、安全 killed 子矩阵、实际路径实验及无限轨迹测度。安全初始行没有被偷偷归一化；时刻 0 和初始失败保留；条件终端结论保留正分母条件；QSD 结论保留实际左特征数据。尾极限通过同一无限测度的递减事件连续性推出，允许极限为零，不能据此声称正无限存活或有限窗条件路径就是固定 Doob 过程。

唯一 injective PMF map 原子证明现在位于 ConditionedTerminal 的公共 `pmf_map_injective_atom`，QSD 真正复用该证明。原生扫描实际发现了另一个 time-zero 定理类型碰撞；ExitFlux 删除了其冗余公共定理，telescope 直接消费 ConditionedTerminal 的 canonical 端点。没有用 private、def、包装假设或排除扫描来隐藏重复。最后的 `have hzero` 修复只改变证明中如何应用现存端点，命题及假设不变。

InfiniteSupportViability 的量词加强在固定整条非自治转移和认证序列、固定初态与观察下完成。有限行动的递减非空可行动作集合提供无限一致选择；构造出的总策略证明其自己的实际支持传播和零未认证占据。其 fallback 仍明确存在。新的无限策略不被冒充为每一个旧有限时域 viablePolicy 的同一个对象。有限记忆最大固定点、有限记忆控制器和两状态 Lean 见证尚未由本批完成；零未认证占据到物理安全仍需初始安全及认证转移支持条件；来源零概率历史上的一致性不能改写参考过程 Q 的检查预算。

SISC 的逐行包装保留预先固定的正样本量、同一个实际概率空间上的真实行内独立性和边缘；共同 Good 及标量 Hoeffding 并合预算不需要跨行独立，也不额外按候选数并合。样本均值与原 kernel/source/action/read 的匹配仍是明确输入，随后才推导实际核风险身份。N3 的非空探针及识别 margin、N6 的完整候选竞争者量词和外部认证责任被保留。真候选没有成为候选选择程序的输入。非空两探针乘积见证及错误模型边界是形式数学实例；它们不被报告为外部实测实验，也未声称任意相关单轨迹或随机停止采样已经得到校准。

## 实际执行证据

| 执行 | 实际结果 | 独立核对内容 |
|---|---|---|
| full-build-04 | exit 0，39.787 秒 | 精确 `lake build UEOT` 命令；原始日志和成功标记；前后完整身份；678 源逐文件及总指纹；环境文件、九个依赖版本和运行工具收据 |
| native-02 首次导出 | exit 0，59.215 秒 | 完整 structured JSON；199 个所有 owned 定理常量；私有范围；公共类型及实际直接依赖 |
| native-02 固定 verifier | exit 0，58.444 秒 | 与首次完整 JSON 相等；独立从实际边和常量集合重渲染 verifier 后逐字节相等 |
| unchanged UMC `--full` | exit 0，67.128 秒 | 原始外层日志与聚合收据相等；validator 与基线逐字节一致；当前 79 UMC 模块和 564 公共词法项重新核对 |

新批次实际完成 373230 次跨既有 4147 公共项的 raw stored-type `isDefEq` 比较，以及 4005 次新公共项内部比较，碰撞为 0。149 条注册直接证明边从实际 `direct_constants` 与旧加新公共集合的交集独立重算，和 overlay 完全相等。历史 repair 为 0。全部 199 项的公理闭包仅含 `Classical.choice`、`Quot.sound`、`propext`，并已逐记录检查。

全局 UMC 聚合范围为 1073 项：103 private、564 confirmed public source candidates、406 other native public constants。unchanged validator 在内部扫描这些编译模块中的所有 theorem constants 并拒绝非标准公理。其归档外层日志只含聚合结果，不含内部每项 JSON；本审查据实际 exit-zero 日志、收据和 unchanged validator 的逻辑确认该执行结果。新增 12 模块的 199 项完整记录则确实在 native-02 原始 JSON 中保留并逐项独审。两种证据范围没有混写。

原始 45 文件、7602900 字节首次转移已逐字节检查；登记后重新检查原清单中全部文件仍保持原字节。失败的 native-01 和 full-build-03 继续归档。native-01 的真实类型碰撞推动了定理复用；full-build-03 的真实重写失败推动了 `hzero` 应用修复。没有把任何失败或历史 PENDING 改写成成功。

| 最终证据 | SHA256 |
|---|---|
| full04 receipt | `61af3bc7bc9e840ed1240fed0809ec47cb027cf8ea8d1bd11491f27ca8785d02` |
| native JSON | `0b6b77967ad43da71cec3a569b361501f591a7a8b384d072dda31af1b897d02c` |
| fixed verifier | `0643f8dfca2daec2ce6b4638f712f6abcacf8f91f31669a37120f397d6c27213` |
| raw overlay | `c04d08aac1ed70cc1dd73ee5821a196aaf8ac7d0168e4eabd5de70bd8c1c7edd` |
| registered overlay | `cb5792eff95b2a1386a7c0832eeeedc5a283f212b462f2c6c6d3342dd5e1bb06` |
| registration receipt | `dff9caf5fdbddf977ab0e7e4a0c5f1daaf9299195503125d5e878c106ccf811f` |
| UMC receipt | `d7fa7e9d1097cdffbd6fdcb6e71b33cc23ba75f7bf0fc9a38168ba7ee856c31b` |

## 登记边界

`register_overlay.py` 的审查绑定 SHA `3679552fc1599894cd1cf0ce5aba3324c1d13d885fbcdd6c96fc1796dbc1c939`。正式注册 overlay 恰好增加 `lexical_pr_preflight`、`registration_provenance` 两个顶层键；删去它们后完整 JSON 与原始 candidate 相等。原始 candidate、native JSON、固定 verifier 及原始日志字节不变。正式 native JSON 与 verifier 以字节复制进入 reuse 路径。21 项输入和协议快照的路径、原始来源、SHA 均已独立核验。

H = 27 来自实际 SOURCE_PREFLIGHT 的 90 个 hint 行，且此前已通过 immutable parser 独立重算逐行一致。登记后的只读 `--check-only` 再次实际 exit 0，26 个规划目标、overlay hash 和 receipt hash 完全相同；前后目标文件字节无变化。已有不同字节目标会拒绝；相同输入的再执行可幂等。此登记脚本不运行 Lean、不修改 consumer、不冒充 Git-object PR preflight。consumer 的四数组追加由另一独立审查负责。

## 科学与发布范围

原 C1–C7 责任、冻结的 106 个 P-ID 及 11 generated / 89 adapters / 6 boundaries 分类没有被本批数学提升替代。模块或公共项计数不证明四生成元自动重推导了全部原命题。全局强统一闭合仍为 `NOT_ESTABLISHED`；外部科学证据仍需独立实验或论证。

本轮已完成上述源码、实际构建/native、元数据登记和全局 UMC 执行材料的独审。Git-object PR 预检、完整最终治理门槛、PR 合并及 resulting-main 验收由主执行者继续完成，不能从本审查的 CLEAR 自动推出。

## 可重核材料

`review_actual_execution.py` 和 `ACTUAL_EXECUTION_REVIEW.json` 保存原始 45 文件冻结时的独立审查。后续增加登记快照和 UMC 文件属于新的归档层；不要把原始 exact-file-set 检查误读为拒绝这些已审增量。`review_registration_umc.py` 和对应两个新收据复核了原始 45 文件仍未改变，并核验正式登记及新增 UMC 收据。全部旧审查文件继续保留，当前索引明确给出适用顺序。
