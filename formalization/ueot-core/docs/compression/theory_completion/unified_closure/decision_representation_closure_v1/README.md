# 许可历史的决策充分表示与实际紧凑控制器

本包完成 2026-11-05 新合同的数学、实现与消费者部分。原全 Core 条件数学合同及 PR441 六项完成裁决保持有效。本合同首次冻结与执行的北京时间为 2026-11-06；起点 main `39e9259f0c8f25c97a55239d852ff4d151f114ac`。发行与原 GI 的真实回执在任务接续目录记录，不在提交前预填成功。

## 结果与入口

[冻结合同](CONTRACT.md)、[事前输入](INPUTS.json)、[定理索引](THEOREM_INDEX.md)、[API 的准确边界](API_BOUNDARIES.md)、[六项验收证据](FINAL_ACCEPTANCE.md)分别给出目的、输入、证明连接及退出范围。主要入口为 `RegisterDecisionRepresentation`，经既有 `UEOT.V3.Compression.TheoryCompletion` 公共导入暴露。

新观察器只接受公开初态、自身请求与 `(birth,paidWrite)` 收据。摘要保留 root/child1、首次分配、stop、elapsed、有信息的正常/故障计数和实际付款计数。坏槽 idle 与 None 请求的 00 似然为 1，不增加故障样本。原世界的程序、真实身份、亲子、owner、label、时钟及尾槽继续保留；控制器没有读它们的免费接口。

固定任意正质量许可历史时，计数后验为 `prior(θ) rθ^s (1-rθ)^f / Z`。证明展开真实 primitive，覆盖任意允许完整历史的实随机策略；相容历史的动作概率因子对 θ 相同，正质量使分母为正，不相容历史质量为零。零先验及 r=0/1 均被处理。同摘要保持原菜单中每个合法请求的收据、下一摘要、实际出生、实际费用和钱包的联合律，不只保持均值。

共享 Array/DAG 的可信精确检查器核对每个合法替代动作的每个正概率后继、精确值及原平局顺序；执行直接沿共享节点走。`returned`/`plan` 返回 Option：已证明的是每个被接受产物的正确性，未另外证明生成器对每个合法输入必然通过检查。13 个本次实际实例全部被接受。实际 driver 先认证并直接执行同一内存数组，再导出 JSON；本包未新增 Lean JSON 解码往返定理，导出字节由 SHA 和独立完整动作检查绑定。

## THIS 实际输出

[RETURN_REPRESENTATION_DAG.lean](native_protocol/RETURN_REPRESENTATION_DAG.lean) 是实际入口；每个目录保留 `stdout.json`、`stderr.txt`、`RUN.json`。节点均含终端行；证明图检查全菜单，执行图仅记录所选策略可达子图。

| 消费者 | 精确最优净值 | 全动作图节点 / 边 | 执行图节点 / 边 | 原生检查 |
|---|---:|---:|---:|---|
| [两步](actual-execution/two-01/stdout.json) | 1/160 | 21 / 43 | 6 / 5 | 完整 32 路径 |
| [三步备用](actual-execution/three-01/stdout.json) | 9/256 | 52 / 127 | 11 / 10 | 完整 128 路径 |
| [三步后验](actual-execution/posterior-01/stdout.json) | 27/320 | 52 / 127 | 11 / 10 | 完整 128 路径 |
| [四步反馈](actual-execution/four-01/stdout.json) | 39525/524288 | 104 / 287 | 16 / 16 | 完整 512 路径 |
| [预登记八步 B=2](actual-execution/long-01/stdout.json) | 884450457/1342177280 | 1661 / 8221 | 151 / 182 | 固定 32 路径及 2 份 Lean 直接图执行 |

四个旧实际返回表只读取复用，没有重跑旧长求表；26 个正支持决策历史逐个同动作。见 [精确旧表比较](independent-execution/PR441_ALL_ACTION_COMPARISON_02.json)。独立执行器按 THIS 导出节点请求原完整 Store 交易，未替换成 Python 最优策略。八步最优性由一般源桥和全动作精确证书承担；32 条路径不是全路径枚举或统计估计。

八步产物 SHA-256 为 `f9a762e2c941a229a5790528792872cc8a48905858fcc4d0bce6da58d9b42bae`，960155 字节。至少一次出生概率为 215/256，付两次写费概率为 1233/4096，期望实际出生 57313/16384，期望实际费用 4673/4096，最小前缀余额为 0。这些未经折扣的总量不同于净值 J。其 151 个执行节点承载 333 个正质量前缀，74 个节点实际合并多个历史。

完整策略是 JSON 中的 `nodes` 与 `root_id=1660`，并非下面的示意路径。首请求为 root 写 goal；若首收据为 11，下一步 root idle；再遇 00，则调度健康 child1。若首收据为 00，slot1 已永久 None，下一步仍可重试 root 写。实际审计路径请求为 `root_write_true, root_idle, child1_idle, child1_idle, child1_idle, root_write_true, stop, stop`，第 1 与第 6 tick 真实收费，余额从 2 到 0；stop 后继续 root idle 交易和时钟。

## 真正的共享、不能删除的区别与数量界

两个可达历史只保留当前体态、钱包、时间会混淆后验：下一步 child1 idle 的出生率分别为 5/8 与 1/2。另一对可达历史的完整摘要一致，在原 root0/child1 菜单下未来联合律及继续值相同，并实际共享八步图节点 1294；它们的旧 Store 尾部不同。允许地址2后，一方该槽为 None，另一方健康，出生律立刻不同。合并不等于身份、过去出生时间或已赚折扣收益相同；地址2只用于边界，没有进入主菜单。

真实返回数组满足 `Graph.size ≤ 24(H+1)^4`，来自唯一键和源可达计数域的检查与定理。本次采用保守四次界；未形式化更紧的钱包三角求和界，也不宣称全局最小表示、一般 POMDP 多项式时间、有理数位长或总内存界。八步上界157464，实际1661节点。

## 成本、边界与失败

详见 [实际成本/结果汇总](independent-execution/INDEPENDENT_RESULTS_SUMMARY.json)、[针对性边界审查](independent/representation_boundary_output_review.json)及 [验证记录](VALIDATION.md)。八步 Mac 生成852ms、Lean全动作认证1740ms、节点界检查1ms、直接图执行1ms、JSON材料931ms、编码6ms；含加载及入口处理的完整墙钟7.250239291s。原始最大RSS为5812731904字节，包含Lean及依赖，不能当成图存储或抹去不报。纯加载未单独隔离。Linux独立全动作检查0.285671s、完整检查0.304112s，峰值RSS27398144字节。

既有 Python memo 强基线八步也得同值，求解0.717298s、12620个缓存键、333个展开策略前缀；环境、键和产物不同，不计算速度倍数。旧1713.890130s是未分段的原入口墙钟，本次未重跑。源码/编译尝试、原输出与检查失败原样保留。

H=0、零/不足钱包、端点率、零先验、重复率、公开 goal=false 的八个实际边界输出全部通过Lean检查和针对性复核；goal=false未冒称通过旧goal=true Python原生适配器。错误写收费、坏idle、None、fresh、stop及零质量默认值由源定理及有区别力的路径覆盖。删除一个未选 stop 动作的正边会被独立检查器拒绝，见 [负向检查](independent-execution/OMITTED_ALTERNATIVE_REJECTION_01.json)。

## 重放与文件身份

在 Core 根目录、已有依赖环境中，运行 `lake env lean --run docs/compression/theory_completion/unified_closure/decision_representation_closure_v1/native_protocol/RETURN_REPRESENTATION_DAG.lean long` 可再次调用同一入口；本交付不要求重复运行。独立检查器接受 `--dag-output`、`--reference-result`、`--reference-source`、`--output`，输出须为新目录；原参考保留为 `native_protocol/exact_reference_pr441.py`。输入、源码、THIS产物、检查器、书稿和PDF的具体哈希统一列入 `DELIVERY.json`；运行日志里的原机器路径保留历史身份。

两书正文见数学 §39.82—39.88、附录F，与哲学第八章/附录C；选页审查不冒称通阅全部221/89页。形式结论仍为条件数学，经验支持 UNVERIFIED。未知goal、任意地址主族、共同老化、无限期限及对象内部计算能耗未纳入。完成发行和原GI交接后本合同结束，不自动启动后续研究。

### 仓库内复现辅助检查

PR442审查发现两项辅助脚本保留了首次临时工作区路径；已改为由脚本位置定位正式交付目录，并要求 `--output` 指向新文件。原脚本快照、原执行结果和原样本保留。以下命令可以从任意工作目录运行（将 `<packet>` 替换为本包实际路径）：

```sh
python3 <packet>/native_protocol/check_representation_omitted_alternative.py --output <new-negative-result.json>
python3 <packet>/native_protocol/compare_prior_lean_tables.py --output <new-comparison-result.json>
```

可选 `--packet` 指向本包，comparison另有 `--prior-packet` 指向旧包；默认值已指向仓库正式布局。修正后在Mac从 `/tmp` 实际运行两项均通过，仅重验这两个辅助入口，未重跑求解、Lean或原生全路径。见[定位修正与实际验证](checks/REPRODUCTION_PATH_VALIDATION.json)。
