# Safe-prefix 私有 Lean 执行增量独立审查

## 结论与范围

**COMPILE_DELTA_CLEAR_PRIVATE_FOCUSED_PASS_NOT_INTEGRATED**。

本收据复用原合同/API 独审，仅审冻结稿相对原稿的执行增量与实际证据绑定。四个端点已由作者的真实第 3 次聚焦 Lean 执行通过；本审查者未运行 Lean、Lake、native、测试或 Git，也未修改作者包、生产、消费者、书稿及既有归档。

最终源码 SHA256：`392468a8ca8c29225f334324eb3c2b5996e2aa4eae4846dfdab371ffb2eeaddf`。

原合同收据 `REVIEW.json`（`b1c04040e9bf22221d29c09ba792bc0963997aa558cbfd91e9c75d44d632b978`）及其 Markdown、24 输入清单均原字节保留。作者 `COMPILE_PASS.json` 的 `execution_delta: PENDING_SEPARATE_INDEPENDENT_REVIEW` 也保持历史原样，由本新收据完成独立审查，不回写历史状态。

## 完整声明与唯一证明差异

独立使用保留偏移的嵌套注释/字符串屏蔽，加括号深度扫描至**顶层** `:=`，比较全部四个完整声明头。尤其 S2 中 `(X := X)`、`(A := A)` 没有被误当成声明结束。最终稿、原稿和三个实际 attempt 快照的四个完整声明头全部逐字一致，也与作者比较文件保存的完整头相符。这是源码声明文本比较，不冒充对未编译原稿的原生类型比较。

| 端点 | 独立增量判断 |
| --- | --- |
| `stateHistoryEquiv_survival_iff` | 完整声明不变；仅零时刻证明体改变 |
| `actual_safe_prefix_pullback` | 完整声明及证明正文逐字不变 |
| `homogeneous_survival_real_eq_killed_pow_sum` | 完整声明及证明正文逐字不变 |
| `homogeneous_survival_mass_eq_ofReal_killed_pow_sum` | 完整声明及证明正文逐字不变 |

独立重建 unified diff，与冻结 `SOURCE_DELTA.patch` 完全一致。S1 后继分支起至文件末尾全部字节不变；零分支之前全部字节也不变。没有新增定义、实例、选项、公理或假设，没有 `sorry`/`admit`。

S1 的唯一修复先由 `Finset.Iic 0` 的唯一索引及既有 `stateHistoryEquiv_last` 推出实际坐标等式，再显式处理 `¬¬(h∈K)`。它保留递归历史的可测实例，解决原 simp/unfold 在零时刻的类型与化简问题；没有更换事件或给结论增加前提。S2 仍在本地按真实 `riskEverFailure` 与 `eraseActionHistory` 递归证明拉回等式，未调用 K1 的隐藏私有名字。S3 仍把 G3 的实际事件质量等式与公开 K1 质量定理组合。S3E 仍从该真实概率测度的有限性推出 real/ENNReal 转换条件。

## 同源量词与边界

S1 只要求 `MeasurableSpace X`；S2 也只保留结构桥所需的 `MeasurableSpace X`。两个质量端点沿用 K1/G3 的有限 `X`、有限且非空行动 `A` 及相应离散可测条件，没有加入 `Fintype Y` 或观察空间可测性要求。

四端点沿用原始任意 `p0 : PMF X`、同一 `M`、同一 `q` 和同一平稳当前观察随机策略 `sigma : Y → PMF A`。实际风险记录使用 `observationMarkovPolicy sigma`，无限轨迹核和 killed matrix 使用同一 `liftedStationaryPolicy q sigma`。事件统一为记录中 0 至 n 的全部状态位于 K，即既有 survival API 的失败目标 `Kᶜ`。来源等式与事件拉回等式均由证明导出，没有放入假设。

- **n = 0：**安全事件包括初态，质量是原始 `p0(K)`，不是人为归一化后的 1。
- **K 为空：**允许空安全子类型；所有有限窗安全质量以及矩阵行总和均为 0，包括 n = 0。
- **初始失败：**保留 `1 − p0(K)`；没有把初态先过滤或归一化。
- **零存活：**所有端点均为未条件化的质量/事件恒等式，无正质量前提，无除以存活概率。
- **策略范围：**此桥需要同一个平稳当前观察策略，不将一般历史策略或 `viableFamilyPolicy` 自动视为该策略。

本轮没有实现尾极限、无限生存固定点、QSD 或 Doob 条件路径定理；也没有声称完成生产 API 集成。

## 实际执行与原始失败保留

| Attempt | 实际结果 | 耗时 | 证据作用 |
| --- | --- | --- | --- |
| 001 | FAIL，exit 1 | 5.634 秒 | 原零分支化简失败；原日志与快照保留 |
| 002 | FAIL，exit 1 | 5.783 秒 | 零分支递归类型/可测实例 elaboration 失败；原日志与快照保留 |
| 003 | PASS，exit 0 | 5.935 秒 | 最终 7214 字节源码；无 warning、无 error |

三次均非超时，实际命令使用冻结绝对路径 Lake `env` 加绝对路径 Lean，单线程；只编译指定私有文件。每轮 `source`、实际快照、`source_after` 的大小/摘要一致。最终 `.olean` 存在，127944 字节，SHA256 `c481111454b7e8df57c51757a82874cab52c3ef9f984df75253ae35966754328`。

最终原始 `lean.log` 为 718 字节，SHA256 `2da324f010cffe133d4e0fdb763de30fb5840427c6e2e19f9de11aac1ad04e05`。逐项解析其四个实际 `#print axioms` 输出，四个上述完整限定名的闭包全部恰为 `propext`、`Classical.choice`、`Quot.sound`。失败日志中的 `sorryAx` 真实保留，未作为通过证据；失败轮没有成功 `.olean`。这是四端点的实际传递公理闭包，不是新一轮全项目 native census。

## 输入与导入身份

独立重新核对原合同的 24 个输入实际字节/摘要、三个冻结私有源/olean 对、666 个完整生产 Core 源文件的路径与逐文件摘要、三个环境文件及 Lean/Lake 可执行文件摘要。结果与完整已通过 build-attempt-9 身份相同：

- 完整源码树身份：`29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。
- 完整 build manifest SHA256：`04acfa12f4b43154cbf1701834aadd459b1647730f789cdff2eccc6436e96b7c`。
- 九个依赖记录与该既有 build 身份及当前依赖锁文件一致。其实际 HEAD/clean 历史收据予以复用；本审查没有重新执行 Git，也没有声称对所有依赖文件做新的全量普查。

三个 `ENV_AFTER_LAKE.json` 都是实际有效 JSON，内容一致。记录的 14 个 Lean 搜索根无多余根：三个冻结私有缓存在前，随后九个依赖缓存、Core 缓存及固定运行时。实际 post-Lake `ELAN_TOOLCHAIN` 是 `leanprover/lean4:4.33.1`；它与调用 Lake 前的空环境值属于不同阶段。

按实际记录的搜索顺序独立重新解析四个直接导入，第一命中和全部命中列表与作者收据一致：`SameSourceInfinitePrefix`、`SameSourceKilledPath`、`UEOT.V3.RecoveryHittingDrift`、`Mathlib.MeasureTheory.Measure.Real`。核对实际 `.olean` 及存在的 `.olean.private`/`.olean.server`；共享传递 `SourcePolicyPathBridge` 另由冻结源/olean 对绑定。没有把仅有文件名相同视为同一导入。

## 可复用结论

该冻结包可作为**私有、同源、有限窗安全质量桥实际 PASS + 独立 CLEAR** 的研究增量归档。已合并研究归档的 Stage1–6、原 NOT_COMPILED/PENDING、原失败日志和旧审查均应原样保留，以独立追加记录表达成熟度变化。生产集成与尾极限仍是后续明确范围，不能由本收据自动升级。

完整逐项核对记录见同目录 `COMPILE_DELTA_EVIDENCE.json`；本次没有新增运行门槛或重复构建要求。
