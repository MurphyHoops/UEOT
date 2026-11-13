# D3 runner v2：缓存目录解析修复与接受条件

状态：**脚本已准备；本文件及本地文件系统检查不代表 Lean 执行通过。** v2 的实际状态以主审随后在 Mac 生成的独立运行回执为准。目标提交仍为 `6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4`，固定工具链、证明源、15 项重编译清单、44 个类型/公理端点和 12 项定义展开均未改变。

## 1. v1 的实际结果保留

主审已实际执行 v1。`run-20261113T0920Z/D3_RECEIPT.json` 报告 `FAILED_OR_BLOCKED`：首个 `01-PredictionDependent-deps` 命令退出码为 0，但输出指向不存在的 overlay `UEOT/V3/PredictionAE.olean`，因而 runner 在依赖路径校验处终止。**生产 Lean 源尚未开始重编译。** 这既不是数学定理失败，也不是 D3 通过。

原因是 Lean 对 `UEOT` 顶层命名空间选择了首个有该目录的搜索根；稀疏 overlay 不能依靠后续搜索根对每个缺失文件逐一回落。v1 脚本、原 ZIP、原准备清单和上述失败目录保持原样，不重写历史状态。当前文件只补充新的执行修订。

## 2. v2 的具体变化

1. 从固定 Lake 环境中识别唯一的真实项目缓存根，条件是同一根下存在 `UEOT.olean` 和 `UEOT/`；按真实路径去重，多于或少于一个都停止。
2. 创建完整的项目缓存目录镜像。overlay 中的每个目录都是实体目录；复用产物只使用逐文件符号链接，并记录来源、真实来源和链接数量，不创建目录符号链接。
3. 15 个重编译目标及 `D3Probe` 的所有同 stem 产物均从镜像中排除，包括 `.olean`、`.ilean`、`.olean.private`、`.olean.server`、`.trace`、`.server` 及其他扩展。命名空间目录 `UEOT/` 本身继续镜像，它不是 `UEOT.olean` 的输出文件。每次编译前输出槽必须不存在，也不能存在断裂链接或同 stem 旧产物；编译后的目标必须是非链接的普通文件。
4. 在创建 overlay **之前**，记录旧缓存中这些 stem 的所有现存文件的报告路径、真实路径、大小和 SHA256。成功结束以及异常退出时尽量重新读取，检测内容、大小、真实路径以及文件增删。只有完全 `UNCHANGED` 才能进入执行成功状态。无需哈希整个 Mathlib。
5. 对 Lean `--deps` 输出的相对和绝对路径一律执行严格真实路径解析，分别保存 `reported_path`、`absolute_reported_path`、`resolved_path`。仅真实路径位于新 overlay 的产物才标记 `fresh_overlay=true`；overlay 中指向旧缓存的文件链接始终是复用依赖。
6. 最后 probe 必须实际解析到全部 15 个新目标的真实普通文件。它不会因为 overlay 下存在指向旧缓存的同名链接而误通过。

精确代码差异见 `run_d3_reproduction_v2.diff`。新增缓存证据为 `OLD_TARGET_CACHE_BEFORE.json`、`OLD_TARGET_CACHE_AFTER.json` 和 `CACHE_MIRROR_MANIFEST.json`，其哈希与摘要写入回执。

## 3. 接受门槛没有放宽

v1 中的 HEAD、源 blob、Lean/Mathlib/所有锁定包版本、包源洁净性、实际 Lean 可执行文件、编译退出码、`sorry`、44 个逐项公理白名单、两个精确 native 公理名、全部显式导入及源文件未变检查全部保留。v2 额外要求旧缓存目标字节未变、所有新目标为普通文件和依赖来源按真实路径区分。

自动成功状态仍仅为 `PASS_TARGETED_EXECUTION_REVIEW_REQUIRED`。主审仍须阅读实际类型/定义展开，核对 Countable、严格折扣条件、独立状态类型、`ValidIdentity`、`ProgramPopulation`、正权重分支、`ProbabilityValid`、全策略和非空人口等边界后，才能裁定 D3。这里不主张全库干净重建、重新编译每个依赖、重新计算两个缓存 native 数值端点、经验真实性或原创性。

第 14 项 `GrowthClassificationCheck.lean` 只导入 `CoreTheoryClosure`，不导入公共 `UEOT` 根；第 15 项公共 `UEOT.lean` 继续最后编译，因此本修订不需要改变模块顺序或 probe。

## 4. 本地针对性检查的实际范围

`test_overlay_v2.py` 在临时伪缓存中运行，无 Lean 调用，不触及生产文件。它覆盖 15 个目标加 probe 的 112 个不同扩展旧文件、实际目录镜像、旧文件链接的相对/绝对解析、新文件普通文件检查、断裂链接拒绝、旧缓存前后不变以及模拟覆写能被检出。结果保存在 `OVERLAY_V2_LOCAL_VALIDATION.json`，状态为 `PASS_FILESYSTEM_REGRESSION_ONLY`，`fresh_lean_execution=false`。

该检查仅检验这次搜索根与缓存隔离修复，不替代 Mac 上的实际 Lean 执行。

## 5. 主审执行方式

解包到全新的 `bundle-v2` 目录，核对 `PREPARATION_MANIFEST_V2.json` 和 ZIP 哈希；保持 v1 bundle 和失败 run 不变。进入当前固定项目的 `formalization/ueot-core` 后，以该项目的固定 Lake 环境运行：

```bash
/Users/murphyhoops/.elan/bin/lake env python3 "$UEOT_D3_BUNDLE_V2/run_d3_reproduction_v2.py" \
  --repo "$UEOT_D3_REPO" --output "$UEOT_D3_OUTPUT_V2"
```

以上三个任务变量由主审赋为已经核实的绝对路径，输出目录必须是尚不存在且位于仓库之外的新 run 目录。不要复用、清空或覆盖 v1 失败目录。若 v2 阻塞，保留回执与日志，停止在实际故障点，不自动更换工具链、放宽公理检查或启动全库重建。
