# 同源长期链生产提升：独立源码与治理审计

审计者：`/root/source_scope_audit`。源码基线：`1532f83fcfd1fc572aa714bad4d7fb1e0fa2de9a`。审计对象：`/workspace/scratch/534b0448126c/ueot-core-next`。本报告为只读静态审计；没有执行 Lean、native、完整构建或远端修改。

## 1. 当前结论

**八源提升 `STATIC_SOURCE_PROMOTION_CLEAR`。** 从不可变基线 Git 对象读取归档源，使用仓库的嵌套注释解析器比较，八个生产文件去掉注释、import、`#print` 后的声明及证明代码全部相同。import 变化恰为私有模块名全限定；生产文件无 `#print`。公开根文件恰增加八个 import，没有删除原 import 或改动其他代码。归档哈希全部对应已审编译收据；生产及归档哈希全部匹配新的 `CHAIN_PROMOTION_SOURCES.json`。完整机器记录见同目录 `CHAIN_PROMOTION_STATIC_REVIEW.json`、`PRIVATE_INPUT_BINDING.json`、`INPUT_SOURCES.json`。

**Ops 已提交候选 `STATIC_COMMITTED_OPS_DIFF_CLEAR`。** 候选 `169274e14873a27a1ef68523a5473889af0f2c2c` 只改 `COMPRESSION_RESEARCH_TRACKS.json`；语义变化只有原 exception 的 ID、branch pattern、reason 三项。六个 exact paths、TC 所有权、`temporary: true`、其他全部 policy 字段不变。policy SHA256 为 `1ba448d36e23201149e510adc64cdd0bbcff7f82000432ae100cc3cbb793444f`。`git diff --check` 为 0。详见 `OPS_COMMITTED_STATIC_REVIEW.json`。此审查不等于 Ops 已 canonical 合并，也不授权研究候选使用候选内新 policy 自行放宽边界。

**发现真实新增代码片段匹配。** 现有 666 模块的当前字节精确重现旧 68 条；加入八个同源链模块后的 674 模块限定诊断得到 69 条，旧 68 全保留。新增是 `SameSourceConditionedTerminal.lean:92–99` 与 `SameSourceQSDBinding.lean:30–37` 的 private `map_injective_atom` 证明，共八个非空代码行。详见 `CLONE_SCOPE_DIAGNOSTIC.json`。不能覆盖不可变 `CLONE_CANDIDATES_68.json`；应以新增证据记录 delta，并使现行 scanner 验证旧集合加显式 delta。所有策略/SISC 文件冻结后需重新取得最终扫描结果。这一诊断不声称现行完整 freshness 检查已通过。

## 2. 最小 API 与不能改变的数学条件

下列文件均在 `formalization/ueot-core/UEOT/V3/Compression/TheoryCompletion/UnifiedClosure/`。命名空间保留各文件的 `*Check` 名称，避免增加同义别名。理论根只导入 QSD、ExitFlux、SurvivalTail 三个叶节点已足以传递覆盖八源；当前八条明确 import 也合法。

| 文件 | 公共 theorem/lemma 数 | 实质端点与声明边界 |
|---|---:|---|
| `SourcePolicyPathBridge.lean` | 2 | L72 `actual_next_state_eq_stationary_row`、L96 `actual_state_path_eq_stationary_path` 从同一实际 `transitionPMF` 与动作擦除推出闭环行及状态路径身份。有限 X/A、A 非空，Y 任意；反馈为时间齐次的当前观察随机反馈。没有把待证核相等放入新字段。 |
| `SameSourceKilledPath.lean` | 5 | L35 killed 矩阵限制同一个 `policyTransition`；L42 `safeInitialRow` 保留 p0 在 K 上原始质量。L187/L277/L320 连接实际终点联合质量及总存活质量到 killed 幂。包含时刻 0，不要求 p0(K)=1、K 非空或存活正。 |
| `SameSourceConditionedTerminal.lean` | 11 | L126 的 PMF 确实过滤实际安全路径后映射末态。L176 等于归一化 killed 终端分布；只在 `hpos : 0 < s` 后构造条件 PMF。L218/L227/L239/L251 分别保留零存活无过滤见证、时刻 0、时刻 0 条件化、空 K 边界。 |
| `SameSourceQSDBinding.lean` | 13 | p0 明确为 `r.map Subtype.val`；hleft 是当前同一 killed 矩阵的左特征等式。推出实际联合质量/存活 `rho^n`、rho 界、正存活条件终端律。L104 的 GOA 包仍消费 hleft 与正 rho；没有证明一般 QSD 的存在。rho=0、n=0 与 n>0 分别保留。 |
| `SameSourceKilledExitFlux.lean` | 13 | L31/L42/L52 是 PMF 扩展与实际因果律前缀边缘。L169 把实际首次退出概率识别为 killed 通量；L216 把失败分成初始失败与后续首次退出。`riskFirstExitAfter K n` 指 0..n 安全、n+1 首次退出，不含初始失败。 |
| `SameSourceInfinitePrefix.lean` | 7 | L76 为完整有限状态历史到 `Finset.Iic n` 前缀的可测等价；L140/L171/L192 连接同一 p0、同一闭环核的实际完整状态前缀与既有 `homTrajMeasure`。只声称经动作擦除后由状态前缀决定的事件，没有声称任意动作依赖事件身份。 |
| `SameSourceSafePrefix.lean` | 4 | L40/L77 从递归定义证明安全事件拉回身份；L105/L131 在上述同一个无限轨迹测度中识别实际有限安全质量。`survivalSet` 的输入是失败集 Kᶜ，包含时刻 0。 |
| `SameSourceSurvivalTail.lean` | 1 | L34 `killed_survival_mass_tendsto_homogeneous_neverHit_real` 用同一测度的递减事件连续性与有限前缀身份，证明 killed 总质量趋于真实永不退出概率。没有 hpos、QSD、初始安全、非空 K 等附加条件。不能据此推出极限严格为正。 |

公共候选合计 **56**。这个数不包括定义、instance、private theorem、编译器生成 theorem；native census 必须包含所有目标模块实际拥有的 theorem constants，而不能只看 56 个词法候选。若后续 native 发现类型重合，应保留真实失败和相应辅助结论，只按真实消费者收缩公共 API；不能伪造零重合收据。

共同边界：一般历史策略/非自治策略不满足本组 stationary-kernel 的固定模型输入；它们必须另建实际核或扩张桥。QSD 条件终端稳定不是有限窗条件路径等于固定 Doob 过程。有限时域每次存活为正不推出无限存活为正。

## 3. 治理授权及需修改的位置

依据：`docs/REPOSITORY_BRANCH_GOVERNANCE.md` §§9、11；`formalization/ueot-core/docs/compression/POST_FINAL_RESEARCH_GOVERNANCE.md` §§1、4、5。L1 允许所属命名空间新增文件与 import-only 根；修改已合并 live consumer 属于 L2，需要真实不可变基线上的精确 exception、完整 UEOT 回归与独审。Ops 应先独立成为 canonical；研究分支必须以含该授权的 main 为基线。

根目录别名（本报告及命令用）：

- `TC = formalization/ueot-core/docs/compression/theory_completion`
- `UC = TC/unified_closure`
- `KN = TC/knowledge`
- `REUSE = KN/reuse`

Ops 原有六路径范围足以处理本轮现行登记，不能扩展到冻结 counted 文件：

| 已有路径 | 必需变化 |
|---|---|
| `UC/UMC_GLOBAL_MODULE_DAG_V4.json` | 在全部新模块与根 import 冻结后，由现有 `build_umc_global_map.py` 重建实际源指纹、模块数、root 可达、cycles/missing imports。该图是源码 metadata，不是内核依赖证据。 |
| `KN/README.md` | 更新当前 census、当前层证据入口及范围；保留历史计数。 |
| `REUSE/fkrg_reuse.py` | 在 L24 起的四个平行 registry 数组末尾登记新 overlay、固定 verifier 与各自 SHA；旧八层、base CSV、环境 pins 均保留。新增 clone delta 必须显式 hash-bound 并 fail-closed；不能悄悄替换旧68。 |
| `REUSE/test_fkrg_reuse.py` | 更新 live totals（L23/L26/L30/L38–42、L736/L775）并保留原层断言；新增真实 scope/owner/axiom/type/edge/hash 及 clone delta 的必要核对。不得把期望 PASS 写成观测结果。 |
| `REUSE/README.md` | 登记第九层实际观测与科学范围，区分 typed/lexical/source/native，保留全部历史事实。 |
| `REUSE/REBUILD_CLONE_CANDIDATES.py` | 改为比对实际 live scope 与不变旧68加新增已固定 delta；保留扫描算法含义。新增 clone 不等于逻辑等价。 |

L1 新增文件应包括：新 overlay JSON、新固定 Lean verifier、新 native JSON、需要的 clone delta JSON、来源/完整 build identity/native 执行/审计收据及适配后的专用 native 工具。`TheoryCompletion.lean` 允许 import-only；`THEORY_COMPLETION_STATUS.json` 是现行唯一 mutable-existing live 状态路径。`fkrg.py`、`pr_preflight.py`、旧 overlay/certificate/native、CSV、`CLONE_CANDIDATES_68.json`、ledger、workflow、toolchain/lakefile/manifest 不需修改。

登记的三个范围必须相符：

1. 新生产源的全部实际集合，包括无限策略/SISC 模块；source scope + 每文件 SHA。
2. 现行完整 UEOT 源集合，加 root source-hash override；`fkrg_reuse.verify_sources` L415 检查精确集合与字节。
3. 所有新公共候选的 native ownership/type/proof-edge/axiom scope；`load_overlays` L130 检查 prior chain 与证书；新增常量的完整 private/generated census 独立保存。

## 4. Native 与类型复用最小责任

当前注册图为 **666 模块、4,147 公共节点、5,418 条注册边、八个 overlay**，其中 655 维护模块、11 上游改编模块。只加入这八源且保留全部 56 公共名时，必需比较计数为 56×4,147=232,232 跨层对与 56 choose 2=1,540 内部对；总模块为 674、节点为 4,203。若同一层还包含策略/SISC，按最终实际集合重算，不能沿用这些子集数。

`UC/registered_interfaces/native_protocol/` 旧工具是之前七源+一历史修复的专用协议，写死 659/4094 predecessor、52+1 candidate、666 source scope。**不能直接拿旧命令运行本轮，不能仅改 scope JSON 就声称兼容。** 需在新增目录形成新的隔离适配工具，当前 predecessor 666/4147，八个 prior overlays，按所有最终新源生成候选集。上一层的 historical repair 已处理完，本轮不能重复登记。

最小真实顺序：全源指纹及构建环境核验 → 实际 focused/full build → 初次实际 native export（不能预填 PASS/边）→ 用观测结果生成固定 verifier → 实际执行固定 verifier → 完整 JSON 对象一致 → 独审 → hash-pin 新 overlay/verifier/native → live freshness 与回归。所有失败日志原样保留。

每次 raw stored type `Meta.isDefEq` 使用原协议的 fresh `liftTermElabM`；保留实际 universe 参数。结果只证明本次编译环境中的定义相等比较，不能表述为逻辑独立性或科学唯一性。完整 native scope 保留 source owner/private 标记/type/direct constants/完整传递 axiom closure，仅允许 propext、Classical.choice、Quot.sound。

实际 build identity 应绑定全部 production 源、三环境文件、九个干净且准确的依赖 checkout、Lean/Lake 二进制及版本、focused/full logs 与退出状态；在 native 前后及 finalization 重查。旧归档私有 `.olean`、本次八文件 focused manifest 均不能代替完整生产 identity。

## 5. 最小命令清单（root 执行，本审计未执行）

所有候选检查中的 `BASE` 必须是 Ops 已 canonical 后的真实研究 PR base；`CANDIDATE` 必须是实际 Git commit。以下变量为路径简写，不可把模板中的未运行命令写成已完成。

```bash
TASK_REPO=/workspace/scratch/534b0448126c/ueot-core-next
TC=formalization/ueot-core/docs/compression/theory_completion
REUSE="$TC/knowledge/reuse"
UC="$TC/unified_closure"
```

源冻结后（获 canonical L2 授权后）重建现行图：

```bash
python3 -B "$UC/build_umc_global_map.py"
git diff --check
```

在 pinned `formalization/ueot-core` 环境运行所有新增模块的 focused build，并在整组实质集成一次运行：

```bash
lake build UEOT
```

新的 native 工具准备好后，其 runner/finalizer 应接受并验证实际 `--repo`、`--output`、`--lake`、`--build-status`、`--build-manifest`、`--build-log-dir`、`--focused-label`、`--full-label`、`--base-ref`。目前不提供旧工具的可执行代用命令，以免误用其硬编码 predecessor。固定证书执行本身为 pinned 环境中的 `lake env lean <新固定证书路径>`，必须保存实际 stdout/stderr/returncode。

完成真实登记后的只读 live gates：

```bash
python3 -B "$REUSE/fkrg_reuse.py" --json status
python3 -B "$REUSE/test_fkrg_reuse.py"
python3 -B "$REUSE/REBUILD_CLONE_CANDIDATES.py"
python3 -B "$TC/knowledge/fkrg.py" build
python3 -B "$TC/knowledge/fkrg.py" verify-index
python3 -B "$TC/knowledge/test_fkrg.py"
python3 -B "$UC/validate_unified_closure.py" --repo-root .
python3 -B "$UC/test_validate_unified_closure.py"
```

immutable-base parser 需要先从 `BASE` 创建隔离 detached worktree `AUTHORITY`，在该工作树运行 base 自己的 `test_pr_preflight.py`，再调用 base parser 读真实候选 Git 对象：

```bash
python3 -B "$AUTHORITY/$REUSE/test_pr_preflight.py"
python3 -B "$AUTHORITY/$REUSE/pr_preflight.py" \
  --repo-root "$TASK_REPO" --baseline-ref "$BASE" --candidate-ref "$CANDIDATE" \
  --report "$AUDIT_OUT/pr_preflight.json" --summary "$AUDIT_OUT/pr_preflight.md"
```

`PASS_WITH_TYPED_REUSE_REVIEW_REQUIRED` 仍要求 typed/native 审查；词法 parser 不替代它。`.github/workflows/ueot-core-compression.yml:288–327` 是权威 base parser 实际流程。

研究 PR 常规 governance（包括 live state）与完整测试依照现行 workflow：

```bash
python3 -B formalization/ueot-core/scripts/validate_compression_research.py \
  --repo-root . --baseline-ref "$BASE" --candidate-ref "$CANDIDATE" \
  --branch-name compression/theory-completion-longterm-policy-sisc \
  --head-repo MurphyHoops/UEOT --base-repo MurphyHoops/UEOT --verify-live-state
python3 -B formalization/ueot-core/scripts/test_validate_compression_research.py --repo-root .
python3 -B formalization/ueot-core/scripts/validate_compression.py \
  --repo-root . --baseline-ref "$BASE" --verify-finalization-refs
python3 -B formalization/ueot-core/scripts/test_validate_compression.py --repo-root .
python3 -B formalization/ueot-core/scripts/test_validate_finalization_receipt.py
```

research/main 保持完整 FKRG 30 项，包括真实 fast audit；只有独立、base-authorized Ops-only PR 才按现行 workflow 自动判定一个 TC-only test 不适用，不允许人为传 skip 开关。当前 cloud proof job 手动触发，自动 SKIPPED 要原样报告。完整本地构建、远端 source/governance、native、PR/合并后 main 是不同证据，不能相互冒充。合并后核对 resulting-main tree 与已审生产候选一致。

## 6. 其他两条并行科学线路的审查提示

无限策略必须固定实际非自治转移/认证序列与初态，构造同一个总因果策略，再证明它自己的占据；`∀T ∃π_T` 不能换名得到 `∃π∞ ∀T`。若公开结果仅为支持安全无限控制器、未连接实际 PMF law/occupancy，应明确作为部分完成。有限记忆由支持与认证齐次条件支持；数值齐次 killed 路线需要额外桥。原有限 `viablePolicy` 的前缀复现与新的无限控制器不是同一策略。fallback 在 source-zero/reference-positive 历史上仍进入参考检查预算。零未认证占据到物理安全还需初始安全与认证转移支持安全。

SISC 包装须保留固定 N_j>0、行内独立与每样本真实均值，建立同一 kernel/source/action/read 与原 risk/prediction 的身份；仅有 [0,1] 读数 concentration 不足以适配现行候选模型风险。Good 经确定性 Lipschitz 同时约束候选不需要额外按候选数并合，但 N3 的非空探针和 N6 当前全候选竞争者量词必须保留。外部认证与统计来源责任不能藏进构造器里当已证。具体 PMF 实验需要真实 source，再检查候选选择程序不把未知真候选当输入。

本轮均为 uncounted post-Core 增量。C1–C7 全局科学闭合仍 `NOT_ESTABLISHED`，106 P-ID 的 11 generated/89 adapters/6 boundaries 与四个 counted generators 不变。原始规格范围的具体出处和完整 C1–C7 检查点见 `/workspace/scratch/534b0448126c/tmp/source_scope_audit.md`。
