# C：3.11 出版绑定代码分离审查

审查者：原生研究子智能体 C。日期：2026-11-14（Asia/Shanghai）。
本审查未修改共享书稿、metadata 或 C 已冻结的 35 文件交付。

## 初审裁决（修复前的历史记录）

**`CHANGES_REQUIRED_BEFORE_FINAL_PUBLICATION_BINDING`**。

后续修复与当前裁决见文末追加回执。

这是对初始出版脚本的静态与局部只读检查，不是实际 3.11 构建/视觉验收。
检查时第70章尚未组合，v31.14 runtime 和 v3.11 acceptance/visual 回执尚未
生成。因此没有宣称这些将来的门已经通过。以下问题均可由主智能体在已授权
出版范围内窄修复，不需要重新请求用户授权。

检查的脚本身份：

| 文件 | 本轮初审 SHA256 |
|---|---|
| `physics/qm/book/build/update_v3_11_metadata.py` | `710490da940b96e14bbb54f128f25fe93cf09996d79ad4508e92b437b21f9301` |
| `physics/qm/book/build/verify_v3_11_increment.py` | `db62eb1a241e39ee9eb21c3c8235bdad5b001c1e771201fd9d8c6938b05dccb8` |

## 已确认的正确部分

1. 新稳定编号恰好九个；中英解析目标都是0–70章、6附录、203结果；账本目标
   为126项。Writer 逐项复制旧194个结果及旧117个主张，独立 gate 比较的是
   JSON 对象相等，未用只有计数的检查替代保全。
2. 旧 source entries 保留并追加 QM3114。新增结果明确
   `PAPER_AND_EXECUTABLE_EVIDENCE_NO_NEW_LEAN`；没有把旧 Lean 执行重新命名
   为第70章机器证明。作者字段从 prior dossier 继承钱德桂，没有以代理取代。
3. 新增实测状态明确 `MATCHED_DEVICE_NOT_CERTIFIED`，并单列外部处理后观测
   复核及强标准 `EQUIVALENT_NO_ADDED_GAIN`。三位原生 AI 审查未被写成外部
   人类同行评议。
4. `SOURCE_MANIFEST -> CHAPTER_DOSSIER -> CURRENT` 的主要 SHA 写入方向
   没有直接自哈希循环。最终 source inventory/acceptance 仍须检查是否反向
   包含这些输出，见后文。
5. 对 writer 的 `body()` 函数进行独立切片比较：检查时中英文各76个
   章/附录切片，均与基于连续锚点的独立切分完全相同。
6. 对 `prior/SNAPSHOT.json` 的11个条目逐个执行只读
   `git show ee7fb2793a1dbb519703bba05f535f0d962d9e56:<origin_path>`。
   **11/11 原 git 字节、snapshot 字节和声明 SHA 全部一致**。这独立确认
   保全基线确实来自恢复第69章后的 ee7fb…，不只是一个自报 SHA 的新备份。

## 需修复的出版绑定问题

### R1：deepcopy 遗留的“当前”字段仍指向3.10/v31.13

Writer 更新了若干顶层字段，但以下 prior 字段仍会原样遗留：

| 目标 | 遗留字段 | 初始值/问题 | 最小修复 |
|---|---|---|---|
| SOURCE_MANIFEST | `unified_source_identity`、`publication_source_identity` | current check仍为v31.13，scope只说不含69章 | 设为本轮已收窄的同一个 proof identity，保留v31.11实际执行身份 |
| SOURCE_MANIFEST | `scientific_execution_partition` | new_runtime/historical_reuse仍v31.13 | 指向v31.14实际回执/复用核验，实测与外部处理后数据分别描述 |
| SOURCE_MANIFEST | `local_release_receipt_scope` | `Book3.10 publication` | 更新为3.11与实际scope |
| DOSSIER | `historical_metadata_scope` | 仍写188个旧结果、current为3.10 | 写194/117保全；明确本轮字段是publication_3_11，旧嵌套历史字段不升级为新执行 |
| DOSSIER | `verified_inventory` | proof_reuse/runtime仍v31.13 | 更新当前检查和执行身份，旧库存由prior快照保全 |

此外，`remote_metadata_completion` 从原字典改为字符串，删除了
`metadata_followup_is_not_a_new_scientific_execution` 说明；canonical identities
也从带 edition/count/language/scope 的对象变为仅 path/hash/bytes。
现行 gate 不依赖这些旧键，故不一定立刻报错，但无必要时应保持一致的字段
类型与完整当前语义，避免下一个接续消费者读出互相冲突的信息。

建议独立 gate 明确核对上述 current 字段。旧 result/claim/source-entry
对象继续逐项原样保留；这里修的是当前别名和说明，不是重写历史。

`proof.scope` 建议写“历史v31.11执行，不含第69或70章新增Lean覆盖”。
只写“no Chapter70”虽然有历史only限定，仍不如同时列出两章准确。

### R2：缺少防止已验证远端状态被默认降级的保护

Updater 每次从 prior 初始化。当本轮已经远端验证后，若再次不带
`--integration` 运行，初始版本会无条件重写为
`LOCAL_VERIFIED_REMOTE_PENDING`，清除本轮已有远端当前身份。

可在普通代码中自动处理：若现行同版本已绑定完整 integration，则校验并
复用该回执；或明确拒绝无 integration 的降级调用。无需增加用户审批。
这不会阻止首次本地 pending 构建，也不应把新 source 自动冒称已获旧 CI。

### R3：视觉 PASS 未与实际受审 PDF 绑定

Gate 当前只检查 `visual.status == PASS_SCOPED` 和非空 `reviewed_pages`。
它没有读取视觉回执中受审 PDF/source SHA 并与现行构建比较。旧 PDF 的
视觉 PASS 可能在重排后被误用，即便现行 pdf-build 的 source/PDF 两个
hash彼此相符。

需验证每种语言视觉回执的 PDF/build 身份等于当前文件，并核清实际审查
页集合与本轮新增/修改范围。不能把局部页面验收改写成全书逐页视觉审查。
实际范围将由后续 C 英文新章视觉审查和其他代理审查回执提供。

### R4：数值证书应加入定向检查

现有“中英显示公式完全相等”是有用检查，但两边一起使用向内舍入仍会通过。
最终发布数值应从 C `FINAL_CERTIFICATE.json` 的 exact Fraction 与向上
显示字段绑定；至少检查正文和绑定条目的上界不小于相应精确数：

| 目标 | 精确值 | 向上显示 |
|---|---:|---:|
| 参数误差 | 0.0365677356444 | 0.036567735645 |
| 完整量子CQ | 0.0365811856444 | 0.036581185645 |
| 加共享固定末端读出 | 0.0404514142049 | 0.040451414205 |

历史 NOMINAL 的 `.036567735644` 显示更正已有独立回执，不能从旧文件拿
这个最近舍入值重新出版成严格上界。归一成功后精度、任意变更中间操作和
真实器件均不在上述数字的无条件范围内。

## 最终集成时需回读的责任

### 1. source/evidence 图不得形成间接哈希循环

源码清单与 local acceptance 的 `current_artifacts` 应限于已冻结的科学
源、构建源/产物及先发生回执，不能包含随后会由 writer 改写的
SOURCE_MANIFEST、CHAPTER_DOSSIER、CURRENT，或最终独立 gate 自己的输出。
否则当前 `manifest -> dossier -> current` 主链虽然无直接循环，外围输入
会在 writer 运行后立即陈旧。初审时这些 inventory 尚未生成，待实物回读。

### 2. preservation gate 的两个整章例外及附录

Gate 跳过第0和48章的全部科学正文，只以注释说明导航更改另审。应保存
具体允许的版号/目录/当前状态编辑清单，或让分离审查对这两个完整 diff
逐项批准。第0/48章的科学段落不能因这个例外不受检查。

附录也没有 old-body equality 检查。若本轮完全不改附录，可直接比较；若
只新增来源或改导航，则明确允许差异。历史程序 payload 的“未改”主张仍
应与实际 fenced-code 字节或既有程序保全回执一致。

### 3. 证明复用应有实际当前核对

Current 将继承 `current_bytes_match_executed_bytes=True`。需确认v31.14
proof-reuse回执确有158输入身份核对、零错误、无新Lean执行，并由当前
运行回执/源码清单绑定。检查一个布尔值或只校验回执文件自己的SHA不等价于
重新确认这158项当前源码与历史执行来源相同。若已有主智能体实际核对，应
复用该证据，无需重跑Lean。

### 4. 其他代码小项

`--require-complete` 在初始 gate 中声明却未使用；实际程序总是执行完整门。
可删除该无效参数或明确定义其效果，避免调用者误解。这不是科学阻塞项。

## 后续验收

主智能体修复并提供实际 build/evidence 后，C 将回读更新脚本、metadata、
数值及英文第70章对应 PDF 页，形成范围明确的追加裁决。当前审查没有发现
需要重开旧194结果、旧117主张或重跑旧Lean的理由。


## 已授权修复与当前代码裁决

**`PASS_FOCUSED_CODE_AND_RUNTIME_CHECKS; COMPLETE_PUBLICATION_PENDING`**。

根代理已明确授权 C 直接修复两个出版代码文件。C 仅修改
`update_v3_11_metadata.py` 与 `verify_v3_11_increment.py`；未修改书稿、现行
metadata、原 C 冻结交付或原始科学程序。当前代码身份与实际检查结果见同目录
`C_METADATA_CODE_CHECKS.json`，其 SHA 是对补丁后的文件字节计算的。

### 已完成的修复

- Writer 更新全部已识别的当前 proof/runtime/publication aliases，保留真实
  v31.11 证明身份；`proof.scope` 明确第69与70章均无新增 Lean 覆盖。
  现行 publication code manifest 指向 v31.14，旧 proof code manifest 保留
  v31.11 并增加明确历史 scope。旧 source entries 不改写。
- 同版本已经 MAIN 验证后，无 `--integration` 的默认重跑会在任何 metadata
  写入前拒绝降级。已有 integration 回执仍可按普通续作传入；没有新增人工审批。
- Writer 与 gate 对两语当前 PDF/source/build identity、真实查看页与必审页
  集合、审查报告 identity 作绑定；local acceptance 必须覆盖两语 md/tex/pdf
  六个当前产物。机器身份检查不替代视觉观察。
- Gate 读取生产 runner 的实际 `source_files`、`copied_inputs`、`output_files`
  结构。原绝对执行目录保持为历史记录；当前读取路径仅按 source/authored/runtime
  三种角色映射至当前 checkout，逐项验证源、工作副本、输出及日志的原 SHA。
  `runtime.json` 与 `execution_receipt.json` 必须字节相同。
- Gate 核验10项命令成功、各检查点输入稳定、1,600,000行历史合成样本复用、
  零新采样/硬件/Lean，以及隔离 calibration readback 的实际输出身份。
- Gate 用 `Fraction` 独立核验参数半径、51/10 常数、截断和修复预算、量子与
  读出总和、向上12位显示、所有96事件的外扩显示与分类一致性；正文和 P-ROB-07
  元数据必须含最终两项上界。原 NOMINAL 仍以原 SHA 保留。
- Gate 对当前158个历史 proof inputs逐项重新核对SHA/字节数，并重算其固定
  source-set hash；没有执行Lean。
- Gate 继续要求旧194个结果对象与旧117个主张对象逐项相等；作者保留钱德桂。
- source inventory/acceptance 不能包含即将改写的 metadata、自身或当前 gate
  输出，从而阻止这些可确定的哈希循环。新增导航审查绑定见下。

### 实际验证与负控

`C_METADATA_CODE_CHECKS.json` 记录13个针对性案例、2,127个已执行检查项：
实际生产 runtime与最终精确证书通过；同一回执的历史绝对根目录替换为不存在的
旧路径后，按角色映射仍通过；四项向内舍入、陈旧生成输出SHA、虚报零新增采样、
旧视觉PDF SHA、缺失必审页面和已验证 MAIN 默认降级均按预期被拒绝。

视觉相关负控使用单独临时单元夹具，其内容没有作为 PDF、正式回执或真实视觉
验收交付。这里没有把这些单元检查宣称为完整出版 PASS。

### root 正式回执字段契约

`visual-review.json`：

```json
{
  "edition": "3.11",
  "status": "PASS_SCOPED",
  "scope": "明确实际查阅范围",
  "independent_human_peer_review": false,
  "languages": {
    "zh": {
      "source": {"path": "repo-relative md", "sha256": "...", "bytes": 0},
      "pdf": {"path": "repo-relative pdf", "sha256": "...", "bytes": 0},
      "build": {"path": "repo-relative pdf-build.json", "sha256": "...", "bytes": 0},
      "page_count": 1,
      "physical_pages": [1],
      "required_pages": [1],
      "review_reports": [{"path": "repo-relative review", "sha256": "...", "bytes": 0}]
    },
    "en": {"same_fields": "as zh"}
  }
}
```

所有示例占位值必须换成实际文件和实际页。`required_pages` 必须非空且为
`physical_pages` 的子集；不允许以本轮局部视觉检查冒充全书逐页验收。

`local-acceptance.json` 保留 `status=PASS_SCOPED`、`new_hardware_data=false`，
`current_artifacts` 至少包含两语md/tex/pdf六个identity，另有
`visual_review={path,sha256,bytes}`。

`navigation-edit-review.json`：`status=PASS_SCOPED`，两语 `languages.zh/en`
各包含 `prior_source` 和 `current_source` identity，
`historical_fenced_code_preserved=true`，以及
`edits=[{anchor,prior_body_sha256,current_body_sha256,allowed_changes}]`。
`allowed_changes` 为实际逐项审查后的非空字符串。edits集合必须恰好等于
第0、48章及六附录的实际变化块集合；哈希覆盖从锚点到下一锚点的完整UTF-8
原始块，包括尾部换行，变化检测使用strip后比较。该回执必须列入本轮
source-manifest的files。C核验哈希与覆盖，root对许可差异的科学语义负责。

### 仍待实际出版验收

两语真实PDF构建、导航/附录逐项审查、真实视觉回执、source inventory及
metadata尚需按最终字节运行完整独立gate。C随后对英文第70章实际物理页作
视觉审查。当前已修复代码没有遗留科学量词阻塞；尚未完成的实物验收不可省略。
