# SOURCE_IDENTITY_REUSE_AUDIT — 现行源码与历史Lean验证回执复用

## 1. 结论

本次仅执行只读源码字节、Git历史对象、导入依赖和回执身份核验；**没有运行Lean、Lake、旧原生枚举或新CI**。核验固定在提交 `3d443ec29eb17af1fc00699a74e2d42d73516d81`。本出版分支的冻结源码、原Core和规格清单差异为空。

现有证据支持按准确范围复用：原106个P-ID的163个端点位于112个实际定义文件，其包括全部传递内部导入在内的287个UEOT源码文件，与106/106最终提升提交完全相同；PR444的1048份生产源码清单中1047份仍精确匹配；剩余一个入口与新增三模块由PR447五份定向编译回执覆盖。当前1051个生产模块可从UEOT静态到达，但本次没有重新构建这张完整图。

机器详表为 `SOURCE_IDENTITY_REUSE.json`；复现脚本为 `audit_identity_reuse.py`。SHA相同证明字节相同，不单独证明定理有效；实际历史编译状态来自原回执和日志。本轮没有向GitHub重新查询旧CI服务状态，故CI成功状态按仓库原账本引用，未改称本轮远端执行。

## 2. 冻结Core与106个P-ID

| 项目 | 实际核验 |
|---|---|
| 原Core文件 | 183440字节；SHA256 `ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`，匹配原账本/现行manifest |
| 原106/106提升提交 | `1e2a3924ef31b5dca589dca69c3838fc355b8850`；为现快照祖先 |
| 账本记载的提升CI | `36249418600`；历史 `lake build UEOT`合同，不是本次CI |
| 实际P端点 | 106个P-ID、163个不同声明、112个实际定义文件；不是163个P-ID |
| 内部依赖闭包 | 287个UEOT源码文件，包括112定义文件；逐文件Git旧对象与当前字节全部相同 |
| 工具链 | `leanprover/lean4:v4.33.1`；与原提升提交逐字节相同 |
| Mathlib | manifest钉住 `0df444a360eaa60ab8c11dca51a86af692955474` |
| 配置身份 | lean-toolchain、lake-manifest.json、lakefile.lean与原提升提交及PR447复用记录均相同 |

正式构建目标仍为 `lake build UEOT`。`V3_COVERAGE_STATUS.md`中的“尚未同步原书”是早期历史检查点；现行 `core/status/CURRENT.md`与实际原书字节已经记录同步完成。本轮没有改写历史账本。287文件是对163端点实际定义文件的静态内部依赖闭包，并非声称Mathlib全部源码于本轮重新编译。

## 3. PR444完整集成回执的精确范围

`core_theory_closure_v1/checks/INTEGRATION_BUILD.json`记录2026-11-07的 `lake build UEOT`，exit 0，模式为 `INCREMENTAL_EXISTING_LAKE_CACHE`，Lake报告9754 jobs。它不是清缓存全库重编译。原构建日志的SHA256与回执相同，构建回执及静态源清单本身的SHA256也与该包 `DELIVERY.json`相同；静态清单1048条的确定性摘要已重新计算并匹配。

| 对照 | 实际结果 | 可用范围 |
|---|---|---|
| 原1048生产文件 | 1047相同，0删除，1不同 | 可复用未变源码与历史集成来源 |
| 唯一不同文件 | `CoreTheoryClosure.lean` | 旧单文件/旧整图身份不能直接冒称当前入口已检查；使用PR447新入口回执 |
| 新增生产文件 | GrowthClassification、GrowthPopulation、GrowthAttainment三个模块 | 使用PR447定向编译来源 |
| 原13个单模块回执 | 12个源码仍完全相同；13份回执文件本身均匹配原分离审查所存SHA，记录returncode均0 | 第13个旧CoreTheoryClosure回执保留历史身份，由新回执接续 |
| 当前静态生产图 | 1051文件、9942251字节、全部从UEOT可达 | 是当前静态身份检查，不是本轮Lean编译 |

旧 `CoreTheoryClosure.lean` SHA为 `2a3ecb1fc672a10e7b0fc74eeae9c8b00fd4d6ac94be8174d6578c9016e48328`；当前为 `c14befb44ce0d87a7db3d044671c1f88ca9415a822597c1bca0eedd9eaec50ac`。当前生产清单摘要为 `d9a10eff0c3c1f3cca22aedfeb088afa1361426242cd7f975d67ec4f0a90b7ce`，与旧整图摘要不同是预期的版本事实，不能把旧整图验证日期改为本轮日期。

## 4. PR447增长扩展的五份精确回执

`core_growth_classification_v1/LEAN_VALIDATION.json`明确 `full_historical_build_rerun: false`。本轮将五份回执各自的source_sha256与当前文件比较，并核对原退出码0、原日志存在、结构化公理列表与原日志15个返回逐项一致。三新增模块、受影响入口和边界消费者全部精确匹配。

| 实际文件 | 当前与历史回执共同SHA256 | 历史结果 |
|---|---|---|
| CoreRegenerativeGrowthClassification.lean | `ce5f6f1119a3a1c209148280200fed532377ba4b28a6745813ab3dcae0bd7dcb` | exit 0；原日志存在 |
| CoreRegenerativeGrowthPopulation.lean | `e69d2ef25be8a7ea0a74bc6e8c7d24580cd1d614691c5e38d9c5292848864b54` | exit 0；原日志存在 |
| CoreRegenerativeGrowthAttainment.lean | `952740533202112b37765f3a887dbe1e65dbee1864f386abb7b3abf759529edd` | exit 0；原日志存在 |
| CoreTheoryClosure.lean | `c14befb44ce0d87a7db3d044671c1f88ca9415a822597c1bca0eedd9eaec50ac` | exit 0；原日志存在 |
| GrowthClassificationCheck.lean | `80e83ae1a7b6b774e605bf7d7d2b55a75419ad45b96fd99c50460db2e9e6dfec` | exit 0；原日志存在 |

该包 `SOURCE_BINDING.json`的11个原执行/再生/人口源码、工具链、manifest、lakefile及三个书籍构建文件的记录SHA目前也全部匹配。该结论只固定这些旧文件；新书成品与新英文构建入口仍由本轮实际出版构建记录负责。

15个原公理打印端点只列 `propext`、`Classical.choice`、`Quot.sound`，原日志与结构化表相同。此项是旧日志复核，不是本次运行#print axioms。它不移除PR443已公开的两处native_decide数值信任，也不扩张成全部历史端点的新公理审计。

## 5. 其他主要UnifiedClosure来源包

进一步读取28个 `SOURCE_VALIDATION.json`中明确记录的Lean源SHA，或其 `proof_bytes_verified`表；合计247个不同源码文件全部与当前字节相同。仅写basename的历史记录通过生产树唯一文件名解析，未猜测重名路径。它们的历史OPEN/PENDING标签保留原日期语义；源码一致不把历史未完成的发布步骤倒填成当时已完成。

| 来源包 | 明确源SHA条数 | 当前匹配 |
|---|---:|---:|
| actual_infinite_sources_v1 | 2 | 2 |
| adaptive_stochastic_sources_v1 | 5 | 5 |
| bounded_control_carrier_source_v1 | 12 | 12 |
| canonical_brownian_source_v1 | 3 | 3 |
| compensator_population_source_v1 | 8 | 8 |
| conflict_family_book_source_v1 | 9 | 9 |
| continuous_history_source_v1 | 2 | 2 |
| continuous_resource_source_v1 | 9 | 9 |
| drift_ou_instruction_qfull_source_v1 | 22 | 22 |
| finite_predictive_source_v1 | 3 | 3 |
| fixed_q_run_stateweighted_source_v1 | 24 | 24 |
| full_qv_vector_training_source_v1 | 15 | 15 |
| funded_countable_block_source_v1 | 5 | 5 |
| general_perron_compact_spectral_source_v1 | 10 | 10 |
| history_integral_source_v1 | 5 | 5 |
| ito_vector_calibration_source_v1 | 17 | 17 |
| native_lifecycle_rank_source_v1 | 4 | 4 |
| owner_discovery_resource_source_v1 | 3 | 3 |
| p9_lineage_organization_source_v1 | 5 | 5 |
| past_feedback_scale_source_v1 | 8 | 8 |
| predictable_finite_purpose_v1 | 4 | 4 |
| predictive_genealogy_source_v1 | 2 | 2 |
| q_integral_vector_qv_program_source_v1 | 23 | 23 |
| resource_block_dynamic_data_source_v1 | 6 | 6 |
| rotating_body_dynamic_price_source_v1 | 6 | 6 |
| state_ito_q_martingale_recovery_source_v1 | 7 | 7 |
| table_continuous_funding_source_v1 | 11 | 11 |
| vector_weighted_population_source_v1 | 17 | 17 |

此外核对决策三包的身份清单：

| 证据 | 当前结果 | 正确复用方式 |
|---|---|---|
| PR441早期 `lean-cached-final-01/SOURCE_AFTER.json` | 15/18相同；两个生产文件及一个driver已被同PR后续修订 | 保留为早期运行身份，不能用于当前三个变更文件 |
| PR441最终 `lean-final-02/SOURCE_AFTER.json` | 280个Lean/config文件全部相同；该清单总计282含非Lean配置 | 使用最终来源绑定；17个 `FINAL_MODULE_COMPILE.json`记录源码亦全部匹配且exit0 |
| PR442 `checks/CORE_SOURCE_IDENTITY.json` | 1018/1019相同 | 唯一不同是后来追加导入的TheoryCompletion入口，后由PR444集成覆盖 |
| PR443 `checks/CORE_SOURCE_IDENTITY.json` | 1034/1035相同 | 同一公共入口后来追加导入；正文新模块字节保留，后由PR444集成覆盖 |

早期清单不匹配是有后继精确来源的历史版本差异，不构成当前Lean错误。本报告没有删除失败或较早成功回执。PR441最终清单的280项在JSON逐项列出；另外两个配置文件与共同配置身份核验衔接。

## 6. 可以发布与不可以发布的验收措辞

可发布：“本轮未修改Lean或冻结Core。对原106个P端点及传递UEOT依赖逐字节匹配原106/106提升提交；现行源码与PR444历史集成、PR447定向编译回执按确切SHA接续，复用其原验证结果。本轮仅新执行出版结构、源身份和书籍构建检查。”

不可发布：“本轮重新编译全部1051模块”“今天运行了原106/106 CI”“PR444旧1048整图就是当前1051整图”“15端点公理表代表全库已无native_decide”“Lean通过证明自然界符合本模型”。

新的中英文Markdown、TeX、PDF、目录、公式溢出和视觉验收不能复用旧数学书/哲学书PDF回执。本报告只核对形式来源与历史证据，出版验收由本轮新构建独立负责。

## 7. 复现及审查限度

在拥有完整Git历史的仓库副本上运行：

```text
python audit_identity_reuse.py --repo /path/to/UEOT --output SOURCE_IDENTITY_REUSE.json
```

脚本读取同目录 `LEAN_DECLARATION_EVIDENCE.json`确定原P端点定义路径，再复用仓库原静态审计器的词法屏蔽和import解析函数计算内部闭包；没有调用它的旧1048文件数验收门，也没有修改原脚本。比较函数只读Git对象与文件、哈希和已保存回执。脚本生成机器明细并报告自己当前运行的时间，原历史构建/CI时间和结果保持各自来源。

本记录由本轮数学语义子智能体A核对；主代理可据机器明细复核。它是分工审计，不是新外部同行评议。当前源码无变化时，无需为书籍编辑重开冻结证明；若源码在后续另改，应重新计算身份并按实际差异决定新的验证范围。
