# C：D3 实际执行的独立范围验收

日期：2026-11-13。审查者：原生子智能体 C。**结论：D3 在本报告界定的针对性执行范围内可以结案；没有发现需要新增证明、修改生产定义或再次运行 Lean 的阻断问题。**主审据实际证据作最终裁决，本意见不以其他智能体同意为理由。

本轮增加的是已有合同的新执行证据，不扩大此前有限 A 的理论主张、形式化覆盖、原生计算信任范围或经验效力。原审计／整改中“未执行”的记录仍是原时段事实。

## 1. 实际取得的证据

执行固定到 main `6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4`、tree `339b3e216d4c036bdd30a87b9653475a88646dde`；Lean 4.33.1（commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`）、Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`，平台 arm64-apple-darwin24.6.0。九个锁定依赖的实际修订与记录一致。此次确有 Mac 命令输出；此前 Remote 名册 Offline 不否定 Local 通道实际可用。

C 对取回的 ZIP（SHA256 `85267f06ecf16ce3394eb5112ca0b3a74ed3c3cb949c4fcc65c8ee4034bb090d`）逐文件比较，57 文件字节一致；对三个回执列出的 35 条 Lean 命令日志独立重算 SHA，全部匹配。又核对 v2→continuation→最终补查记录的哈希引用、实际执行范围、15 项源码与源清单、导入路径和产物记录。【E1：实际记录及 C 的独立计算】

| 项目 | 实际范围 |
|---|---|
| 源码新编译 | 15 项目标全部 exit 0，含公共 UEOT 入口及文档中的增长分类消费者；不是全部生产模块干净重建 |
| 类型／公理请求 | 最终 probe exit 0；44 项类型查询、公理报告及 12 项定义查询存在 |
| 声明的证明来源 | 37 项来自上述新编译目标；7 项复用已有 `.olean`，只取得新的查询输出 |
| 源及锁配置 | 1,055 文件与固定清单相符；引导恢复另含 Crooks–Jarzynski 的 LICENSE、UPSTREAM.md 两文件，共 1,057，范围不混算 |
| 新产物与旧缓存 | v2 的 30 项新 `.olean/.ilean` 记录与最终 Mac 补查一致；63 项选定旧缓存产物前后记录不变 |
| continuation | 生产源码重编译数为 **0**；只运行修正 probe 的 deps 和编译两条 Lean 命令，均 exit 0 |

**证据身份限制：**30 项新二进制和最终 probe 二进制保留在 Mac，未随本次 ZIP 取回。主审实际在 Mac 重算其哈希；C 独立重算的是取回日志／清单字节，并把这次实际产物读回与编译回执、导入记录交叉绑定。不能写成 C 或 B 在云端直接重哈希了这些 Mac 二进制，也不能写成另一个平台的完整重建。

## 2. 三个 wrapper 失败均保留

| 记录 | 实际失败点 | 已成功及未成功的边界 |
|---|---|---|
| v1，09:21 UTC | 首次 deps 输出路径不存在，wrapper exit 1 | 只有 deps 命令 exit 0；尚无生产源码编译 |
| v2，09:32–09:33 UTC | probe 第 30 行不支持 `pp.width`，Lean probe 与 wrapper exit 1 | 此前 15 项源编译均已 exit 0；旧缓存不变。失败 probe 不作为最终成功记录 |
| continuation，09:39 UTC | Lean 完成后，wrapper 以未带宇宙参数的字符串比较 `Classical.choice.{u}`／`Quot.sound.{u}`，自身 exit 1 | deps、最终 Lean probe 均 exit 0；事后字符串比较失败不是 Lean 编译失败 |

原三个状态仍为 `FAILED_OR_BLOCKED`，没有改成 PASS。仅删除唯一 24-byte 排版选项得到新 probe，原脚本、计划、白名单与历史回执保持。主审在 09:41 UTC 实际补做原 wrapper 中止前尚未完成的源码／产物／旧缓存检查；`FINAL_SOURCE_ARTIFACT_CHECK.json` 明确它不是语义验收。最终接受依赖这些分项事实和独立读回，不依赖 wrapper 的总标签。

## 3. 公理检查没有通过放宽白名单过关

C 没有调用 B 的解析器取得独立结果，而是对每条完整原公理列表使用实际出现的五个字面 token，要求全字符串匹配且端点与计划原顺序一致：`propext`、`Classical.choice.{u}`、`Quot.sound.{u}`，以及两个完整限定的 `exact_cached_data._native.native_decide.ax_1_1`／`exact_two_data._native.native_decide.ax_1_1` 名称。全部 44 条完整匹配，没有剩余字符、未知公理或漏掉的报告。【E1】

结果为 **42 项只含标准逻辑公理的子集，2 项含各自已披露的精确原生归约公理**。`.{u}` 是同一常量的宇宙参数显示，并非增加一个假设；本次没有重新计算两个缓存 native 数值端点。不能把这两项说成只有普通三公理，也不能因其存在把所有导入定理都判为带原生依赖。

C 全文读取 B 的严格解析器，确认其要求完整常量名、合法且元数相符的末尾宇宙项、完整列表及声明覆盖，未知项失败；native 名称按完整名字精确核对。双方得到的 44 条原列表、原 token 和常量名称逐项一致，0 差异。B 的解析器检查只是输出处理验证，不是新 Lean 执行。

交叉质询后，B 在冻结报告 `B_D3_MATHEMATICAL_REVIEW.md` §2、§5 明确回答了 C 的两项范围要求：云端未直接重哈希 Mac 二进制；有省略的类型按固定源补核，不能称无省略全文打印。C 已只读回核这两节（该报告 SHA256 `7e89fa36f5ccaa2fbcd6b1e694ade5fa7453e2e3b301cfd6294606845a0c470b`）；两项质询已闭合，不据此扩大执行结论。

## 4. 类型语义与省略范围

实际输出直接保留严格正折扣 `0 < β < 1`；`Countable I` 与逐协议 a.e. 因子化；新生新鲜性的 `ValidIdentity`；State 仅给 `GoodPopulation`；体内程序解释的 `ProgramPopulation θ` 初态、可达继承及正分支；严格概率域、完整允许 Policy、非空人口和期望增长评价。付款、形成候选、继承及增长条件仍在模型给定前提下；查询成功不把它们升级为普遍身份、任意身体自生成、必然存续或道德最优。

raw 中有 **19 处 `⋯`**。C 不宣称 44 类型或 12 定义均已完整无省略打印。对涉及预测和装配的省略位置，已补读与实际编译 SHA 完全一致的两份源：

- `PredictionDependent.lean`，SHA256 `54f2569cf7323471f9f4214a78df41ab53f276231f78645a810bba44e1172e92`，尤其 `canonical_ae_minimal`／`canonical_ae_sigma_minimal`。
- `CoreOperationalAssembly.lean`，SHA256 `1f8c4f5be6d3906cdeaa6d88809cc5e0fa5f601ce8b69b21cef67a16dc7a7384`，误差桥、间隔桥、`FixedSourceApproximation`、`CorePointwiseCertificate` 与 `p_core_01` 的实际字段／量词。

这些补读仍显示预测历史 H、控制状态 X/M 与失效对象 Obj 可分离；共同事件装配没有自动提供共同身体映射。内部误差→动作间隔桥仍有实质内容，外层装配继续维持既有 K2/K3 定位。此次执行没有改变原审计的数学—哲学限定。【E1：实际输出及绑定源】

## 5. 最终范围裁决与停止

**本轮针对性 D3 执行证据足以接受。**三个失败是已定位、保留的执行器或显示处理事件，未产生定理反例；最终 Lean 请求及实际源编译的成功不依赖抹去这些事件。没有剩余证据要求重做已成功的 15 项编译、重放反模型、清空全部 Mathlib 缓存或新增生产 Lean。

仍保留：其他依赖的缓存复用、两个原生计算的已披露信任、未作跨平台干净重建、未作人类外部复现、经验效力与全球原创性未由此确立。这些是本次准确范围，不是新的 Core 基础缺口。

可复算附表：`C_OBSERVED_EVIDENCE_VERIFICATION.json` 与 `verify_observed_evidence_c.py`；源补读及与 B 的交叉身份：`C_D3_ACCEPTANCE_DETAILS.json`。C 的首次辅助类型标题识别未计 `pp.explicit` 的 `@` 前缀，原结果已留存；只修正该显示识别后得到当前结果，没有改变任何原始执行证据、公理列表或数学条件。
