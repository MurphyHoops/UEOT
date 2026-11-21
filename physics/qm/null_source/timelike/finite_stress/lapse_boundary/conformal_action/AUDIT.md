# 审计：实际运行、冻结复用与不可变源码审查

当前计时状态见 [session_timing.json](session_timing.json)。
最后实际运行见 [verification.json](verification.json)。

## 执行与证据类型

本轮仅 root 在 Local Mac 执行新 cohort 科学入口；三个原生代理只读推导、源码及结果。
27 个科学证书入口与 1 个范围／源码绑定入口分列。检查包括精确代数、向外区间和明确容差回归；
无限维结论的解析证明另列，不称为 27 个机器定理或外部同行评议。

前驱 248 项复用，924 个科学文件逐字节冻结。旧科学模块、旧 mode/geometry ODE 的新增执行数均为零。
新 runner 执行前后复核精确 inventory、Git 身份、源码 manifest；最多两个新入口并行。

## 已完成不可变检查点

| 检查点 | 提交 | science CI | publication CI |
| --- | --- | --- | --- |
| CP1 | 3dcae50d930a92cdfe678a3cb4a892d04452e2d5 | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44937647192) | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44937647100) |
| CP2 | 29e8d890b417add09eeb462dceb062f94d6ad390 | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44940214863) | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44940214906) |
| CP3 | a8c7a5571323299c9e38466735861b2f5709eb3a | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44943638400) | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44943638386) |
| CP4 | 7e3db814594eded62a0dab1e867b90908b66d1fa | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44944553370) | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44944553286) |
| CP5 | dc9929f81cffff94d53a61eb55cb39f0fb36f401 | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44946091511) | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44946091527) |
| CP6 | b280a5a413701d27f244516ca6ce15586efb7342 | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44948450877) | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44948450884) |
| CP7 | 33a7cf2f0150961743439b32a3edcd5c9bdbff25 | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44948931331) | [success](https://github.com/MurphyHoops/UEOT/actions/runs/44948931353) |

## 原生源码审查

最终已入账 21 份不可变记录、223 个提交—文件身份：3 位原生只读代理、7 个不可变科学检查点。
各条同时保留实际 reviewer、commit、Git blob 与 SHA256；root 从 Git 重新取得原字节比对。
CP5 三位审查均 PASS；CP4 的有限低模 trace 标记 finding 已在 CP5 独立复审解决。
Z 与 AA 的三组数学审查及 CP6/CP7 实际不可变源码审查全部通过。
工作树讨论没有被计作提交审查。最终科学文件与 CP7 字节相同，身份清单入账。

findings 的历史状态和解决提交保留于 [source_audits.json](source_audits.json)。
全部已记录 finding 已解决；三位代理实际审查后，final_audit_complete 已置 true。

## 核心范围

Core 只读，GI 排除，原分支保留；PR #468 开放草稿，不合并。
27 个入口不代表 27 个新基本定律；模型内正常性、稳定性和仪器不代表完整 Einstein–CTP 解。
所有新科学 JSON 保留 physical_unification=OPEN。

## 实际失败与修复

执行中发生的白名单、符号表达式归一、有限回归过慢及 runner 参数错误，均在 SESSION.md 记载；
失败没有计作 PASS。source binding 在文档或脚本改变后重新生成，完整 runner 不以旧 receipt 代替本轮执行。

## 三小时独立计时及最后科学 CI

独立开始 2026-11-21T18:02:22Z，研究与不可变科学审查段结束 2026-11-21T21:02:36Z，实际 10814 秒。
前轮时长未计入。最后 Git/验证/CI 交付在该工作段之后继续。

CP7 science 的实际解码日志观察到正确 head、28 个 PASS 入口及248/924冻结摘要。
job日志 SHA256、artifact ID/digest/head 见 [scientific_checkpoint_ci.json](scientific_checkpoint_ci.json)。
最终交付提交的 exact-head CI 另在 PR #468 和最终报告给出，避免把 CP7 的 CI 冒充其他提交的结果。
