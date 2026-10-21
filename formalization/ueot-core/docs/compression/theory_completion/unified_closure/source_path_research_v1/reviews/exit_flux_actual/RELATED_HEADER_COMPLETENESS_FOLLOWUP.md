# K2 与 QSD：声明分隔符风险的窄复核

结论：**HEADER_COMPLETENESS_CONFIRMED_NO_PRIOR_CLEAR_RETRACTION**。

触发点是首次退出作者比较文件在三个命名参数 `:=` 处截断。按 root 的追加要求，本次只重新提取一般 K2 与 QSD 的完整公开声明头，检查这一具体证据风险；不重复数学审查、不运行 Lean、不修改任何旧 CLEAR 或作者包。

提取时区分真正声明赋值、括号内命名参数赋值、定理类型中的 `let ... := ...`，并兼容 `:= by` 和直接项证明。提取出的全部头原文与各 SHA 记录在同名 JSON。

| 私有包 | 完整比较结果 | 原比较文件是否截断 |
|---|---|---|
| 一般 K2 | 13 个公开声明；11 个完整头逐字不变。`actual_survival_pos_iff_support` 与 `actual_zero_survival_no_filter_witness` 两处仅把 `nu.support` 改为 `(nu).support`。 | 否；13 条原/最终记录都包含完整声明头。 |
| QSD | 原 10 个完整头逐字不变；保留已审的 3 个新增端点；实际 attempt001 到最终版的全部 13 个完整头逐字相同。 | 否；包含定理类型内的完整 let 绑定，没有误截断。 |

此次也用支持 let/项证明的扫描重新确认首次退出新证据中的全部 15 个完整头。没有发现此前 K2 或 QSD 数学结论需要更正之处；其旧 CLEAR 收据均保留原字节与 SHA。

一般 K2 源码仍为 `8114278dc02e54f681bd576cf62af0dcc83df47a5b4a61bdc506a868750aea3c`；QSD 源码仍为 `be6c14557d455e8e4c6d752bb9255388a4dc5a561a85bf96112fbfba604f66ed`。本收据只确认源码头比较的完整性，不替代此前实际编译证据，也不声称未通过的原稿存在可比较的 kernel 类型。
