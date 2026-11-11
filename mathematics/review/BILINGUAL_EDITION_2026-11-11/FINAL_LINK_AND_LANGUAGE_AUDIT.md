# FINAL_LINK_AND_LANGUAGE_AUDIT — 正式双语稿链接与残余中文验收

## 1. 结论

中文共289个链接，其中本地文件成功109、唯一显式内部锚点成功153、仅列示外部URL 27；英文共289个链接，其中本地文件成功109、唯一显式内部锚点成功153、仅列示外部URL 27。需处理或进一步核对的项目共0项；读取期间改变的文件共0项。中英文链接目标次序相同。

英文残余汉字共16行，分类为{'AUTHOR_ORIGINAL_NAME': 1, 'HISTORICAL_SOURCE_FILENAME': 15}；围栏代码中的中文共0行。此项是字符与链接审计，数学语义完整性仍由本轮逐区间交叉审译记录负责。

## 2. 准确文件身份与检查方法

| 文件 | SHA256 | 链接数 |
|---|---|---|
| mathematics/UEOT_MATHEMATICS.md | `9c821995f39d9ae70add9ae2d949a90cb2781e202bc7940ee743759bd036a625` | 289 |
| mathematics/UEOT_MATHEMATICS.en.md | `d0f5dd162219d52efad1cceb47b867dbdd88c6402cd4e395031cd9d895fee4fc` | 289 |

读取前后文件字节一致；本审未修改主文。使用实际Pandoc Markdown解析为AST，逐个遍历Link/Image节点，避免把公式中的 `](y)`误认成链接。未发现引用式链接定义；所有真实链接均被解析。显式锚点按实际HTML id核对，未用不可靠的中英标题slug互换。

原v4.0来源为 `3d443ec29eb17af1fc00699a74e2d42d73516d81` 的 `mathematics/UEOT_MATHEMATICS.md`，通过Git对象读取。每个当前目标在JSON中标记是否出现于原v4及其当时本地存在情况；由于本次失效项为零，无需列出旧错误豁免。此前已纠正的外部文献归属错误属于文献语义审计，不以本地链接存在性代替其查证。

## 3. 英文残余汉字逐项清单

| 英文行号 | 分类 | 保留文本或文件名 |
|---|---|---|
| 7 | 作者原名 | Degui Qian (钱德桂) |
| 7239 | 历史源文件名 | UEOT_v1.0_核心理论正式版.md |
| 7240 | 历史源文件名 | UEOT_数学基础_统一正式版_v1.1(1).md |
| 7241 | 历史源文件名 | UEOT_数学基础_完整系统正式版_v2.1.md |
| 7242 | 历史源文件名 | UEOT_数学扩展_v2.1_五大开放主线系统推进.md |
| 7243 | 历史源文件名 | UEOT_数学基础IV_Dynamic-Composition与Multi-GOA_v0.4.md |
| 7244 | 历史源文件名 | UEOT_数学基础IV_Metastable-Object-GOA与Teleology-Bridge_v0.5.md |
| 7245 | 历史源文件名 | UEOT_数学基础IV_Persistence-IProjection与Anchored-Dual-Drives_v0.6.md |
| 7246 | 历史源文件名 | UEOT_数学基础IV_Lineage-IProjection与Positive-Operator-Evolution_v0.7.md |
| 7247 | 历史源文件名 | UEOT_数学基础IV_Realized-Lineage_Heredity_Object-Selection_v0.8.md |
| 7248 | 历史源文件名 | UEOT_数学基础IV_Endogenous-Teleological-Bridge_v0.9.md |
| 7249 | 历史源文件名 | UEOT_数学基础IV_Causal-Omega_Teleonomy_Variational-Realization_v0.10.md |
| 7250 | 历史源文件名 | UEOT_数学基础IV_Protocol-Saturated-Objecthood_v0.11.md |
| 7251 | 历史源文件名 | UEOT_数学基础IV_Factor-Ontology与Directed-Identity_v0.12.md |
| 7252 | 历史源文件名 | UEOT-QOD_Interface_v1.0_通用对象实现-分辨率-组合接口_严格版.tex |
| 7253 | 历史源文件名 | UEOT_Core_v2.2_QOD-G融合_双主线收敛核心_严格版.tex |

所有15个历史文件名所在行的“内容/作用”和“相关章节”说明已为英文；不应为消除字符扫描命中而改写这些准确来源标识。作者原名是身份信息。没有要求保留却被误算为正文漏译的中文代码段。

## 4. 范围及复现

机器明细保存全部578次链接出现、目标、行号、分类、原v4存在性及残余汉字清单，文件为 `FINAL_LINK_AND_LANGUAGE_AUDIT.json`。复现入口为 `audit_final_links_language.py`，默认目标为正式中英文主文。

```text
python mathematics/tools/audit_final_links_language.py --repo /path/to/UEOT
```

本项没有逐一访问27个外部URL，没有代替PDF目录点击/视觉检查，也没有以字符检测代替逐命题英译审查。若正式主文在上述SHA之后改变，应更新本报告；旧报告只证明它所绑定的确切字节。
