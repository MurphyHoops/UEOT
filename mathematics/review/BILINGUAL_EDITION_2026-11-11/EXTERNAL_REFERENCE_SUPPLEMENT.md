# EXTERNAL_REFERENCE_SUPPLEMENT — 正文外部数学引用覆盖补核

日期：2026-11-11。责任：子智能体A。范围：正式双语数学主文的Markdown外部链接，不扩展到被链接的Lean文档及其他仓库文件中的外链。本报告补充 `BIBLIOGRAPHY_AUDIT.md`，不替代其15项第一方核验记录。

## 1. 差集结论及准确文本身份

`FINAL_LINK_AND_LANGUAGE_AUDIT.json` 中每种语言各27次外链出现，目标次序相同；去重后为17个URL、16项作品。附录C.4七项均已包含在C.5的15项作品中。Gretton论文的PDF与HTML是同一作品的两个入口，不应重复计为两项数学来源。

唯一尚未在既有文献审计中列出的作品是正文§23.3的Wainwright–Jordan。已实际打开出版社第一方元数据与作者公开存放的2008版PDF，核对身份及正文用途。补入本报告后，17个主文外部URL对应的16项作品均有明确的书目核验责任记录。此处的“覆盖”不表示对所有作品全文重证，也不表示本次重新网络打开全部17个URL；原有15项的实际访问层次继续以既有审计为准。

| 文件 | 本报告所核正文SHA256 |
|---|---|
| mathematics/UEOT_MATHEMATICS.md | `1f12c74c0d69df9f513a09fd98320e06c1b7d23e4953b61c20e247609cc1357c` |
| mathematics/UEOT_MATHEMATICS.en.md | `c1130c6ffc2eeb8c1ff237542476791b9e46693f3be14df5ed7bd29b37e861c3` |

## 2. 全部17个去重URL及覆盖归属

行号指上述中文正式主文；链接保留原URL，包括百分号编码与期刊入口。所有URL均从实际链接审计JSON提取。

| 序号 | 作品与原URL | 中文出现行号 | 既有覆盖或本次处理 |
|---|---|---|---|
| 1 | [Champagnat–Villemonais](https://arxiv.org/abs/1404.1349) | 1363, 7315, 7329 | C.4；C.5第3项；既有审计 |
| 2 | [Gretton等，JMLR PDF](https://www.jmlr.org/papers/volume13/gretton12a/gretton12a.pdf) | 2096, 7316 | C.4；与C.5第4项同一作品；既有审计的期刊HTML为另一入口 |
| 3 | [Abbasi-Yadkori–Pál–Szepesvári](https://arxiv.org/abs/1102.2670) | 2270, 7317, 7331 | C.4；C.5第5项；既有审计 |
| 4 | [Léonard](https://leonard.perso.math.cnrs.fr/papers/2012-Leonard-Girsanov%20theory%20under%20a%20finite%20entropy%20condition.pdf) | 3129, 7319, 7333 | C.4；C.5第7项；既有审计 |
| 5 | [Wainwright–Jordan](https://www.emerald.com/ftmal/article/1/1-2/1/1332382/Graphical-Models-Exponential-Families-and) | 3212 | 正文§23.3；未在C.4/C.5或既有审计列出；本报告补核 |
| 6 | [Shalizi–Crutchfield](https://arxiv.org/abs/cond-mat/9907176) | 7313, 7327 | C.4；C.5第1项；既有审计 |
| 7 | [Aubin–Cellina](https://doi.org/10.1007/978-3-642-69512-4) | 7314, 7328 | C.4；C.5第2项；既有审计 |
| 8 | [Ravindran–Barto](https://all.cs.umass.edu/pubs/2004/ravindran_b_KBCS04.pdf) | 7318, 7332 | C.4；C.5第6项；既有审计 |
| 9 | [Gretton等，JMLR HTML](https://www.jmlr.org/papers/v13/gretton12a.html) | 7330 | C.5第4项；既有审计 |
| 10 | [Kallenberg](https://doi.org/10.1007/978-3-030-61871-1) | 7334 | C.5第8项；既有审计 |
| 11 | [Cover–Thomas](https://doi.org/10.1002/047174882X) | 7335 | C.5第9项；既有审计 |
| 12 | [Puterman](https://doi.org/10.1002/9780470316887) | 7336 | C.5第10项；既有审计 |
| 13 | [Hernández-Lerma–Lasserre](https://doi.org/10.1007/978-1-4612-0729-0) | 7337 | C.5第11项；既有审计 |
| 14 | [Seneta](https://doi.org/10.1007/0-387-32792-4) | 7338 | C.5第12项；既有审计 |
| 15 | [Revuz–Yor](https://doi.org/10.1007/978-3-662-06400-9) | 7339 | C.5第13项；既有审计 |
| 16 | [Davies](https://www.cambridge.org/core/books/heat-kernels-and-spectral-theory/39DC7EE2A5DCCE9DEF581D2F52A73E1F) | 7340 | C.5第14项；既有审计 |
| 17 | [Warner](https://doi.org/10.1007/978-1-4757-1799-0) | 7341 | C.5第15项；既有审计 |

## 3. 唯一补核作品：Wainwright–Jordan

**规范记录。** Martin J. Wainwright and Michael I. Jordan. *Graphical Models, Exponential Families, and Variational Inference*. Foundations and Trends in Machine Learning **1**(1–2):1–305, 2008. DOI: [10.1561/2200000001](https://doi.org/10.1561/2200000001)。出版社页面与作者PDF首页的题名、作者、卷期、页码、年份、DOI相符。本次核验的是2008年期刊版本；未将早期2003年技术报告当作同一版本。

**实际内容核对。** 作者PDF §3.5.1、Proposition 3.1（印刷页62–63）给出正则指数族累积量函数的梯度与均值、Hessian与协方差关系；严格凸性另需极小表示。§3.6.1、Theorem 3.4（印刷页67–68）给出共轭对偶、熵与变分表示，并区分可实现均值的内部和边界。这里按作者的正则性、定义域和表示条件读取，未省略这些前提。

**本书用途判断。** §23.3用它支持有限指数族的协方差及变分对偶背景，来源与该用途相符。这项文献不证明UEOT的Π/Φ必为普适二维表示，不消除冗余统计量造成的规范不唯一，也不保证任意表示的Fisher矩阵非奇异。未发现需要修改冻结Core或Lean的数学错误。本轮只补齐出处审计记录，未改正式正文。

## 4. 第一方访问回执与复核入口

| 实际访问入口 | 实际取得的内容 | 查询引用标识 |
|---|---|---|
| [主文所用出版社URL](https://www.emerald.com/ftmal/article/1/1-2/1/1332382/Graphical-Models-Exponential-Families-and) | 题名、作者、2008卷期页码、DOI及摘要；跳转至同刊摘要页，全文要求访问权限 | `turn181492225view0`；原始打开 `turn998593004view0` |
| [作者Berkeley公开PDF](https://people.eecs.berkeley.edu/~jordan/papers/wainwright-jordan-fnt.pdf) | 305页2008期刊版，首页身份一致；实际读取下列具体段落 | `turn181492225view1`；原始打开 `turn182963613view0` |
| 同一作者PDF，§3.5.1，Proposition 3.1 | 正则指数族的导数、协方差及凸性条件；印刷页62–63 | `turn538378020view0`；前次段落打开 `turn388899437view0` |
| 同一作者PDF，§3.6.1，Theorem 3.4 | 共轭/熵/变分关系与均值匹配；印刷页67–68 | `turn252974212view0`；前次段落打开 `turn388899437view1` |

出版社的付费全文没有被访问；实际数学段落核对来自作者公开PDF。查询标识是本轮工具检索回执，不是持久文献编号；长期复核应使用URL、DOI、版本和明确章节页码。未以搜索结果摘要或二手转载代替以上数学内容读取。

## 5. 影响与验收边界

本项发现的是原有审计清单遗漏一项正文引用，未发现该引用的作者、题名或用途错误。C.5本身未声称穷举全书引用；无需为补此审计而修改已验收正文及PDF。主编可把本报告连同既有15项文献审计交付，或在该审计中加入指向本报告的说明。

本补核没有扩展到全部Lean文档外链，没有重跑形式化验证，也没有把书目和主题对应称为全文数学证明的独立审查。

## 主编最终文本接续

补核后仅进行了已列明的下标、表项短语和英文缩写句点修正；外部链接目标及对应来源段落未改动。最终主文身份与27次链接序列由同目录 `FINAL_LINK_AND_LANGUAGE_AUDIT.json` 绑定（中文 `9c821995f39d9ae70add9ae2d949a90cb2781e202bc7940ee743759bd036a625`；英文 `d0f5dd162219d52efad1cceb47b867dbdd88c6402cd4e395031cd9d895fee4fc`）。上文保留A原审阅文件的散列，不冒称该时点直接读过后续排版版本。
