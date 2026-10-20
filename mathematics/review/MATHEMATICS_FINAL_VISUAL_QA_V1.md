# 数学书最终 PDF 视觉核验

结论：**PASS**。这是文档版式核验；数学证明的检查由独立的来源审查与 Lean 证据承担。

## 文件身份

- PDF：`mathematics/UEOT_MATHEMATICS.pdf`，156 个物理页，941465 bytes。
- PDF SHA-256：`907c1635f9c6a0b6a7307f6d9e965dda3e5e8bee3ae852c58db17730b08b0245`。
- Markdown SHA-256：`7981369dc93272afec006aa2d18486de3ffc28fe9b06e9f6f9e855c29cf9126b`。
- LaTeX SHA-256：`eda39469074739ec80aee070c82e738c6141c8a3a35e0d981331e3ce13447558`。
- 实际 XeLaTeX 最后一遍：0 条 overfull hbox，无 Missing character。

## 实际审阅范围

主审将最终 PDF 全部 156 页以 45 dpi 渲染，按页序制作并实际查看全部十张 contact sheet。该检查覆盖封面、完整目录、39 章正文、六个附录及最后一页的布局和连续性。没有把 contact sheet 的布局检查当作逐字数学审读。

主审另以 144 dpi 渲染并实际查看物理页 **1、8、14、98、103、106、136、142、148、152、155、156**。这些页面覆盖封面、三位数目录页码、历史检查范围声明、H0 八类表、校准与标度公式、P0–P12 边界表、来源长表、完整历史程序、历史 JSON 输出、长 Lean 限定名和最终源证据表。未见裁切、重叠、缺字、越界或错误缩放；长程序行和限定名保持可读换行。

独立审阅者另实际查看物理页 **119–129** 的全部十一张 144 dpi 原图，特别检查有限支持递推、可执行检查器、注册联合风险、`17/32`、`9/64` 及正概率失败记录。其原始收据是 [KEY_PAGES_VISUAL_QA_V1.md](./KEY_PAGES_VISUAL_QA_V1.md)，SHA-256 为 `bdc6e1d94b49b02bad0b1d9435a703bc15446d622f926e6e5fc14de8e3950886`。

两位审阅者合计实际查看 23 张互不重复的高清页；其余页面由完整 contact sheet 布局检查覆盖。本记录不宣称所有 156 页都接受了高清逐字检查。

## 修正及保持事项

三位数目录页码栏已扩宽；长代码与限定名使用正常换行。第 37.3 节的长 Viable 递推增加一处对齐换行，数学记号、量词和推理未改变。相应源文差异在 [PRINT_DELTA_V2.json](./PRINT_DELTA_V2.json) 中记录。原 v3.0 程序、两段历史 JSON 和 106 个 P-ID 的身份另由来源检查核验；没有把旧 2371 项数值检查改记为本轮运行。

图像身份在 [render-manifest.json](./render-manifest.json) 和 [key-pages-visual-status.json](./key-pages-visual-status.json) 中保留。完整渲染图像存放于本次实施检查点，书的 Git 版本保留最终 PDF 和这些可核对记录。

数学内容独立审查见 [MATHEMATICS_CH32_38_INDEPENDENT_REVIEW_V1.md](./MATHEMATICS_CH32_38_INDEPENDENT_REVIEW_V1.md)；现行 Lean API 的三项范围区别见 [LEAN_API_SCOPE.md](../LEAN_API_SCOPE.md)。本次没有重新运行 Lean 或历史数值程序。
