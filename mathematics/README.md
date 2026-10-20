# UEOT 数学著作

本目录维护独立的数学主文，包括定义、明确假设、定理与证明、反例、算法，以及可核查的 Lean 对应。

- [完整 Markdown 主文](./UEOT_MATHEMATICS.md)
- [完整来源与 Lean 对应索引](./UEOT_MATHEMATICS_SOURCES.md)
- [现行 Lean 接口的范围说明](./LEAN_API_SCOPE.md)
- [PDF 阅读版](./UEOT_MATHEMATICS.pdf)
- [LaTeX 排版源](./UEOT_MATHEMATICS.tex)
- [编译与审页记录](./BUILD.json)

本版保留原 Core 第 0—31 章和附录，并逐章补充后续形式化的实际范围。第 32—38 章进一步展开层级压缩、关系缺陷与校准、客体和目的接口、同源统一闭合、实际占据、有限支持可行性与注册选择后的联合风险。历史代码与历史运行输出保留各自的身份；新的编译和检验不能替代旧的执行记录。

## 冻结来源与新增工作

[Core Mathematics v3.0 原文](./source/core-v3.0/UEOT_Core_Mathematics_v3.0_Complete.md) 与旧规范账本记录的 SHA-256 完全一致：

`ed00dd102157cdafe3a79c45506e86dc574d6cba65feb2df8686e63ce2726303`

它的 106 个 P-ID 保持冻结。新书是另一个持续维护的版本，新增章节和更精确的边界说明不自动改变已有 P-ID 覆盖状态。三份提供的历史科学接口资料完整保存在 `source/roadmaps/`。

数学证明接受给定模型与假设；从中得到现实对象、经验定律或规范结论，还要说明相应接口。独立的[哲学著作](../philosophy/README.md)对这些哲学问题给出自己的论证。

生成方法见[两书构建说明](../tools/books/README.md)。文档编译记录与 Lean 证明证据分别维护。
