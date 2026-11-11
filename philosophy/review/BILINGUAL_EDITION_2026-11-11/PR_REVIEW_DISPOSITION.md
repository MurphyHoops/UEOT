# PR #452：自动代码审查问题的实际处理

本记录只处理交付工具，不改变两种语言的书籍正文、LaTeX 或 PDF。
仓库自动代码审查不属于外部哲学同行评议，也不替代三位原生编辑的学术审查。

## 已发现的问题

[自动审查 P2](https://github.com/MurphyHoops/UEOT/pull/452#discussion_r4534531348)
指出初始提交 `e151924d73341f0ffa39fdf7833e02ff7956ee8e` 中的验证器从被 Git 忽略的
`.build/` 内读取 `.aux`。在没有编译缓存的干净检出中，正式 PDF 的真实
`chapter*.N`／`section*.N` 目的地因此无法映射回 Markdown 锚点。
这会把完好的交付文件误报为导航失效。

## 实际修改

验证器直接读取已经提交的 Markdown、LaTeX 与 PDF：

1. 核对 47 个 Markdown 锚点及其标题的完整顺序。
2. 核对 LaTeX 的章／节标签和分编目标顺序与之相同。
3. 将这 47 个源标题与实际 PDF 书签标题逐项比对。
4. 读取 PDF 书签自身记录的命名目的地，核对其解析页与书签页一致。
5. 保留原来的脚注、链接、字体、页码、文件指纹与受保护来源检查。

因此，本次没有通过关闭锚点检查来“解决”报错，也不要求读者先复造
原编辑环境的临时缓存。

## 真实回归检查

[CACHELESS_REPRODUCTION.json](CACHELESS_REPRODUCTION.json) 记录了一份不含
`.build/` 的 96 文件目录。旧验证器实际退出 1，唯一错误为 82 个非分编
锚点无法映射；新验证器实际退出 0，全部检查通过。新目录与编辑目录
生成的 `LAYOUT_VALIDATION.json` 逐字节相同。

两种语言的六个正式文件仍与 `EDITION_MANIFEST.json` 完全一致，不需要
重新排印或沿用错误的视觉回执。本次独立代码逻辑复核另见
[CACHELESS_VALIDATOR_REVIEW.md](CACHELESS_VALIDATOR_REVIEW.md)。GitHub 线程
的最终状态以 PR 实际记录为准，不由本文件提前宣称。
