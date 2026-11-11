# 构建与复核双语哲学书 3.0

Markdown 是编辑源。两种语言分别生成完整的 LaTeX 与 PDF；本目录的
构建器复用 `tools/books/` 的字体校验、打印过滤器和公共前导，不改动
数学书、物理书或共享构建文件。本版应使用下面的本地入口，以保留双语
标题、固定来源链接、重复注释回链和本版排印规则。

## 通常环境

安装 Python 3、Pandoc、XeLaTeX，以及 `fontspec`、`unicode-math`、`xeCJK`、
`fvextra`、`xurl`、`etoolbox`、`fancyhdr`、`footnotehyper`、`bookmark` 和
DejaVu 字体。英文需要标准英语断词规则。仓库根目录执行：

```bash
python3 philosophy/build_edition.py all --download-fonts
```

`zh`、`en` 可替代 `all` 单独构建。无网络时用 `--font-dir /absolute/path`
提供与共享构建器固定 SHA-256 一致的三款 Noto 字体。字体许可在
`tools/books/FONT_LICENSE.txt` 和 `FONT_LICENSE_SANS.txt`；PDF 只嵌入使用到的子集。
缓存位于本目录被 Git 忽略的 `.build/`，不会改写其他书的缓存。

每种语言执行一次 Pandoc 和三次 XeLaTeX。`BUILD.json`、`BUILD.en.json`
绑定 Markdown、TeX、PDF、构建器、过滤器和字体；构建过程中若输入变化则停止。
`SOURCE_DATE_EPOCH` 固定为 2026-11-11 UTC。不同 TeX 发行版之间不保证 PDF
逐字节一致；同一版本的交付以发行清单的 SHA-256 为准。

## 本次真实环境与兼容处理

本次实际使用 Pandoc 3.1.11.1、XeTeX/TeX Live 2025/dev（Debian）、
LaTeX 2024-11-01。环境已有大部分宏包，但 TeX 文件数据库链接失效、
没有 `xeCJK`，且预生成格式不适用于当前局部宏包树。首次编译因此失败。
未更改系统配置；下列环境变量与局部宏包/格式修复用于本次构建。

从 `https://github.com/CTeX-org/ctex-kit` 取 `xeCJK-v3.9.1`，提交
`c4ccfaefe803ab4a12c9fedc929be1e349e3c612`。该版本兼容这里的 LaTeX；
仓库当前开发分支所需的更新版接口不适用于本环境。将其置于单独的
临时目录，例如 `/tmp/ueot-ctex-kit`，创建 `philosophy/.build/texmf` 与
`philosophy/.build/formats`。在 `.build/texmf` 目录运行：

```bash
TEXMF=/usr/share/texlive/texmf-dist \
TEXINPUTS=/tmp/ueot-ctex-kit/xeCJK//:/tmp/ueot-ctex-kit/support//:/usr/share/texlive/texmf-dist/tex//: \
xetex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=xeCJK \
  '\input plain \input xeCJK.dtx'

TEXMF=/usr/share/texlive/texmf-dist \
TEXINPUTS=/tmp/ueot-ctex-kit/ctex//:/usr/share/texlive/texmf-dist/tex//: \
xetex -ini -etex -interaction=nonstopmode -halt-on-error -jobname=ctexhook \
  '\input plain \input docstrip \keepsilent \askforoverwritefalse \generate{\file{ctexhook.sty}{\from{ctex.dtx}{ctexhook}}}\endbatchfile'
```

然后在仓库根目录生成局部格式并编译：

```bash
TEXMF=/usr/share/texlive/texmf-dist \
TEXINPUTS=/usr/share/texlive/texmf-dist/tex//: \
xetex -ini -etex -interaction=nonstopmode -halt-on-error \
  -jobname=xelatex -output-directory=philosophy/.build/formats \
  -progname=xelatex '*xelatex.ini'

TEXMF='{/usr/share/texmf,/usr/share/texlive/texmf-dist}' \
TEXINPUTS=/usr/share/texlive/texmf-dist/tex//: \
python3 philosophy/build_edition.py all \
  --texmf philosophy/.build/texmf --format-dir philosophy/.build/formats
```

这些是本次环境的兼容步骤，完整 TeX Live 安装通常无需采用。
实际字体 SHA、工具版本与输入指纹以两份 BUILD 回执为准；本地生成的
第三方宏包、字体、格式和缓存不作为本仓库的新原创代码提交。

## 本版的排印决策

编标题与编名分行。章标题用 18 磅字、23 磅行距，英文标题和目录标题不自动断词，
目录保留页码空间。每章末段保持完整；附录 C.1 为标题、表头和首行预留空间，
书目用 10 磅左齐文字，避免单个短条目孤占末页。前置版本与权利说明采用稍小字号，避免末尾两行独占一页。
长脚注保持完整；68 条完整注释各印一次，其他 10 次引用通过原注号回链，
Markdown 中仍保留全部 78 次引用。所有研究来源的 PDF 链接指向固定基线
提交，版本版权链接指向本 PR 分支；Markdown 保持仓库内相对链接。

这些变动只调整阅读与导航，不删改正文、注释或表格内容。编译成功不等于
全书语义正确，也不自动获得排印验收。

## 检查

```bash
python3 philosophy/validate_edition.py
```

验证器使用 PyMuPDF（`fitz`）与 Poppler `pdffonts`，核对输入和产物指纹、
双语结构、注释、书签、链接、字体嵌入及页面边界；保存机器检查回执。
已提交的六个文件可在完整仓库的干净检出中直接验证，不依赖临时 `.aux`
文件：验证器对照 Markdown 标题、LaTeX 标签顺序与 PDF 中的实际书签目的地。
如在不同工具版本下重新排印，文件散列可能不同；与发行清单不一致会明确报出，
不被默认为原发行文件已经复现为逐字节相同。
人工式逐页视觉检查由原生 AI 审查者实际查看页面图像完成，与程序扫描分别记录。
最终版面判断见 [审查目录](review/BILINGUAL_EDITION_2026-11-11/README.md)。
本次未运行新的 Lean 证明或物理实验；数学接口以只读基线的既有合同为依据。
