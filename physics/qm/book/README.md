# UEOT物理学

《UEOT物理学》是钱德桂（Degui Qian）的UEOT理论及量子物理研究正式连续总著，稳定身份UEOT-PHYSICS，当前正式整合版为**3.3**。正文涵盖理论思想、全部继承推导、具体例子、证明责任、反例与开放问题。本版局部及统一证明、结构、排印和实际视觉验收已完成，当前发布状态为**LOCAL_VERIFIED_REMOTE_PENDING**；后续远端状态单独记录。

## 完整正文与身份

| 文件 | 内容 |
|---|---|
| [UEOT_PHYSICS.md](UEOT_PHYSICS.md) | 唯一规范正文，第0–59章及附录A–F |
| [UEOT_PHYSICS.pdf](UEOT_PHYSICS.pdf) | 同一正文的完整正式阅读版，203页 |
| [UEOT_PHYSICS.tex](UEOT_PHYSICS.tex) | 本版实际构建的完整LaTeX源 |
| [CHAPTER_DOSSIER.json](CHAPTER_DOSSIER.json) | 60章与6附录的源、分类、逐项证明责任、实际状态和正文片段哈希 |
| [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) | 11份原材料独立身份及本版受验源码引用 |
| [结构回执](evidence/v3.3/book-structure.json) | 291章内小节、197稳定锚点、131编号结果 |
| [发布门](evidence/v3.3/local-release-gates.json) | 实际正文、证明、排印、视觉与发布状态 |

本版保留3.2全部117个稳定编号和旧origin，第57–59章新增14项结果，按4/5/5分布。编号不代替原创性、Lean定理数或自然规律计数。形式化声明与全书物理推导的覆盖范围分别登记。

## 本轮三个完整新章

| 章节 | 已完成的理论与形式化连接 | 下一项独立责任 |
|---|---|---|
| 57 完整状态空间中的纯化与操作原则 | 完整凸极点纯性、PSD导出的任意有限复态纯化、实际偏迹、三种完整状态呈现及七项规律；Bell正控与受限态空间控制 | 纯性反向、纯化本质唯一性、复局部层析、原则的UEOT物理来源 |
| 58 联合记录、量子记忆与有限自适应协议 | 异型CPTP、任意有限辅助放大、真实联合块与边际、原协议所有叶的实际通道、事件TV及whole-protocol缺陷；两步反馈控制 | 共同时序控制器逐步预算、动作缺陷上界及必要的稳定化距离 |
| 59 非交换条件持续的精确动力学 | 原同一模型Doob全矩阵迭代、唯一不变态、实际源成功概率与条件态、到源固定态的精确距离衰减、成功质量趋零；identity-Doob反例 | 一般正谱存在、可验证混合条件、无限条件过程与物理适用性 |

章57–59具体编号由[章节档案审查](evidence/v3.3/dossier-review.json)逐项绑定实际源与命名证明。原第49–56章的响应、坐标、证书、误差、平均、生存与选择分离继续保留。正式著作包含量子基础、测量、连续变量、多体、热与开放系统、QFT/QED、粒子候选、条件三代、拓扑、格点和实验统计；其领域假设与未完成责任没有被有限Lean验证消除。

## 实际证明、运行与出版

| 证据 | 本版实际结果 |
|---|---|
| [统一证明](../kernel/evidence/v31.7/lean-verification.json) | 29模块、646显式定理、855唯一全名公理报告 |
| [七组具体见证](../kernel/evidence/v31.7/finite-witnesses/verification.json) | 110定理、39定义、2缩写，共151独立审计；86个QM/Core源与olean绑定 |
| [精确证书门](../kernel/evidence/v31.7/lean-exports/verification.json) | 6正证书42审计；4篡改真值证明拒绝与4同数据假值证明接受 |
| [运行回执](../kernel/evidence/v31.7/runtime-verification.json) | 100测试方法；四份演示另有[实际回执](../kernel/evidence/v31.7/demos-verification.json) |
| [依赖与Core](../kernel/evidence/v31.7/core-import-closure.json) | 固定Lean4.33.1、九项Git锁依赖、56项Core实际递归源码保持一致 |
| [排印](evidence/v3.3/pdf-build.json) | 同一完整源，三遍XeLaTeX退出0；登记版面警告为空 |
| [视觉审查](evidence/v3.3/pdf-visual-review.json) | 根代理总览与指定完整页、协作代理实际新章与附录页审阅；精确页范围见回执 |

全部公理仅含propext、Classical.choice、Quot.sound。本版新增7公共模块、187显式定理和282审计，其中QuantumDoobModel包括前版见证提取；不把每条语法声明宣称为新物理规律。

实际80项源集SHA-256为b453ce5028eb1ef7d324326245ae5c6cc1a0bf3f40cabf691f25bb1aae7a5911。科学源清单、构建、公理、实例、见证与远端身份分别记录；历史HEAD不代替受验源字节。当前源码基线是7b1f7c3cf2e86cb85dcdb1b4618c247c517407f8。

| 正式产物 | SHA-256 |
|---|---|
| Markdown | 83f9f0a470816a49db9e6c3e5d6456ac83cd191612d5691b67979cf8822c7c9c |
| PDF | 9241acdebfbf132032832027cd18be4f7b8b80f351483eaecf9a0ebe8952043c |
| LaTeX | 364545a8607c5021b1facfd6678f521b11590a1923151415ec5711527e76c57c |

## 旧证据与分类

三套旧程序源码及正文嵌入块本版保持不变，[本版复用核对](evidence/v3.3/legacy-source-reuse.json)只核身份，未重跑旧757项检查。237+423+97仍属于[3.0实际执行](evidence/v3.0/legacy-regression.json)。原始来源登记、历史文本见证及两份同名v28.1身份保持各自范围，不冒充所有附件重新读取。

沿用[Core–Physics接口](../../interfaces/CORE_PHYSICS_CONTRACT.md)：argument_status记录定义/推导/外部定理/假设/解释/实验/反例/开放；dependency_class记录Core、桥、选择原则、标准物理、有效模型、可观测后果或专属科学猜想；verification_kind记录analytic、exact_arithmetic、synthetic、lean、experiment。没有实验数据就不会登记experiment。AI作者与互审不代替独立人类同行评审。

## 复现与持续维护

从仓库根执行python3 physics/qm/book/build/verify_book.py核完整结构。阅读版使用python3 physics/qm/book/build/build_pdf.py --output-dir /tmp/ueot-physics-v3-3-build --font /path/to/DroidSansFallback.ttf；需要Pandoc、XeLaTeX及对应字体，构建不开启shell-escape。字体与实际日志哈希见排印回执，重新排印后须检查实际页面。

[本轮v31.7合同](../UEOT_QM_EXECUTION_v31.7.md)记录执行范围；[下一轮v31.8合同](../UEOT_QM_EXECUTION_v31.8.md)聚焦全效应分离及复层析、完整纯性与辅助酉唯一性、逐动作记录预算。后者仅为未执行规划。冻结Core的106项与四生成器保持独立。

现实三代仍需完整谱、表示、阈值、有效窗口、真空与质量等责任；阅读相关结论须同时核第36章反例和49.7节前提。复量子唯一选择、连续/QFT和真实实验检验仍开放。正式完整著作的维护完成与完备自然理论的完成具有不同证据门。
