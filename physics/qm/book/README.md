# 《UEOT物理学》正式整合版 3.4

作者：**钱德桂（Degui Qian）**。

当前状态：**LOCAL_VERIFIED_REMOTE_PENDING**。第0–62章、6个附录和147项稳定编号已经连贯纳入正式正文；原131项编号对象、11项原始来源记录和全部旧书证据保持原身份。本版新增16项编号：第60章4项、第61章6项、第62章6项。正文完成、有限条件证明和自然界适用性分别承担责任。

## 正文与阅读路径

- [UEOT_PHYSICS.md](UEOT_PHYSICS.md)：规范全文，63章、6附录、320小节、216个稳定锚点、147项编号。
- [UEOT_PHYSICS.pdf](UEOT_PHYSICS.pdf)：正式排印PDF，229页。
- [UEOT_PHYSICS.tex](UEOT_PHYSICS.tex)：与当前规范正文绑定的排印源。
- [CHAPTER_DOSSIER.json](CHAPTER_DOSSIER.json)：逐章思想、前提、量词、完整公名、具体见证、来源及开放责任。
- [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json)：保留11项原始来源，另列本版实际受验源码身份。

第60章证明完整合法效应分离任意有限复密度态，建立Hermitian算符的实线性效应张成，并证明原复操作模型对所有联合态满足局部层析；双相干负控说明对角效应库仍有盲区。第61章证明完整凸纯态必为归一向量态，同辅助载体纯化由实际酉变换联系，不同辅助载体单列等距嵌入和共同直和；具体复数见证检测酉、伴随、转置和共轭方向。第62章从真实历史块、零块和合法效应出发，对共同固定深度经典历史控制器建立逐动作误差和，接到原Protocol的真实叶路径和完整记录TV。

## 实际本地验收

本版实际统一验收通过35个公共模块、747条显式定理和985项唯一命名公理审计；新增6个模块、101条显式定理、130项审计目标。10组具体见证单列193条定理、71个定义、5个缩写，共269项命名审计。六个精确证书的42项审计通过，四个篡改真证明被拒绝，四个同数据假值证明被接受。100个运行测试方法和四个演示实际通过。Lean实际构建8799 jobs、退出0，存在普通linter警告；允许基础仅propext、Classical.choice、Quot.sound。92项QM/Core源与olean绑定，56项实际递归Core源码未变。

本次三遍实际排印均退出0，版面警告为空。视觉验收以[root实际回执](evidence/v3.4/pdf-visual-review.json)及[渲染身份](evidence/v3.4/pdf-render-manifest.json)明确列出的范围为准：root实际完整页为 1, 4, 40, 151, 152, 153, 170, 180, 186, 199, 205, 209, 213, 214, 229。协作者A另行[实际查看25个完整页](evidence/v3.4/pdf-collaborator-review.json)：168–189页覆盖新增三章全部22页，另查213、214与229页的身份、计数和公名清单收尾。总览与指定完整页审查不表示全书229页逐页完整精读；书目helper本身只绑定这些实际回执，不产生额外视觉观察。

- [实际统一数学与运行验收](../kernel/evidence/v31.8/lean-verification.json)
- [实际89项源码清单](../kernel/evidence/v31.8/source-manifest.json)
- [结构回执](evidence/v3.4/book-structure.json)、[排印回执](evidence/v3.4/pdf-build.json)
- [逐项档案审查](evidence/v3.4/dossier-review.json)、[本地发布门](evidence/v3.4/local-release-gates.json)
- [旧3.3精确档案](evidence/v3.4/dossier-prior-v3.3.json)、[历史字节保护](evidence/v3.4/prior-v3.3-preservation.json)

附录D三套程序和字面代码块与3.3逐字节一致；757项旧程序检查保留3.0的实际执行身份，本轮只核对源码，未重跑。详见[本版继承程序身份回执](evidence/v3.4/legacy-source-reuse.json)。旧章与旧结果对象内的检查点和未闭合责任保持其原版语境；第60–62章已经解决的有限责任由本版新证明和当前聚合验收承担。

## 精确身份与远端状态

| 对象 | SHA-256 |
|---|---|
| Markdown | `868a51150eb1a4cf56b86b06090e9d31b25096311689dbff6bf8da6e3210a08a` |
| PDF | `24b61ee3dd8d935afd47386460b352c40d4373e8328e2b4cfcfb8d8c460c60f0` |
| TeX | `2ff9b64cc69a065f2a2a1b96c836c4c329bb982b25f17e41d751aefa94284599` |
| 89项实际统一受验输入集合 | `a34337cd75cd70b0f2e1125899c4dcd09aa7b132642adaad2c17ef8a69f12f6e` |
| 89项当前发布字节集合 | `054f2e01c50f25d2519a2200eeda5ccd9849c27cfc67141eeaaf552dd4d995d1` |

统一验收后，只把 `PurificationUniqueness.lean` 文档注释中的一个英文词替换为同义词，以免旧workflow的字面扫描误判；数学代码和声明均未改变。原8799 jobs只绑定统一受验输入集合。[发布源码核对桥](../kernel/evidence/v31.8/publication-source-reconciliation.json)逐字节证明这一处注释变更并绑定当前发布字节集合，没有追加本地Lean构建；远端CI仍须实际验收最终发布字节。

本轮作者基线为 `7d05d0369b6793e28f0e39efaa77c0c9887479d1`，这是完成v31.7源码和远端元数据后的主线身份。本版当前远端门仍为 **PENDING**，没有填入尚不存在的v31.8源码commit、PR或CI运行号。旧v31.7的真实PR347、独立源码/主线CI与后续元数据发布，保留在[3.3远端回执](evidence/v3.3/remote-publication.json)，不计为本版CI。

## 科学边界

有限量子内核继续采用明示的有限复矩阵、全部合法效应和规定的过程。纯化唯一性、局部层析和逐动作预算均有具体前提与作用范围；不同辅助维数不被命名成异型酉，固定深度经典控制预算不扩大到相干控制器、变长停止树或额外环境。未从冻结Core的106项和四生成器唯一导出复量子理论，没有新增真实实验。三代结论仍依赖谱、表示、阈值和有效窗口等前提。完整自然理论、一般无限条件过程、非微扰四维QFT及量子引力继续列为开放责任。
