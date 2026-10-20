# UEOT-QM v31.5 数学、源码与见证审查

状态：CLEAR；本地实际执行 PASS。日期：2026-10-20。审查由多个 AI 子智能体及根智能体完成，不宣称独立人工同行评议或新增实验。

## 审查对象与分工

finite_response 实现 Mixture，kernel_certificates 实现 Cesaro，spectrum_bridge 实现 Survival；三者使用独占文件。之后轮换互审：混合作者审查 Cesàro 及运行混合入口，Cesàro 作者审查 Survival 和运行源，Survival 作者审查 Mixture/Cesàro 并把具体证明写入持久复验门。根智能体负责实际对象与前提审查、公共导出／审计集、运行入口、统一执行、正文和最终身份协调。详细日志见 [聚焦档案](../kernel/evidence/v31.5/focused-evidence-archive.json)。

## 通用数学的实际边界

| 模块 | 定理／定义／本模块审计 | 实际证明对象 | 不能省略的前提与未闭合范围 |
|---|---|---|---|
| Mixture | 23／7／30 | PSD 密度混合、完整 sqrt-weight Kraus 混合、分支／拉回／通道等式、全效应与全态 TV 上界、联合界、有理解释 | 非负归一；同库 TV；联合误差明确加成员项；共同载体；无通用 Python 细化或 diamond norm 识别 |
| Cesaro | 23／7／30 | 真实平均密度态、矩阵残差、全效应 1/N、PSD／迹一紧性、通道连续性、不变子极限和平稳存在 | N>0；无初态版本要求非空载体；不声明唯一、逐时 mixing、全平均收敛或随机轨迹遍历 |
| Survival | 32／13／45 | measure–prepare 完整仪器、任意矩阵成功分支、对角全成功记录、QSD 几何律、Doob 完整实现及不变成功记录 | 行约定 pQ；次随机性；明确合法左右谱数据与 r>0；正后验；不宣称一般谱数据存在或无限条件极限 |

Mixture 的 TV 常数 1/2 使用归一后的中心化效应概率，未用松的逐项 1 上界冒充尖锐结果。两通道族的联合上界按 q 加权成员缺陷；对不同输出标签没有未经建模的历史误差推论。运行 MixtureWeightBudget 绑定一份实际成员库和精确有理权重，API 拒绝负权、未归一、非精确输入及上下文不相容。

Cesaro 的紧性在原生有限复矩阵拓扑中完成。所使用的 L2Operator 范数通过保持 topology/uniformity 的接口进入证明；PSD 闭、迹一闭、范数界及实际通道连续性均有证明。它以标准有限维矩阵数学实现长期平均主题，没有实际调用 Core M-OI/P-PER，因此不登记为直接 Core 推导。

Survival 真正导入 Core 的 leftPerron_pow、qsd_survival_mass_pow、qsd_all_steps、perron_root_le_one_of_substochastic，以及 doobTransform_row_sum、doobInvariant_sum、doobInvariant_stationary。它先证明量子矩阵实现，再应用这些标量结果；没有把最终量子响应等式直接当成假设。失败分支补齐迹保持，但没有新增墓地态。给定谱关系不替代主谱半径识别、存在性、吸引条件或自然界解释。

Doob 的当前量子登记范围是成功分支、全部有限成功词、成功概率 1 和正后验不变；并未引用不存在的单独完整 channelState 不变定理。首次失败时间允许无穷取值，期望寿命的尾和论证仅登记为正文解析结果。

## 正例、前提删除与具体证明门

运行内核新增 13 个有意义的方法，验证 TV 达界与非达界、换库失败、未归一／负权拒绝、周期轨道与平均残差、恒等通道非唯一、QSD 生存、Doob 的 qh、行方向、初态及损失分支、零概率后验。完整 100 方法实际通过；不把合成有限模型称为实验。

持久 [MixtureExamples](../../../formalization/ueot-qm/scripts/witnesses/MixtureExamples.lean) 有 5 定理／4 定义；[SurvivalTwoState](../../../formalization/ueot-qm/scripts/witnesses/SurvivalTwoState.lean) 有 24 定理／6 定义。全部 39 名都在实际 Lean 执行中产生公理报告，且不进入通用 334／392 计数。具体例子证明数学语义，负例指出删去前提后的错误结论；它们不替代已编译的通用定理。

持久 [verify_finite_witnesses](../../../formalization/ueot-qm/scripts/verify_finite_witnesses.py) 独立定位包，使用固定工具链，核对两个源文件中显式 theorem／def 与 print-axioms 清单的逐项一致性。它记录 32 个通用 QM／递归 Core 模块的源和 olean，以及见证源、验证器、包配置、Lake 执行文件的实际身份，检查运行前后一致。脚本按这些受控见证的声明风格解析；没有被表述为一般 Lean 语法验证器。

最终 verifier 修正了 Lake 调用入口的符号链接处理，以保留经 lake 名称分派的工具链管理器语义。最终脚本及两见证在修正后实际执行 PASS，回执为 [finite-witnesses/verification.json](../kernel/evidence/v31.5/finite-witnesses/verification.json)。

## 全包、基础与源码绑定

18 通用模块共 334 显式定理；392 项命名审计由 334 定理和 58 个列入清单的定义／构造组成。新增 78 定理和 27 定义共 105 项。允许基础为 propext、Classical.choice、Quot.sound，无 sorry、admit、native_decide 或未审查公理。完整 Lean 4.33.1 编译实际退出 0，8739 jobs；旧 Core／Observables 的既有 linter 提示单独保留。

原有六个精确导出实例、42 项审计重新运行；四个被篡改的通过证明被拒绝，同时四个相同数值数据的 check=false 证明通过。错误环境、超时或失败归约没有单独计作数学拒绝。

最终 64 项源清单相对全包验证时的 61 项，只新增独立执行的有限见证门及两份见证，并更新相应 workflow 步骤；通用数学和运行输入字节相同。[源码冻结协调](../kernel/evidence/v31.5/source-freeze-reconciliation.json) 明确记录这种先后关系，不假称完整构建曾包含之后才增加的脚本。冻结 Core 13 个递归模块源与研发基线逐字节相同，106 项与四生成器计数不变。

## 正文、分类与出版审查

第 51–53 章包含完整证明、例子、反例、源码对应和开放责任。13 个新编号加入原有 88 个编号，全部旧锚保留。第 0、1、20、47、48、50 章及附录更新当前边界。

本版修正原逐章档案对合同字母 E/O/X 的混用。dependency_class 采用冻结合同的 E=有效／建模假设、O=可观测后果、X=开放 UEOT 科学猜想；argument_status 继续单独记录经验、反例和开放研究。标准定理尚未迁入 Lean 不是科学猜想。物理依赖为空的纯出版附录允许空集合。

PDF 实际全页概览和指定全文页面的视觉检查均已完成，171 页无阻断排版问题。P-QCE-02 的一个内部链接落在标题前一实际页，链接有效，保留非阻断注记；不以重新编译消耗掩盖该观察。源码、PDF、TeX 与档案均使用本版 SHA256。

## 科学判断

接受的是明确量子扇区中的有限数学与可复验实现。完整 UEOT→QM 选择、现实三代、具体物理参数、实验检验和连续／场论扩展保持其独立研究责任。下一轮以可反驳的量子选择前提和含记录的误差模型为优先；详见 [路线图](../ROADMAP.md)。
