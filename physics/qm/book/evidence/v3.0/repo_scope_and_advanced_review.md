# UEOT 物理总著：来源范围、继承清单与高阶章节审查

审查对象：既有《UEOT_Physics_Unified_v2.0.md》及仓库 `qm_v313_work/physics/qm`；高级正文范围为第 14–32、36–46 章，另检查第 35 章的误差接口。审查方式是实际源文阅读、公式与假设逐项复核；本审查没有重新执行历史验证程序，没有修改原件，也没有把本审查写成新的独立著作。

## 1. 总体结论与必须修正的项目

现有总著具有第 **0–48 章**及附录 A–E 的完整结构。第 14–32、36–46 章的大部分主要公式和解析论证可保留。尤其第 31 章的条件三代选择器、第 36 章的正确高能双候选分类及五色反例、第 37 章的味秩一和式、第 38 章的 CP 相位—损耗界、第 39 章的四能级锐见证、第 40 章的条件吸收和第 46 章的历史依赖统计，应成组继承。把书缩成有限矩阵内核说明会丢掉其主要物理内容。

| 编号 | 精确位置 | 审查发现 | 处理 |
|---|---|---|---|
| AR-01 | 24.1 首个拉氏量 | 裸参数 `m₀,λ₀` 与 `L_ct` 同时出现，但没有先说明裸式与重整化分解；后续顶点改用 `λ`，容易双计数 | 完整重写 24.1，显式给 `φ₀=√Zφ φ`、`Zφ m₀²=m²+δm²`、`Zφ² λ₀=μ^ε(λ+δλ)` 及两个反项顶点 |
| AR-02 | 27.3 | v29.2 曾给独立顶点 UV 张量收缩；v2 仅列 `δZ₁=δZ₂` 和自能积分，丢失一条有区分力的推导 | 补回四维 UV 张量缩并和有限部分/红外边界，保留 K-QWARD-01 |
| AR-03 | 40.2 标题 | “规范保持”容易被理解成 gauge preservation，正文证明的是 norm preservation | 改为“范数保持”，不改变 C-02 |
| AR-04 | 40.4 相干式；40.5 交叉引用 | A 的简并谱标签不唯一指定 H 的能量；“5.3”是旧分章号 | 用共同本征基 `(a,α)` 区分 H 能量；改为“第 40.3 节”，保留 C-03/C-04 与能量公式 |
| AR-05 | 42.2 末句 | “未使用形式化证明助手”如果照搬为整本新书状态，会与 v31.3 的 196 定理冲突 | 仅限定“本组高级物理解析推导及三套历史科学回归未由 Lean 形式化”；独立列当前有限内核证据 |
| AR-06 | 14–19、21–23 | 正确结果被压缩，部分历史重要适用域与反例没有正文落点 | 增补共同算符域、Galilei 大质量支、置换/超选反例、Davies/GKSL 与过程 Markov 的差别、Shale/Type III/Haag/Maxwell no-go |
| AR-07 | 25–26 | 正确式子可留，但历史 Wilson/CS 独立系数对照、有限方案匹配及重介子散射例丢失 | 增补带明确维数与余项的推导；两份 v28.1 互补内容并存 |
| AR-08 | 31–32、36 | 算术和反例正确；容易被“196 Lean 定理”包装成完整粒子理论已证明 | 在对应正文声明 Lean 只实现指定整数合同和指定谱/弱窗口桥；六局域异常、FAD、五色高能分类仍分别为纸面/精确回归层 |
| AR-09 | 35.2（root 负责） | 正确的 diamond telescoping 需完整 CPTP 对象；选择分支本身不是 TP，末端误差也须统一量词 | 将每步 instrument 写成保留全部结果的 cq 通道，经典反馈并入载体；末端 `ε_M` 应为共同允许输入上的 TV 一致界；后验另带正概率下界 |
| AR-10 | 39、46 | 主要统计结论正确，不能删掉两层校准和历史条件 | 永久保留 E-02、共享 Bernoulli 反例、条件逐次下界、置信事件的条件化责任与可选停止超鞅 |

以上没有发现必须撤回 G-01、G-02、F-01–03、M-01–05、C-01–05、P-UGL-01、P-UTP-01/02、P-ULG-01/02 或 P-UST-01/02 的实质反例。这里的 CLEAR 是源级数学审查结论，不等于这些命题已进入 Lean 或被真实实验检验。

## 2. 物理来源的真实覆盖与身份

### 2.1 原总著与归档

主文原件：`/workspace/scratch/474cf6b1f047/qm314_sources/UEOT_Physics_Unified_v2.0.md`，260407 字节，SHA256 `2fa47d663bb212153a2829e816444e99805348266eefd5a27882e8dbbf4e58a1`。与 ZIP 内同名 Markdown 逐字节一致。

TeX：311222 字节，SHA256 `2b7d85a6c4629d629318d8b191a91015c2d44b504b2418af640a2661ffcf085a`；与 ZIP 成员逐字节一致。

两个 PDF **不是同一字节产物**。独立原件 832671 字节，SHA256 `18187b7b949901867260d795d1840bf597669167cd8da86f1740c5b0c128dff2`；ZIP 内 657100 字节，SHA256 `9c448ea5e4c2027e678d3b91d9fe7e48401aa86ffda315f5a618b040e5a6de36`。本审查不以文件名宣称二者同版排印。新版应从冻结的新主源重新渲染并单独留回执。

ZIP：4443142 字节，SHA256 `bde734fc240f88b2c984f345ed2e73abae47d37f4aadf895870abab28b25acb9`。已解压的三套 `verify_ueot_quantum.py`、`verify_frontier.py`、`verify_completion.py` 和各结果 JSON 是可复核来源；本审查只读其来源，不重新执行。旧的量子主文 v1.0 为 174250 字节，SHA256 `6640e0be8e3b615dadbe01dcf8063a0ad1ab458b765f1ec0f4e8fcafd0cad9b5`。

完整逐文件哈希在同目录 `advanced_source_catalog.json`；其中缓存 text view 的哈希只绑定缓存字节，不替代原 TeX 的 SHA。

### 2.2 仓库入口分层

| 入口 | 实际作用与继承方式 |
|---|---|
| `physics/README.md`、`physics/interfaces/CORE_PHYSICS_CONTRACT.md` | 现行领域扩展入口及 C/B/S/P/E/O/X 类型合同，必须成为书的依赖轴 |
| `physics/status/CURRENT.md` | 较早的领域路由状态；不得覆盖 `physics/qm/status/CURRENT.json` 与 v31.3 实际证据 |
| `physics/qm/UEOT_QM_UPGRADE_PLAN_v31.0.md`、`audits/*20261019.md` | v23–v30.11 继承与退役来源；计划与已实现内容必须分开 |
| v31.1、v31.2、v31.3 报告与 ledger | 内核演进与逐项形式化边界；应接入既有总著，不替换高级物理 |
| `domains/physics-cosmos/STATE.md`、相关 council/memo | 明标 LEGACY/PRECURSOR 的拓扑前沿研究历史；保留研究动机，不升级为当前定理 |
| `book/chapters/10-*`、11、12 | 原仓库章节是脚手架/研究占位，不是刚取得的完整总著；不得据此误称历史高级物理不存在 |
| `source/paper/` | 早期主论文归档；该 PDF 与用户根目录 `UEOT_v3_top.pdf` 不是同一 blob |
| `source/extracted/` | 早期 ontology、quantum/topology/GR 解释性与经验目标摘录；其中研究纲领用语不能盖过正式 Core 条件化定义 |
| `archive/README.md`、`publications/README.md` | 归档及发布快照约定，当前主要是入口；不能把预期目录当作已存在的研究全文 |
| `validation/` | 规定对照、否证和证据类型；数值相容与 UEOT 独有解释力必须分开 |

### 2.3 原论文到正式 Core 再到 QM 的桥

原上传 43 页 PDF 的 SHA256 为 `6c2acdf8d8232377066c3363ce3f0b0a14b3b60608c485ce70f2089c8a2263c3`；原始 Ω 与 β₁/三环/指标论证是研究动机。正式 Core 的泛对象是指定未来与协议下的响应等价/充分压缩；强自维持 Ω 还需合法破坏、修复、持续窗及资源合同。二者不可混称。

`SOURCE_AND_REPRESENTATION_REVIEW_v31.2.md` 已明确：Core Ω 的破坏证书中 `χ=1` 表示存活，失败量是 `1−χ`；单调性须有条件。动态信息、目的与 Π/Φ 评价需要独立任务桥。Python 哈希只标识固定表示数据，不是同一历史物理对象的身份证明。量子坐标维数不是拓扑 Betti 数，也不是 Hilbert 最小维数。

原来的 `β₁=3 ⇒ Index D=3 ⇒ 三代` 链应保留为退役路线；合法替代是指定 `(M,E,D)`、计算扭曲指标、区分净手征数与成对零模，再说明载体为何独立被选择。有限矩阵不能满足全域精确 CCR：`tr[Q,P]=0`，而 `tr(iℏI)=iℏd≠0`。这条界同时约束 CV、数值截断和新有限 Lean 内核的宣称。

## 3. v23–v30.11 必须继承的推导、反例与证据清单

历史源位于 `/workspace/scratch/474cf6b1f047/qm_text_views`。以下版本对应的缓存具完整可读行段，但原 TeX 未在 v31.0 取证中取得字节；历史“通过数”只作来源报告，不冒充本次运行。

### 3.1 v23：有限量子操作、测量父层、SRN 与 QDRR

来源：`UEOT-QM_v23.0_有限维最终收敛核心-相干测量父级完成_SRN生成元完备分类_QDRR实验闭包_严格版.tex`，缓存来源 `libfile_baee8c0ec7d8819191d930c74371b209`，原文 1–1473 行。

必须保留的推导包括：tomographically complete Hermitian effects ⇒ ρ 唯一（对 Δ 取 `tr Δ²`）；正概率 instrument conditioning；`V=ΣA_aμ⊗|aμ⟩` 的 isometry、投影、部分迹；测量的父完成/公共商/归一化三层；强 SRN 固定每分支内部全部态 ⇒ block-Schur，Gram 逆构造；Hadamard 复合与时间齐次连续半群；生成元在零和子空间 CPSD 的充分必要性；write–noise–erase 对编码子空间的精确恢复；两相位恢复每个 K_ab 的实虚部。

永久反例：公共块对角读出不能区分相干父态与去相干态；K=全一矩阵才是无附加通道，K=I 是完全去相干；`Λ=[[0,-1,-1],[-1,0,-10],[-1,-10,0]]`、`z=(2,-1,-1)` 给 `zᵀΛz=-12`，证明逐对衰减不保证多分支 CP；一般 Born 或保守对象谓词不生成新物理。

统计继承：观测范围 [-1,1] 时每设置 `n≥2 ε⁻² log(2m(m−1)/α)`，不是已退役的 `1/(2ε²)`；m(m−1) 是指定单事件 SRN 模型的标量坐标计数。全矩阵 Frobenius/算符误差、独立/条件试次假设、基线校准与串扰要保留。只有独立且仍为 Schur 的硬件噪声才允许 `K_obs=K_hw⊙K_act`。

历史报告有分支保持 9635、公共盲性 3000、复合 2200、pair 坐标 21684 等数值检查；这些是旧回归计数，不是 Lean 定理数，不是器件数据。总著第 38–41、46 章给出后续更强见证和统计，不能回退成“测两角即可证明整个 Born/坍缩”。

### 3.2 v24.4：量子选择、无限维与连续变量

来源 `libfile_c5e392fe284081919dc2739e6301f5a7`，原文 1–2288 行，尤其 P2 exact background、LE/ESP、UCA 和 energy-tail sections。

需继承：有限操作理论的组合、因果、粗化、有限维实线性载体与状态集条件；LE/CIT 与 ESP 的独立领域选择地位；所调用重建定理是外部原始研究而非 UEOT/Lean 已证；经典模型不满足 ESP、实量子可满足 ESP 而不满足 LE，泛 Core 两者都不强迫。不能以“两个原理”宣称语法无关最少公理数。

有限系统重建不决定无限对象是否存在、正常态还是奇异态，也不决定完整无限复合。连续变量需自伴域、闭二次型、Stone 连续性、有限 canonical DOF 的 Weyl 正则性与不可约性。UCA 在指定 Weyl 扇区就是不可约性；非平凡 cocycle、全辛协变及维数大于一是有区分力的前提。轨道 Weyl 因子可与自旋重数张量积；不应在整个粒子 Hilbert 空间错误要求轨道表示不可约。两个互不混合扇区可有 κ₁≠κ₂；统一 ℏ 需要跨扇区混合或额外物理输入，数值仍需标定。

CV 证书要写 `G≥0` 自伴且低能谱投影有限秩；自由粒子仅动能在 ℝ 上的低能子空间仍无限维，是必留反例。保留尾界 δ≤E/Λ、正概率归一、IC 逆问题条件数、频率误差与后选择代价。旧文有较弱 `||ρ−ρ_Λ||₁≤2√δ+δ`；新版若采用更强 gentle bound 应给独立证明与 D=½trace 约定，不能用计划冒充形式化。连续结果后验是 `p_ρ` 几乎处处分解，不是除以零概率单点。

自由 Gaussian、双缝、HO、井、隧穿、氢原子、Williamson 与网格细化是标准物理复现。finite-well 的收敛不应硬称所有模型都是二阶。旧 42 gates 不是当前 196 Lean。

### 3.3 v25.2：自旋、粒子、交换与超选

来源 `libfile_50a2d54a18b08191b489ea5bef33f42b`，原文 1–1192 行。

需继承 Wigner 射线定理与连续分支/全局射影区别、共同光滑域、SU(2) 表示、Bargmann 中心质量、`Q=K/m`、`S=J−Q×P` 和内部能量 Schur 推导。`m>0` 是指定 massive 分支；不是完整 Galilei 不可约表示分类。反酉是射线对称实现，不是复杂线性 CPTP 通道；transpose Choi 的负本征值是具体反例。g 因子、质量与磁矩耦合非旋转群导出。

置换不变只给 `⊕ V_λ⊗M_λ` 的交换表示分解；N≥3 的 para 扇区可存在。传统 Bose/Fermi 选择或文献中的完整扩展不变性是额外前提，ESP 的纯化唯一性不等价于那条完整不变性。NR 自旋 1/2 Bose、自旋 0 Fermi 是形式上相容反模型；“半扭转”不证自旋统计。二维编织、无限模 Fock 的非唯一表示另有域。

超选中心 `Z(A)` 与一般交换子 `A′` 要分开；后者投影可能仅是重数空间。DHR 的不等价表示不是固定 Hilbert 空间的中心投影穷尽。Bargmann 质量和粒子数超选均是框架相关。

必须继承 SG、Rabi、CHSH、交换投影、Galilei boost–translation 两条独立路径，以及 N=3 para 反例和非 CP 转置测试；只能标作标准物理/历史回归。

### 3.4 v26.3：多体、开放、非 Markov 与热统计

来源 `libfile_b18f7cdf70048191bb16b228fd87c94b`，原文 1–1113 行。

多体继承：有条件 Lieb–Robinson 指数尾；无限准局域 C* 态；SSB 两极限次序；MPS 的一维局域有限维/统一隙条件及存在/算法/任意态三种不同问题。有限峰、能级交叉或一步 Schmidt 截断不证热力学相变或长期高效。N=1 hopping 不检验 Fermi 多粒子符号，必须保留 N=2 CAR/Fock 回归。

开放继承：固定乘积初态的 CP reduced map 不意味着半群；有限 GKSL 刻画半群物理性，Davies 的浴混合、弱耦合/van Hove 缩放、Bohr 频率、正谱矩阵、KMS 比值与 commuting Lamb shift 给微观桥；Gibbs 驻定不等于唯一热化。unraveling 的选择取决于环境监测，不独自选择本体坍缩。

记忆继承：Nakajima–Zwanzig 的投影依赖核与初始相关非齐次项；CP-divisibility 与全 instrument 过程 Markov 的区别；CNOT 写环境—reset S—CNOT 回写的 causal-break 反例，同 reset ρ 而未来 D=1，任意仅当前态预测器最坏误差至少 1/2。被动观测相同不能替代干预充分性。

热统计继承：真实 Lehmann 权重和 KMS strip βℏ；自由能—相对熵变分；非对易 Kubo 独立小 kick 对照；Spohn 的满秩驻定与支持条件；闭系统时间平均保留简并能量块，时间平均不等于逐时收敛，ETH 不是通用定理。

对象证书须保留 `(ε_pred,ε_mem,ε_leak,Π_pers,R_δ,C_glob)` 的每项协议、距离和估计方法。`ε_mem` 是给定记忆模型的剩余误差，不要求真实系统无记忆。量子 Darwinism 的 χ plateau、片段大小、冗余计数、强客观性以及可存的全局相干是不同指标。旧 48 gates/多模型回归不等于整章形式化。

### 3.5 v27.1：相对论、自由场与局域代数

来源 `libfile_9c8e09622a0881918075be0361725504`，原文 1–645 行。

必须继承 Minkowski、Poincaré、正能谱、真空与局域性为新领域输入；谱条件不独自保证真空唯一。场是共同域上的涂抹算符值分布。KG 模、Pauli–Jordan 因果支持、非零类空 Wightman、Dirac massive kernel 与 Clifford/spinor 完备、Maxwell helicity±1 和 gauge-invariant F 的因果性应有明确推导/输入。

四个 Aμ 模式不能全当正范数 photon；正度量、点局域、协变规范势、Maxwell 方程不可任意同时坚持，辅助不定度量/物理商与横向局域场的区别必须保留。Shale 的 Bogoliubov β Hilbert–Schmidt 条件、局域 Type III、split 的额外条件、Reeh–Schlieder 的生成性与循环性条件、Haag 对天真全局 interaction picture 的限制不能省略。自由场/有限调节/四维相互作用微扰是三个闭合等级。

旧 21 tests 是 boosts、spinors、传播核、偏振等数值基准；regulator 的非零类空尾不自动是真实因果破坏。标准自旋统计与 LSZ 是外部重定理。

### 3.6 v28.1 双来源：标量场、重整化、EFT 与三种 RG

来源 `(1)`=`libfile_590320d1e3ac81918dc270b77ca5b1ac`（737 行），无后缀=`libfile_be4ef8a6eab48191a5da170bbb6b54da`（686 行）。两者不是已证相同原件，内容互补。

必须继承裸/重整化字段关系与反项顶点；d=4−ε 的 λφ⁴/4! 一圈因子；有调节 tadpole 的质量减除；三个通道的 bubble、Minkowski 解析继续、相同粒子 1/2! 与 optical theorem；MS 与带质量 MOM 阈值；固定裸量的 CS 算符和场异常维数符号；有限方案重定义只能在声明条件下保留 leading coefficient；Landau 是微扰外推诊断。

`g=λ/(16π²)` 才是方便的 Wilson–Fisher 无量纲圈展开参数，`g*=ε/3`；不能因 λ* 数值大就错误否定小 ε。Wilson 薄壳与 CS/一圈系数要独立计算，红外 s 与 UV log μ 的方向不同，不能用一条式子两边抄写自证。

无后缀原文保留质量矩阵正定条件 `m_l²M²>κ²`、Schur 补和反项规则；(1) 保留完整 heavy-mediator scattering 与归一化 WF 展开。总著已保留 Schur 补及稳定性，还应补回散射/匹配与回归责任。smooth MOM threshold 不等于删除重场后的 EFT matching。

三种 RG 分别作用于 action/couplings、multi-time process、protocol-response quotient；实时 Feynman–Vernon/Schwinger–Keldysh 桥还需同一分割、初态、干预、读出和合法极限。Euclidean 積快模不自动 CPTP；没有一般 `ObjectRG fixed point ↔ Wilson fixed point/Markov order`。

### 3.7 v29.2：QED 的真正计算与 gauge 边界

来源 `libfile_2e0cca3318608191b5e18fb919264c98`，948 行。

必须继承 D=∂+ieA 与顶点符号、Gauss/边界、Abelian FP 零模与 BRST、完整 Ward 恒等式的外部定理地位；树级 Ward 不证明所有圈阶。保留 photon UV、electron UV 以及独立顶点张量缩并；direct mass coefficient δ(Z₂Z_m)=−4a 与 Z_m−1=−3a 的区别。

QED 三个基准：massless photon-only e⁺e⁻→μ⁺μ⁻ 的完整自旋迹和相空间；一圈 vacpol 的减除/IR/UV/阈值/活跃味；Schwinger 的完整圈图来源与二维 simplex 积分。所谓独立仅指已完成标准 loop reduction 后的数值积分独立于最终 α/(2π)，不是从裸 Minkowski 积分机器推完。BRST/Slavnov 的假设、soft inclusive resolution、infraparticle、vector gauge anomaly 与 axial anomaly不能混同。

规范轨道可实施一致下降并不选出 U(1) 或唯一 SM；公共概率可能看不到 determinant-line phase，全局相位/holonomy 要由完整动态规范一致性另行控制。旧 31 regression 不构成精密 QED 实验拟合。

### 3.8 v30.11 与 v31 的 G3 修订

来源 `libfile_a8385e429bac8191a32f48e62b75928c`（330 行），另有 deep-audit/mainline/regression sidecars；仓库的 `G3_SELECTOR_REFINEMENT_20261019.md`、`G3_PHYSICAL_ADAPTER_CONTRACT_20261019.md` 是本轮正式修正。

必须继承：复制封闭 no-go；GOIT 的 determinant/Pfaffian line、connection-compatible equivariant trivialization 与 inflow；HGP 的真正手征谱而非“存在父对象”；一般整数解；弱 SU(2) 活跃窗口预算；atomic packet 由方程+预算已推出，故删除独立原始性公理。

永久反例：去掉弱界有多包/大色；放开复色 SU(2) 有 `(2,4,1)`；轻子也允许 R/Rbar 时 `(Nc,Nf,l,k,β)=(3,2,1,1,0)` 可过六局域异常及弱预算，说明 homogeneous lepton 实质而非语法；一般 β 缺 Eᶜ 会留下 grav²X 与 X³ 残差，RHN 特殊 q_E=0 不代表全 β；以 Nc-依赖 Qu,Qd 替代固定 2/3,−1/3 时三色强制消失；高能扩展群 AF 不能替代低能弱窗口 AF，第 36 章五色点是关键新反模型。

完整物理仍要 HGP 存在、场内容唯一性、全局群/异常、破缺稳定真空、阈值、Yukawa、质量混合与实验。重中性矢量“普适”必须完整矩阵 κI，等对角但有非零 off-diagonal 的旋转反例不能删除。第 37 章的单重矢量 rank-one EFT 后果是条件预测，不是新粒子发现。

## 4. 0–48 章总范围登记（避免升级时缩水）

| 章节 | 必须保留的主线 |
|---|---|
| 0–3 | 定义/证据类型、Core 实现边界、量子选择、Fisher–作用量/复振幅/Born 的条件链 |
| 4–9 | 有限操作、对象充分性、测量父完成、SRN、QDRR、信息/纠错/计量 |
| 10–13 | 无限维、算符域、Weyl/CCR、NR 基准、Gaussian |
| 14–20 | 对称/自旋、交换/Fock/超选、多体、开放、记忆、热响应、任务/控制 |
| 21–28 | SR/QFT 域、自由 KG/Dirac/Maxwell、相互作用/LSZ、RG/EFT、QED计算 |
| 29–32 | YM/SM候选、Higgs/味/中微子、条件 G3、FAD/指标与退役路线 |
| 33–35 | 统一实现/应用/误差装配；root 应接入新的真实核验证切片 |
| 36–42 | 正确高能三代问题、五色反例、FCNC和式、SRN相位、四能级见证、随机实际化/能量/不可识别性、实验合同 |
| 43–46 | 环上全局域/holonomy、Berry/SSH、有限格点规范、相关试次与可选停止 |
| 47–48 | 研究计划、AI/状态回写接口；计划不得成为已实现物理 |
| A–E | 符号/单位、外部定理、命题注册、来源与完整代码/结果、生成与修订记录 |

GR、cosmology 与强 Ω 的统一性仍是有来源的研究接口：本次没有 Einstein 方程、完整曲率动力学、量子引力或宇宙学参数的形式化/经验新结果。保留这些入口的开放状态比从目录删除它们更准确。

## 5. 196 Lean 定理究竟覆盖哪里

v31.3 已冻结主线证据：13 模块、196 个显式通用 theorem、213 个命名通用公理审计；六个具体导出实例另外 42 个审计目标，四个坏数据 false witness 另 4 个；87 runtime tests。PR 和 main 的真实日志已独立核对。它们是不同计数对象，不能相加成物理定理或实验数量。

覆盖范围：有限复 PSD/密度与 Kraus/Born；实际 all-finite-word 记录响应及 Core M-QD/递归充分商；真实词 effects 的实线性 span；有限 presentation 的局部生成/拉回闭包 ⇒ 全词坐标充分性与可达后验 Ax/p；保留所有结果的完整有限确定自适应树；标量 M-TC 接口；指定整数选择器和明确谱/弱预算桥；有理复矩阵 exact interpretation、sqrt 权重 ordinary Kraus、ragged padding；实例数据条件由 Lean kernel 的 `decide +kernel` 核实。

**不能从该数目外推：** 通用 JSON/Python 导出器正确性、标签映射、线性基搜索/Gram消元、d²终止公式、最小 Hilbert realization；一般 trace/diamond 上界的数值算法；CV/unbounded算符、量子选择/重建、SRN全分类、QDRR统计、Wigner/Galilei/Fock/超选、GKSL/Davies/热化、多体极限、QFT/LSZ/重整化/QED、Higgs/flavor、六局域331所有实β、全局异常、FAD、五色高能分类、Berry/SSH、随机Itō吸收或实验统计。

本轮 v31.4 新 `Effects.lean`/`Stability.lean` 已另作只读语义交叉审查：实际全部 effect Born 区间、完整/分支拉回、全 effect supremum 距离、完整通道收缩、正概率后验 `2d/p`、实际 channelDefect 与轨迹到 M-TC 的链在源级 CLEAR。其最终 build/audit 与精确数目由集成回执决定，不混进上述冻结 196。尤其新距离尚未在 Lean 识别为 ½trace norm，channelDefect 是非可计算全态 sup 定义，不是已实现数值证书算法，也不自动提供 diamond/任意 ancilla 或所有自适应误差合同。

## 6. 证据语法与接下来正文的规则

旧书 D/P/K/H/S/E/N/O 表示定义、纸面证明、标准重定理、假设、综合桥、计算/经验、反例、开放等证明状态；新 Core contract 的 C/B/S/P/E/O/X 表示依赖类型。它们是两个轴，尤其两套 P/S 不能混同。每段应说明采用哪一轴，避免用单字母“P”暗示 Lean 证明。

下一份 `advanced_revisions.md` 将给完整插入/替换块，保留原命题 ID、数学思想和正确详细正文。未列入替换的段落应原样继承，不把此审查报告当作删节书稿。新增段落用局部来源标识衔接本报告的版本/章节，不伪造未知原件哈希，不宣称旧验证本次已运行。
