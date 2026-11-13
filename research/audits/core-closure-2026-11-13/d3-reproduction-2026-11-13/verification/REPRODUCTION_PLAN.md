# D3：固定版本关键 Lean 证明的最小充分复现

准备日期：2026-11-13。准备者：B；实际 Mac 操作和最终接受由主审统一执行。

**准备状态：未在准备环境执行 Lean。** 本目录的脚本、检查文件和计划不是成功回执。只有实际运行生成的 `D3_RECEIPT.json`、编译日志、来源身份和人工语义核对才能支持 D3 结案。

## 1. 要解决的证据缺口

原 D3 缺的是锁定环境中的关键证明新执行，既不是 Lean/Mathlib 升级，也不是要求重新证明全部数学。本轮建议直接重编译 15 个固定源文件，随后重新 elaboration 44 个端点的完整类型并打印实际传递公理；其余未变依赖明确复用 E2。

主审已报告本次实际 Mac 的 Lean 4.33.1 / arm64 可以运行。计划仍自行核对：目标 HEAD `6dd6a3bc13e26f41eddc10ee4d2f39fa1c8ab3d4`，Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`，Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`。生产源与原审计 `cb17211653fde30aa50e0e9848798a6a5b3b3f12` 相同；源身份表保留这个历史来源，不把新 main 文档提交虚构成新的数学版本。

## 2. 新执行的准确范围

| 实际重编译模块（按执行顺序） | 不可由 `--version` 或旧 olean 读入替代的作用 |
|---|---|
| `UEOT.V3.PredictionDependent` | 可数协议、共同 a.e. 因子化与规范预测最小性 |
| `UEOT.V3.FiniteDiscountedControl` | 严格正折扣 Model、固定点和主控制定义 |
| `UEOT.V3.FiniteDiscountedGreedy` | 由实际因果控制类型得到全因果策略最优与达到 |
| `UEOT.V3.CoreOperationalAssembly` | Q 误差、动作间隔及泛型装配的实际假设和证明 |
| `…UnifiedClosure.CoreRegenerativeSource` | 原身体、程序、损伤、执行与后继均值的共同来源 |
| `…UnifiedClosure.CoreRegenerativeRepair` | 付费恢复及实际程序调用同一步修复的桥 |
| `…UnifiedClosure.CoreRegenerativeFormation` | 给定物理响应源中的形成候选与非空性 |
| `…UnifiedClosure.CoreRegenerativePopulation` | 实际后继、费用、亲本记录及有前提的新鲜身份 |
| `…UnifiedClosure.CoreRegenerativeControlPopulation` | 完整 Policy、实际人口、程序继承与表示运输 |
| `…UnifiedClosure.CoreRegenerativeGrowthClassification` | ProbabilityValid 扩大域、真实各行上界及取等 |
| `…UnifiedClosure.CoreRegenerativeGrowthPopulation` | 全允许策略统一增长界、达到与内部程序正分支 |
| `…UnifiedClosure.CoreRegenerativeGrowthAttainment` | 最小统一指数底数、两程序 iff 与失败区 |
| `…UnifiedClosure.CoreTheoryClosure` | 当前同源公共装配入口 |
| `docs.…core_growth_classification_v1.GrowthClassificationCheck` | 已存在的扩大域、临界和亚临界实际消费者；不新增数学 |
| `UEOT` | 当前公共入口对上述新产物的实际导入装配；直接编译该文件，不跑全库 `lake build` |

完整模块名、源路径、Git blob、44 个端点及其归属在 `D3_PLAN.json`。37 个查询端点属于实际新编译模块；其余 7 个是 Ω、共同二维、HJB、选择桥、GOA 和两个原生数值端点的重新类型/公理查询。后 7 个不得计为生产证明重新编译。两个 `native_decide` 的数值计算不在本轮重算范围；它们仍使用已披露原生求值信任。

该范围保留新执行与历史依赖复用的分界，覆盖此前主报告最重要的 K1/K2 数学链及其前提。没有理由为了 D3 将全部 1,051 个生产模块强制清缓存重建。公共 `UEOT.lean` 的直接编译提供导入证据，不意味着被导入的每个模块都重新编译。

## 3. 如何避免把旧缓存读入说成新证明

`run_d3_reproduction.py` 必须从固定项目的 `lake env python3` 启动。它继承已有依赖环境，但不执行 `lake build`、`lake update`、下载或工具链升级。

脚本在工作树之外创建新的 output 目录并依次执行 `lean -o … -i … 当前相对源路径`。每个目标的输出起初必须不存在，因此不会被 Lake 的 up-to-date 判断跳过。`LEAN_PATH` 首项为新 output 的 `overlay`，其余项来自固定 Lake 环境。后面的模块、公共入口和探针均能消费前面刚产生的 olean。

每个编译目标和最终探针还执行 `lean --deps`，保存该固定编译器报告的实际依赖路径、文件 SHA-256、可得的 Lake trace 哈希和新/旧来源标志。探针显式导入全部 15 个新目标；脚本要求 `--deps` 对这 15 个名称全部命中新 overlay，才接受“探针检查了新产物”。只运行 `import UEOT`、只打印版本、只观察 `.trace` 已存在，均不足以通过此判准。

源身份检查覆盖全部 1,051 个生产 Lean 文件及三个工具链/Lake 配置文件和现有边界消费者，共 1,055 个 blob。脚本核对当前 HEAD、项目 tracked 修改状态、各锁定依赖实际 Git revision 和 tracked 状态。执行后再次核对源字节。缓存复用不等于重新构造所有依赖；实际读取的缓存和已有 E2 证据应继续以各自身份报告。

## 4. 交给主审的四个执行文件

- `run_d3_reproduction.py`
- `D3Probe.lean`
- `D3_PLAN.json`
- `EXPECTED_SOURCE_BLOBS.json`

将四文件放在同一独立目录。下列命令中的路径由主审替换为其已核实的 Mac 路径；输出目录必须尚不存在，并且位于 Git 工作树外。

```bash
UEOT_D3_REPO="/absolute/path/to/isolated-current-UEOT"
UEOT_D3_BUNDLE="/absolute/path/to/d3-bundle"
UEOT_D3_OUTPUT="/absolute/path/outside-repo/d3-run-unique"
cd "$UEOT_D3_REPO/formalization/ueot-core"
/Users/murphyhoops/.elan/bin/lake env python3 "$UEOT_D3_BUNDLE/run_d3_reproduction.py" \
  --repo "$UEOT_D3_REPO" --output "$UEOT_D3_OUTPUT"
```

若主审又核实了更新的 main，而且证明源和锁文件仍与计划一致，可明确传入 `--expected-head 新SHA`；脚本仍不放松全部源 blob 检查。不要为了绕过真正的差异任意填写该参数。

脚本顺序执行，每 15 秒报告当前步骤；默认单步骤上限 900 秒，超时或错误停止并保存 `FAILED_OR_BLOCKED`。本限制不是定理否定：应先检查具体错误。只有明确缺失或不兼容的依赖才交主审定点处理，不自动全库重建，不自动改版本或生产源码。

## 5. 类型和公理不能省略什么

`D3Probe.lean` 用完整限定名和 `#check @…` 打印全部显式化参数，开启 universes/fullNames；另 `#print` 12 个结构或定义，避免只看到结构名而漏掉字段前提。44 个端点均紧接其 `#print axioms`，结果与源路径、模块、作用及 fresh/reused 模式一一对应。

主审实际回读日志时至少确认：

1. 预测最小性的 `[Countable I]`、逐协议核/共同 a.e. 因子前提；它不是现实身份唯一性。
2. `Model.discount_pos` 和 `discount_lt_one`；全因果策略最优声明使用实际可用信息和动作。
3. P-CORE 中 H/I/Y、X/M 和 Obj 的独立性；误差与间隙桥须有它们的真实假设。
4. `ValidIdentity` 出现在新生新鲜性前提；State 仅有 GoodPopulation，不能读取出全局 NoDup。
5. `ProgramPopulation θ`、可达继承和 `0 < branchWeight…`；外部 programPolicy 与内部执行有条件相接。
6. 新分类的 `ProbabilityValid` 没有偷加旧超临界/行动优势；全 Policy、非空初态及 `HasExpectedGrowth` / `UniformExpectedUpper` 的真实量词被保留。
7. 形成候选属于给定源；同源公共入口是条件装配，未从无组织材料推出任意身体。
8. 普通端点实际公理只在 `propext`、`Classical.choice`、`Quot.sound` 中；两个原生计算端点允许的额外项必须与其已披露精确名字一致。任何 `sorryAx`、未登记公理或误配端点均不通过。

脚本对 44 项实际公理输出逐一解析、检查允许集合；原生项要求精确后缀对应，不能以“名字里有 native 就都放行”。它不试图用字符串自动证明自然语言语义相符：上面的语义回读仍由主审和 B 对真实输出承担。

## 6. 接受与结案措辞

满足以下条件才足以结案原 D3 的关键证明新执行义务：

- 固定源、工具链、Mathlib 与依赖身份全部匹配；没有生产修改。
- 15 个直接源码编译均真实启动、退出码 0，并产生原先不存在的新 olean；保留命令、时间、日志和产物哈希。
- 探针编译退出码 0，确认从 overlay 解析全部新目标；44 项类型输出和公理记录齐全，无未披露依赖。
- 实际告警得到检查；语义回读确认上述关键前提与合同一致。

推荐结案表述为：**“D3 已完成固定版本的关键源码定点重编译、公共入口装配及指定端点类型/公理复核；未变依赖复用已有证据，未执行干净全库重建。”** 不能改写为“全部 Lean 已独立从零证明”“所有 Mathlib 依赖新内核复验”或“原生计算信任已取消”。

历史报告里当时“没有运行 Lean”的原文保留不变，新增本次实际证据和时间即可。即使 D3 完成，数学闭合与经验真实、哲学正确性和全球原创性仍分别评价。

## 7. 准备阶段已完成的验证

本准备阶段已从当前固定 main 精确读取 14 个必要源文件，Git blob 均与原审计源一致；另复用此前已核对的现行增长模块和回执。所有 44 个声明名称按实际源码核对，Python 脚本通过语法解析，探针 paired 命令数和 SHA 与计划一致。公理日志解析器在历史实际 Lean 4.33.1 的 59 项日志上成功解析。

上述只叫准备验证；尚未在本准备环境编译 `D3Probe.lean`、运行本脚本或执行任何生产 Lean 复现。实际结案必须依据 Mac 输出。
