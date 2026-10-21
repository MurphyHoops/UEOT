# Registered interfaces：实际原生与证据复用独审

## 结论

**CLEAR_ACTUAL_NATIVE_AND_PRIOR_SEMANTIC_REVIEW_BOUND。** 已读取 sequence 2 的实际四阶段执行、完整双原生输出及 finalizer 产物，并核对完整构建身份、历史补登及全部旧引用修复边。没有发现阻断问题，可以由根推进获授权消费者的应用与后续发布验证。

对应机器收据：`NATIVE_EVIDENCE_REVIEW_2.json`，SHA256 `919778dce84e198458e979513c7af2fcf8eef66bff12eba596886c6ade61af4e`。其中 67 条是本次只读证据一致性条件，不是新增 Lean 运行或测试套件。本审查没有执行 Lean/native、重跑结构/回归测试、再生协议、修改消费者或写 Git。

## 1. 实际身份与执行

实际 canonical 基线为 `86dfbec88c20a9da3c98cd222611aac55cc55f2f`，受审本地候选为 `7eeccd98c84f42a55f9bac1ff71e3204a18e4652`。此前已独审的 canonical 政策收据仍独立有效；此处不将原生证据当作授权来源。

`native-repair-sequence-2/STATUS.json` 已实际记录 `PASS_NATIVE_AND_PROVISIONAL_EVIDENCE`。`prepare_export`、`native_export`、`prepare_fixed`、`fixed_verifier` 四阶段均实际 exit 0，wrapper 的 native pipeline 及 observed finalizer 也均 exit 0；每份实际日志与状态所载 SHA 一致。

| 产物 | SHA256 |
|---|---|
| 完整 native JSON | `75945bbff2e0212a406f27859c68a777bc3deba75b0b8aece66c84236b5e39c1` |
| 实际 fixed certificate | `0d3eb26c9471e1701a28652f308c9dd1e1ccac72c0b9ef36eec27c1bc3165d32` |
| finalizer 临时 overlay | `6667bf7a908d713394e5daae5291c3a82f1ff7b3da144e2addf3da5959d0e781` |
| 未改的冻结工具 manifest | `c0c8593ab385220d9b6551aaa1df866b62706b798801634861a25af5fa4f22cf` |

两份 Lean 日志各自只有一个完整 `REGISTERED_INTERFACES_NATIVE_JSON` 对象。已比较全部字段，而非计数摘要：日志对象、`observed_first_native.json`、`observed_fixed_native.json`、observed/final 两份 canonical native 对象完全相同，fixed 与 canonical 文件字节也相同。实际比较收据与 pipeline 内 binding 一致。

## 2. 聚焦结果复用及完整构建

第 8 轮旧 full 状态保持 `RUNNING`，其原始日志和中断恢复记录没有被改成 PASS。第 9 轮进行了新的实际增量 `lake build UEOT`，exit 0，耗时 107.420741685 秒，日志明确以 `Build completed successfully (9372 jobs).` 结束。

第 9 轮 focused 项复用第 8 轮真实已完成的结果，没有重复执行。两份 focused 日志逐字节一致；状态中的原结果、原日志、原 manifest 和原状态摘要全部相符，且专门记录其复用来源。

第 8/9 轮完整 `build_identity` 对象完全相同。已只读重新核对当前全部 666 个生产源码的路径集合、逐文件 SHA 与完整 fingerprint；三份环境文件、实际 Lean/Lake 二进制摘要和九个依赖实际 HEAD/干净状态也吻合。完整源码 fingerprint 为 `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。

已阅读实际 resume 脚本：其在新构建前以第 8 轮完整身份为 expected 校验，成功执行后再以相同身份校验；只有真实 returncode 0 且后置校验完成才记录 PASS。旧 manifest 的历史基线 `65db…` 保留，新 manifest 和原生流程绑定真实 `86df…`，未改写旧执行历史。本地候选构建不是合入后 resulting-main 验证。

## 3. 实际原生范围

| 项目 | 实际值 |
|---|---:|
| 七模块新公开声明 | 52 |
| 已有遗漏公开声明补登 | 1 |
| 待注册节点总数 | 53 |
| 历史已注册比较目录 | 4094 |
| 跨目录实际 isDefEq 比较 | 216982 |
| 新源 × 旧目录 | 212888 |
| 历史补登 × 旧目录 | 4094 |
| 候选内部实际比较 | 1378 |
| 52 个新源内部 | 1326 |
| 新源 × 历史补登 | 52 |
| 实际类型碰撞 | 0 |
| 完整物理模块范围 | 7 新模块 + 1 旧模块 |
| 原生 theorem constants | 92 |
| 私有 theorem constants | 17 |
| 其余 public native constants | 22 |

完整 92 行均保留类型、宇宙参数、物理归属、直接常量、直接 theorem 常量及传递公理闭包；全部闭包是 `propext`、`Classical.choice`、`Quot.sound` 的子集。其余 22 个 public 常量不全部称为生成项，其中包括既有注册声明。53 个新注册节点也不称为 53 个新数学证明。

## 4. 真实历史补登及旧边

历史补登是精确名称 `UEOT.V3.FreeInformationValue.integrable_finset_sup'`，尾部 ASCII 撇号完整保留。该声明由真实 native 确认是旧模块中的公开 theorem；旧源 SHA 仍为 `e4375851def0e735d54c7d3f56ba48517040e064073fdc1283a006f1d33c1a87`。

实际旧证明 `proof.value` 窄扫描覆盖 4094 个已注册节点，全部正命中调用者恰为 `UEOT.V3.FreeInformationValue.p_ref_03`。这是读取本轮实际结果得到的集合，并非预设只有一条。该节点 prior 边表为空，实际新增唯一目标为上面的完整 helper 名称；`actual = prior ∪ delta`，与完整 census 中同一调用者的真实直接常量一致。路径、行号、归属和旧源摘要也吻合。

53 个待注册节点共有 **97 条 outgoing 注册直接证明边**；旧节点新增 **1 条修复边**，两类分别计数。精确历史 CSV 和 `fkrg.py` 与 canonical 基线字节相同。旧 parser 尾部词边界缺陷未修，不以本轮精确补登谎称旧 parser 已修复。原 4094 注册目录也没有被机械改称 4095。

## 5. 既有语义审查增量绑定

finalizer 重新得到的词法提示与已有独审精确相同：18 组、39 对名称组合；原 25 个受审生产文件的 SHA 全部保持，相关新声明都在实际原生公共范围内。因此原审查的语义结论可直接复用，并由本收据绑定实际零类型碰撞结果，无需再次逐组重审。

原语义收据的 `SEMANTIC_CLEAR_NATIVE_PENDING` 和 finalizer 的 `PENDING_TYPED_REUSE_REVIEW` 作为历史输出保留。此处是完成实际绑定的新独立收据，不覆盖旧 PENDING。首轮导出尚待 fixed 时的 `FIRST_NATIVE_OBSERVATION_2.json` 也保留原状态。

## 6. 后续门槛

finalizer 只提升了五个实际证据子项：类型区分、公开证明依赖、完整公理 census、历史公开补登和既有依赖修复。消费者注册仍由根实施并另行检查；当前收据不宣称 live graph 已更新至 4147。

完整 `knowledge/test_fkrg.py` 的真实 fast-audit、最终 immutable Git-object preflight、PR 检查与合入后 resulting-main 验证仍按根的发布流程完成。既有 parser/政策门槛有各自实际收据，不由本原生审查替代。这里没有计数型 FINAL push-event 收据，也不把数学条件命题扩成经验世界、意识、伦理或完整自然理论的证明。
