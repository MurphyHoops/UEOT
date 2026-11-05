# 验证范围与保留的失败

## Lean 与公共入口

13个新增模块和实际 driver 均在原 Mac Lean4.33.1 / Mathlib固定依赖下编译成功。最终文件对应的成功批次：Refinement/Observer批02，ObserverSource/CountPosterior批03，CountHistory/Model/Witnesses批05，DAG批06，Generator批07，Bounds/Native批08，Payment批09，Entry/Driver批10。完整命令、源SHA、退出码及警告保留在 `checks/COMPILE_BATCH_*.json` 与逐文件log。

`TheoryCompletion.lean` 增加主入口import；既有TheoryCompletion、Compression、V3、UEOT公共根均实际编译。最终 `checks/PUBLIC_CONSUMER.lean` 通过现有正确的TheoryCompletion入口检查18个主要端点；`AXIOM_AUDIT.json` 确认仅标准背景公理，一项合并端点无公理。没有sorry、新占位公理或以结论作为来源输入的循环字段。

初轮证明中的类型/证明脚本失败及其源快照原样保留在 `attempts/` 和各批日志；它们不是成功结果。第一版公共消费者误以为UEOT.V3包含TheoryCompletion，报未知命名空间；修为实际既有TheoryCompletion公共根后通过，失败文件及log保留。所有调整未改变被冻结的源、输入、J或权限。

## 非作者审查与实际运行

`independent/` 保存源观察/后验、模型精化、DAG/边界、原生/付款、实际driver与独立checker的非作者语义审查，均绑定最终源SHA。八个额外边界由求解器作者进行针对性产物复核，报告明确作者身份，不冒称独立非作者。

`actual-execution/` 是13个真实Lean返回结果及分段/进程日志。`reference-execution/` 是已存在memo化PR441算法的5个同源参考结果。`independent-execution/` 逐行核查THIS实际DAG的全部原菜单合法替代动作、所有正后继、精确Q与tie次序；随后使用原完整Store执行该产物。四旧例共800条完整mode/label/θ路径；八步仅32条冻结区别路径加2条Lean直接图执行，不能将这些有限路径当作全局最优性的证明。

13实例均首次执行成功，未超预登记300秒求解/600秒消费者预算。旧四步长求表没有重复。边界包括H0、B0、B<c、r0/r1、零先验、重复率、goal=false；不等同于对所有公开输入的运行性保证。保存一次故意删除未选动作正边的拒绝记录，原成功产物字节未改。

## 两书

现有构建脚本未改。首次philosophy字体文件查找失败保留；改为只对本次命令设置缓存字体搜索路径并传已有TeX2023目录，未改全局配置。两书重新构建，无overfull警告。初版选页审查发现正文需显式限定相容历史、检查器接受范围、计时口径，并发现两处小分页；这些文字/版面已修，Lean源定理原已保留对应前提。首轮报告和修订理由保留，最终报告绑定最终MD/PDF与实际阅页。

## 不同证据的含义

本地Lean与独立有理检查是实际执行结果；云端只有仓库现行启用的检查会运行，禁用Core工作流没有被启用。公共源码可以证明被接受控制器的一般性质，实际返回字节另由哈希和独立检查绑定；没有JSON往返Lean定理。经验支持仍UNVERIFIED，外部电脑成本没有被新增进原对象钱包。

## PR442 自动审查后的复现入口修复

自动审查准确指出负向probe仍引用临时工作区目录；同类检查发现旧表comparison也存在该打包问题。两脚本现默认使用实际packet与同级旧packet，要求新输出路径；原核心断言、DAG变异与比较逻辑保持。旧脚本及原报告保留，未重抽或替换产物。Mac从 `/tmp` 用默认输入各执行一次，负向遗漏边被拒绝，四旧表26条正历史比较通过，耗时约0.217s与0.032s。源码/证明/两书及原成功运行字节不变，独立记录见REPRODUCTION_PATH_CHANGE_REVIEW与REPRODUCTION_PATH_VALIDATION。
