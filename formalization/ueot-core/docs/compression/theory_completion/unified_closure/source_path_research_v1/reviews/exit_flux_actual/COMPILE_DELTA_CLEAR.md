# 首次退出通量：实际编译增量独立审查

结论：**COMPILE_DELTA_CLEAR_PRIVATE_FOCUSED_PASS_NOT_INTEGRATED**。

复用 books_resume 对原稿的独立数学静态审查，仅审查 math_resume 的实际编译修复、执行证据与来源身份。原稿作者是 audit_resume，原独立数学审查者是 books_resume，本次修复作者是 math_resume，本收据由 audit_resume 核对其增量。旧 REVIEW、原合同、原始 manifest 和失败日志全部保留；没有运行 Lean、build、native、测试或 Git，也没有改动作者或生产文件。

## 实际执行证据

第三轮实际 exit 为 **0**，耗时 **7.091 秒**，没有超时。最终源码与该轮快照逐字一致，状态记录的执行前后源码 SHA 相等，实际日志及 `.olean` 的 SHA 均与作者通过包一致。

| 对象 | SHA256 |
|---|---|
| 最终源码 | `4ae9df91e5808f7294bb3c141bfe2e038f252adb2267e7e36380e0ba9b1aac18` |
| 保留的原稿 | `8f88617f06f793492b04b875d38dbc097b7043bbe9ef12567b8492cb1eaf3c8c` |
| attempt003 状态 | `4919776a00308bb4edfb3035d1b3478fa1a9473cc90f9bac282fa54e87d444e6` |
| attempt003 日志 | `dd5f21163a01a920bf459e257b40185bc5b5c14451fa1cc086cc6bafb2a7badd` |
| 实际 `.olean` | `edcea2cf0b4bedb70c93c39ab809e1c9b70c35690053cefff1b64b8a8d672cdd` |
| 作者 COMPILE_PASS.json | `e7361dbfc994e9302a6b3ef2f84f8697afbeda71a267c70ea10886672bf64707` |

实际成功日志中的 **10 个指定端点传递公理闭包**逐项匹配作者汇总，且均只含 `propext`、`Classical.choice`、`Quot.sound`。成功日志没有 error 或 sorryAx。这是十个实际打印闭包，不是全模块原生声明枚举。

前两轮分别真实 FAIL，exit 1，耗时 6.434 秒与 7.745 秒，原始失败源码、状态和日志均仍存在。其错误恢复输出中的 sorryAx 没有被算作通过证据。第三轮正式启动前的一次 exec-server 传输中断另有 `LAUNCH_INTERRUPTION.json`；它没有创建一次 Lean attempt，不虚构 Lean 返回码，也不计作第四轮。

## 声明与证明修复

独立重新计算了原稿到最终版、实际 attempt001 到 attempt003 的两个完整 diff，均与冻结 patch 字节一致。对真实源文本做完整声明边界提取，确认 **13 个定理与 2 个定义，全部 15 个公开声明头逐字相同**；两个定义 `killedExitFlux` 与 `riskFirstExitAfter` 的完整正文也逐字相同。首轮实际编译输入到最终版的完整声明头同样一致。原稿没有成功 kernel 类型导出，本结论明确属于源码级比较。

作者 `DECLARATION_COMPARISON.json` 中有三条头在命名参数 `(A := A)` 内提前截断：`actual_first_exit_mass_eq_survival_drop`、`actual_first_exit_mass_eq_killedExitFlux`、`actual_failure_eq_initial_failure_add_first_exits`。该历史文件只能单独支撑这三个头的前缀比较，不能单独充当完整头比较。此处已按真实声明赋值边界补齐，完整原/最终头及 SHA 写入新的 `COMPILE_DELTA_EVIDENCE.json`。作者冻结文件保持原样，结论由这份补充证据支撑。

实际数学证明的改动限于：

- 生存质量局部记号改为显式 `Measure.real (PMF.toMeasure ...) (Set.ofPred ...)`，表示同一个实际事件与概率质量；量词、分母和来源均没有改变。
- 先 `dsimp only` 展开局部记号 lambda，再把同一个 M、q、sigma、p0、K 和 n 显式传给 K1 总质量身份；`convert ... <;> congr!` 处理相同矩阵幂表达式的 DecidableEq 实例差异，没有新增数学假设或透明度选项。
- 局部证明变量 `prefix` 改为 `safePrefix`，避免 Lean 语法关键字冲突；`Set.mem_ofPred_eq` 取代旧集合成员化简名称。真实前缀证明和不交事件分割保持原结构。
- 添加十条实际 `#print axioms`，更新源码说明其私有地位。三组无用 section-variable 警告如实保留。

## 已审数学范围保持

令同一实际动作/状态路径律为 νₙ，Sₙ 表示从时刻 0 到 n 从未离开 K，sₙ=νₙ(Sₙ)，η₀ 是原 p0 在 K 上的未归一化限制，ηₙ=η₀Qⁿ。以下等式仍针对同一实际 M、q、平稳当前观察策略 sigma 与任意原始 p0：

\[
\nu_{n+1}(\text{前缀始终安全且第 }n+1\text{ 步首次退出})
=s_n-s_{n+1}
=\sum_{u\in K}\eta_n(u)\left(1-\sum_{v\in K}Q_{uv}\right).
\]

前缀身份仍由实际 `pmfExtend` 的 bind/map 构造及 `causalLaw` 递归推出。它没有变成输入假设；一般前缀引理允许历史依赖核，固定矩阵 Q 的结论仍保留 K1 的平稳当前观察策略范围，没有自动识别任何别的完整因果策略。

最终实际失败分解保留初始失败：

\[
\nu_T(\text{截至 }T\text{ 曾失败})
=1-s_T
=p_0(K^c)+\sum_{n<T}\nu_{n+1}(\text{上述首次退出事件}).
\]

n=0、T=0、空 K、p0(K)<1 与后续零存活均未排除；没有正存活或 QSD 前提，也没有初态条件化。已退出后返回的路径不重新计作首次退出。没有无限路径、无限存活、QSD 存在或完整 Doob 条件路径结论。

## 输入身份与复用限度

独立核对作者通过包及相关收据的 40 个不同文件引用，原 manifest 的 11 项输入与 SourcePolicyPathBridge/K1 的源码和 olean 共四个私有钉住身份均匹配。旧静态审查、原合同和原 manifest 的原字节保持不变。

本次只读检查还核对完整生产 666 个源码的路径集合、逐文件 SHA/大小、三个环境文件与 Lean/Lake 程序 SHA，均匹配已完成构建第 9 轮的输入身份，source-tree 为 `29d2c7d10b332e0b6c39f5072a2e7af8e6609d1ba7e2c638200cebccdc8bc1f1`。九个依赖及导入环境复用那份已审构建收据，没有新运行 Git、版本命令、构建或导出。

因此原独立数学静态审查可以绑定到此次真实通过实现。当前成果仍是**私有有限窗桥**；本收据不宣称已纳入生产入口、FKRG 注册、生产原生枚举或 canonical resulting-main 验收，不扩大已发布七模块范围。
