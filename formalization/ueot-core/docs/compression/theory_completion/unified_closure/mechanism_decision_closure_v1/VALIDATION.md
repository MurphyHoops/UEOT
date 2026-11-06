# 运行证据与复现
冻结输入、上述 16 个新 Lean 模块及唯一新增公共 import 使用 PR442 的实际 main，未回退。每个模块最终 SHA 对应的成功日志位于 `checks/<module>-<sha前12位>.json` 及同名 .log。四层既有公共根另见 [PUBLIC_BUILD.json](checks/PUBLIC_BUILD.json)；只 import TheoryCompletion 的消费者核查 34 个证明端点。没有新增手写公理或占位。Lean 4.33.1 的 #print axioms 对两个闭合有限求值分别打印 `exact_cached_data._native.native_decide.ax_1_1`、`exact_two_data._native.native_decide.ax_1_1`；源注释出现的旧称 Lean.ofReduceBool 不是本版本实际打印的公理名。其余背景见 [AXIOM_AUDIT.json](checks/AXIOM_AUDIT.json)。对数值归约的信任与独立 Fraction 重算分别记录。

## 两个不同的实际执行

[冻结返回](actual-execution/THIS_POLICY.json)，SHA-256 `e679b9cb68b32e045482a88962fc880206eb956a3bbf875ed91c406d530a8c03`，由旧完整求解器已证明相等的缓存入口产生；两张各 21 决策行的控制表及同表 packed 运行在同一输出内。整个新 H3 入口 819.619 秒，非基准比较，未重跑旧长入口。[完整 Store 原生账本](actual-execution/NATIVE_RUN.json) 与[独立核对](actual-execution/THIS_EXACT_CHECK.json)绑定该 SHA；512 条运行和 1536 个非空付款前缀全部通过，最低余额 0。每个固定机制下每项带种子路径质量为 1/256。独立精确递归覆盖全部允许备选动作。错误私随机质量、漏损未派发个体与零钱包写请求均被拒绝。

[固定分辨协议](actual-execution/SHARP_PACKED.json)另以正好一笔预付款 B=c=1 运行：[实际核对](actual-execution/SHARP_NATIVE_CHECK.json)逐一比较 128 条 mode/label 路径、384 个前缀，每机制每原子质量 1/64。S 的 8 条给出 11/00/10，G 没有；各机制首次写收费 0、1 各 32 条。实际 TV=1/8，错误=7/16。完整人口样本保留在报告中；它不是四点决策策略的运行。H3 末端证据不被用作同 H3 的后续学习收益。

## 从仓库复现

在仓库运行下列命令，使用项目固定 Lean/Mathlib 环境。输出目录由调用者选择，不覆盖发布原样本：

```sh
cd formalization/ueot-core
pkg=docs/compression/theory_completion/unified_closure/mechanism_decision_closure_v1
out=$(mktemp -d)
lake build UEOT.V3.Compression.TheoryCompletion
lake env lean "$pkg/checks/PUBLIC_CONSUMER.lean"
lake env lean --run "$pkg/native_protocol/RETURN_MECHANISM_POLICY.lean" > "$out/THIS_POLICY.json"
python3 "$pkg/native_protocol/run_mechanism_native.py" --policy "$out/THIS_POLICY.json" --output "$out/NATIVE_RUN.json"
python3 "$pkg/native_protocol/verify_mechanism_output.py" --policy "$out/THIS_POLICY.json" --native "$out/NATIVE_RUN.json" --output "$out/CHECK.json"
lake env lean --run "$pkg/native_protocol/RUN_MECHANISM_EXPERIMENT.lean" > "$out/SHARP_PACKED.json"
python3 "$pkg/native_protocol/verify_sharp_experiment.py" --packed "$out/SHARP_PACKED.json" --adapter "$pkg/native_protocol/run_mechanism_native.py" --original-native "$pkg/../joint_decision_closure_v1/native_protocol/exact_reference.py" --output "$out/SHARP_CHECK.json"
```

源绑定和 [Core 身份清单](checks/CORE_SOURCE_IDENTITY.json)用于发行核对，不称为整个 Core 重编译。直接内核展开未完成、早期 Lean 脚本报错、PDF 构建时的格式/字体查找失败均保留在 `attempts/` 和 `checks/`。两书使用未改变的构建脚本和本任务临时字体搜索路径；数学 225 页、哲学 90 页、均无 overfull；[最终选页报告](../../../../../../../mathematics/review/MECHANISM_DECISION_BOOKS_2026-11-06/ROOT_FINAL_VISUAL_REVIEW.json)。没有启用旧禁用工作流、增加权限、改变费率、重抽样或设置性能门。
