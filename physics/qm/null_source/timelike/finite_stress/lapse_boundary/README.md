# Lapse、真实源张量噪声、因果响应与正常准备

从 eae6769b97393b310054c21b804d7ed03a1371dc 接续同一分支/PR #468。
核心物理统一目标、完整几何—物质—装置闭环仍未实现。

本轮先完成有限截止lapse/端点分类，再计算已匹配实际非静态历史上的完整绝对source tensor噪声、
实际齐次retarded RSET导数、初始source荷混合块与六个Killing momentum荷。
短窗预算发现source pressure RMS/mean>400。
复盘后另一次选参并构造平滑器，得到新的齐次source弱噪声窗口，同时证明真实mean族仍有极强快方向敏感性。
允许改变裸态的21级正常记录也已构造，其source观测保持和有限资源已明确。
这些都是模型内逐项结果，不是统一物理或真实引力仪器的验收。

| 研究对象 | 主要结果 | 证明与可复现证书 |
|---|---|---|
| lapse、端点、初始密度与接触 | 完整有限截止恒等式；纯canonical混合不产生新载体荷 | [ACTION_BOUNDARY](ACTION_BOUNDARY.md), [JSON](action_boundary.json) |
| 无限模端点定义域 | Q方差线性增长；单独sharp shear无旧Fock强极限 | [ENDPOINT_DOMAIN](ENDPOINT_DOMAIN.md), [JSON](endpoint_domain.json) |
| 实际完整绝对source tensor N | 同向Hadamard乘积+全部有限非Gaussian累积量；明确平滑域 | [TENSOR_NOISE](TENSOR_NOISE.md), [JSON](tensor_noise.json) |
| 当前固定短窗预算 | 严格非零密度差；pressure绝对RMS/mean>400；差/基线<3e−27 | [DYNAMIC_WITNESS](DYNAMIC_WITNESS.md), [JSON](dynamic_witness.json) |
| 源侧CTP及约束块 | lapse/scale顶点、量子Gram、初始C混合列、六个Killing荷 | [SOURCE_CTP](SOURCE_CTP.md), [JSON](source_ctp.json) |
| 正常平滑有限记录 | sure误差B/20；Dtr>0.8；声明连续类最少21级；有限共轭资源 | [SMOOTH_PREPARATION](SMOOTH_PREPARATION.md), [JSON](smooth_preparation.json) |
| 源观测验收 | 原观测商原则在本薄层21级正常记录和实际历史上的应用 | [OPERATIONAL_STATE](OPERATIONAL_STATE.md), [JSON](operational_state.json) |
| 实际因果齐次RSET响应 | 固定incoming、全部AE接触、参数导数统一全场收敛 | [RETARDED_RESPONSE](RETARDED_RESPONSE.md), [JSON](retarded_response.json) |
| 新一次选参窗口 | 同一新history上density<1e−12、pressure<1e−5相对RMS；mean快方向log增益>18709 | [QUIET_WINDOW](QUIET_WINDOW.md), [JSON](quiet_window.json) |

所有RMS比值都有指定测试、同一实际态/几何和模型单位；不是度规误差、SI时间或实验灵敏度。
源二阶核也不是完整Gaussian几何过程；高阶累积量、初始joint state和真实装置仍承担各自责任。

## 入口与复现

[验收合同](CONTRACT.md) · [下一任务](INPUTS_AND_NEXT_TEST.md) · [进度与反思](SESSION.md) ·
[审计](AUDIT.md) · [证据来源](SOURCES.md) · [自动验证回执](verification.json)

用Python3.14及固定numpy2.5.4/scipy1.18.1/sympy1.14.0/mpmath1.3.0执行：

~~~sh
python -B physics/qm/null_source/timelike/finite_stress/lapse_boundary/run_verification.py
~~~

新入口复用旧163项，冻结600个前驱科学文件，只执行本目录新检查。
自动证书、解析证明、原生代理审读和GitHub CI各自记录，不相互替代。
Core只读，GI排除，PR保留草稿且不合并。
