# Lapse、真实源张量噪声、因果响应与正常准备

从 eae6769b97393b310054c21b804d7ed03a1371dc 接续同一分支/PR #468。
核心物理统一目标、完整几何—物质—装置闭环仍未实现。

最新闭环：原lapse作用量强制的混合初始列已推出；实际全场齐次逆、双约束弱解和具体读数成本已完成。该弱解的指定读数失控；继续构造正常相关门后，又发现全场门的Hadamard失败，并给出有限模式正常Hadamard近似修正。进一步构造incoming能量门后，原source应力functional可精确保留，但其pointer与真实两对几何canonical变量尚未识别；把单独端点shear用于第二对的具体normal极限又被拒收。下一门是共同action/态/端点下的真实canonical embedding与总源。

本轮先完成有限截止lapse/端点分类，再计算已匹配实际非静态历史上的完整绝对source tensor噪声、
实际齐次retarded RSET导数、初始source荷混合块与六个Killing momentum荷。
短窗预算发现source centered pressure RMS/|mean|>400。
复盘后另一次选参并构造平滑器，得到新的齐次source弱噪声窗口，同时证明真实mean族仍有极强快方向敏感性。
允许改变裸态的21级正常记录也已构造，其source观测保持和有限资源已明确。
这些都是模型内逐项结果，不是统一物理或真实引力仪器的验收。

| 研究对象 | 主要结果 | 证明与可复现证书 |
|---|---|---|
| lapse、端点、初始密度与接触 | 完整有限截止恒等式；纯canonical混合不产生新载体荷 | [ACTION_BOUNDARY](ACTION_BOUNDARY.md), [JSON](action_boundary.json) |
| 无限模端点定义域 | Q方差线性增长；单独sharp shear无旧Fock强极限 | [ENDPOINT_DOMAIN](ENDPOINT_DOMAIN.md), [JSON](endpoint_domain.json) |
| 实际完整绝对source tensor N | 同向Hadamard乘积+全部有限非Gaussian累积量；明确平滑域 | [TENSOR_NOISE](TENSOR_NOISE.md), [JSON](tensor_noise.json) |
| 当前固定短窗预算 | 严格非零密度差；pressure绝对centered RMS/|mean|>400；差/基线<3e−27 | [DYNAMIC_WITNESS](DYNAMIC_WITNESS.md), [JSON](dynamic_witness.json) |
| 源侧CTP及约束块 | lapse/scale顶点、量子Gram、初始C混合列、六个Killing荷 | [SOURCE_CTP](SOURCE_CTP.md), [JSON](source_ctp.json) |
| 正常平滑有限记录 | sure误差B/20；Dtr>0.8；声明连续类最少21级；有限共轭资源 | [SMOOTH_PREPARATION](SMOOTH_PREPARATION.md), [JSON](smooth_preparation.json) |
| 源观测验收 | 原观测商原则在本薄层21级正常记录和实际历史上的应用 | [OPERATIONAL_STATE](OPERATIONAL_STATE.md), [JSON](operational_state.json) |
| 实际因果齐次RSET响应 | 固定incoming、全部AE接触、参数导数统一全场收敛 | [RETARDED_RESPONSE](RETARDED_RESPONSE.md), [JSON](retarded_response.json) |
| 新一次选参窗口 | 同一新history上density<1e−12、pressure<1e−5相对RMS；mean快方向log增益>18709 | [QUIET_WINDOW](QUIET_WINDOW.md), [JSON](quiet_window.json) |
| 静态因果逆与全过去源域 | weighted H4工具；实际平稳压力对完整逆的无限过去GNS卷积发散 | [CAUSAL_DOMAINS](CAUSAL_DOMAINS.md), [JSON](causal_domain.json) |
| 有限模式实际因果逆 | 精确Peano–Baker构造；保留initial运输和有限K背景缺陷 | [FINITE_CAUSAL](FINITE_CAUSAL.md), [JSON](finite_causal.json) |
| 实际初片源定义域 | 尖起始K³/K系数；同源Q/D边界块与bulk共同L²极限 | [FINITE_SOURCE_DOMAIN](FINITE_SOURCE_DOMAIN.md), [JSON](finite_source_domain.json) |
| 原作用量响应重写 | 固定AE trace/Q核、完整局部项与共同主部 | [ACTION_RESPONSE](ACTION_RESPONSE.md), [JSON](action_response.json) |
| 协变source响应接口 | 固定测度因果两腿、规范检验、全部类型接触及lapse映射；AE全tensor匹配未完成 | [COVARIANT_RESPONSE](COVARIANT_RESPONSE.md), [JSON](covariant_response.json) |
| 实际全场因果逆 | 同一 quiet U 的相对算子界与因果/advanced逆；q_inv<e−1100 | [ACTUAL_INVERSE](ACTUAL_INVERSE.md), [JSON](actual_inverse.json) |
| 同源准备读数 | 实际固有时测试、H³伴随域、全场L²及完整zero–shell混合 | [PREPARED_READOUT](PREPARED_READOUT.md), [JSON](prepared_readout.json) |
| 密度残差与carrier下界 | 原fullmode R留下非零H_i荷；明确有限低模自由 | [CONSTRAINT_RESIDUAL](CONSTRAINT_RESIDUAL.md), [JSON](constraint_residual.json) |
| 完整齐次lapse action代表 | 同AE两行、边界势和canonical约束；初始动量–源相关来源 | [ACTION_LIFT](ACTION_LIFT.md), [JSON](action_lift.json) |
| 真正含源初始修复 | 同源GNS transpose解同时满足pressure/density；尚非正常geometry物理解 | [MIXED_BOUNDARY](MIXED_BOUNDARY.md), [JSON](mixed_boundary.json) |
| 明确读数拒收 | 固定c下修复读数RMS>e19000；完整cross和误差保留 | [READOUT_WITNESS](READOUT_WITNESS.md), [JSON](readout_witness.json) |
| 正常canonical对照 | 自伴H_i、正常近似联合态、CP仪器与完整资源；源态改变 | [CANONICAL_PREPARATION](CANONICAL_PREPARATION.md), [JSON](canonical_preparation.json) |
| 准备态UV再验收 | 全场Gaussian门同AE密度log发散；有限模正常Hadamard修正及tail界 | [HADAMARD_GATE](HADAMARD_GATE.md), [JSON](hadamard_gate.json) |
| 准备后mean入口 | 同门全部二/四矩、zero mean严格增加、完整新mean方程；拒收只调几何初导 | [PREPARED_MEAN](PREPARED_MEAN.md), [JSON](prepared_mean.json) |
| 同应力 incoming 准备 | 正常Hadamard、原source functional保持；实际Hi约束RMS受控，裸态Dtr>0.999和巨大P资源 | [INCOMING_PREPARATION](INCOMING_PREPARATION.md), [JSON](incoming_preparation.json) |
| 第二几何对端点门 | 固定normal geometry input的active shear纯度趋0，无normal trace极限 | [QUANTUM_ENDPOINT](QUANTUM_ENDPOINT.md), [JSON](quantum_endpoint.json) |

所有RMS比值都有指定测试、同一实际态/几何和模型单位；不是度规误差、SI时间或实验灵敏度。
源二阶核也不是完整Gaussian几何过程；高阶累积量、初始joint state和真实装置仍承担各自责任。

## 入口与复现

[验收合同](CONTRACT.md) · [下一任务](INPUTS_AND_NEXT_TEST.md) · [进度与反思](SESSION.md) ·
[审计](AUDIT.md) · [证据来源](SOURCES.md) · [自动验证回执](verification.json)

用Python3.14及固定numpy2.5.4/scipy1.18.1/sympy1.14.0/mpmath1.3.0执行：

~~~sh
python -B physics/qm/null_source/timelike/finite_stress/lapse_boundary/run_verification.py
~~~

本检查点执行25个科学证书入口及1个范围检查；数目不等于新定理数。
新入口复用旧163项，冻结600个前驱科学文件，只执行本目录新检查。
自动证书、解析证明、原生代理审读和GitHub CI各自记录，不相互替代。
Core只读，GI排除，PR保留草稿且不合并。
