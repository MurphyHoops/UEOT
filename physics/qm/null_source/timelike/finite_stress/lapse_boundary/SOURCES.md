# 证据与去重来源

## 冻结项目输入

基线eae6769b97393b310054c21b804d7ed03a1371dc。
原finite_stress的GEOMETRY_MATCHING、FINITE_SLICE_UV、DYNAMIC_CHARGE、
BOUNDARY_STATE、BOUNDARY_EXTENSION、TOTAL_BOUNDARY_GATE及ORIGINAL_CTP_GATE为直接输入。
nonlinear_history/KERNELS、EXISTENCE提供完整AE处方、同态mean族、固定根和正则性。
旧JSON只读，不import/execute旧科学代码。

constraint_states/RELATIONAL §5已有stress/influence观测商原则；
QUANTUM_FLOOR §1和TOTAL_BOUNDARY_GATE §4已有连续谱强additive约束的正常态阻断及完整谱证明；
total_source/PRESSURE_NOISE已有一般矩阵元差式与static pure-pressure结论。
本轮新增是实际非静态thin态的完整absolute N与各分量、
齐次retarded参数导数、具体有限平滑记录及实际窗口预算，不重复计数这些原则。

## 外部一手方法文献

- Brunetti–Fredenhagen–Köhler，microlocal spectrum/Wick polynomials：
  https://arxiv.org/abs/gr-qc/9510056 。用于同向Hadamard分布乘积的域依据。
- Hollands–Wald，stress/action Ward：
  https://arxiv.org/abs/gr-qc/0404074 。不把smooth noise Ward当作retarded contact证明。
- Anderson–Eaker，原固定AE处方：
  https://arxiv.org/abs/gr-qc/9906055 。本轮具体表达沿冻结KERNELS逐项保留。
- Fewster–Verch，local measurements，特别是Theorem3.3：
  https://arxiv.org/abs/1810.06512 。用于精确全局谱effect的局域性门槛，不声称它已建成引力仪器。
- Anderson–Molina-París–Mottola，linear response criterion：
  https://arxiv.org/abs/gr-qc/0209075 。区分mean方程成立、因果响应及扰动控制。
- Hu–Roura–Verdaguer，semiclassical validity and fluctuations：
  https://arxiv.org/abs/gr-qc/0402029 。未把两场非Gaussian源直接当成large-N Gaussian极限。
- Vassilevich，heat kernel coefficient与Lorentzian局部counterterms：
  https://arxiv.org/abs/hep-th/0306138 。若引入新F(χ)耦合，必须另声明新增局部参数，不能借旧free AE处方自动固定。

- Moretti，守恒point-splitting与四维η=1/3：
  https://arxiv.org/pdf/gr-qc/0109048 。用于COVARIANT_RESPONSE的接触账本，尚不替代固定AE转换。

文献用于明确方法与适用范围；本模型新增公式、数字及限制以本目录证明/证书为准。
原生代理的审读不冒充文献作者确认、外部人类同行评议或形式化证明。

## 后续定义域核验的一手资料

Bruneau–Dereziński, Bogoliubov Hamiltonians and one-parameter groups of Bogoliubov transformations, https://arxiv.org/abs/math-ph/0511069 ：Hilbert–Schmidt implementability与二次Hamiltonian自伴域的外部参考；本轮Hi的具体ω阶数另由原incoming解算出。
Hu–Roura–Verdaguer, https://arxiv.org/abs/gr-qc/0402029 ，Appendix D：有限初时、不相关初态和noise distribution的边界问题；该Minkowski/large-N讨论不能替代当前闭S3最小耦合的准备构造。root已实际打开PDF相应段落。

Junker–Schrohe, Adiabatic Vacuum States on General Spacetime Manifolds, https://arxiv.org/abs/math-ph/0109010 ，用于区分有限adiabatic regularity与Hadamard的背景参考。本轮具体H^(3/2)/log阻断由已写模式展开独立导出；不套用未核模型条件。
