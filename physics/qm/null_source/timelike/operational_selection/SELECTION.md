# 完整参考时标下的选解：分类、反例与新增物理责任

## 1. 冻结的共同历史

承接 577d0ba1 的 [精确存在定理](../nonlinear_history/EXISTENCE.md)。
同一个实际 incoming Q/P 联合态、参考时标 t=eta_ref、完整源谱、两场、M2/U0 与 AE 处方不变。
几何为 u(eta)=U(z,w)，z=epsilon exp(s eta)，w=delta exp(sigma eta)，
U=z+w+v；两幅度只选择一次。s、sigma 是冻结完整响应的两条正实根。

本页研究的是给这一精确解族增加什么选择规则，而不是重新证明平均方程。
单条历史在时间上解析和 Hadamard，并不自动使“制备参数到解”的选择映射在参数原点解析。

## 2. 加上几何自治性后，可以严格分类

假设另行要求只依赖 epsilon 的几何图 delta=f(epsilon) 满足
\[
f(e^{sc}\epsilon)=e^{\sigma c}f(\epsilon).
\]
每个符号分支的缩放轨道连通，故 f(epsilon)/|epsilon|^q 必须恒定：
\[
f(\epsilon)=C_\pm|\epsilon|^q,\qquad q=\sigma/s.
\]
原点的协变性要求 f(0)=0。冻结证书给
\[
q\in(468087.119,468087.342),\quad N=468087,\quad\alpha=q-N\in(.119,.342).
\]
非零分支第 j≤N 阶导数趋于零，第 N 阶导数具有恰好 alpha 阶 Hölder 正则性；
第 N+1 阶在至少一侧按 |epsilon|^(alpha−1) 发散。
因此非零图属于 C^(N,alpha)，不属于 C^(N+1)，也不属于任何 C^(N,beta)、beta>alpha。

所以“几何自治图 + 原点 C^(N+1)”或“几何自治图 + 原点解析”选出 delta=0；
C^N 和全部到 N 阶的零 jet 都不够。只在 epsilon≠0 解析也不够。
这是明确附加条件下的定理，尚不是原物理制备给出的选解原理。

## 3. 完整态的时间平移还要移动参考时标

记
\[
B=\Theta^{-1}(e^{-2U}-1),\qquad
q_{\epsilon,\delta,t}(\eta)=Q+\frac{P}{A^2}[\eta-t+B_{\epsilon,\delta}(\eta)].
\]
令 epsilon_c=e^(sc)epsilon、delta_c=e^(sigma c)delta。
几何与 B 都随 eta→eta+c 变换，但若 Q/P 与 t 均固定，
\[
q_{\epsilon,\delta,t}(\eta+c)
=q_{\epsilon_c,\delta_c,t}(\eta)+Pc/A^2.
\]
表示同一个完整历史，必须同步做以下等价变换之一：

- 保持 Q/P，令参考时标 t→t−c；
- 保持 t，将 canonical datum 写作 Q→Q+Pc/A²、P不变，并同步变换该 datum 的态表示。

后一项是正则 shear，不是保持原 Q/P 联合分布数值不动。
忽略这一点，会把一个额外的几何自治合同误当作完整量子态的时间协变性。

正确的带参考时标协变图满足
\[
F(e^{sc}\epsilon,t-c)=e^{\sigma c}F(\epsilon,t).
\]
取 c=t 即得一般局部解
\[
\boxed{F(\epsilon,t)=e^{-\sigma t}H(e^{st}\epsilon).}
\]
不变量为 X=e^(st)epsilon、Y=e^(sigma t)delta，协变只要求 Y=H(X)。

任取非零常数 k，
\[
H(X)=kX^2,\qquad F(\epsilon,t)=k e^{(2s-\sigma)t}\epsilon^2
\]
就在参数原点附近解析，具有纯慢切向，满足完整参考时标协变，却含非零快模。
取足够小参数即可留在冻结存在域。故“完整时间协变 + 解析制备”没有唯一选定纯慢支。

## 4. 对下一任务的直接约束

纯慢支仍是合法数学支，但若采用它，必须注明所加的物理准备条件、有效理论尺度或自治性假设。
当前半无限过去和有限正窗定理没有给未来有界性；线性层面 s、sigma 均为正，朴素未来无增长条件甚至同时删去两种增长项。

相同完整 O(2) twirl 的记录等价仍沿用前驱的共同线性 CP 合同。
任意非线性、群不变的选解不因名称自动满足它；前驱纯度反例继续有效。
人为给 old/new 制备选择不同 delta，不能记作原制备降噪产生的引力信号。

本轮随后检查两件更具体的事：[理想几何数据能否识别幅度](GEOMETRY.md)，以及
[完整源在更大的正时间窗候选类中能否满足联合约束](FLUCTUATIONS.md)。

[selector.py](selector.py) 验证完整时标的符号恒等式、解析反例和冻结指数区间。
正则性分类及一般函数解由本页证明承担，不将有限符号检查称作全部形式化证明。
