# 从静态种子到同一窗口的全阶正则性

研究基线：741209b3c010bc6dcfe695d8d3b71cba4448fe3f。日期：2026-11-20。本文是 [共同历史构造](README.md) 的解析证明部分；有限区间算术见 [history.json](history.json)，关键代数见 [algebra.py](algebra.py)。这不是 Lean 形式证明或外部同行评议。

## 1. 需要证明的命题与相空间

此前任一实际初片根固定后，保持它的完整量子态、同一 \(M_2\)、同一 AE 处方。取
\[
t_i=-1/8,\quad T=2^{-40},\quad b=T/4,\quad \rho=1/16.
\]
所有未来候选满足
\[
\mathcal X_\rho=\{f\in C[0,T]:f=f_{\rm ref}\text{ 于 }[0,b],
\ \|f-f_{\rm ref}\|_\infty\le\rho\}.
\]
这是非空完备的闭球与闭仿射子空间之交。给定 \(f\)，以共同初值解
\[
q'=f,\qquad h'=-1-q-h^2,\qquad a'=ha.
\]
同一完整 KG Cauchy 核在该候选几何上演化。中间候选只用于定义完备的积分方程；其 RSET 不被提前宣称为光滑 Hadamard RSET。

数值证书已经给出每个预定驱动 \(F_\alpha\) 的 \(C^0\) 因果固定点。本文证明该固定点在同一个 \(T\) 上为 \(C^\infty\)，然后恢复标准 Hadamard RSET 与约束恒等式。

关键是固定的整段相等条件，而不是仅保留初端 jets。以前的 \(f_n(t)=\varepsilon t\chi(nt)\to\varepsilon t\) 反例使用趋零的缓冲长度，不属于本轮固定 \([0,b]\) 的候选类。光滑性仍须由以下证明得到，不能从 \(C^0\) 闭性直接推出。

## 2. 解析证明回到真实静态种子

原 [准备函数](../instrument/instrument.py) 在 \(t\le-1/8\) 等于 \(\sqrt3\)，与后续准备段的连接为光滑平坦连接。参数因子在这里也恒为一。因此 \(q=-1,\ f=0\)，所有 \(f\) 的初端导数为零。

将未来候选接上已知过去。若未来 \(f\in C^m\)，固定缓冲区保证整个
\[
I=[t_i,T]
\]
上的 \(f\in C^m\)，且 \(f^{(j)}(t_i)=0\)。总长度 \(1/8+T<\pi\)，没有球面回返奇点。

选固定有限整数 \(K\)，使所有高模在过去和整个未来球上满足
\[
k\ge K\Longrightarrow k^2+q(t)\ge k^2/2.
\]
已知过去光滑且紧，未来 \(q\) 有统一界，故这样的 \(K\) 存在。不需要重新计算过去的模式，也不需要把瞬时频率基错误用于可能出现虚频的低模。全部 \(k<K\) 留作有限个实际 KG 模式。

## 3. 高频逐阶估计

对 \(k\ge K\)，令 \(\Omega_k=\sqrt{k^2+q}\)。实际瞬时变量满足
\[
C_k'=-2i\Omega_k C_k+\frac{f(1+2n_k)}{4\Omega_k^2},
\qquad
n_k'=\frac{f\,\Re C_k}{2\Omega_k^2}.
\]
静态种子给 \(C_k=n_k=0\)，且它们的全部初端导数为零。这里 \(C_k\) 的虚部取 \(\Re(\bar v_kv_k')\)，所以 \((|v_k|^2)'=2\Im C_k\)。

基础阶由
\[
I_k=\int_I\frac{|f|}{4\Omega_k^2}=O(k^{-2})
\]
及纯种子的 Bogoliubov 双曲函数界得到
\[
C_k=O(k^{-2}),\qquad n_k=O(k^{-4}).
\]

若 \(f\in C^m\)，对每个 \(r\le m\) 归纳：
\[
\boxed{C_k^{(r)}=O(k^{-2}),\qquad n_k^{(r)}=O(k^{-4}).}
\]
先对 \(n_k'\) 求 \(r-1\) 阶导数，由低阶 \(C_k\) 得到 \(n_k^{(r)}=O(k^{-4})\)。再对第一式求 \(r\) 阶导数：
\[
(C_k^{(r)})'+2i\Omega_k C_k^{(r)}
=D^r\!\left[\frac{f(1+2n_k)}{4\Omega_k^2}\right]
-2i\sum_{j=1}^r {r\choose j}\Omega_k^{(j)}C_k^{(r-j)}.
\]
因 \(\Omega_k^{(j)}=O(k^{-1})\) 对 \(j\ge1\) 成立，右侧为 \(O(k^{-2})\)。零初值及单位模传播子给出所需估计。最高只使用 \(f^{(r)}\)，没有导数损失。

每一阶只要求有限的常数；不假设阶数之间满足 Gevrey、解析或阶乘增长率。有限阶数值 \(S_2,D_5\) 证书不承担这个全阶命题。

## 4. 一次普通导数和对角导数

记 \(\tau=t-s\)、\(A(t,s)=\int_s^tq\)，定义高模规则核
\[
D(t,s)=\sum_{k\ge K}\left[
\frac{k^2}{k^2+q(s)}(1+2n_k(s))
\sin\!\left(2\int_s^t\Omega_k\right)-\sin(2k\tau)\right].
\]
设 \(\mathscr D=\partial_t+\partial_s\)，\(\mathcal K=\partial_tD\)。要证明的是
\[
|\mathscr D^j\mathcal K(t,s)|
\le C_j(1+|\log(t-s)|),\quad j\le m.
\]

### 4.1 真空部分

置 \(r=q(t)/2-q(s)\)。高频振幅和相位为
\[
\Omega_k(t)\frac{k^2}{k^2+q(s)}
=k+\frac r k+O(k^{-3}),\qquad
2\int_s^t(\Omega_k-k)=\frac A k+O(\tau k^{-3}).
\]
相位必须保留到二次。用 Abel 意义的
\[
\sum_{k\ge1}\frac{\cos2k\tau}{k}=-\log(2\sin\tau),\qquad
\sum_{k\ge1}\sin2k\tau=\tfrac12\cot\tau
\]
得到
\[
\boxed{\partial_tD_{\rm vac}
=(A^2-2r)\log(2\sin\tau)-A\cot\tau
+R_{\rm abs}+R_{\rm finite}.}
\]
\(R_{\rm abs}\) 的逐模余项为一致可和的 \(O(k^{-2})\)，\(R_{\rm finite}\) 仅为删去 \(k<K\) 的有限项。遗漏 \(A^2\log\) 会遗留谐和发散；[精确代数](algebra.json) 单独检验了这个系数。

对角导数保持 \(\tau\) 不变，且
\[
\mathscr D^j A=\int_s^tq^{(j)}=O(\tau).
\]
所以 \(A\cot\tau\) 及其所需对角导数在对角处有界，唯一需要积分控制的是 \(\log\tau\)。对余项作相同导数不作用于 \(2k\tau\)，只在相位修正产生 \(O(\tau/k)\)，故每个有限阶的余项仍为 \(O(k^{-2})\)。

### 4.2 Occupation 部分

一次普通导数为
\[
\partial_tD_n=
4\sum_{k\ge K}
\Omega_k(t)\frac{k^2}{k^2+q(s)}n_k(s)
\cos\!\left(2\int_s^t\Omega_k\right).
\]
由 \(n_k^{(r)}=O(k^{-4})\)，每项及所需对角导数具有 \(O(k^{-3})\) 可和界；相位的对角导数为
\[
\mathscr D^j\left(2\int_s^t\Omega_k\right)
=2\int_s^t\Omega_k^{(j)}=O(\tau/k),\quad j\ge1.
\]
故不会增加高频幂。另有 \(D(t,t)=0\)。

## 5. Volterra 求导的边界

对
\[
V(t)=\int_{t_i}^t f(s)\mathcal K(t,s)\,ds
=\int_0^{t-t_i}f(t-\tau)\mathcal K(t,t-\tau)\,d\tau
\]
求导，内部只产生 \(f\) 导数与 \(\mathscr D\) 导数。移动上端的每个边界项含 \(f^{(j)}(t_i)=0\)，所以对 \(j\le m\)
\[
V^{(j)}(t)=\sum_{r=0}^j {j\choose r}
\int_{t_i}^t f^{(r)}(s)\mathscr D^{j-r}\mathcal K(t,s)\,ds.
\]
前节统一的对数可积界允许支配收敛，给出这些导数及其连续性。又因 \(D(t,t)=0\)，得到
\[
f\in C^m\Longrightarrow \int_{t_i}^t f(s)D(t,s)\,ds\in C^{m+1}.
\]

## 6. 有限模的准确消项

令 \(y_k=|v_k|^2\)、\(c=(8\pi^2)^{-1}\)。Wick 平方为
\[
P=\frac1{2\pi^2}\sum_{k\ge1}
\left(k^2y_k-\frac k2+\frac q{4k}\right).
\]
低模导数含 \(k^2y_k'/(2\pi^2)+cf/k\)。高模 principal 相对完整谱少去的有限部分为
\[
\frac c k\int_{t_i}^t f'(s)\cos2k(t-s)\,ds.
\]
利用 \(f(t_i)=0\) 精确分部积分，两项中的 \(cf/k\) 消去。真正的低模规则项为
\[
\boxed{R_{\rm low}=\sum_{k<K}
\left[\frac{k^2y_k'}{2\pi^2}
+2c\int_{t_i}^t f(s)\sin2k(t-s)\,ds\right].}
\]
有限 KG 模式及此卷积都具有一阶增益。不能把孤立的 \(cf/k\) 当成增益项。

因此完整分解成立：
\[
P'=\mathcal T_s^{(t_i)}f+\mathcal R[f],\qquad
\mathcal R:C^m\to C^{m+1},
\]
\[
\mathcal T_s^{(t_i)}f=-c\int_{t_i}^t f'(s)\log[2\sin(t-s)]\,ds,
\quad
\mathcal R=R_{\rm low}-\frac1{4\pi^2}\int fD.
\]
\(m=0\) 时主项按分布导数解释。

## 7. 先有连续 \(P\)，再在解上升阶

不能对任意 \(C^0\) 候选假设 \(P\in C^1\)。先由有限模恒等式取极限得
\[
P(t)=P(t_i)-c\int_{t_i}^t f(s)\log[2\sin(t-s)]\,ds
+\int_{t_i}^t\mathcal R[f](u)\,du.
\]
对数核在 \(L^1\)；其 Fourier 部分和因系数平方可和而在 \(L^2\)、从而在有限区间 \(L^1\) 收敛。这给连续 \(P\)，并与收敛的减项模式和一致。

在固定点上，实际积分 trace 方程为
\[
P'-2hP=\frac J{480\pi^2}+K_{\rm init}
+\int_0^t I(a,h,q)\,ds+6\int_0^t aF_\alpha\,ds.
\]
当 \(f\in C^m\) 时，除 \(2hP\) 外的源属 \(C^m\)。一阶线性方程的正则性给
\[
\boxed{P\in C^{m+1}\quad\text{在解上成立}.}
\]
这避免把未知压力高阶模和先行逐项求导。

## 8. 变量主算符的同窗光滑逆

写
\[
\mathcal L=L_{\rm flat}+K_{\rm sm}* -d(t),\quad
K_{\rm sm}=c\,\frac d{dt}\left[-\log\frac{\sin t}{t}\right],
\quad d=c\log(a/a_0).
\]
\(L_{\rm flat}\) 的 Laplace 乘子为 \(c\log(z/\alpha_0)\)，
\(\alpha_0=a_0e^{19/30}\)。正实极点继续保留。

旧证书给冻结因果逆 \(J_{\alpha_0}*\in L^1\) 以及
\[
\theta_0=M_0(\|K_{\rm sm}\|_1+\|d\|_\infty)<1.
\]
对每个有限 \(r\)，在真正的 Banach 空间
\[
X_r=\{u\in C^r[0,T]:u^{(j)}(0)=0,\ j\le r\}
\]
使用等价范数 \(\|u\|_{r,\varepsilon}=\max_{j\le r}\varepsilon^j\|u^{(j)}\|_\infty\)。
消失的初端 jets 给
\(D^j(J_{\alpha_0}*u)=J_{\alpha_0}*u^{(j)}\)。

方程
\[
u=J_{\alpha_0}*g+J_{\alpha_0}*(du-K_{\rm sm}*u)
\]
在该范数上的收缩系数至多
\[
\theta_0+M_0\sum_{j=1}^r {r\choose j}
\varepsilon^j\|d^{(j)}\|_\infty.
\]
取足够小的 \(\varepsilon_r>0\) 即严格小于一。每阶改变的是等价范数，不是时间窗。\(C^0\) 唯一性保证这些解都是原来的同一个解。

## 9. 完整非线性 bootstrap 与 Hadamard 性

令 \(w=f-f_{\rm ref}\)。固定缓冲区使 \(w\) 在初端一整段恒零；所有过去相同，所以
\[
\mathcal T_s^{(t_i)}f-\mathcal T_s^{(t_i)}f_{\rm ref}
=\mathcal T_s^{(0)}w.
\]
若 \(f\in C^m\)，则 \(q\in C^{m+1},h\in C^{m+2},a\in C^{m+3}\)。前面已证明规则态响应增益一阶，解上的 \(P\in C^{m+1}\)；其余局部项、积分项和预定光滑驱动具有所需正则性。参考接触系数之差乘 \(f_{\rm ref}\) 也满足该条件。

故差分方程为
\[
\mathcal L[a]w=g_m,\qquad g_m\in X_{m+1}.
\]
应用同窗光滑逆，得到 \(w\in C^{m+1}\)。从已有 \(C^0\) 固定点归纳，在同一 \(T\) 上得到
\[
\boxed{f,q,h,a\in C^\infty.}
\]

实际静态高频真空加原正规有限模为 Hadamard 种子。沿最终同一光滑几何作 KG 传播，保持正性、CCR 和 Hadamard 性。标准 Hadamard 传播使重整化应力光滑；此前分布恒等式成为经典恒等式，因此随后使用 \(C'=2a'B\) 和 Hamiltonian 射击合法。有限随机相干位移也保持 Hadamard 性，原旧／新分布的平均源相同。

## 10. 文献与适用范围

本证明直接处理当前紧空间模式与实际准备历史。没有把已有存在定理未经条件核查套入。

- [Meda–Pinamonti–Siemssen，2007.14665](https://arxiv.org/abs/2007.14665) 的正则性讨论说明，低阶 mild 解本身不自动给更高阶几何；这里的逐阶核证明承担该责任。
- [Gottschalk–Siemssen，1809.03812](https://arxiv.org/abs/1809.03812) 的 smooth towing、Hadamard 传播和 energy shooting 提供方法背景；本文没有声称实际态已经满足其加权 moment 空间假设，也没有把其平直空间结论直接当作本球面模型的证明。

本文闭合的是指定预定数学驱动下的局部光滑共同历史。装置的真实 RSET 实现、全部噪声、非齐性反馈、长时行为及独立物理选择不由正则性定理给出。
