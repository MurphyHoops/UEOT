<a id="ch-62"></a>

# 62. 保留历史的逐动作记录误差预算

第58章给出了真实仪器、全部有限自适应叶记录与量子记忆的联合通道，并用该通道的整体缺陷控制完整记录 TV。整体缺陷说明怎样度量两个协议的差异，但通常仍须进一步求出或估计它。本章在固定有限深度和同一个因果控制器下，把误差追到每一步实际选择的仪器：先构造读取历史的矩形 Kraus 通道，再从共同输入的 PSD 主块、真实块权重和合法块效应导出动作预算。

这种控制器实际读取并去相干历史寄存器。形式化通道可以作用于任意历史—记忆密度矩阵，证明也确实使用所有输入主块；这不等于把经典历史控制改成相干量子控制。原有有限树解释器继续保持其更一般的变长叶语义，本章通过一个明确的固定深度子类与它连接。[QM318]

## 62.1 有限时间、真实历史与同一个控制器

固定有限结果载体 $O$、有限复量子记忆载体 $\iota$ 和有限深度 $N\in\mathbb N$。第 $t$ 步之前的完整结果历史为

$$
\mathsf H_t=\{h:\operatorname{Fin}(t)\to O\}.
$$

这里的下标就是已记录结果数；$\mathsf H_0$ 只有空历史。动作载体记为 $A$。有限深度只要求控制器在相应时间和历史上给出动作，不要求 $A$ 本身有限。实际类型为

$$
C:\prod_{t:\operatorname{Fin}(N)}(\mathsf H_t\to A).
$$

两种实现分别使用 $I_a$ 与 $J_a$，但都把同一个 $C_t(h)$ 当作该历史上的动作。共同结果字母表并不足以蕴含共同控制器；这里两者使用的是同一个函数值。每个仪器都有完整 Kraus 家族，例如

$$
\Phi^I_{a,o}(X)=\sum_{k:\kappa}K^I_{a,o,k}X(K^I_{a,o,k})^\dagger,
\qquad
\sum_{o,k}(K^I_{a,o,k})^\dagger K^I_{a,o,k}=I_\iota.
$$

$J$ 的 Kraus 下标可以来自另一个有限载体 $\eta$。本章比较真实通道，不要求两种实现具有相同的 Kraus 表示。保留结果的单动作联合通道仍是第58章的

$$
\mathcal R^I_a(X)=\sum_o|o\rangle\langle o|\otimes\Phi^I_{a,o}(X).
$$

记 $d_{\rm eff}$ 为全效应距离，并定义实际动作记录缺陷

$$
\delta_{\rm rec}(I_a,J_a)
=\sup\left(\{0\}\cup
 \{d_{\rm eff}(\mathcal R^I_a(\rho),\mathcal R^J_a(\rho)):
   \rho\in\mathcal D(\iota)\}\right).
$$

上确界的同一输入量词不能删去，记录标签也不能在定义缺陷前丢弃。插入零保证空输入态类型下定义仍有明确非空集合；给历史通道缺陷设统一上界时，源码显式保留该上界非负的条件。

## 62.2 PSD 历史主块、真实权重与合法效应

对任意有限历史载体 $H$ 和任意 $X\in M_{H\times\iota}(\mathbb C)$，定义主块

$$
X_h(i,j)=X((h,i),(h,j)).
$$

它不是取出某些任意矩阵元后另行宣称为状态。将嵌入 $V_h:e_i\mapsto e_{(h,i)}$ 写出，便有 $X_h=V_h^\dagger XV_h$。同一个主子矩阵构造也用于输出效应。

<a id="p-arb-01"></a>

**P-ARB-01（历史块、归一权重与合法块效应）。** 若 $\zeta\in\mathcal D(H\times\iota)$，则每个主块 $\zeta_h$ 都是 PSD，且

$$
p_h=\operatorname{Tr}\zeta_h\ge0,
\qquad \sum_h p_h=1,
\qquad p_h=0\ \Longleftrightarrow\ \zeta_h=0.
$$

若 $E\in\mathcal E(H\times\nu)$ 是任意合法输出效应，则主块 $E_h$ 也是 $\mathcal E(\nu)$ 中的合法效应。对任意块族 $B_h$，还有真实迹配对等式

$$
\left\langle E,\operatorname{diag}_hB_h\right\rangle_{\mathbb R}
=\sum_h\langle E_h,B_h\rangle_{\mathbb R}.
$$

**证明。** PSD 在主子矩阵下保持，因此 $\zeta_h\succeq0$。总迹按积指标求和，给出 $\sum_h\operatorname{Tr}\zeta_h=\operatorname{Tr}\zeta=1$。对 PSD 矩阵，迹为零当且仅当矩阵为零；这一已有定理直接用于每个主块，未给零权重历史强行指定一个后验态。

对效应，$E\succeq0$ 与 $I-E\succeq0$ 分别限制到历史 $h$。由于 $i\mapsto(h,i)$ 是单射，单位矩阵的主块就是 $I_\nu$，故 $E_h\succeq0$ 且 $I_\nu-E_h\succeq0$。最后展开矩阵乘法和迹，输出块的非对角历史元素为零，剩余项恰为主块配对之和。∎

这里 $\zeta$ 可以有不同历史间的非零相干项。主块正性与迹归一性不要求输入事先块对角。下一节构造的通道会实际消去这些历史相干项；证明范围由该明确动作决定。

## 62.3 从真实读取 Kraus 到加权动作界

先考虑一般的历史依赖矩形通道 $\mathcal C_h:M_\iota\to M_\nu$。若其 Kraus 矩阵为 $L_{h,k}$，在历史与记忆联合空间中定义

$$
\widetilde L_{h,k}((g,a),(g',i))
=\mathbf 1_{g=h}\mathbf 1_{g'=h}\,L_{h,k}(a,i).
$$

这个矩阵读取输入历史 $h$、对记忆执行 $\mathcal C_h$，并把同一个 $h$ 写入输出。对不同 $h$ 的 Kraus 求和是通道的非相干 Kraus 求和，因而是历史去相干的真实实现。

<a id="p-arb-02"></a>

**P-ARB-02（实际历史读取通道的动作加权界）。** 上述 Kraus 家族构成迹保持完全正通道 $\mathcal S_{\mathcal C}$，对每个实际矩阵输入都有

$$
\mathcal S_{\mathcal C}(X)
=\operatorname{diag}_h\mathcal C_h(X_h).
$$

若 $\mathcal D_h$ 是另一组具有相同输入输出载体的通道，则任意 $\zeta\in\mathcal D(H\times\iota)$ 满足

$$
d_{\rm eff}(\mathcal S_{\mathcal C}(\zeta),
             \mathcal S_{\mathcal D}(\zeta))
\le \sum_h p_h\,\delta(\mathcal C_h,\mathcal D_h),
\qquad p_h=\operatorname{Tr}\zeta_h.
$$

特别地，若所有 $h$ 上的实际缺陷都不超过 $\varepsilon$，则该同输入距离不超过 $\varepsilon$。若还显式要求 $\varepsilon\ge0$，历史通道的实际缺陷也不超过 $\varepsilon$，包括空输入载体的上确界边界。

**证明。** 对固定输入指标 $(g,i),(g',j)$，矩阵积 $\widetilde L_{h,k}^\dagger\widetilde L_{h,k}$ 只有 $g=g'=h$ 时非零。先对 $k$ 使用各 $\mathcal C_h$ 的完整性，再对 $h$ 求和，得到联合单位矩阵。矩形通道的完全正性由已证的有限辅助放大定理给出。类似展开 $\widetilde L_{h,k}X\widetilde L_{h,k}^\dagger$，只有 $X_h$ 进入对应输出块，给出作用公式。

对 PSD 块 $X_h$，分两种情况。若 $p_h=0$，P-ARB-01 给出 $X_h=0$，两个线性通道输出均为零。若 $p_h>0$，令 $\rho_h=X_h/p_h$，它具有实际 PSD 与迹一证明。对任意合法效应 $F$，由通道实线性和缺陷定义，

$$
\begin{aligned}
&\left|\langle F,\mathcal C_h(X_h)\rangle_{\mathbb R}
 -\langle F,\mathcal D_h(X_h)\rangle_{\mathbb R}\right|\\
&\quad=p_h\left|p_{\mathcal C_h(\rho_h)}(F)
                 -p_{\mathcal D_h(\rho_h)}(F)\right|\\
&\quad\le p_h\delta(\mathcal C_h,\mathcal D_h).
\end{aligned}
$$

再取任意联合输出效应 $E$。P-ARB-01 保证每个 $E_h$ 合法，并把整个概率差展开成主块概率差的和。绝对值三角不等式给出所述加权界；最后对全部效应取上确界。统一界使用 $\sum_hp_h=1$，历史通道缺陷界再对所有输入态取上确界并检查所插入的零。∎

关键权重来自同一个 $\zeta$。没有把两个不同演化轨迹的历史分布假定相同；本结果为下一节的三角分解提供一个可合法使用的共同输入。

## 62.4 追加结果的真实时间顺序与原协议

对长度 $t$ 的历史 $h$ 和新结果 $o$，记 $h\mathbin{\|}o$ 为把 $o$ 追加到末尾的长度 $t+1$ 历史。真实载体双射为

$$
\mathsf H_t\times(O\times\iota)
\longleftrightarrow\mathsf H_{t+1}\times\iota,
\qquad(h,(o,i))\longmapsto(h\mathbin{\|}o,i).
$$

逆映射取前 $t$ 项和最后一项。这一双射由一个矩形置换 Kraus 矩阵实现，其逆双射也给出真实通道。因此重标记保持完整态，并保持全效应距离，而不只是保持迹。

第 $t$ 个实际步骤 $S^I_t$ 先读取历史，使用 $\mathcal C_h=\mathcal R^I_{C_t(h)}$，再经上述置换追加结果。于是

$$
S^I_t(X)_{h\|o,h\|o}
=\Phi^I_{C_t(h),o}(X_h),
$$

不同完整历史之间的输出块为零。初态通过 $\iota\simeq\mathsf H_0\times\iota$ 的真实置换嵌入；依次执行这些步骤得到联合密度态 $\zeta^I_{C,\rho}$。零深度没有动作调用，不要求动作载体非空。

<a id="p-arb-03"></a>

**P-ARB-03（有限历史演化与原完整协议的矩阵一致性）。** 任意固定 $N$、控制器 $C$、实际仪器族 $I$ 和初态 $\rho$ 所构造的真实输出满足

$$
\zeta^I_{C,\rho}
=\operatorname{diag}_{h\in\mathsf H_N}
 \operatorname{recordOperator}(I,\operatorname{word}_C(h),\rho).
$$

从同一个 $C$ 构造原类型中的协议 $\pi_C$，则存在实际叶双射 $e_C:\operatorname{Leaf}(\pi_C)\simeq\mathsf H_N$，并有

$$
\operatorname{word}_{\pi_C}(\ell)
=\operatorname{word}_C(e_C\ell).
$$

经过 $e_C\times\operatorname{id}_\iota$ 的真实置换，两份联合密度态相等；相应叶概率、完整记录 TV 和终端量子边际全部一致。量子边际具体为

$$
\operatorname{Tr}_{\mathsf H_N}\zeta^I_{C,\rho}
=\sum_{\ell:\operatorname{Leaf}(\pi_C)}
 \operatorname{recordOperator}(I,\operatorname{word}_{\pi_C}(\ell),\rho).
$$

**证明。** 原协议从词的首项递归：停止对应空历史，动作节点对全部 $o\in O$ 给出后继控制器。叶到历史的映射将当前结果放到首项并递归处理尾部；逆映射读取首项，再递归还原尾叶。两个复合分别等于恒等，由此得到真实双射。

通道执行采用逐步末尾追加，因此还须证明两种递归顺序相符。源码先证明

$$
\operatorname{word}_{C}(h\|o)
=\operatorname{word}_{C_{<t}}(h)
 \mathbin{+\!+}[(C_t(h),o)],
$$

其中 $C_{<t}$ 是去掉最后动作时刻的同一控制器。另对原解释器证明

$$
\operatorname{recordOperator}(I,w\mathbin{+\!+}v,X)
=\operatorname{recordOperator}
  (I,v,\operatorname{recordOperator}(I,w,X)).
$$

零深度时置换嵌入保留原矩阵。归纳步把真实 $S^I_t$ 的主块公式、归纳假设和上述两条词顺序等式连接起来，就得到完整输出矩阵，而非仅有概率相等。最后用叶双射换序有限和，得到原协议全态置换等式及量子边际。∎

原 `Protocol` 允许不同叶具有不同长度，本章的 $\pi_C$ 则是由同一个固定 $N$ 构造的完整子类。零概率结果仍保留其合法后继动作。这里没有补齐任意停止树的语义证明，也没有借由叶类型转换自动取得那项更广范围。

## 62.5 逐动作递推、有限总和与完整记录 TV

对于同一 $C$，把两种初态分别记为 $\rho,\sigma$。令 $\zeta^I_t$ 是从 $\rho$ 经 $I$ 和前 $t$ 步控制器所得的实际联合态，$\zeta^J_t$ 则从 $\sigma$ 经 $J$ 得到。定义

$$
\begin{aligned}
q^J_t(h)&=\operatorname{Tr}(\zeta^J_t)_h,\\
a_t&=\sum_{h\in\mathsf H_t}q^J_t(h)
 \delta_{\rm rec}(I_{C_t(h)},J_{C_t(h)}).
\end{aligned}
$$

这就是源码的 `actionCost`。其中前缀态由 `run J (C.truncate t) σ` 实际构造；$a_t$ 非负，零质量历史按零块定理贡献零。它不是重新命名整个协议的缺陷。

<a id="p-arb-04"></a>

**P-ARB-04（实际逐动作和预算与完整记录 TV）。** 在上述固定有限深度、共同控制器与共同记录/记忆载体条件下，对任意初态 $\rho,\sigma$ 有

$$
\begin{aligned}
d_{\rm eff}(\zeta^I_N,\zeta^J_N)
&\le d_{\rm eff}(\rho,\sigma)+\sum_{t=0}^{N-1}a_t,\\
\operatorname{TV}(p^I_N,p^J_N)
&\le d_{\rm eff}(\rho,\sigma)+\sum_{t=0}^{N-1}a_t.
\end{aligned}
$$

若对每个时间 $t$、每个长度 $t$ 历史 $h$ 已实际证明

$$
\delta_{\rm rec}(I_{C_t(h)},J_{C_t(h)})\le\varepsilon_t,
$$

则两式右端都可换成 $d_{\rm eff}(\rho,\sigma)+\sum_{t<N}\varepsilon_t$。$p^I_N,p^J_N$ 是完整历史分布；经 P-ARB-03 的叶双射后，同样的界适用于原协议的完整叶律。

**证明。** 设 $D_t=d_{\rm eff}(\zeta^I_t,\zeta^J_t)$。在同一个 $S^I_t(\zeta^J_t)$ 处使用三角不等式，得到

$$
\begin{aligned}
D_{t+1}
&\le d_{\rm eff}(S^I_t(\zeta^I_t),S^I_t(\zeta^J_t))\\
&\quad+d_{\rm eff}(S^I_t(\zeta^J_t),S^J_t(\zeta^J_t))\\
&\le D_t+a_t.
\end{aligned}
$$

第一项由真实 CPTP 效应拉回给出收缩。第二项的两个仪器实现在同一个 $\zeta^J_t$ 上比较，P-ARB-02 给出以 $q^J_t(h)$ 为共同权重的动作界；结果追加置换保持距离。归纳和有限求和给 $D_N\le D_0+\sum_ta_t$，零历史的初态置换给 $D_0=d_{\rm eff}(\rho,\sigma)$。若每个动作缺陷不超过 $\varepsilon_t$，P-ARB-01 的权重归一性给 $a_t\le\varepsilon_t$，再求和即可。

对任意有限记录事件 $S\subseteq\mathsf H_N$，构造真实效应

$$
E_S=\sum_{h\in S}|h\rangle\langle h|\otimes I_\iota.
$$

它与补效应均 PSD，且在任意联合态上的概率恰为主块质量在 $S$ 上之和。因此 $|p^I_N(S)-p^J_N(S)|\le D_N$。有限归一化分布的全部事件刻画给 $\operatorname{TV}(p^I_N,p^J_N)\le D_N$；这一步保持系数一，没有按单点误差再乘历史总数。最后使用 P-ARB-03 已证的 TV 重标记等式，传回原协议。∎

$J$ 在此只是选取三角分解共同输入的一个明确方向。公式没有要求 $\zeta^I_t=\zeta^J_t$，也没有要求两者的历史权重相同。实际 $a_t$ 可以反映 $J$ 前缀中很少访问的历史；统一 $\varepsilon_t$ 则只需核对所有被控制器选择的底层动作，使用更保守但较易外部估计的上界。后者仍需真实仪器误差证明、校准或其他独立误差输入；本章不把一个定义为上确界的数自动称为已数值算出。

## 62.6 精确有理的两步预算正控

以下例子固定 $O=\iota=\operatorname{Fin}(2)$，每个仪器使用四个 Kraus 下标。令 $\mathsf D_b$ 确定输出 $b\in\{0,1\}$，唯一非零 Kraus 是该标签的第零个单位矩阵，因此每个矩阵输入均满足

$$
\Phi_{\mathsf D_b,o}(X)=\mathbf1_{o=b}X.
$$

再定义有偏仪器 $\mathsf B$：标签零下的 Kraus 四元组为 $(I/2,I/2,I/2,0)$，标签一下为 $(0,0,0,I/2)$。四个非零项的 Gram 之和是 $I$，所以它是实际完整仪器，且

$$
\Phi_{\mathsf B,0}(X)=\tfrac34X,
\qquad \Phi_{\mathsf B,1}(X)=\tfrac14X.
$$

所有矩阵系数都是精确有理数，没有浮点近似或通过估算平方根设置 Kraus。

控制器在第一步选择动作 $\mathrm{none}$，读到首个结果 $o$ 后，在第二步选择动作 $\mathrm{some}(o)$。参考实现令 $I_{\mathrm{none}}=\mathsf D_0$；近似实现令 $J_{\mathrm{none}}=\mathsf B$；两种实现均令 $I_{\mathrm{some}(o)}=J_{\mathrm{some}(o)}=\mathsf D_o$。因此控制器的确读取前一步记录并影响后一步仪器。

<a id="p-arb-05"></a>

**P-ARB-05（精确有理逐步预算的饱和见证）。** 对任意二维输入密度态，第一动作的真实记录缺陷为 $1/4$，第二动作的对应缺陷为零。实际加权成本分别为 $a_0=1/4$、$a_1=0$，完整两步记录 TV 精确等于 $1/4$。不同初态时则有

$$
d_{\rm eff}(\zeta^I_{2,\rho},\zeta^J_{2,\sigma})
\le d_{\rm eff}(\rho,\sigma)+\tfrac14.
$$

相同输入态 $\rho$ 时，两种实现的终端量子边际都恰为 $\rho$。原协议叶表示的完整记录 TV 也精确等于 $1/4$。

**证明。** 对任意合法联合效应 $E$，令 $x=p_\rho(E_0)$、$y=p_\rho(E_1)$。P-ARB-01 给出 $0\le x,y\le1$。两种第一步输出的概率分别为

$$
x,\qquad \tfrac34x+\tfrac14y.
$$

它们之差的绝对值是 $|x-y|/4\le1/4$，所以这是所有输入态、所有合法联合效应上的上界。记录事件“输出零”在两种输出中具有概率 $1$ 和 $3/4$，给出匹配下界；对输入态取上确界得到实际动作缺陷 $1/4$，没有把单一被测试输入当作上确界证明。

第二步两方在共同历史 $h$ 上选取的仪器同为 $\mathsf D_{h(0)}$，故该动作缺陷为零。前缀权重归一后得到 $a_0=1/4,a_1=0$，P-ARB-04 给出全程上界。完整历史 $(0,0)$ 的实际概率在两实现中分别为 $1$ 与 $3/4$，其事件差给 TV 下界 $1/4$，与上界相等。

终端量子边际直接由实际 `run_matrix` 对四个长度二历史求和：参考实现总和为 $\rho$，近似实现总和为 $3\rho/4+\rho/4=\rho$。最后使用叶 TV 等式得到原协议结论。∎

该例检验了“当下结果加入历史、控制器读取既有历史、下一步动作依赖它”的实际顺序，同时检验权重、总和与 TV 系数。精确计算属于有限形式见证，不是实验确证。[QM318]

## 62.7 同一个反馈下的删除标签反例

保留上一节的控制器和参考实现 $I$，另取 $\widehat J_{\mathrm{none}}=\mathsf D_1$，并令 $\widehat J_{\mathrm{some}(o)}=\mathsf D_o$。对于每一个动作，这两种实现丢弃标签之后的实际量子通道都相同：都是恒等通道。

<a id="n-arb-01"></a>

**N-ARB-01（无标签动作零缺陷仍可给出最大完整记录误差）。** 上述两个实际仪器族的每个无标签动作缺陷均为零，但相同任意初态下的两步完整记录 TV 为 $1$。第二次结果为零的事件概率分别为 $1$ 和 $0$。两种实现的终端量子密度态均等于输入 $\rho$，因而彼此相同。

**证明。** $\mathsf D_0$ 与 $\mathsf D_1$ 的无标签通道都把每个输入矩阵 $X$ 送到 $X$，后续动作两方更是相同仪器。因此无标签通道作为函数相等，已有 `channelDefect_self` 给出零缺陷。

参考实现必定得到历史 $(0,0)$；另一实现必定得到 $(1,1)$。这些概率由原时间顺序词及真实分支公式求得。历史事件 $\{(0,0)\}$ 的概率差为 $1$，给出完整 TV 下界；有限概率分布 TV 至多为 $1$，故正好为 $1$。对实际事件 $\{h:h(1)=0\}$ 展开四个历史，得到第二次结果的概率 $1$ 与 $0$。两边终端量子边际分别对实际记录块求和，均为 $\rho$。原协议叶 TV 由实际叶双射保持。∎

本反例把第58章的标签责任具体接到了新逐步实现与旧协议之间，未把它重新解释成终端量子态不同。若误用零的无标签动作缺陷替换 P-ARB-04 中的 $\delta_{\rm rec}$，同初态预算会给出错误的零记录误差；真正的带标签动作缺陷不允许这一步替换。

## 62.8 公共接口、实际证据与物理责任

本章新增公共模块为 `UEOTQM.HistoryChannels` 与 `UEOTQM.ActionRecordBudget`。下表给出稳定责任入口；具体正负控位于 `UEOTQM.ActionRecordBudgetExamples`。[QM318]

| 编号结果或接口 | 实际源码责任 |
|---|---|
| P-ARB-01：PSD、质量和零块 | `principal_posSemidef`、`sum_mass_principal`、`weight_nonneg`、`sum_weight`、`zero_weight_iff_zero_principal` |
| P-ARB-01：合法块效应与真实配对 | `restrictEffect`、`restrictEffect_matrix`、`pairing_block` |
| P-ARB-02：读取 Kraus 与实际块作用 | `readKraus`、`readKraus_gram`、`readKraus_conjugation`、`controlled`、`controlled_operator_eq_block` |
| P-ARB-02：从 PSD 块到动作界 | `pairing_operator_difference_le_mass_mul_defect`、`controlled_state_distance_le_weighted_defect`、`controlled_defect_le_uniform` |
| P-ARB-03：有限控制器和时间顺序 | `Controller.leafEquiv`、`Controller.protocol_word_eq`、`Controller.word_snoc`、`recordOperator_append` |
| P-ARB-03：真实步骤与原完整状态 | `step`、`step_operator_eq_block`、`run_matrix`、`run_eq_protocol_state`、`terminal_memory_matrix`、`weight_run_leaf` |
| P-ARB-04：实际逐动作和 | `actionCost`、`run_succ_distance_le`、`run_distance_le_actionCost_sum`、`actionCost_le`、`run_distance_le_budget_sum` |
| P-ARB-04：完整记录与原叶律 | `record_tv_le_actionCost_sum`、`record_tv_le_budget_sum`、`protocol_record_tv_eq`、`protocol_record_tv_le_budget_sum` |
| P-ARB-05：精确有理正控 | `biased_record_defect_exact`、`first_actionCost_exact`、`second_actionCost_exact`、`two_step_record_tv_exact`、`original_protocol_record_tv_exact` |
| N-ARB-01：删除标签与量子边际 | `negative_unlabelled_defect_zero`、`negative_two_step_record_tv`、`exact_second_record_zero`、`flipped_second_record_zero`、`negative_terminal_memories_equal` |

两份公共模块含54条显式 theorem、20项定义和1项缩写，共75个实际逐名公理审计目标。具体见证另含36条 theorem、14项定义和2项缩写，共52个目标。三份源码均有实际聚焦编译成功回执；两个完整审计序列与实际源码顺序对应，基础只包含 `propext`、`Classical.choice`、`Quot.sound` 或其子集。开发中遇到的失败与最终成功日志均保留，最终日志有普通 linter 警告。独立 B→C 审查分别覆盖公共证明与完整具体见证。实际证据位于 `physics/qm/kernel/evidence/v31.8/C`，本轮统一验收和远端发布另由 root 的完整回执承担；这里的局部通过不替代那两项身份。

已闭合的数学责任是：给定明确的有限复量子仪器和共同因果动作规则，预测误差可以通过真实历史通道分解到实际动作记录缺陷，并传到完整记录分布。这让一个难以整体评估的协议对象有了可逐项审查的误差入口。量子记忆维数、每个动作的完整性、记录范围、实际控制器以及输入态误差都保留在前提中。

变长停止树的逐动作补齐、相干控制器、未纳入当前载体的任意环境记忆、diamond 距离和连续时间极限各需新的定义与证明。这里的全效应距离不自动具有这些放大后量词。把动作缺陷变成现实设备校准值、处理建模外泄漏和验证实验适用条件，也有独立经验责任。本章没有新增实验，没有从有限误差内核推出完整自然理论，更没有改变三代结论所依赖的谱、表示、阈值和有效窗口条件。冻结 Core 的106项与四生成器保持原身份。
