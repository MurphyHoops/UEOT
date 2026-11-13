这里的延伸针对登记的基本寄存器及其生成的电路，不把逐系统的直接和操作认作强幺半函子。非平凡基本寄存器按上述方式完成；空寄存器、即张量单位，仍为 $\mathbb C$。联合载体使用这些完成代数的**真实代数张量积**，例如 $(M_d(\mathbb C)\oplus\mathbb C)\otimes(M_e(\mathbb C)\oplus\mathbb C)$。其全可见中心块为 $M_d(\mathbb C)\otimes M_e(\mathbb C)$，其余中心块的直接和组成隐藏部分；不得把它们默认替换成单独一个 $\mathbb C$。一般地，将输入、输出写为 $\widetilde{\mathcal A}=\mathcal A_{\rm vis}\oplus\mathcal A_{\rm hid}$、$\widetilde{\mathcal B}=\mathcal B_{\rm vis}\oplus\mathcal B_{\rm hid}$，丢弃为各中心块普通矩阵迹的总和。没有输入或输出寄存器时，相应可见代数为 $\mathbb C$，隐藏部分为零。

任意多输入、多输出的原始完整 CP 仪器 $\{\Phi_y\}$ 都可在可见联合块上按原式实现，并取

$$
\widetilde\Phi_y(\rho\oplus\xi)
=\iota_{\mathcal B}\Phi_y(\rho)+\Xi_y(\xi),
\qquad
\Xi_y(\xi)=w_y\operatorname{Tr}(\xi)\tau_{\mathcal B},
\quad w_y\ge0,\quad\sum_yw_y=1,
$$

其中 $\iota_{\mathcal B}$ 是可见块嵌入，$\tau_{\mathcal B}$ 是实际输出代数中的任意固定归一态；输出为张量单位时取 $\tau_{\mathcal B}=1$。这样各分支为 CP，总和对完整输入总迹保持；对恒等操作可以专门选择隐藏部分的恒等延伸，对丢弃选择完整总迹。只为登记的生成操作选择延伸，顺序、并行和条件电路随后使用实际 CP 复合与实际代数张量积构造。从可见准备出发，$\xi=0$，所有这些电路的可见分支及概率保持原值。这里证明的是可达电路的操作等价；没有断言原库的所有操作等式在新增的不可达扇区也成立，也没有断言 $\widehat{\mathcal A\otimes\mathcal B}=\widehat{\mathcal A}\otimes\widehat{\mathcal B}$。完成理论可以另外允许隐藏态准备，但它们不属于本命题固定的可达准备库。
