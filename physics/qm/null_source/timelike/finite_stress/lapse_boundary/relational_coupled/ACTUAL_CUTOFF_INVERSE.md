# 同一实际历史的有限截止因果逆：统一控制与强收敛

本页关闭原 FINITE_CAUSAL 留下的一个明确门：同一实际 U、同一 incoming
态、同一 AE_K 处方和零过去准备域下，有限 K 的齐次线性作用量逆强收敛
到 ACTUAL_INVERSE 已构造的全场逆。保留 off-shell Ward 修正后，压力逆
也在充分大 K 强收敛。这里不声称算子范数收敛、量子几何联合态的全场极限，
或已将实际随机应力接成合法 forcing。

## C1. 固定对象和原 action 截断的身份

I=[0,1/50]，gamma=24A，Y=L²(I,e^(-2gamma eta)deta)，
X={w in H4(I):w(0)=w'(0)=w''(0)=w'''(0)=0}，
||w||X=||w^(4)||Y。实际 quiet 背景 epsilon<exp(-1158)，
mu=sum_(j=0..3)||V^(j)||1<5epsilon；8e4<A<1e5。

令 D_K(y) 是 dynamic_inverse/SPECTRUM 第1节的同一表达，将 Dnum 的和
截到 k<=K：
\[
 D_K(y)=y-4+{2\over A^2}\left({8B\over3}-D_0+
                    {Z_K(y)\over4\pi^2}\right)
       +{4J_n\over3A^2}{y+24\over y+12},
\]
\[
 Z_K=D_{\mathrm{num},K}+C_Ay^2/360-(C_A-29)y/180-1/24,
\]
\[
 D_{\mathrm{num},K}=-1+y/2-y^2/12+
 \sum_{k=2}^K\left[-{4k^2\omega_k y\over3(y+4\omega_k^2)}
                   +{yk\over3}+{y/6-y^2/12\over k}\right].
 \tag{C1}
\]
B,D0,Jn,CA 是该冻结文件的固定常数；P_K(s)=D_K(s²)。
新的薄层态保持所需的 summed derivative two-point mean/response，
故复用这一静态参考，不重算旧谱常数或旧模式。

这确实是同一有限 K 的归一化静态 action 行。逐壳恒等式为
\[
 {1\over3V_0A^2}
 \left\{y^2\left[{k^2\over\omega(y+4\omega^2)}-{1\over4k}\right]
       -2y\left[{k^2\over2\omega}-{k\over2}-{1\over4k}\right]\right\}
 ={1\over V_0A^2}
 \left[-{4k^2\omega y\over3(y+4\omega^2)}
       +{yk\over3}+{y/6-y^2/12\over k}\right].
 \tag{C2}
\]
V0=2pi²，omega²=k²-1。参考 k=1、thermal、零模、U0 和完整 AE 局部项
不变。C1 不是自动 on-shell 的有限截止压力行；二者的区别在 C6 处理。

## C2. 一个所有大截止共同有效的根位置界

取明确充分阈值 K0=10^9。冻结 SPECTRUM 第4节已经解析证明：
K>=2^20 时 D_K 恰有两个正实根，没有非实右半 s 平面根；
D_K(0)=D_infty(0)<-4，D_K(9)>0。因此 r1,K<9。
复用的全场快根给 r2<(11.47A)²<132A²。
F(y)=D(y)/[(y-r1)(y-r2)] 在 y>=0 为负且递减，
-c=F(0)，可取 c>1/(396A²)。

令 y0=144A²，则
\[
 -D_\infty(y_0)>{143\cdot12\over396}A^2>4A^2 .
\]
SPECTRUM 的紧集逐壳 majorant，D=y0/4+1，给
\[
 |D_\infty(y_0)-D_K(y_0)|
 \le {y_0(1+3D+8D^2)\over12\pi^2 A^2K^2}<10^7<A^2 .
 \tag{C3}
\]
例如 y0<1.5e12，D<4e11，1+3D+8D²<1.3e24，
A²>6.4e9，pi²>9，而 K>=10^9 满足 k²>=2max(1,D) 的尾条件。
故 D_K(y0)<0，r2,K<144A²=gamma²/4，且
\[
 c_K={-D_K(0)\over r_{1,K}r_{2,K}}>1/(432A^2).
\]
没有执行十亿项求和或数值求根。K0 是充分阈值，不声称最小。

## C3. 统一静态 resolvent 界，含快极点

有限差商精确给
\[
 -F_K(y)=c_K+\sum_{k=2}^K\mu_{k,K}{y\over y+b_k},\qquad
 F_K={D_K\over(y-r_{1,K})(y-r_{2,K})},\quad b_k=4(k^2-1),
\]
\[
 \mu_{k,K}={W_k\over b_k(b_k+r_{1,K})(b_k+r_{2,K})}>0,\qquad
 W_k={8k^2\omega_k^3\over3\pi^2A^2}.
 \tag{C4}
\]
k=2 另有冻结的正 thermal residue。所有项保留。
在 s=gamma+i tau 分三段控制。

- |tau|<=4gamma：
  Re[-F_K(s²)/s]>=c_K gamma/|s|²，因为
  Re[s/(s²+b)]>0。故 |F_K|>=c_K/sqrt(17)。
- 4gamma<=tau<=2omega_K：取整数带
  k in [tau/2-gamma/2,tau/2-gamma/4]。带内至少 gamma/8 个整数，
  全部小于 K 且 k>=36A。于是 b_k>=tau²/2，
  |gamma²-tau²+b_k|<=3gamma tau，给
  Im[s²/(s²+b_k)]>=tau/(13gamma)。
  同时 omega>k/2、b_k+r_j,K<5k²，
  mu_k,K>1/(75pi²A²k)>c0/k，c0=1/(100pi²A²)。
  所有虚部同号，且 1/k>=2/tau，合得 |F_K|>=c0/52。
- tau>=2omega_K：每个 b_k<=tau²，
  Re[s²/(s²+b_k)]=[(gamma²+tau²)²+b_k(gamma²-tau²)]/
  |s²+b_k|²>=0，所以 Re[-F_K]>=c_K。

负 tau 用共轭。单侧整数带保证 tau 接近最大模式频率时不丢掉一半窗口。
因此整条竖线
\[
 |F_K((\gamma+i\tau)^2)|\ge m={1\over5200\pi^2A^2}.
\]
delta_j=1-r_j,K/gamma²>3/4 且
|s²-r_j,K|>=delta_j|s|²，最终
\[
 \boxed{\sup_\tau|s^4/P_K(s)|
             \le {16\over9m}<10^{15}=:M_0,\quad K\ge10^9.} \tag{C5}
\]
gamma 在两个增长极点右侧；本证明没有删除快根或改用慢根投影。

C1 的补偿和局部一致收敛，故 s4/P_K 在竖线逐点趋于 s4/P。
C5 与 weighted Plancherel 的支配收敛给
\[
 G_{0,K}f\longrightarrow G_0f\quad\hbox{in }X
 \quad\hbox{for every }f\in Y,\qquad \|G_{0,K}\|_{Y\to X}\le M_0.
 \tag{C6}
\]
可将 f 在 I 外补零，取各因果卷积再限制到 I；H4 因果轨道自动具有四个
零初迹。此处是强算子收敛，不声称算子范数收敛。

## C4. 实际背景与静态参考之差：截止无关预算

记 K_U,K 为 ACTUAL_UV_BRIDGE 的同 AE_K potential 核，
K0,K 为其静态对应，R_j,K=(partial_t+partial_s)^j(K_U,K-K0,K)，j<=2。
实际和静态的接触项精确抵消。ACTUAL_INVERSE I6 给逐壳
\[
 D_+^j(\chi_{U,k}-\chi_{0,k})
 =-{D_+^j I_V\cos(2\omega_k\tau)\over2\omega_k^3}+r_{j,k},
 \quad |D_+^jI_V|\le\mu\tau,\quad |r_{j,k}|\le500\mu/\omega_k^4 .
\]
对 S_K(tau)=sum_(2..K)k² omega^-3 cos(2omega tau)，在
floor(1/tau) 分段，低段绝对和、较高段 Dirichlet 界及系数/相位差给
|S_K(tau)|<=-log(tau)+6，0<tau<=T=.02。
所以 weighted Schur row/column 加同一 k2 thermal 项仍小于
\[
 \mu[1000T+T^2(-\log T+6.5)/4]+.18\mu<23\mu ,
 \tag{C7}
\]
独立于 K。

无限尾用
|sum_(k>K)cos(2k tau)/k|<=1/[(K+1)sin(tau)]、
|k²/omega³-1/k|<=4/k³、|omega-k|<=1/k，得到
\[
 \tau|S_\infty-S_K|\le2/K+2\tau/K^2+2\tau^2/K .
\]
余项 sum_(k>K)k²/omega4<2/K，故每个 j<=2 有真正范数界
\[
                    \|R_{j,K}-R_j\|_{Y\to Y}\le22\mu/K.   \tag{C8}
\]
thermal 在此尾中完全相消。

静态 multiplier 是
\[
 K_{0,K}(z)=-z^2\sum_{k=2}^K{k^2\over4\omega_k^3(z^2+4\omega_k^2)}
       +(K_{3,K}-1)/4+{8n\over\omega_2(z^2+12)} .
\]
I4 的正 majorants 对所有有限子和保持，
||K0,K f||Y<=3||f'||Y/sqrt(gamma)。
结合逐点 multiplier 收敛，给零初值 H1→Y 的强收敛。
这里输入未来接常数、过去补零，导数没有端点 delta。

令 DeltaQ_K=Qbar_U,K-Qbar_0,K。U10 逐壳减掉静态后，常数余项相消；
其值与一阶导数各自的尾至多
3Dmu/(16K²)+(64/3)mu/K。因此
\[
 \|\Delta Q_\infty-\Delta Q_K\|_{C^1}<45\mu/K,\qquad
 \|\Delta Q_K\|_{C^1}<3\varepsilon\quad(K\ge10^9).
\]
最后一步使用冻结 full DeltaQ 的 C1 界 2epsilon 和 mu<5epsilon。

设 B_U,K=H_U,K/(3V0A²)-L0,K。用 ACTION_RESPONSE A8 和 I9 的相同拆分，
预算分别为 R 块500epsilon、静态变系数61epsilon、链式接触12epsilon、
AE 4epsilon、gravity17epsilon、zero3epsilon、U0 30epsilon；
合计627epsilon，故
\[
 \|B_{U,K}\|_{X\to Y}\le1000\varepsilon,\qquad
               B_{U,K}w\longrightarrow B_Uw\ \hbox{in }Y .
 \tag{C9}
\]
强收敛由 C8、C1 mean 收敛及静态 K0,K 的强 H1→Y 收敛逐项给出。
外部时间导数移入输入时，w(0)...w'''(0)=0 保留所需全部零迹；
例如 D²K0,K(2hw')=K0,K(2hw')''，右侧输入在 H1 且初值零。
这不是把全场行与截断行之差当成一个 H4→L2 小算子。

## C5. 实际 action 逆的强极限

Rinv,K=B_U,K G0,K 的范数统一小于
q=10^18 exp(-1158)<exp(-1100)<1，而且强收敛到 B_U G0。
因此
\[
 \widehat G_{U,K}=G_{0,K}(I+R_{\mathrm{inv},K})^{-1},
 \quad \|\widehat G_{U,K}\|_{Y\to X}\le {M_0\over1-q}.
\]
每个有限阶 Neumann 多项式强收敛，余项由同一个 q 几何级数控制。
所以
\[
 \boxed{\widehat G_{U,K}f\longrightarrow
                  \widehat G_Uf\quad\hbox{in }X,\ f\in Y.} \tag{C10}
\]
全场极限正是已冻结 I10 的算子，没有重新定义。每项因果且保留声明零过去、
四零初迹及共同 incoming mode 运输。

## C6. 压力逆：必须带着有限截止 off-shell 项

在同一 U 上有限 K 的 E_K,S_K 一般不为零。原 Ward 和 action 行精确给
\[
 \widehat H_K=M_U L_{p,K}+D_{\mathrm{off},K},\qquad
 M_U f=e^{2U}f+e^U\int_0^\eta e^U h f,
\]
\[
 D_{\mathrm{off},K}w=e^{2U}(2S_K+E_K)w
       +{e^U\over2}\int_0^\eta e^U(2S_K-E_K)w' .           \tag{C11}
\]
这由 e_K'+he_K=2h s_K+w'(2S_K-E_K)、e_K(0)=0
及 Gamma_u,K=3V0a²(S_K+E_K/2) 的变分得到。

冻结 RETARDED_RESPONSE R1–R6 在实际解析窗严格内部已经证明：
同 AE k 减项的 mean 高壳尾为 C/(2K²)，C 由有限高阶背景 seminorm
控制但尚未数值化。因此
eK=||E_K||infty+||S_K||infty=O(K^-2)。
这里只调用背景的 mean 部分，没有对 L² forcing 添 C8 假设。
I2 与 weighted Volterra 界给
\[
 \|D_{\mathrm{off},K}\|_{X\to Y}
                 \le3e^{2\varepsilon}eK/\gamma^4\longrightarrow0.
\]
故存在 K1>=10^9，使 ||Doff,K Ghat_U,K||<1/2。
**K1 仅证明存在；尚未数值认证为10^9。** 它还须包含该 WKB 余项的有效阈值。

K>=K1 时，
\[
 G_{p,K}=\widehat G_{U,K}
       (I-D_{\mathrm{off},K}\widehat G_{U,K})^{-1}M_U,
 \quad
 \|G_{p,K}\|\le {2M_0\|M_U\|\over1-q},
\]
\[
 \boxed{G_{p,K}f\longrightarrow\widehat G_U M_U f=G_Uf
                                 \quad\hbox{in }X.}       \tag{C12}
\]
有限 K 初值 ODE 的唯一性将它与 FINITE_CAUSAL F5 的同零初值压力逆识别。
未删除实际初态/准备过去造成的其他独立列；非零初始约束荷仍需原有验收。

## C7. 新结果的物理范围

新增内容是共同 finite-K action 的统一谱/响应控制，以及实际齐次线性逆的
强比较；旧谱计数、旧全场逆和旧高频背景余项均复用。
它关闭了此前“全场逆已直接构造，但有限截断逆尚未证明趋向它”的缺口。
它没有给一般张量/lapse 行、非线性背景、正常联合量子几何态或装置的
K→infinity 极限，也没有把尖锐压力噪声变成合法平坦初值 forcing。
快根、AE 常数、U0、低模相关、有限截止 off-shell 项和准备条件全部保留。
