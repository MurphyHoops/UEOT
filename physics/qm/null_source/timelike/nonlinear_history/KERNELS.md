# 完整非线性 RSET：同半径解析核与固定 AE 处方

## 1. 固定物理合同与函数空间

所有背景量是 [joint_history/history.json](../joint_history/history.json) 中 unfiltered case 的相关精确定义量；展示区间只作包围。沿用两相同自由实标量、minimal massless、闭 S3、G=2T、固定 U0/M2、AE mu=1 与零额外有限曲率项。没有重算旧谱常数。

记两条固定正根为 s=s_*、sigma=sigma_F，lambda_nm=ns+m sigma。A 是双变量完整 unital Wiener 代数，范数为 sum |f_nm| Rz^n Rw^m。定义

\[
w_j(\lambda)=(1+\lambda)^j\log(e+\lambda),\quad
\|f\|_{E_j}=\sum w_j(\lambda_{nm})|f_{nm}|R_z^nR_w^m.
\]

常数的权重为 1。由

\[
1+a+b\le(1+a)(1+b),\quad
\log(e+a+b)\le\log(e+a)+\log(e+b)-1
\le\log(e+a)\log(e+b)
\]

知 E_j 是乘法常数为 1 的 Banach 代数，Theta:E_(j+1)→E_j 的范数≤1。所有正频率至少为 s>1。Theta 的逆只作用于无常数项的级数。

令 u00=0，a=Ae^u、h=Theta u、V=Theta²u+h²。在 ||u||E4≤t 时，

\[
\|h\|_{E_3}\le t,\qquad \|V\|_{E_2}\le M=t+t^2.
\]

本轮统一取 t≤0.1、M≤0.11、H=||h||E1≤0.1。这是完整求解空间，不是有限 Taylor 截断。

## 2. 精确 Jost 乘积及正频率递推

沿用前驱精确 incoming Jost F±。复参数上 F+、F− 是独立解析伙伴；仅实几何上互为共轭。设

\[
W_k=F_{+,k}F_{-,k}=2\omega_k X_k,\qquad\omega_k=\sqrt{k^2-1}.
\]

由精确 KG 方程，

\[
\Theta(\Theta^2+4\omega^2)W
=4V\Theta W+2(\Theta V)W,\qquad W_{00}=1.
\]

若输入频率为 a,b≥0、总频率 Lambda=a+b>0，卷积系数为

\[
W_\Lambda=\sum_{a+b=\Lambda}
\frac{2(\Lambda+b)}{\Lambda(\Lambda^2+4\omega^2)}
V_aW_b.
\]

a>0，因为 V00=0。定义 R_omega=(Theta²+4omega²)^−1 和

\[
\mathcal B(V,g)=Vg+\Theta^{-1}(V\Theta g).
\]

在两个正频输入上 beta(a,b)=(a+2b)/(a+b)∈[1,2]，且 B(V,V)=3V²/2。于是

\[
W=1+2R_\omega V+2R_\omega\mathcal B(V,W-1),
\quad W_1=2R_\omega V,\quad
W_2=4R_\omega\mathcal B(V,R_\omega V).
\]

W_j 是对 V 的 j 次齐次项，不是时间／双变量总次数截断。每项无低于 j 的总次数。正频递推逐系数唯一，因此它与原精确 Jost 乘积相同；没有换量子态。

对任一上述次乘权重，

\[
\|W_j\|_{E_p}\le \frac{\|V\|_{E_p}^j}{2\omega^{2j}}.
\]

M<3 时所有 k≥2 的 Born 级数在当前球内一致收敛。外层核又给

\[
\|\Theta^2W_j\|_A\le
\frac{2M^j}{\omega^{2j-2}}.
\]

这里使用外层 resolvent 的平滑性，避免把两次导数逐一丢到每个输入上。

## 3. 精确裸压力与能量

由 X=|v|²、Y=Re(v* v')、Z=|v'|² 的解析 partner 延拓，保持真正 canonical 导数 (v'−hv)/a²。利用 Theta h=V−h²，

\[
p_k=\frac1{2\omega}\left[
\frac{\Theta^2W}{2}-\Theta(hW)+\frac{2\omega^2W}{3}\right],
\]

\[
e_k=\frac1{2\omega}\left[
\frac{\Theta^2W}{2}-\Theta(hW)+2\omega^2W\right].
\]

压力拆为

\[
p_k=\frac\omega3+\frac{h^2}{2\omega}
+L_\omega V+Q_\omega(V,V)+C_\omega(h,V)+R_{p,k},
\]

其中

\[
L_\omega=-\frac{4\omega}{3}R_\omega,\quad
Q_\omega=\frac1\omega(\Theta^2+4\omega^2/3)
R_\omega\mathcal B(V,R_\omega V),
\quad C_\omega=-\frac1\omega\Theta(hR_\omega V).
\]

能量的一次 V 项精确相消，其二次项为 Q_e=omega^−1 B(V,R_omega V)，其余同样分组。

必须保留的高阶余项是

\[
R_{p,k}=\frac{
(\Theta^2/2+2\omega^2/3)W_{\ge3}
-\Theta(hW_{\ge2})}{2\omega}.
\]

能量将 2omega²/3 改为 2omega²。最后一项包含 hW2，不能遗漏。

## 4. 重整化低核

先采用便于分解的 omega 减项，再在第 6 节精确转换回原 k 处方。压力减项是

\[
p_\omega^d=\frac\omega3+
\frac{h^2/2-V/3}{\omega}
+\frac{-V^2/8+h^2V/4-h\Theta V/4+\Theta^2V/12}{\omega^3}.
\]

等价地，omega^−3 分子为 Theta²V/12+V²/8−Theta(hV)/4。能量为

\[
e_\omega^d=\omega+\frac{h^2}{2\omega}
+\frac{V^2/8+h^2V/4-h\Theta V/4}{\omega^3}.
\]

能量最后分子亦等于 3V²/8−Theta(hV)/4。两种写法的 V² 符号差由 Theta h=V−h² 精确补足，并不是改变处方。

记 D(t)=t²+4omega²。对输入频率 t 或 a,b>0，Lambda=a+b，

\[
L^{ren}_\omega(t)=-\frac{t^4}{12\omega^3D(t)},
\]

\[
Q^{ren}_\omega(a,b)=
\frac{\beta}{\omega}\left[
\frac{2\Lambda^2}{3D(\Lambda)D(b)}
-\frac{b^2}{12\omega^2D(b)}\right],
\]

\[
C^{ren}_\omega(a,b)=
\frac{\Lambda b^2}{4\omega^3D(b)},\qquad
Q^{ren}_{e,\omega}(a,b)=
-\frac{\beta b^2}{4\omega^3D(b)}.
\]

这里 Q 核非对称，但卷积是完整的；beta 的交换平均为 3/2，产生恰当的局部 V² 减项。特别地 Cren 是正号。

由 beta≤2、b≤Lambda 及 t²/D(t) 单调增加，

\[
|Q^{ren}_\omega(a,b)|
\le\frac{\Lambda^2}{2\omega^3D(\Lambda)}.
\]

## 5. 无限模和与高 Born 尾

设 ell(t)=log(e+t)，t≥1。omega²≥3k²/4，故 c=8/(3sqrt(3)) 给

\[
U(t)=\sum_{k\ge2}\frac{k^2t^2}{\omega_k^3(t^2+4\omega_k^2)}
\le c\sum_{k\ge2}\frac{t^2}{k(t^2+3k^2)}.
\]

在 m=ceil(t) 处分开，低段≤log(1+t)，高段≤t²/(6m²)≤1/6，因而

\[
U(t)\le c[\log(1+t)+1/6]<
\frac95\ell(t).
\]

这同时给

\[
\sum k^2|L^{ren}_k(t)|\le t^2\ell(t),\quad
\sum k^2|Q^{ren}_k(a,b)|\le\ell(\Lambda),
\]

\[
\sum k^2|C^{ren}_k(a,b)|\le\Lambda\ell(b),\quad
\sum k^2|Q^{ren}_{e,k}(a,b)|\le\ell(b).
\]

相应范数界分别为 M、M²、HM、M²。对交叉项使用
Lambda ell(b)≤(1+a)(1+b)ell(a)ell(b)，无需额外的 Theta V∈E2。

高尾用 E1 的乘法和 Theta:E1→A：

\[
\|\Theta(hW_{\ge2})\|_A
\le\frac{HM^2}{2\omega^4(1-M/\omega^2)}.
\]

所以

\[
\|R_{p,k}\|_A\le
\frac{2M^3/3+HM^2/4}{\omega_k^5(1-M/\omega_k^2)},
\quad
\|R_{e,k}\|_A\le
\frac{M^3+HM^2/4}{\omega_k^5(1-M/\omega_k^2)}.
\]

而 sum k²/omega^5≤(4/3)^(5/2)/2<1.027。在 M≤0.11,H≤0.1 的整个球，

- 压力高 Born 尾 <0.00132；
- 能量高 Born 尾 <0.00175。

各低核是连续线性／双线性映射，高尾是局部一致绝对收敛的 Banach 值齐次级数。因此完整无限模减除和同半径全纯。这里没有假设精确模式在 1/k=0 解析，也没有调用旧七阶 WKB 余项。

## 6. 精确回到原 AE k 减项

统一写 T_omega^d=b omega+A/omega+C/omega³。能量取

\[
b=1,\quad A_e=h^2/2,\quad
C_e=V^2/8+h^2V/4-h\Theta V/4;
\]

压力取

\[
b=1/3,\quad A_p=h^2/2-V/3,\quad
C_p=-V^2/8+h^2V/4-h\Theta V/4+\Theta^2V/12.
\]

原 AE 的 T1、T3 精确等于

\[
T_1=A-b/2,\qquad T_3=C+A/2-b/8.
\]

定义不作数值重求的精确常数

\[
K_0=\sum_{k\ge2}k^2[\omega_k-k+1/(2k)+1/(8k^3)],
\]
\[
K_1=\sum_{k\ge2}k^2[\omega_k^{-1}-k^{-1}-(2k^3)^{-1}],
\quad
K_3=\sum_{k\ge2}k^2[\omega_k^{-3}-k^{-3}].
\]

有严格恒等式

\[
\sum_{k\ge2}k^2(T_\omega^d-T_k^d)=bK_0+AK_1+CK_3.
\]

在 d=1/k²≤1/4 作有限 Taylor 余项估计，逐模相应括号被 k^−5、k^−5、4k^−5 控制。因此

\[
-1/2\le K_0<0,\quad 0<K_1\le1/2,\quad0<K_3\le2.
\]

原谱常数未被重新计算或替换。这是精确加回有限局部差，原重整化尺度与所有有限项保持。

## 7. 完整实际应力及全部 AE 局部项

令 E1,E3,P1,P3 为冻结 k 减项。去除参考正规零模并加入实际零模后，

\[
\rho=\rho_{z,0}e^{-6u}+U_0+
\frac{-1-E1-E3+\sum_{k\ge2}k^2(e_k-e_k^d)+4r_{\rm an}}
{2\pi^2a^4}+\frac{4n}{\pi^2a^4}e_2,
\]

\[
p=\rho_{z,0}e^{-6u}-U_0+
\frac{-1/3-P1-P3+\sum_{k\ge2}k^2(p_k-p_k^d)+4p_{\rm an}}
{2\pi^2a^4}+\frac{4n}{\pi^2a^4}p_2.
\]

rho_z0=M2 mu/(2A^6)。n 是原两个完整 k=2 热壳的每振子占据。原 k=1 减除仍在；实际 Q/P 零模没有重复计入参考零模。

为明确没有漏掉接触项，记 v=a''/a、a3=a'''/a、a4=a''''/a，ell=log(x/4)+2 gamma+2u。所有无量纲局部式沿用：

\[
H_1=-36a3h+72vh^2+18v^2+36h^2-18,
\]
\[
T_1=-36a4+144a3h-216vh^2+108v^2+72v-72h^2,
\]
\[
H_3=3h^4+6h^2+3,\quad
T_3=12vh^2-12h^4+12v-12h^2.
\]

这里局部张量 T1 与前节减项系数 T_1 的符号仅在各自公式中使用，不是同一对象。定义

\[
r_{\rm an}=\frac{-H_1/6+H_3}{2880}-\frac{H_1}{1728}
+\frac{H_1(2+\ell)/32-\frac94(h^2v+h^2)}{36},
\]

\[
t_{\rm an}=\frac{-T_1/6+T_3}{2880}-\frac{T_1}{1728}
+\frac{T_1(2+\ell)/32-\frac98(4a3h-10vh^2+3v^2+4v-6h^2+1)}{36},
\quad p_{\rm an}=(r_{\rm an}-t_{\rm an})/3.
\]

这些是单个参考场的 pi²a⁴ 量，trace 约定为 rho−3p。两个实际场的完整系数如上。处方来源为 [Anderson–Eaker](https://arxiv.org/abs/gr-qc/9906055)，实际采用的冻结表达见 [dynamic_seed/DYNAMICS.md](../dynamic_seed/DYNAMICS.md)。

在 ||u||E4≤0.1 时，v≤0.11、a3≤0.121、a4≤0.1331（各自在所需剩余 E_j 范数中），完整局部表达给 r_an<1、t_an<1、p_an<2/3。由前述所有项，真空压力括号<5，减除后模和的密度／压力范数均<1。精确 k=2 乘积界给 ||p2||<1。

冻结数值包围又认证 x>6e9、x rho_z0<0.6、x U0<1.01、n<0.02。所以

\[
\mathcal S(u)=\Theta^2u+\frac{h^2+1}{2}+a^2p
\]

在此完整球上满足

\[
\|\mathcal S\|_A
\le0.605+0.6e^{0.4}+1.01e^{0.2}
+\frac{5e^{0.2}}{2\pi^2x}
+\frac{4ne^{0.2}}{\pi^2x}<4.
\]

没有把 a^−4 因子、动态 log、实际零模或热项省略。

## 8. 完整线性化与冻结 P 精确相同

新表达式中的每个正频单项式 lambda 给原裸压力一次项
−4omega lambda²/[3(lambda²+4omega²)]；AE 一次减项为 P1=−lambda²/3、P3=−lambda²/6+lambda⁴/12。这逐模还原冻结 Dnum 的完整无限和。

令总真空括号的静态能量／压力为 R0,K0，未包含参考零模：

\[
R_0=4\pi^2B-1/2,\quad
K_0=4\pi^2B/3+4\pi^2D_0-1/2.
\]

新真空压力括号的一次项为 K1(lambda)=Z(lambda)+1；其中 +1 恰好来自参考零模已剔除。完整 AE 局部张量的线性化逐项给出 Z 中所有 CA、log 和常数项。

设 j=x rho_z0、U=xU0，冻结静态约束给

\[
2j+(R_0+K_0)/(2\pi^2x)+4Jn/(3x)=1,
\]
\[
1/2+j-U+K_0/(2\pi^2x)+Jn/(3x)=0.
\]

消去 j,U 后，完整 DS(0) 的符号为

\[
P(\lambda)=\lambda^2-4+
\frac2x\left[\frac{8B}3-D_0+\frac{Z(\lambda)}{4\pi^2}\right]
+\frac{4Jn}{3x}\frac{\lambda^2+24}{\lambda^2+12}.
\]

[kernels.py](kernels.py) 对任意符号 lambda 验证这些等式；它没有只比较有限几个根。全部无限阶、求和和函数空间结论由本页证明承担，有限符号检查不是机器形式化的全部证明。

因此本轮解析映射、原线性逆和固定物理处方确属同一算子。下一步可合法使用 [显式收缩构造](EXISTENCE.md)。
