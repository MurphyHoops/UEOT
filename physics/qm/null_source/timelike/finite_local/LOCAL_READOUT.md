# 有限支撑、shift 不变的局域读源基准

固定原 unfiltered 静态解 a=A 与其完整高模态：k>=2 静态真空，
两场各完整 k=2 壳占据 n_old。两个实际零模及其 Q/P 协方差保持原样。

## 1. 光滑局域测试

令 t 为宽 pi/4 的归一均匀时间块与半径 pi/16 的 even 光滑概率核卷积。
令 b 为 S3 北极帽半径 pi/6 的归一 indicator 与半径 pi/24 的光滑概率核卷积。
S3 作为 SU(2) 的 Haar 卷积保持归一性和 positivity；Young 不等式给

integral t=integral b=1，
||t'||1<=D=8/pi，
||b||2^2<=1/V0，V0=pi^2/3-pi sqrt3/2。

实际时间支撑长 3pi/8、空间支撑帽半径 5pi/24。
同时间南极帽的对应测试与它严格类空分离；
这些严格余量避免仅在支撑边界上碰到 null separation。

取 f=A^-4 t'(eta-eta_ref)b。dvol=A^4 d eta dOmega，所以
A_i=phi_i(f)=beta P_i+H_i(f)，beta=-1/(sqrt(2pi^2)A^2)，Q 系数严格为零。
f 的时空积分为零，故该读数对 phi_i→phi_i+c_i 不变，不需绝对 Q 参考。

用两个独立 Gaussian 指针读取 A_i，完整记录为
Y_i=beta P_i+Gaussian noise。仪器与全部 P_i 交换，
所以 S0 的完整非选择谱律精确保留。局域仪器也激发高模，
条件态一般有零—高模相关；它不是全局 Gaussian(S0) 仪器。

## 2. 全高模方差与有限注能

记 b_km 的全简并度谱系数，omega_k=sqrt(k^2-1)。
对应高模系数为

c_km=i sqrt(omega_k/2) b_km t_hat(omega_k)/A，

故完整高模方差

Vh=(1/(2A^2)) sum_{k>=2,m}(2n_k+1)omega_k |b_km|^2|t_hat(omega_k)|^2。

使用 |t_hat(omega)|<=min(1,D/omega)、
omega min(1,D^2/omega^2)<=D 以及 Parseval，得到

Vh<=(1+2n_old)D/(2A^2 V0)。

没有截断模数，也没有用“高模很小”代替计算。
取指针分辨率 vm=1/(2pi^2 A^2)，其输入动量噪声 w_ptr=vm/beta^2=A^2。
总 w=(Vh+vm)/beta^2 直接送入 RECORDS 的完整源估计风险。

对 out-region 的光滑经典响应 u=E_ret f=E f，

E[u]=(1/(2A^3)) sum omega_k^2|b_km|^2|t_hat(omega_k)|^2。

两独立最小指针使目标场非选择平均额外能量不超过
D^2/(4vm A^3 V0)=pi^2D^2/(2A V0)。
零模仅发生 Q 位移，不注入零模动量能量；上述能量在高模。

## 3. 指针、时序与重力责任

理想仪器的 Kraus 密度是
K_y=(2pi vm)^(-1/4)exp[-(y-A_f)^2/(4vm)]。
时间有序线性耦合与它相差一个已知 Pi^2 Magnus 相位。
只有明示补偿该相位后，分辨率才是 vm；未补偿时还多出
Delta_ret(f,f)^2/(4vm) 的读数噪声。

这是一套固定背景上的代数/理想指针基准。
它的时间尺度远长于前轮约 0.087 模型固有时间的快模检验窗。
探针自身、补偿、切换及控制器的总应力尚未由 out-field 注能一个数结清；
有限场设备的推进见 KINETIC_PROBE.md。


The fixed member used for ACTUAL_HISTORY.md is explicitly t=u_(pi/4)*u_(pi/16)*kappa, with kappa an even smooth probability bump of radius pi/32. The inner convolution has radius pi/16, so every support and first-derivative bound above is unchanged; additionally ||t second derivative||_1 <= 256/pi^2.
