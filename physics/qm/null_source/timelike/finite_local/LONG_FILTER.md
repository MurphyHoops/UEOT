# 全模精确时间滤波及其有限时长代价

## 1. 一个显式正核

静态 S3 的全部非零频率是 omega_k=sqrt(k^2-1)，k>=2。
定义

F0(omega)=-2 sin(pi sqrt(1+omega^2))/(pi omega^2 sqrt(1+omega^2))。

0、±i 处均可去，F0(0)=1，且所有 F0(omega_k)=0。
这不是只消若干模式的数值拟合。

令 g(s)=J0(sqrt(pi^2-s^2))，|s|<=pi。
Bessel 与指数的绝对收敛级数逐项 beta 积分给

integral_-pi^pi exp(i omega s)g(s) ds
=2 sin(pi sqrt(1+omega^2))/sqrt(1+omega^2)。

对 0<=t<=pi 定义
t0(t)=pi^-1 integral_t^pi (s-t)g(s) ds，
再偶延拓、外置0。由 integral_0^pi g=sin pi=0，
t0,t0' 的边界均匹配，t0''=g/pi，故其 Fourier 变换恰为 F0。

J1(r)>0 对0<r<=pi可由交错级数下界
1-x/2+x^2/12-x^3/144>0（x=r^2/4<=5/2）证明；
J0(pi)<0 则由四阶偶截断上界证明。
因此 g 单调增且只过零一次，t0'(t)<0、t0(t)>0，
t0(0)=J1(pi)，integral t0=1，||t0'||1=2J1(pi)<0.57。

取固定 even C-infinity 概率核 j_eps，eps=1/20，
t=t0*j_eps。它真实光滑、非负、归一、支撑长2pi+1/10，
全谱零点仍精确保持，||t'||1不增。

## 2. 精确纯零模读数及最小时长

对任意上述光滑局域空间 b、integral b=1，

f=A^-4 t' b，phi(f)=-P/(sqrt(2pi^2)A^2)。

全部高模系数严格为零。相位补偿后的最终 Gaussian P 仪器保持原高态，
不产生最终零—高模相关，source 全谱非选择保持。
这条世界管的因果补区为空，不受 LOCALITY 的短区域定理排除。

必要时长也可证明。任意 compact L1 时间核，若 integral t=1 且 Fourier
在全部 ±sqrt(k^2-1) 消失，设支撑凸包长 L。
中心平移后 |F(z)|<=||t||1 exp[(L/2)|Im z|]，
零点计数 n(r)>=2r-4。Jensen 公式给

2r-4-4log(r/2)<=log||t||1+Lr/pi。

r→∞ 推出 L>=2pi。上面的任意小 eps 构造使 infimum 恰为2pi。
没有声称光滑核达到极限，也没有把这个必要界外推为所有局域设备的普适时限。

## 3. 完整记录、时钟与校准误差

最终两指针给 z=P+N(0,w I2)，w=2pi^2 A^4 vm。
无偏源估计风险为4w mu/C+4w^2/C^2。
若开放实际准备的经典 p 标签，令 c=vw/(v+w)，则

E Var(S0|z,p)=4c(C mu-c)/C^2，
F_clock=4c(C mu-c)/A^4。

记录本身对原零模时间编码盲；w→0时，丢弃相干指针后的零模可用时钟信息趋零。
若保留相干 pointer 或增加高模时钟，须另计那些资源，不能套用此界。

对共同参考时刻上的相对计时伸缩 eps，|eps|<=0.1，
|F0((1+eps)omega_k)|<(9/2)|eps|/omega_k^2。
全高模泄漏的输入动量噪声满足

w_leak<=27pi^2(1+2n)A^2 eps^2/(4sqrt3 V0)。

令 r=w_leak/(4w_ptr)、d=delta R/(4vm)，delta R 为残留 Magnus 相位系数。
两个独立指针、固定实际输入的完整联合态迹距离满足

D<=sqrt[1-((1+r)^2+d^2)^(-1)]。

任何共同后续 CP 读数或丢弃操作都收缩此界。
eps<=0.001、|d|<=0.001、w_ptr=A^2 的有向证书给 D<0.0061。
这是条件校准预算，不是已完成实测校准；也不是任意未知输入的 diamond 界。
必须在晚于两脉冲的同一 Cauchy 时刻比较，不能混入不同结束时刻的自由时钟相位。

## 4. 最终零反作用不等于过程零应力

实际 retarded 响应满足 u_k''+omega_k^2u_k=-A^-2 b_k t'。
所有中间时刻，两场平均注能上界为
||t'||1^2/(4vm A^3 V0)，最终 high 注能精确回零。

但中间零模严格满足 u0'=-Y0 t/A^2。
因此两场额外零模正能量是

Delta E0(eta)=A t(eta)^2/(4w)。

若支撑长 L、integral t=1，则
max Delta E0>=A/(4wL^2)，
integral dproper_time Delta E0>=A^2/(4wL)。

实际 matter 零模动量平方源在作用期的增量为
Delta<S_matter,0>=A^4 t^2/(2Cw)，峰值至少A^4/(2CwL^2)。
只有 t=0 的 out-region 才恢复输入自由 P。
保持原静态几何而不加入补偿总源时，目标场已产生非零平均方程残差，
归一密度峰值至少1/(12pi^2 wL^2)。

这直接对应共同物理历史的验收：不能只检查读出后回归，
然后把探针、控制器和相互作用期间的源变化删去。
