# 固定 incoming 态的实际齐次因果响应及统一全场极限

本页直接求本实际非静态历史上ρ,p对lapse与scale的一阶响应。
它补齐source侧齐次RSET导数，保留冻结AE处方的全部局部项。
不构造几何初态，不把齐次结果扩大为任意tensor retarded Hessian。

## 1. 固定过去、参数族和合法高阶界

取uε=U+εw，w∈C∞_c，ε在一个固定小实区间，η≤T位于原解析双圆盘严格内部。
hε=uε′，Vε=hε′+hε²。零模incoming P和非零模incoming Jost数据固定，
不能在有限片重新取一个瞬时真空。

原E4小球本身不是所有高阶导数的小球。以下提供需要的有限高阶界：
选δ>0使|z_T|exp(sδ)≤Rz、|y_T|exp(σFδ)≤Rw。
U00=0及正频λ≥s给
\[
 |\partial_\eta^jU(\eta)|
 \le\rho\,j!\delta^{-j}e^{s(\eta-T)},\qquad\eta\le T.
\tag{R1}
\]
用λ^j e^−δλ≤j!δ^−j逐系数证明。故各有限阶有显式L∞和L¹界。
对w至8阶的有限compact-support seminorm，Leibniz给
Vε及∂εVε的0…6阶时间导数共同L∞∩L¹界。
这些常数可以很大；没有把原ρ=10^−25假称为每个高jet的界。

## 2. 不是形式渐近：有精确余项的近似模式

ω=√(k²−1)，定义
\[
 A_1=-V/2,\quad A_3=(V''-V^2)/8,\quad
 A_5=(-V^{(4)}+5V'^2+6VV''-2V^3)/32,
\]
\[
 \Omega=\omega+A_1/\omega+A_3/\omega^3+A_5/\omega^5 .
\tag{R2}
\]
选有限ω0≥1，使(||A1||∞+||A3||∞+||A5||∞)/ω0²≤1/2，
那么F=Ω/ω在[1/2,3/2]。设
\[
 W=(2\Omega)^{-1/2}
  \exp[-i\omega\eta-i\int_{-\infty}^{\eta}(\Omega-\omega)ds].
\]
相位可积、Wronskian精确，incoming归一化与实际v相同。
\[
 W''+(\omega^2-V)W=RW,\quad
 R=\omega^2-V-\Omega^2-\Omega''/(2\Omega)
                         +3\Omega'^2/(4\Omega^2).
\]
z=ω^−2时有有限多项式恒等式
\[
 4F^2R=4F^2[(1-F^2)/z-V]-2FF''+3F'^2=z^3P(z).
\tag{R3}
\]
z的0、1、2次系数严格为零。P只含V至6阶；程序逐项检验这些消去。
因为F≥1/2，R和∂εR的L∞、L¹范数≤CR ω^−6，
CR由有限多项式的共同界明确构造。不假设逆k展开收敛到exact mode。

## 3. 误差与参数导数都一致可和

e=v−W满足e″+(ω²−V)e=−RW及零incoming数据。
Z=(√ωe,e′/√ω)的自由传播是范数1的旋转，扰动矩阵范数≤|V|/ω。
Duhamel与Gronwall给
\[
 \sup_{\eta,\epsilon}\|Z\|
 \le C e^{\|V\|_1/\omega}\|R\|_1/\omega=O(\omega^{-7}),
\]
所以e=O(ω^−15/2)、e′=O(ω^−13/2)。
由
Wε/W=−Ωε/(2Ω)−i∫Ωε，
得到Wε=O(ω^−3/2)、Wε′=O(ω^−1/2)。
而
\[
 (e_\epsilon)''+(\omega^2-V)e_\epsilon
 =V_\epsilon e-R_\epsilon W-RW_\epsilon
\]
有同样零incoming条件，同一估计给相同eε阶数。

r=v′−hv，e_k=|r|²+ω²|v|²，
p_k=|r|²−ω²|v|²/3。
因为|r|=O(ω^1/2)，v=O(ω^−1/2)，exact与WKB的两种应力差
及其一阶ε导数均O(ω^−6)。有限低模由光滑参数ODE理论单独处理，
本轮程序没有对它们做数值ODE积分。

## 4. 精确绑定冻结的 AE k 减项

令cΩ=h+Ω′/(2Ω)，直接算
eΩ=(Ω²+ω²+cΩ²)/(2Ω)，
pΩ=(Ω²−ω²/3+cΩ²)/(2Ω)。
有限Taylor余项（分母F≥1/2）给
\[
 e_\Omega=\omega+\frac{h^2}{2\omega}
 +\frac{V^2/8+h^2V/4-hV'/4}{\omega^3}+O(\omega^{-5}),
\]
\[
 p_\Omega=\frac{\omega}{3}+
 \frac{h^2/2-V/3}{\omega}
 +\frac{-V^2/8+h^2V/4-hV'/4+V''/12}{\omega^3}
 +O(\omega^{-5}).                                  \tag{R4}
\]
ε导数同阶一致。令b=1或1/3，中间两个分子为A,C；
冻结k减项恰是
\[
 T_k^d=bk+(A-b/2)/k+(C+A/2-b/8)/k^3.
\tag{R5}
\]
ω→k的有限Taylor余项及ε导数均O(k^−5)。
因此
\[
 \sup_{\eta,\epsilon}
 (|e_k-e_k^d|+|p_k-p_k^d|
 +|\partial_\epsilon(e_k-e_k^d)|
 +|\partial_\epsilon(p_k-p_k^d)|)\le Ck^{-5}.
\tag{R6}
\]
乘简并k²后，函数与参数导数的全场和绝对一致收敛，尾≤C/(2K²)。
可直接使用R5，不改变有限重整化；
若改用ω减项，必须加回原bK0+AK1+CK3。
这是一个C8控制方向上的C1响应定理，不是任意粗糙metric变分或完整量子引力存在定理。

## 5. 真正的 retarded 导数与全部接触项

δV=w″+2hw′，δh=w′。由固定incoming归一化，
\[
 \delta v_k(\eta)=\int_{-\infty}^{\eta}G_k(\eta,s)\delta V(s)v_k(s)ds,
\quad G_k=i[v_k(\eta)v_k^*(s)-v_k^*(\eta)v_k(s)],
\tag{R7}
\]
∂ηG|η=s=1，δr=(δv)′−hδv−w′v。
δe=2Re(r*δr+ω²v*δv)，δp把ω²改为−ω²/3。
所有前因子a^−4再贡献−4w；零模实际项贡献−6wρz，U0固定。

若B_e=−1−E1−E3+Σk²(e−e^d)+4r_an，则
\[
 \delta\rho=-6w\rho_z+
 {-\delta E1-\delta E3+\sum k^2(\delta e-\delta e^d)
            +4\delta r_{\rm an}-4wB_e\over2\pi^2a^4}
 +{4n\over\pi^2a^4}(\delta e_2-4we_2).              \tag{R8}
\]
δp同式换P1、P3、p、p_an及B_p；零模同号。
R6证明这些求和和参数导数合法交换。

明确的减项接触是
\[
 \delta A_e=hw',\quad \delta A_p=hw'-\delta V/3,
\]
\[
 \delta C_e=(V/4+h^2/4)\delta V
 +(hV/2-V'/4)w'-h\delta V'/4,
\]
\[
 \delta C_p=(-V/4+h^2/4)\delta V
 +(hV/2-V'/4)w'-h\delta V'/4+\delta V''/12.          \tag{R9}
\]
δE1=δAe，δE3=δCe+δAe/2；压力类似。
冻结KERNELS §7的H1,T1,H3,T3,r_an,p_an全部原样保留并作链式导数（此处局部v=a″/a即V，不是R7的模式v_k）：
\[
 \delta h=w',\quad \delta v=w''+2hw',\quad
 \delta a3=w'''+3hw''+3vw',\quad
 \delta a4=w^{(4)}+4hw'''+6vw''+4a3w',\quad
 \delta\ell=2w .                                   \tag{R10}
\]
例如不能漏掉显式log的贡献
δr_an|ell=H1 w/576，
δp_an|ell=(H1−T1)w/1728。
R8–R10连同冻结有限多项式给完整可计算的齐次source响应，
不是一个任意未定R，也不是只有裸θ×commutator。

若有限初片i落在w支持之后，δv(i)、δv′(i)由R7的真实过去积分给出；
只有w在i以前恒零才可设为零。
纯canonical端点导数按ACTION_BOUNDARY抵消，不能冒充额外几何初始自由度。

## 6. Lapse、Ward 与初始密度的共同检查

一般Nε=1+εν，令τ=η+εf，f′=ν且固定incoming过去f=0。
转到τ后的有效scale方向是w_eff=w−hf。
物理标量的完整响应为
\[
 \delta O=D_{w_{\rm eff}}O+fO',\qquad O=\rho,p.
\tag{R11}
\]
若∫ν≠0，f未来为常数，必须保留未来切片的实际移动；
不能当作两端都anchored的gauge变换。有限η≤T上R1及有限L¹条件仍适用。
一个充分条件是ν至7阶、w至8阶和U至9阶的有限共同界。
物理ρ与coordinate Tηη不同，后者还要显式lapse/scale因子变分。

每个ε的同一AE Ward恒等式在分布意义下微分给
\[
 \delta\rho'+3h(\delta\rho+\delta p)+3w'(\rho+p)=0.
\tag{R12}
\]
这里用R6的一致参数收敛，不额外偷换时间导数的无限和。

δκ=w′−hν，实际E=S=0上
\[
 \delta E=2h\delta\kappa-\tfrac23a^2(\delta\rho+2w\rho),
\]
\[
 \delta S=(\delta\kappa)'-\nu h'+h\delta\kappa
               +a^2(\delta p+2wp),
\quad
 \delta E'+h\delta E=2h\delta S.                    \tag{R13}
\]
anchored gauge w=hf、ν=f′使R11为δρ=fρ′、δp=fp′，从而δE=δS=0。
这同时核对过去态、度规因子、接触项和两约束的兼容性。

## 7. 验收结果及尚未完成的几何问题

本页完成实际源ρ,p对齐次N,u方向的因果一阶RSET响应，含固定AE局部项、
有限片过去依赖和全场尾的解析存在证明。
两个NOON符号的W2相同，所以mean response相同；其非Gaussian noise差不产生不同的mean retarded kernel。

没有签收任意tensor metric的全部retarded延拓、几何自身的正常初始密度、
C_geom−C_pre=C_source的实现、完整Einstein–CTP联合正窗或仪器校准。
R6的C依赖明确高阶seminorm，未作实际数值估算，不能用它宣称任意频段的小响应。
